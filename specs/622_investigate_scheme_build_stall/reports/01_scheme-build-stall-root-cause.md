# Scheme.lean Build Stall — Root Cause

**Task**: 622 — Investigate why `Tableau/Intuitionistic/Scheme.lean` never completes a build
**Date**: 2026-08-10
**Status**: Resolved — premise falsified, no code defect
**HEAD**: `b83ae232`

---

## 1. Verdict (read this first)

**There is no build stall. `lake build` completes on `main`, green, in 3 minutes 42 seconds.**

The task premise — "A full `lake build` on `main` does not complete; it stalls indefinitely
while elaborating `Scheme.lean`" — is **false as stated**. It was measured directly:

```
Build completed successfully (3325 jobs).
FULL_BUILD_SECONDS=222.31
errors: 0
```

`Scheme.lean` itself elaborates in **18 seconds** under `lake build`, producing a 1.8 MB
`.olean` and a 217 KB `.c`.

The 92-minute hang was real, but it was **an artifact of the command used to reproduce it**, not
a property of the file. Invoking `lean` on `Scheme.lean` **without Lake's `--setup` argument**
diverges; invoking it **with** `--setup` — which is what `lake build` always does — succeeds in
~20 seconds.

**Recommended disposition: close as NOT-A-BUG.** No change to `Scheme.lean` is warranted.
Section 6 lists two small, genuinely-useful hygiene follow-ups that are independent of the
stall.

---

## 2. The measurement that settles it

Every row below was run at `HEAD = b83ae232` with a clean `Cslib/` working tree.

| # | Command | Result |
|---|---------|--------|
| 1 | `lake build` (full, `defaultTargets = Cslib`) | **green, 3325 jobs, 0 errors, 222.31 s** |
| 2 | `lake build` (re-run, all cached) | **green, 1.68 s** |
| 3 | `lake build Cslib.…Intuitionistic.Scheme` | **green, 26.08 s total (Scheme itself 18 s)** |
| 4 | `lake env lean --setup Scheme.setup.json Scheme.lean` | **exit 0, 23.78 s** |
| 5 | `lake env lean Scheme.lean` *(no `--setup`)* | **HANGS — killed at >19 min** |
| 6 | `lake env lean -Ddebug.skipKernelTC=true` (no `--setup`) | **HANGS — killed at 400 s** |

Rows 4 and 5 differ **only** in the presence of `--setup`. That single flag is the entire
difference between a 24-second success and an unbounded hang.

### The hang signature matches the report exactly

Row 5 reproduced the reported symptom precisely, which is what confirms it is the same event:

| Reported symptom | Row 5 observation |
|------------------|-------------------|
| single `lean` worker at ~101% CPU | 101–128% CPU, one core |
| resident memory ~1.3 GB, stable | RSS 1,340,544 KB, byte-identical across samples |
| no completion, no error | ran >19 min, no diagnostic emitted |
| `lake` exit 143 (SIGTERM) | `lake env lean` forwards the child's SIGTERM status → 143 |
| no `.olean` produced | `lake env lean` without `-o` **never writes an `.olean` at all** |

That last row is the tell. The task description infers from the missing `.olean` that the module
"has never successfully built in this checkout". The correct reading is the opposite: the
invocation that hung was **never asked to produce one**. Absence of the artifact is a property
of the command line, not evidence about the file.

---

## 3. Where the time actually goes (the hang, isolated)

Even though the hang is not on the real build path, it was localised, because doing so is what
proved the file itself is sound.

Truncating the file at declaration boundaries and elaborating each prefix (all without
`--setup`):

| Prefix | Lines | Time |
|--------|-------|------|
| 1 … 6248 | 6,248 | 10.10 s |
| 1 … 7023 | 7,023 | 14.95 s |
| 1 … 8310 | 8,310 | **15.89 s** |
| 1 … 9631 | 9,631 | **>420 s (timeout)** |

So 84% of the file elaborates in ~16 seconds, and the entire cost sits in the single declaration
spanning lines **8311–9631**:

- `intExpandBranches_openBranch_sat` — a ~1,320-line `private lemma` with 24 hypotheses,
  concluding an 11-conjunct existential.

Its proof shape is the stressor:

```
induction pending, pendingExp, pendingNW, pendingEdges, pendingFuels, done, doneExp,
    doneNW, doneEdges, doneFuels
    using intExpandBranches.go.induct (closurePred := closurePred) with
```

That is a **10-target simultaneous induction** using the functional-induction principle derived
from `intExpandBranches.go` (`Scheme.lean:5453`), a well-founded recursive definition with a
lexicographic `termination_by ((pendingFuels ++ doneFuels).map (3 ^ ·)).sum, pending.length)`.
Each of the 10 cases then `intro`s ~30 hypotheses. The motive is correspondingly enormous.

Two negative results worth recording, because they rule out the obvious hypotheses:

- **Not the kernel.** `-Ddebug.skipKernelTC=true` did not help (row 6). The divergence is in
  elaboration, not in `addDecl`.
- **Not heartbeat-bounded.** Row 6 ran 400 s on *default* `maxHeartbeats` (200000) without
  emitting a deterministic-timeout error. Whatever loops does not check heartbeats. This is also
  why the file has no `set_option maxHeartbeats` masking anything — it has **zero** `set_option`
  lines, and adding one would not have changed the behaviour.

The mechanism is consistent with the Lean 4.33 module system: without `--setup`, `lean` has no
module-artifact configuration, so the `module` / `public import` exposure and reducibility
information that Lake supplies is absent. `intExpandBranches.go.induct`, `…go.eq_def`, and the
`simp only []` unfoldings in the case arms then operate against differently-exposed imported
definitions, and the motive unification blows up. With correct setup the same proof discharges
in seconds.

---

## 4. Why the file is fine — independent corroboration

Beyond the direct measurement, the build history confirms `Scheme.lean` has been building all
along:

- `Completeness.lean:11` carries `public import …Intuitionistic.Scheme`. Lake cannot build a
  module whose import has no `.olean`. `Completeness.olean` is dated **08:59**, and
  `DecisionProcedure.olean` (transitively downstream) **07:47** — so `Scheme.olean` existed at
  both times.
- `Scheme.trace` (09:03:18) records a **successful** build with concrete output hashes
  (`140aff11b3342d89.olean`, matching `Scheme.olean.hash`).
- The last commit changing *code* in `Scheme.lean` is `f78d0556` (07:32). Everything after it —
  `54a8ad8a`, `0bdf038d`, `a0aafc5e`, `7e8b56b1` (08:46 → 09:04) — is comment and docstring
  rewriting only. Every diff hunk since `f78d0556` lands in prose. **The elaboration workload has
  not changed since the last known-good build.**

The file is also genuinely **sorry-free**: all 26 occurrences of the string `sorry` are prose
inside docstrings discussing historical obligations; none is a `sorry` term.

---

## 5. Reconstructed timeline

| Time | Event |
|------|-------|
| 07:32 | `f78d0556` — last *code* change to `Scheme.lean` |
| 07:47 | `DecisionProcedure.olean` built ⇒ `Scheme.olean` existed |
| 08:46–09:04 | Comment-only commits touch `Scheme.lean` |
| 08:59 | `Completeness.olean` rebuilt ⇒ `Scheme.olean` existed again |
| 09:03:18 | `Scheme.trace` records a successful build |
| ~11:56 | `Propositional/Defs.lean` edited (connective-notation experiment); `Defs`, `Rules`, `Expansion`, `Soundness`, `Minimal.Soundness` rebuild at 11:57 |
| 11:57 → ~13:29 | The 92-minute run — a `lean` invocation on `Scheme.lean` **without `--setup`** — hangs and is SIGTERMed (exit 143), leaving `.hash`/`.trace` bookkeeping but no `.olean` |
| 13:31 | `Defs.lean` reverted, leaving `Defs.olean` (11:56) stale on disk |
| 14:06 | This investigation: `lake build` green in 222 s |

The stale `Defs.olean` is a second reason the ad-hoc `lake env lean` runs were untrustworthy:
they bypass Lake's dependency resolution and silently consume whatever `.olean` files happen to
be on disk. `lake build` rebuilt `Defs` correctly in 1.2 s and the staleness is now resolved.

---

## 6. Answers to the task's suggested starting points

| Suggested step | Finding |
|----------------|---------|
| Establish termination (slow vs divergent) | **Neither.** Under the real build path it is fast (18 s). The divergence exists only under the `--setup`-less invocation. |
| Profile the heaviest declarations | Done by prefix bisection: 100% of the anomalous cost is `intExpandBranches_openBranch_sat` (8311–9631). Under `lake build` that same lemma is unremarkable. |
| Check `maxHeartbeats` / `maxRecDepth` overrides masking a runaway | **None exist** — the file has zero `set_option` lines. Nothing is being masked. |
| Is the module reachable from the `Cslib.lean` barrel? | Yes, `Cslib.lean:636`. It is also pulled in via `Completeness.lean`, so it is *not* an unreachable leaf. |
| Is it new/unfinished work that was never green? | **No.** It has been green repeatedly today (§4) and is sorry-free. |
| Bisect against history | Unnecessary — no code has changed since the last known-good build. |

---

## 7. Recommendations

**Primary: close task 622 as NOT-A-BUG.** No edit to `Scheme.lean`, and no plan phase, is
justified. `lake build` is green and CI step 1 is not blocked.

Two optional, independent hygiene items surfaced along the way. Neither is a defect and neither
should be bundled into this task's closure:

1. **Barrel inconsistency.** `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` imports
   `Rules`, `Expansion`, `Soundness`, `Completeness`, `DecisionProcedure` — but **not** `Scheme`,
   even though the top-level `Cslib.lean` does import it (line 636). Harmless today because
   `Completeness` pulls `Scheme` in transitively, but it makes the sub-barrel a misleading
   description of its own directory.

2. **Tooling guidance.** `lake env lean <file>` is not a sound way to check a `module`-system
   file in this repo: it omits `--setup`, bypasses dependency resolution, consumes stale
   `.olean`s, and — as here — can diverge where the real build succeeds. The correct single-file
   check is `lake build <Module.Name>`, or `lake env lean --setup <module>.setup.json <file>` if
   raw `lean` output is genuinely needed. Worth a line in the Lean/CSLib tooling context so this
   misdiagnosis is not repeated.

---

## 8. Reproduction commands

```bash
# Green, authoritative:
lake build                                                    # 222 s, 3325 jobs, 0 errors
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme   # 26 s

# Green, raw lean with correct setup:
lake env lean --setup \
  .lake/build/ir/Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.setup.json \
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean        # 23.78 s

# Reproduces the reported hang (do not use this to check files):
lake env lean Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean   # never returns
```
