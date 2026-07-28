# Research: Restore `lake shake` CI Gate (Alignment-Preserving)

**Task**: 580_shake_ci_gate_restore_green
**Audit date (this research)**: 2026-07-28
**Upstream SHA compared against**: `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1` (fetched live from
`upstream/main` — this SHA is unchanged since the dated audit cited in the task description, so
the 12-file split has not moved upstream-side; only local repo state could have moved it, and it
has not).
**Local HEAD**: `2e7323c93b1ad83f23c1ae547d9a99e84f2ee8b1`

## 1. Live classification (re-derived, not copied from the dated audit)

Ran the exact CI invocation:

```
lake shake --add-public --keep-implied --keep-prefix Cslib
```

Exit code: **1**. Flagged: **12 files** — the same count as the dated audit. Diffed each
flagged file against `upstream/main` with `git diff --quiet upstream/main -- <file>`:

| # | File | vs upstream/main | Shake suggestion |
|---|------|-------------------|-------------------|
| 1 | `Cslib/Algorithms/Lean/TimeM.lean` | **IDENTICAL** | add `Mathlib.Tactic.Attr.Core` |
| 2 | `Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean` | **IDENTICAL** | remove `Mathlib.Data.Finset.Max`, `Mathlib.Data.Int.Interval`; add `Mathlib.Algebra.Ring.Int.Defs`, `Mathlib.Data.Nat.Cast.Basic` |
| 3 | `Cslib/Foundations/Data/StackTape.lean` | **IDENTICAL** | add `Mathlib.Tactic.Attr.Core` |
| 4 | `Cslib/Foundations/Relation/Defs.lean` | **IDENTICAL** | remove `Mathlib.Order.Basic`; add `Mathlib.Data.Subtype`, `Mathlib.Tactic.ToDual` |
| 5 | `Cslib/Computability/Machines/Turing/SingleTape/NonDeterministic.lean` | **IDENTICAL** | remove `Cslib.Foundations.Relation.Defs` |
| 6 | `Cslib/Foundations/Relation/Confluence.lean` | **IDENTICAL** | add `Mathlib.Tactic.Attr.Core` |
| 7 | `Cslib/Foundations/Control/Monad/Free.lean` | **IDENTICAL** | add `Mathlib.Tactic.Attr.Core` |
| 8 | `Cslib/Foundations/Data/HasFresh.lean` | **DIVERGES** (locally modified) | remove `Mathlib.Analysis.Normed.Field.Lemmas`; add `Mathlib.Analysis.Normed.Group.Basic`, `Mathlib.Topology.MetricSpace.Bounded`, `Mathlib.Data.EReal.Operations`, `Mathlib.Topology.Algebra.InfiniteSum.Order` |
| 9 | `Cslib/Languages/CCS/Basic.lean` | **IDENTICAL** | add `Mathlib.Tactic.Attr.Core` |
| 10 | `Cslib/Languages/CombinatoryLogic/Defs.lean` | **IDENTICAL** | add `Mathlib.Tactic.Attr.Core` |
| 11 | `Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/LcAt.lean` | **IDENTICAL** | add `Mathlib.Data.Int.ConditionallyCompleteOrder` |
| 12 | `Cslib/Logics/Modal/Basic.lean` | **DIVERGES** (locally modified) | add `Mathlib.Order.Notation` |

**Result: the split is unchanged — 2 fixable-at-zero-alignment-cost / 10 upstream-identical.**
Both counts and the exact suggested edits match the dated audit verbatim (down to the specific
import names), so no re-triage of the fix content is needed; only re-confirmation was performed
here, live.

Also confirmed via `git log -1 upstream/main -- .github/workflows/lean_action_ci.yml`:
upstream's own `lean_action_ci.yml` has the `lake shake` step **commented out** (last touched by
upstream commit `74600063621f66f0dbfbac31963cd1219e0e05ed`, "ci: disable shake again (#397)",
2026-03-05, author Chris Henson). This corroborates the "upstream's own import debt" framing —
upstream disabled the exact same check for the exact same underlying reason (unresolved import
drift it has not gotten around to fixing).

## 2. The two locally-modified files: fixable at zero alignment cost

Both `Cslib/Logics/Modal/Basic.lean` and `Cslib/Foundations/Data/HasFresh.lean` already diverge
from upstream (substantial local rewrites — Modal/Basic.lean adds native `bot`/`imp`/`and`/`or`
constructors and a large satisfaction-lemma refactor; HasFresh.lean drops a `meta import
Lean.Elab.ConfigEval` / `import Qq` pair and renames `to_infinite` → `toInfinite`). Applying
shake's suggested import edits to these two files adds **no new divergence type** — they are
already forked, and the import line is part of that same fork. This is squarely in scope for
implementation:

- `Cslib/Logics/Modal/Basic.lean`: add `public import Mathlib.Order.Notation` to the header.
- `Cslib/Foundations/Data/HasFresh.lean`: remove `public import Mathlib.Analysis.Normed.Field.Lemmas`;
  add `public import Mathlib.Analysis.Normed.Group.Basic`,
  `public import Mathlib.Topology.MetricSpace.Bounded`,
  `public import Mathlib.Data.EReal.Operations`,
  `public import Mathlib.Topology.Algebra.InfiniteSum.Order`.

I did not apply these edits (this is a research dispatch), but I did mechanically verify the
diagnosis: `lake shake`'s own suggestion is exactly the fixed-point delta needed for these two
files to stop being flagged (that is what shake computes — the implementer should re-run
`lake shake --add-public --keep-implied --keep-prefix Cslib` and `lake build
Cslib.Logics.Modal.Basic Cslib.Foundations.Data.HasFresh` after applying, to confirm both build
clean and no longer appear in shake's output).

## 3. Exemption/scoping mechanism investigation — CONFIRMED with an important refinement

The audit-time claim was: *"`lake shake` accepts `[<MODULE>...]` arguments but checks everything
transitively reachable, and no per-file ignore mechanism was found in the repo or in the
importGraph package at audit time."*

**First correction to the audit's own framing**: `lake shake` is not implemented by the
`importGraph` Mathlib package — it is a **built-in `lake` subcommand**, shipped in Lean's own
toolchain (`Lake/CLI/Shake.lean`, at
`~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/lake/Lake/CLI/Shake.lean` for this
project's pinned toolchain, `leanprover/lean4:v4.33.0-rc1`). `lake shake --help` confirms this
(`shake  minimize imports in source files` is listed as a top-level `lake` command, not routed
through a package). This doesn't change the substantive conclusion, but the audit's pointer to
"the importGraph package" as the place to look was the wrong location — a fresh agent repeating
this investigation would find nothing there, as I did before locating the actual source.

**Per-file annotation mechanisms genuinely exist**, confirmed by reading `Shake.lean` and by
`lake shake --help`'s own "ANNOTATIONS" section:

```
* `module -- shake: keep-downstream`   preserves this module in all downstream modules
* `module -- shake: keep-all`          preserves all existing imports in this module
* `import X -- shake: keep`            preserves this specific import
```

These are **already in active use in this exact repo** — 11 files currently carry `-- shake:
keep` on a specific import, plus `Cslib/Init.lean` carries `module -- shake: keep-downstream,
shake: keep-all` (confirmed `Cslib/Init.lean` is itself byte-identical to upstream, so this
mechanism is not a local invention — upstream uses it too, just not for the 10 residual files).
So the audit's claim "no per-file ignore mechanism was found in the repo" is **REFUTED** as
literally stated: the mechanism exists, is documented in `lake shake --help`, and this repo
already uses it in 12 places.

**However, the mechanism is not usable for the 10 upstream-identical residual files**, for two
independent reasons, which is why the audit's *practical* conclusion (disable, don't
selectively-exempt) still holds:

1. **It requires editing the flagged file itself** (adding an inline `-- shake: keep` /
   `keep-all` comment to the header or import line). Doing that to any of the 10 upstream-
   identical files forks a pristine file — exactly what this task's NON-GOALS prohibit ("do not
   modify any upstream-identical file") and what the governing principle is designed to avoid
   (merge-conflict cost on every future sync, for upstream's own unfixed debt).

2. **`keep-all`/`keep-downstream` only suppress *removal* reports, not *addition* reports.**
   Read closely in `Shake.lean::visitModule`: the `addOnly` flag (set by `keep-all`, by
   `--only <mod>` for modules not listed, or by `--add-only`) causes every *currently present*
   import to be force-added into the computed `deps` set (so it is never proposed for removal).
   It does **not** touch the separate `toAdd` computation, which is driven purely by `needs`
   (the module's actual constant/elaboration dependencies) — a missing-but-required import will
   still be reported and will still make `edits` non-empty (and thus the command still exits 1),
   *even on a `keep-all`-annotated file*. Checking the 10 residual files against this: **9 of
   10 need an `add`** (only `Cslib/Computability/Machines/Turing/SingleTape/NonDeterministic.lean`
   is a pure `remove`). So even if editing pristine files were permitted, `keep-all` /
   `--only`-exclusion would silence at most 1 of the 10 files; the other 9 would still fail the
   gate. There is no annotation or CLI flag that suppresses an "add" finding short of adding the
   import.

**Module-scoping via positional `[<MODULE>...]` args was also independently confirmed
impractical**, refining rather than just repeating the audit's framing. Reading
`Shake.lean::run`/`visitModule`: `pkgs := mods.map (·.getRoot)`, and *every* loaded module whose
root matches `pkgs` gets visited and reported on — not just the modules on the path from the
given roots, but everything transitively reachable with that root name. Since `Cslib` is the
project's only root, passing any subset of `Cslib.*` module names as roots still visits every
`Cslib`-rooted module the environment ends up loading. The only way to keep a specific file out
of the report is to keep it (and everything that transitively imports it) *unreached* by the
supplied roots. Fan-in check on the 10 residual files confirms this is not viable — several are
import hubs, not leaves:

| File | # files importing it (fan-in) |
|------|-------------------------------|
| `Foundations/Relation/Defs.lean` | 7 |
| `Foundations/Relation/Confluence.lean` | 6 |
| `Languages/LambdaCalculus/LocallyNameless/Untyped/LcAt.lean` | 4 |
| `Foundations/Control/Monad/Free.lean` | 2 |
| `Languages/CombinatoryLogic/Defs.lean` | 2 |
| `Algorithms/Lean/TimeM.lean`, `Foundations/Data/StackTape.lean`, `Languages/CCS/Basic.lean` | 1 each |
| `Computability/.../MultiTape/Deterministic.lean`, `.../SingleTape/NonDeterministic.lean` | 0 |

Excluding `Foundations/Relation/Defs.lean` from the checked closure, for example, would also
exclude the 7 files (and everything transitively downstream of those) that import it — an
unacceptable coverage hole for the sake of silencing one already-known finding.

**Conclusion on item 3**: the audit's *literal* "no mechanism exists" claim is refuted (the
annotation mechanism exists and is in active local/upstream use), but its *practical*
conclusion — no way to exempt the 10-file residue without either forking pristine files or
gutting coverage — is confirmed. Disabling the CI step (with a local guard to recover
enforcement, see §5) remains the only approach consistent with both NON-GOALS.

## 4. Disabling the CI step

`.github/workflows/lean_action_ci.yml` **already diverges from upstream** — independently of
shake. `git diff upstream/main -- .github/workflows/lean_action_ci.yml` shows this fork also
carries a locally-modified `TEST_ARGS`/`test-args` (empty instead of `--wfail --iofail`, from the
separate sorry-gate work) *and* has the `lake shake` step **enabled** where upstream currently
has it **commented out**. This means:

- This file was already a legitimate target for local editing before this task; it is not a
  pristine file, so re-commenting the shake step does not newly fork anything.
- Re-disabling the step actually **reduces** the diff against upstream for that specific hunk
  (upstream's own state for this block is "commented out"), rather than increasing it — worth
  noting explicitly in the implementation commit message, since it undercuts any worry that this
  is "diverging further."

Recommended inline comment content for the disabled step (paraphrased, for the implementer to
adapt) should record: this repo's own audit date, the upstream SHA compared
(`f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`), the fact that after fixing the 2 locally-touched
files the remaining flagged set is byte-identical to `upstream/main` (upstream's own unresolved
import debt, last touched by upstream's own `74600063621f66f0dbfbac31963cd1219e0e05ed` "ci:
disable shake again (#397)"), and a pointer to the local guard script (§5) that still enforces
the gate for this fork's own code.

## 5. Recommended local guard — modeled on `scripts/check-lint-suppressions.sh`

`scripts/check-lint-suppressions.sh` is the established in-repo ratchet pattern: a checked-in
baseline (`scripts/lint-suppression-baseline.txt`) + exact/ceiling-count comparison against the
live tree + `--update`/`--list` flags + exit 0 (clean/improved) vs exit 1 (regression). It is
invoked from a **separate** workflow file, `.github/workflows/lint-hygiene.yml`, whose own header
comment states exactly the applicable rationale for this task:

> "Local-only workflow. Deliberately a SEPARATE file rather than a step added to
> lean_action_ci.yml: every workflow under .github/workflows/ is shared with the
> leanprover/cslib upstream remote, so editing one adds a conflict hunk to every future sync. A
> new file is a pure local addition and conflicts with nothing."

**One caveat for the shake guard that doesn't apply to `check-lint-suppressions.sh`**:
`lint-hygiene.yml` is deliberately a pure-text check with no Lean/Mathlib build dependency, so it
runs standalone in seconds. A shake-based guard cannot follow that exact "no build needed"
sub-pattern — `lake shake` requires built `.olean` files (it errors without a completed `lake
build --no-build`-checked state; note `--force` skips only the build **sanity check**, not the
need for built artifacts to exist). So a new shake-residue guard has two realistic placements,
both consistent with "local (non-CI, or CI-advisory)" per the task wording:

- **As a manual/local script** (`scripts/check-shake-residue.sh`), runnable standalone after a
  local `lake build`, in the same spirit as `scripts/pre-pr-check.sh`'s manual pre-PR checklist
  usage — this alone satisfies "local guard" and requires no CI wiring at all.
- **Optionally, as an additional step appended to `lean_action_ci.yml`** (which, per §4, is
  already a locally-diverging file, so adding one more step is marginal, not novel, divergence),
  positioned where the disabled `lake shake` step used to be, so it reuses that job's already-
  built environment rather than triggering a second full Mathlib build. If the sorry-gate build
  step remains red (`--wfail --iofail`, out of scope here) and the job stops on first failure,
  this step will not currently execute in live CI regardless of placement — same as the disabled
  shake step today — but it becomes live again the moment the sorry gate is resolved, with no
  further edits needed.

**Suggested script shape** (mirroring `check-lint-suppressions.sh`'s structure):

```
scripts/check-shake-residue.sh [--update|--list]
scripts/shake-residue-baseline.txt   # checked-in: exactly the 10 upstream-identical file paths
```

- No args: run `lake shake --add-public --keep-implied --keep-prefix Cslib`, extract the flagged
  file-path set from its stdout (`grep '^/'` or equivalent, then relativize), and compare against
  the baseline set.
  - **Any file in the live flagged set but not in the baseline** → FAIL (exit 1): this is new
    import debt introduced by this fork's own code, exactly the case the disabled CI step used
    to catch and that must not go unenforced.
  - **Any baseline file no longer flagged** → report as an improvement (exit 0, print a note to
    re-run `--update`): this means upstream (or a future local fix) resolved that file's import
    drift, and the baseline should tighten to lock in the gain — same ratchet-only-decreases
    philosophy as the lint-suppression baseline.
  - Exact-set equality (mirroring the task's own "assert the flagged set is EXACTLY the known
    upstream-identical residue" wording) is the right comparison, not just a ceiling count, since
    unlike blanket-suppression counts, shake findings are per-file existence, not a magnitude to
    bound.
- `--update`: rewrite the baseline from the current live flagged set (for use immediately after
  a `--fix` cycle or after confirming a new upstream sync changed the residue).
- `--list`: print the live flagged set for inspection.

This restores exactly the enforcement value the task's Definition of Done calls for: the CI gate
stops being red for reasons outside this fork's control, while any *new* import debt this fork's
own development introduces into previously-clean files is still caught (a file not on the
baseline appearing in `lake shake`'s output fails the guard, same as before disablement — just
scoped to exclude the known, upstream-owned residue).

## 6. Other CI steps — independently re-verified, all exit 0

Ran each of the four non-build steps named in the task, locally, against current `HEAD`
(`2e7323c93b1ad83f23c1ae547d9a99e84f2ee8b1`):

| Step | Command | Result |
|------|---------|--------|
| `lake test` | `lake test` | **exit 0** (warnings only: pre-existing `sorry` declarations in `Modal/Tableau/FrameSoundness.lean`, `Propositional/Tableau/Intuitionistic/{Scheme,Completeness}.lean`, `Propositional/Tableau/Minimal/Completeness.lean`, plus one pre-existing `privateInPublic` warning in `CslibTests/FreeMonad.lean` — all pre-existing and out of scope) |
| `lake exe mk_all --check` | `lake exe mk_all --check` | **exit 0** ("No update necessary") |
| `lake exe checkInitImports` | `lake exe checkInitImports` | **exit 0** (silent success) |
| `lake exe lint-style` | `lake exe lint-style` | **exit 0** |

Note: the live CI workflow invokes text-style linting via the `leanprover-community/lint-style-
action` GitHub Action (pinned to
`e6128ab22cb03b509075ae46c33727e3952ffab7`) rather than a bare `lake exe lint-style` call, but
`lake exe lint-style` is the underlying executable that action wraps, and it also passed
locally — no local reproduction of the composite Action itself was attempted (would require a
GH Actions runner or the action's own container), but this is very low risk since the only
proposed content edits (§2) are two import lines in files that already build and lint clean
today.

## 7. Summary / recommendation for the implementation phase

1. Apply the two shake-suggested edits from §2 to `Cslib/Logics/Modal/Basic.lean` and
   `Cslib/Foundations/Data/HasFresh.lean`. Rebuild both modules and re-run `lake shake
   --add-public --keep-implied --keep-prefix Cslib`; expect exactly the same 10 upstream-
   identical files (and no others) in the output, exit code still 1.
2. Do **not** touch any of the 10 upstream-identical files — confirmed genuinely unfixable
   in-place without either forking a pristine file or gutting shake's checked-module closure
   (§3). Item 3's "confirm or refute" is answered: refute the letter (mechanism exists, is
   already used 12x in this repo/upstream), confirm the substance (unusable here under this
   task's own NON-GOALS and coverage requirements).
3. Comment out the `lake shake` CI step in `.github/workflows/lean_action_ci.yml` (this reduces,
   not increases, that file's existing divergence from upstream — see §4), with an inline
   comment recording the 2026-07-28 audit date, upstream SHA
   `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`, and upstream's own disabling commit
   `74600063621f66f0dbfbac31963cd1219e0e05ed` ("ci: disable shake again (#397)").
4. Add `scripts/check-shake-residue.sh` + `scripts/shake-residue-baseline.txt` (baseline seeded
   with exactly the 10 files from §1), modeled on `scripts/check-lint-suppressions.sh`'s
   baseline/exact-set/exit-0-1/`--update`/`--list` shape (§5). Wire it in as (at minimum) a
   documented manual pre-PR script; optionally as an additional `lean_action_ci.yml` step reusing
   the existing build job, noting it won't execute live until the (out-of-scope) sorry gate is
   green, same as the step it replaces today.
5. Re-run the four commands in §6 after the above edits to confirm they remain exit 0 (no reason
   to expect regression — none of the edits touch test code, `Cslib.lean`, `Cslib/Init.lean`
   imports, or lint-style-relevant formatting).

## Files referenced

- `/home/benjamin/Projects/cslib/.github/workflows/lean_action_ci.yml`
- `/home/benjamin/Projects/cslib/.github/workflows/lint-hygiene.yml`
- `/home/benjamin/Projects/cslib/scripts/check-lint-suppressions.sh`
- `/home/benjamin/Projects/cslib/scripts/lint-suppression-baseline.txt`
- `/home/benjamin/Projects/cslib/scripts/pre-pr-check.sh`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean`
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Data/HasFresh.lean`
- `/home/benjamin/Projects/cslib/Cslib/Init.lean`
- `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/lake/Lake/CLI/Shake.lean` (lake
  shake source, read directly for the annotation/CLI semantics analysis in §3)
