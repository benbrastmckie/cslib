# Research: Scoping `pre-pr-check.sh` step 1's sorry gate

**Task type**: cslib (tooling / gate-scoping — explicitly NOT proof work)
**Scope**: `scripts/pre-pr-check.sh`, `scripts/check-sorry-suppressions.sh`, `scripts/README.md`
**Explicit non-goals** (from task description, upheld throughout): do not narrow step 5
(`lake build --wfail --iofail`); do not resolve any existing sorry.

---

## 1. Executive summary

The decisive finding is stronger than the task description assumed, and it changes which of the
three offered designs is viable:

1. **Step 1's sorry-detection logic is a verbatim duplicate of `check-sorry-suppressions.sh`'s
   `count_sorries()`** — same four-step discrimination rule (block-comment strip via the same
   `perl -0777` expression, line-comment strip, `warn.sorry` exclusion, `\bsorry\b` count).
2. **Step 8's baseline already contains step 1's entire failure set, per file, exactly.**
   Measured: step 1's 24 hits across 6 files are byte-for-byte the first six rows of
   `scripts/sorry-suppression-baseline.txt` (7, 2, 12, 1, 1, 1 → 24).
3. **Step 8's scan root (`Cslib`) is a strict superset of step 1's four hand-picked trees.**

Therefore option (a) from the task — "a frozen per-file sorry baseline it ratchets against" — is
not a *new* gate to build. It already exists as step 8. Implementing it a second time inside
step 1 would produce a strict-subset duplicate that can never report a failure step 8 misses.
The task's own instruction ("prefer reusing its baseline machinery over inventing a second one")
taken to its conclusion means: **step 1's baseline IS `sorry-suppression-baseline.txt`**, and
step 1 should become a *scoped invocation* of that gate, not a parallel implementation.

Second decisive finding, which rules out option (b) standing alone:

4. **A changed-files mode does NOT by itself make step 1 satisfiable.** Measured against
   `git merge-base HEAD origin/main`: 114 `.lean` files under the four trees are changed, and
   **3 of the 6 debt-carrying files are among them** (`Bundle/SuccRelation.lean`,
   `Bundle/UntilSinceCoherence.lean`, `BXCanonical/Frame.lean`). A changed-files gate that still
   fails on ANY sorry reproduces exactly the same wall, just narrower. Changed-files scoping is a
   useful *additional* narrowing; it is not a substitute for changing the failure predicate from
   "any sorry" to "above baseline".

**Recommendation**: change the predicate (mandatory), reusing step 8's baseline via a new
`--scope` filter on `check-sorry-suppressions.sh`; add `--changed` as an optional extra narrowing
behind a flag (nice-to-have, not load-bearing); fix the wording. Full design in §5.

---

## 2. Verified measurements (this dispatch, 2026-07-29)

All figures below were re-derived directly, not carried over from the task description.

### 2.1 Step 1's live failure set

Reproduced step 1's exact pipeline over its four trees:

| Sorry hits | File |
|---|---|
| 7 | `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` |
| 2 | `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` |
| 12 | `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` |
| 1 | `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` |
| 1 | `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` |
| 1 | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` |
| **24** | **6 files** |

Matches the task description exactly.

### 2.2 The step-8 baseline (non-comment rows)

```
7  7  Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean
2  2  Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean
7 12  Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean
1  1  Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean
1  1  Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean
0  1  Cslib/Logics/Modal/Tableau/FrameSoundness.lean
0  1  Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean
0  2  Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean
0  1  Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean
```

The sorry column of rows 1-6 is *identical* to §2.1. Rows 7-9 (4 sorries) are the
`Cslib/Logics/Propositional/Tableau/*` files that lie **outside** step 1's four trees — this is
the same asymmetry the task description flags for step 5, and it confirms step 8 (whole-`Cslib`)
already covers what step 1 cannot see.

### 2.3 Step 8 status

```
markers: 18 (baseline ceiling 18); sorries: 28 (baseline ceiling 28)
OK: sorry/suppression counts match the baseline (or improved).   exit=0
```

Ratchet is exactly at baseline. 28 = 24 (in step 1's trees) + 4 (Propositional/Tableau).

### 2.4 Logic-equivalence of step 1 and `count_sorries()`

| | step 1 (`pre-pr-check.sh:17-18`) | `count_sorries()` (`check-sorry-suppressions.sh:112-124`) |
|---|---|---|
| Block-comment strip | `perl -0777 -pe 's/\/-.*?-\///gs'` | identical expression |
| Line-comment strip | `sed -e 's/--.*//'` | identical |
| `warn.sorry` exclusion | `grep -v 'warn\.sorry'` (after `grep -n`) | `grep -v 'warn\.sorry'` (before match) |
| Match | `grep -n '\bsorry\b'` (counts **lines**) | `grep -oE '\bsorry\b' \| wc -l` (counts **occurrences**) |

The only semantic difference is lines-vs-occurrences, which is currently vacuous on this tree
(both yield 24). Reuse eliminates the discrepancy entirely rather than preserving two near-copies
of a rule whose header comment explicitly says "do not weaken".

### 2.5 Changed-files feasibility probe

- `git merge-base HEAD origin/main` = `20712f65…`; 366 files / 132 `.lean` changed vs HEAD.
- Restricted to the four trees: **114** `.lean` files changed.
- Of the 6 debt files, **3 are in the changed set** (SuccRelation, UntilSinceCoherence, Frame).
- `git merge-base HEAD upstream/main` = `f36649cf…` → 626 `.lean` changed (far too coarse to be
  a useful default; this fork has diverged substantially from `leanprover/cslib`).
- Working tree at time of measurement: 0 uncommitted, 0 staged, 0 untracked `.lean` files.

**Interpretation**: `origin/main` is the only sane default base ref; `upstream/main` is not.
And, per §1 finding 4, changed-files narrowing alone leaves 3 debt files in scope.

---

## 3. Ownership, blast radius, and constraints

### 3.1 Fork-local files (safe to modify freely)

Verified against `upstream/main` (`leanprover/cslib`):

| File | Upstream? |
|---|---|
| `scripts/pre-pr-check.sh` | **fork-local** (absent upstream) |
| `scripts/check-sorry-suppressions.sh` | **fork-local** |
| `scripts/sorry-suppression-baseline.txt` | **fork-local** |
| `scripts/README.md` | **exists upstream** — edits add sync-conflict surface |

`scripts/README.md` already carries fork-local sections added by prior gate work (shake residue,
axiom census, sorry/suppression), so the conflict surface is pre-accepted; keep edits additive
and localized to the existing "Sorry/suppression volume ratchet" section plus a short note under
a pre-pr-check heading, rather than restructuring the file.

### 3.2 Step numbering is a cross-file contract

Step numbers in `pre-pr-check.sh` are cited by name in four places outside the script:

- `scripts/README.md:57` — "step 7 of `pre-pr-check.sh`" (shake)
- `scripts/README.md:83` — "step 9 of `pre-pr-check.sh`" (axiom census)
- `scripts/README.md:101` — "step 8 of `pre-pr-check.sh`" (sorry/suppression)
- `docs/lint-suppression-policy.md:11` — "step 6 of `scripts/pre-pr-check.sh`"

Plus three in-script header comments: `check-sorry-suppressions.sh:62` ("step 1 of
`scripts/pre-pr-check.sh`'s local checks" — note this comment is **already inaccurate**, since
the script is wired as step 8, not step 1), `check-shake-residue.sh:41`,
`check-axiom-census.sh:46`.

**Consequence**: any design that renumbers steps incurs a 7-site documentation edit. This is the
main argument against the "just delete step 1" variant (§5, Option 2).

### 3.3 `pre-pr-check.sh` is not wired into CI or `/pr`

- `.github/workflows/lean_action_ci.yml` invokes `check-sorry-suppressions.sh` and
  `check-axiom-census.sh` **directly**, never via `pre-pr-check.sh`.
- `.github/workflows/lint-hygiene.yml` invokes `check-lint-suppressions.sh` directly.
- The `/pr` command's 7-step CI pipeline (`lake build`, `checkInitImports`, `lake lint`,
  `lint-style`, `lake test`, `mk_all`, …) does **not** call `pre-pr-check.sh` at all and has no
  sorry step of its own.

So `pre-pr-check.sh` is purely a **local developer/agent pre-flight aggregator**. Changing step 1
cannot regress CI. This is a low-blast-radius change.

### 3.4 The "completion bar" phrasing is per-plan, not templated

Grep across `agent-system/extensions/cslib/`, `.claude/skills/skill-cslib-*/`, and
`.claude/agents/cslib-*.md` found **zero** occurrences of "pre-pr-check", "passes end to end", or
an equivalent completion-bar template. Every citation lives in per-task plan/summary prose under
`specs/`. Consequence: **no extension source-store change is required or appropriate here**
(and the source-store/deploy-boundary rule is not engaged, since `scripts/` is a real tracked
repo directory, not a `.claude/**` deploy artifact). The durable fix for future plans is that the
gate itself becomes satisfiable, so the natural phrasing stops being a trap.

---

## 4. Reuse check (CSLib reuse-first protocol)

Applied to the tooling layer rather than the Lean layer, since this task authors no Lean.

| Candidate abstraction | Already exists? | Verdict |
|---|---|---|
| Per-file sorry-count ratchet w/ frozen baseline | **Yes** — `check-sorry-suppressions.sh` + `sorry-suppression-baseline.txt` | **Reuse.** Do not author a second baseline. |
| Exact-set frozen baseline (path in/out) | Yes — `check-shake-residue.sh` | Wrong shape here (we need counts, not set membership). |
| Per-file count ceiling ratchet | Yes — `check-lint-suppressions.sh` | Same shape as the sorry gate; already the model the sorry gate was built from. Nothing further to borrow. |
| Sorry discrimination rule (comment stripping etc.) | **Yes** — `count_sorries()` | **Reuse.** Deleting step 1's copy is a net simplification. |
| Changed-files / merge-base helper | **No** — only `create-adaptation-pr.sh` uses `git merge-base`, for an unrelated bump-branch workflow | New code, but small and self-contained. |
| `--update` / `--list` / exit-code-2 environment-error convention | Yes — shared by all three ratchet scripts | **Follow it exactly** for any new flag. |

No new abstraction is warranted beyond a scope filter and (optionally) a changed-files resolver.

---

## 5. Design options

### Option 1 (RECOMMENDED) — step 1 delegates to `check-sorry-suppressions.sh --scope`

Add a scope filter to the existing gate; step 1 calls it with the four trees. Step numbering is
preserved; no second baseline; the duplicated discrimination rule is deleted.

```
check-sorry-suppressions.sh [--list|--update] [--scope PATH...] [--changed [--base REF]]
```

Step 1 becomes roughly:

```bash
echo "1. Sorry ratchet over PR-scope trees (baseline-relative; fails only on NEW debt)..."
if ! bash "$(dirname "${BASH_SOURCE[0]}")/check-sorry-suppressions.sh" --scope \
    Cslib/Foundations/Logic Cslib/Logics/Modal Cslib/Logics/Temporal Cslib/Logics/Bimodal; then
  echo "  FAIL: new sorry debt in PR-scope trees beyond the baseline"
  failed=1
fi
```

**Pros**: satisfiable by construction on a clean tree; single baseline; single discrimination
rule; step numbers unchanged (zero doc renumbering); keeps step 1's fast-fail-before-build
position (the gate is a pure text sweep with no build dependency — `check-sorry-suppressions.sh`
header, "WHAT THIS GATE DOES NOT NEED"); the scoped output names PR-scope files first, which is
what the "PR scope" label was reaching for.

**Cons**: step 1 is now a strict-subset duplicate of step 8 in *failure power* — it can never
fail where step 8 passes. This is honest and worth stating in the script comment: step 1's value
is **early, scoped feedback**, not additional coverage.

### Option 2 — delete step 1, move the sorry ratchet to position 1

Simplest possible fix: remove step 1 entirely, renumber 2-9 → 1-8, and move the
`check-sorry-suppressions.sh` invocation to the front (it needs no build).

**Pros**: zero new code; zero redundancy; strictly more coverage than today's step 1 (whole
`Cslib`, catching the 3 Propositional/Tableau files step 1 is blind to).
**Cons**: 7-site renumbering edit across `scripts/README.md` (×3), `docs/lint-suppression-policy.md`,
and three script header comments (§3.2); loses the four-tree focus entirely; a larger diff in a
file other tasks cite by step number. **Not recommended** on cost/benefit grounds, but it is the
technically cleanest end state and should be recorded as a considered-and-rejected alternative.

### Option 3 — scoped disclosure + hard-fail-on-above-baseline

Option 1 plus an always-printed informational block listing pre-existing in-scope debt
("this PR's scope contains 24 known sorries across 6 files; you added 0"). Costs a few lines;
turns the step into something a PR author actually wants to read. Recommended as a **sub-item of
Option 1**, not a separate option.

### The `--changed` sub-mode (optional, non-load-bearing)

Genuinely new signal — "which files does *this branch* touch, and do any carry debt" — but per
§1 finding 4 it does not fix satisfiability and must never be the sole predicate. Recommend
implementing it as an opt-in flag, defaulting OFF in `pre-pr-check.sh`, so the default local run
stays deterministic and independent of git state.

---

## 6. Implementation constraints the plan MUST encode

These are correctness traps discovered while reading the existing gate's contracts. Each maps to
an explicit rule in `check-sorry-suppressions.sh`'s header ("EXIT-CODE CONTRACT (READ BEFORE
CHANGING)").

1. **`--update` must refuse `--scope` / `--changed`.** A scoped `--update` would rewrite
   `sorry-suppression-baseline.txt` from a partial sweep, silently deleting rows for
   out-of-scope files (e.g. the 3 Propositional/Tableau entries) and thereby *lowering* the
   whole-tree ceiling to zero for them — a silent ratchet break. Must `exit 2` with a usage
   error. **This is the single highest-risk item in the change.**

2. **Distinguish "scope matched nothing" from "scan root is broken".** The existing contract
   makes a zero-file `find` a fatal `exit 2` ("a scan root that resolves to nothing must never
   read as clean"). That must be preserved for `--scope` (a mistyped path is an error), but
   `--changed` legitimately yields zero files when the branch touched no in-scope `.lean` file —
   that is `exit 0` with an explicit "no changed .lean files in scope; nothing to check" line.
   Two different conditions; do not collapse them.

3. **Baseline comparison must stay whole-file-keyed.** Scoping filters *which files are swept*,
   never *which baseline rows are loaded*. Loading a filtered baseline would let an out-of-scope
   file's row go missing and read as ceiling 0.

4. **The improvements / ACTION REQUIRED message must not suggest a scoped `--update`.** When a
   scoped run detects an improvement, the remediation command it prints must be the bare,
   whole-tree `bash scripts/check-sorry-suppressions.sh --update` (per constraint 1).

5. **`--changed` git mechanics**:
   - default base `origin/main`, overridable via `--base REF`; resolve with
     `git merge-base HEAD <base>`;
   - union of `git diff --name-only --diff-filter=d <mb> HEAD`, `git diff --name-only
     --diff-filter=d HEAD` (unstaged), and `git diff --name-only --diff-filter=d --cached`;
     optionally `git ls-files --others --exclude-standard` for new untracked files;
   - `--diff-filter=d` (lowercase) excludes deletions so vanished paths are never stat'd;
   - unresolvable base ref, absent remote, or detached HEAD → `exit 2` (environment error),
     never a silent empty/clean set — matching the existing contract's philosophy;
   - do **not** default to `upstream/main` (626 changed `.lean` files; useless as a filter).

6. **Wording fix (explicitly required by the task).** `"1. Checking for sorry instances in PR
   scope..."` is false on two counts: it is not PR-scoped (it is four hand-picked whole trees),
   and it is not a check for "instances" in any actionable sense (it fails on frozen debt). New
   text must name the predicate: baseline-relative, fails only on NEW debt, and name the trees.
   The `Cslib.Foundations.Logic` / four-tree set is itself a stale artifact of an earlier PR
   series (see step 4's hand-picked module list) — say so in the comment so the next reader knows
   the list is not a live definition of "PR scope".

7. **Fix the stale cross-reference** at `check-sorry-suppressions.sh:62`, which already claims
   the script "can run as step 1 of `scripts/pre-pr-check.sh`'s local checks" — it is wired as
   step 8. Under Option 1 it becomes true of *both* steps 1 and 8, which is worth stating
   precisely rather than leaving ambiguous.

8. **Update the step-8/9 rationale comment** (`pre-pr-check.sh:95-99`). It currently justifies
   the split by saying step 1 "fails on ANY sorry found there" — that sentence is exactly what
   this task removes, and leaving it would leave the file self-contradictory. Replace it with
   the honest new relationship: step 1 = early, scoped, same-baseline fast-fail; step 8 =
   whole-tree authority. Also record that neither step 1 nor step 8 substitutes for step 5, and
   preserve the existing note that steps 1 and 5 have different scopes (the three
   `Propositional/Tableau/*` files trip step 5 but are invisible to step 1).

9. **Non-goal guardrails to restate in the plan**: no edit to step 5; no edit to any file under
   `Cslib/`; no change to `sorry-suppression-baseline.txt` contents (the ratchet is currently
   exactly at baseline — §2.3 — and must remain so, byte-identical, after this change).

---

## 7. Verification plan for the implementer

The gate's own precedent (the way the sorry/axiom gates were proven) is to demonstrate **both**
the pass path and the fail path, then restore a bit-identical tree.

1. **Baseline invariance**: `git diff --stat scripts/sorry-suppression-baseline.txt` is empty
   after all edits; `bash scripts/check-sorry-suppressions.sh` still prints
   `markers: 18 … sorries: 28 …` and exits 0.
2. **Step 1 now passes**: `bash scripts/pre-pr-check.sh` — step 1 green on the unmodified tree.
   (Step 5 will still fail; that is the declared non-goal and is expected.)
3. **Step 1 still catches regressions**: add a scratch `.lean` file under one of the four trees
   containing a bare code-position `sorry`, confirm step 1 exits nonzero naming that file,
   then delete it and re-confirm green.
4. **Out-of-scope regressions are NOT caught by step 1 but ARE by step 8**: same scratch probe
   under `Cslib/Logics/Propositional/`, confirm step 1 green / step 8 red. This is the
   experiment that documents the scope asymmetry rather than asserting it.
5. **`--update` guard**: `bash scripts/check-sorry-suppressions.sh --update --scope Cslib/Logics/Modal`
   exits 2 without writing the baseline (verify mtime/content unchanged).
6. **Bogus scope is an error, empty changed-set is not**:
   `--scope Cslib/Does/Not/Exist` → exit 2; `--changed --base HEAD` (empty diff) → exit 0 with
   the "nothing to check" line.
7. **Doc consistency**: grep that every surviving "step N of `pre-pr-check.sh`" citation
   (§3.2, 7 sites) still names the correct step after the change — under Option 1 none should
   need editing, which is itself the check.
8. Optional: `shellcheck` is not installed in this environment (prior tasks recorded the same);
   the path-triggered `shellcheck.yml` workflow will sweep on push. Model any new code closely on
   the three existing passing ratchet scripts.

---

## 8. Answers to the task's open questions

| Question posed by the task | Finding |
|---|---|
| Frozen per-file baseline, changed-files mode, or both? | **Baseline predicate is mandatory; changed-files alone provably does not fix it** (3 of 6 debt files are in the changed set). Recommend baseline-by-delegation now, `--changed` as an opt-in extra. |
| Reuse `check-sorry-suppressions.sh`'s machinery? | **Yes, and further than expected** — its baseline already contains step 1's exact failure set, and its `count_sorries()` is step 1's logic verbatim. Reuse means *delegation*, not copying. |
| Fix the misleading "in PR scope" wording | Required; §6 item 6. Also fix the two stale companion comments, §6 items 7-8. |
| Does this risk weakening the sorry gates? | No. Step 8 (whole-`Cslib`, in CI) and step 5 (`--wfail`, mirrors CI) are untouched and retain full authority. Step 1 today contributes **zero** unique failure coverage — every file it can flag is already in step 8's baseline and scan root — so making it baseline-relative removes no real enforcement. |

---

## 9. Sorry-free / zero-debt compliance

This task authors **no Lean**. The zero-debt completion gate is satisfied vacuously on the proof
axis: no `sorry`, no new axiom, no Option-B deferral is proposed or needed. The tooling-side
analogue — "do not weaken a ratchet" — is preserved explicitly by §6 items 1, 3, 9 and verified
by §7 items 1, 4, 5.

No blockers identified. The task is well-posed, low-risk, and fully specified by the findings
above; it does not warrant `[BLOCKED]` escalation or decomposition.
