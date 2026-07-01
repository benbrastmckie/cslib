# Implementation Summary: Task #458

- **Task**: 458 - Fix lake shake import findings in shared Measure module + Classical consumer (task 455 vet)
- **Plan**: plans/01_shake-import-hygiene.md
- **Status**: Implemented

## What Was Done

Applied the two verified `lake shake` import-hygiene edits from the task 455 vet, plus one
necessary follow-on fix discovered during dependent-module verification:

1. **`Cslib/Foundations/Logic/Tableau/Measure.lean`** (line 11): removed the unused import
   `import Mathlib.Algebra.BigOperators.Group.List.Basic`. `List.sum_cons`/`List.map_cons`/
   `List.length_cons` uses at line 48 resolve via other already-present imports.

2. **`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`** (line 11): replaced
   `public import Cslib.Logics.Propositional.Tableau.Classical.Soundness` with two direct
   public imports: `Cslib.Logics.Propositional.Tableau.Classical.Expansion` and
   `Cslib.Logics.Propositional.Semantics.Bool`. Completeness.lean itself uses zero of
   Soundness's own declarations and heavily uses Expansion/Bool decls that were previously
   obtained transitively through Soundness.

3. **`Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean`** (line 11,
   deviation): added a direct `public import Cslib.Logics.Propositional.Tableau.Classical.Soundness`.
   This was **not** in the original plan. Verification of dependent modules (per the task's
   explicit instruction to check dependents, beyond what the plan's two-module scoped build
   covers) surfaced that `DecisionProcedure.lean` directly calls `classicalTableau_sound`
   (defined in `Soundness.lean`), which it had been obtaining transitively through
   `Completeness.lean`'s old `public import ...Soundness`. Removing that transitive path (edit
   #2) broke `DecisionProcedure.lean` with `Unknown identifier 'classicalTableau_sound'`. Adding
   the direct import restores availability with no proof/declaration changes and is fully
   consistent with the shake philosophy (direct imports over relying on transitive publicity).

## Verification

- `lake build Cslib.Foundations.Logic.Tableau.Measure Cslib.Logics.Propositional.Tableau.Classical.Completeness` — green, no errors.
- Baseline comparison (via `git stash`/`git stash pop` around the two edits): warning count for
  the same scoped build is **52 before and 52 after** — identical, confirming import-hygiene-only
  impact (all 52 are pre-existing style/environment-linter warnings unrelated to the changed
  import lines, e.g. `unusedSectionVars`, `unusedSimpArgs`, `longLine`, `flexible`).
- Dependent modules rebuilt green: `Cslib.Logics.Propositional.Tableau.Classical`,
  `Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure` (after the follow-on import
  fix), `Cslib.Foundations.Logic.Tableau`.
- `grep -n "\bsorry\b"` on all three touched files: zero sorries (two doc-comment mentions of
  the phrase "sorry-free" in `DecisionProcedure.lean`, not actual `sorry` tactics).
- `grep -n "^axiom "` on all three touched files: zero new axioms.
- `import Cslib.Init` preserved (untouched) in all three files.

### Known blockers on wider CI (out of scope, not caused by this task)

- `lake exe checkInitImports` failed: a concurrent session is mid-edit on
  `Cslib/Logics/Modal/Tableau/*` (task 457's territory), leaving stale/missing `.olean` files
  for those modules. Unrelated to this task's edits.
- `lake shake --add-public --keep-implied --keep-prefix Cslib.Logics.Propositional.Tableau.Classical.Completeness`
  attempted a wider rebuild that hit the same concurrent-session staleness
  (`Cslib.Logics.Propositional.SequentCalculus.LK.Decidability`, `Cslib.Logics.Propositional.Tableau`
  reported "out-of-date and needs to be rebuilt") and could not complete. Per the plan's
  contingency, the scoped `lake build` of the touched modules and their direct dependents is
  used as the authoritative verification gate instead.
- The pre-existing `sorry` in `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:104`
  was observed during the (incomplete) shake attempt; it is explicitly out of scope per the
  plan's non-goals and was not touched.

## Plan Deviations

- **Task 1.4 (altered)**: The plan's scoped build target list (Measure + Completeness only)
  passed, but checking dependents (per the orchestrator's explicit instruction) revealed a real
  transitive-import breakage in `DecisionProcedure.lean`. Fixed by adding one additional direct
  `public import` line to that file (see item 3 above). No proofs, declarations, or semantics
  were changed anywhere; this is a third import-hygiene line, not a plan violation of the
  "no proof/declaration changes" non-goal.
- **`lake shake` re-run (plan's optional verification step)**: skipped/incomplete, blocked by a
  concurrent session's mid-edit state on unrelated Modal/Temporal-adjacent modules, exactly as
  the plan anticipated. Scoped build used as the reliable gate instead, per plan contingency.

## Files Changed

- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Tableau/Measure.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean`
