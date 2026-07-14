# Implementation Summary: Task #392

- **Task**: 392 - Remove dead code and fix naming (Propositional logic)
- **Plan**: plans/01_deadcode-and-naming-fixes.md
- **Status**: Implemented (all 4 phases complete)
- **Session**: sess_1782924983_6bcecb_392

## What Was Done

### Phase 1: Dead-code deletion
Deleted 21 grep-verified 0-reference declarations and fixed one stale comment:
- 12 `classicalApplyOne_*` helper lemmas + `classicalBranchSatisfiable_not_closed` in
  `Tableau/Classical/Soundness.lean`.
- `mem_extendMany_of_mem` + `hintikka_inv_mono` in `Tableau/Classical/Completeness.lean`
  (re-verified live, no task-317 WIP conflict, no conservative fallback needed).
- `propImpOrNegOf?` in `Tableau/Defs.lean`, plus fixed the stale comment referencing it
  at `Tableau/Intuitionistic/Rules.lean:203` (no Rules.lean declaration was deleted, per
  research reconciliation showing 0 dead decls there).
- `closurePred_false_of_sat` + `isAccessible_go_mono_fuel` in `Intuitionistic/Soundness.lean`.
- `hilbertAxiomToND` in `NaturalDeduction/Equivalence.lean`.
- `mem_insert_left` + `mem_insert_right` in `SequentCalculus/LK/Completeness.lean`.

### Phase 2: Small renames
- `lift_int_to_cl` -> `liftIntToCl` (`Metalogic/IntLindenbaum.lean`).
- `goodSelection_seq` -> `goodSelectionSeq` (`Foundations/Combinatorics/InfiniteGraphRamsey.lean`),
  applied with a word-boundary `sed -E 's/\bgoodSelection_seq\b/goodSelectionSeq/g'` to avoid
  corrupting the sibling `goodSelection_seq_prop` (verified intact, 2 hits unchanged;
  `goodSelectionSeq_prop` confirmed 0 hits).
- `HasFresh.to_infinite` -> `HasFresh.toInfinite` (`Foundations/Data/HasFresh.lean`).
- `emptyHrelation_apply` -> `emptyHRelation_apply` (`Foundations/Relation/Domain.lean`,
  capitalization fix to match `emptyHRelation`).

### Phase 3: `Extention` -> `Extension` typo rename
Renamed 3 theorems and all call/comment sites: `instIsIntuitionisticExtention`,
`instIsClassicalExtention` (`Defs.lean`), `instIsMinimalExtention` (`Equivalence.lean`),
with call-site updates in `NaturalDeduction/Basic.lean` and `AxiomAdmissibility.lean`.
Confirmed `git grep -n Extention` returns 0 hits repo-wide.

### Phase 4: `modus_ponens` constructor rename (large, isolated)
Renamed the Propositional `DerivationTree.modus_ponens` constructor to `modusPonens`
across 106 sites (code + comments) in 26 files, edited per-file with a word-boundary
`sed -E 's/\bmodus_ponens\b/modusPonens/g'` (never a repo-wide sed). The word-boundary
guard correctly skipped the `height_modus_ponens_left`/`height_modus_ponens_right` helper
lemmas (kept snake_case, out of scope per plan). Verified isolation: `git diff --name-only`
touches exactly the 26 intended Propositional files, with zero Bimodal/Temporal/Modal/
ExtDerivation files affected (those logics define separate, identically-named constructors
on unrelated inductive types, with no cross-imports).

## Verification

- `lake build` (scoped, per phase, and full-tree after Phase 4): green, 3189/3189 jobs,
  zero errors.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean (no output) after every phase.
- `lake test` (CslibTests suite): passes after every phase.
- Zero new `sorry`: confirmed via diff-scoped grep across all 38 touched files (the only
  `sorry`/`axiom` textual hits are pre-existing doc-comment mentions, e.g. "sorry-free" and
  prose using the word "axiom", not actual `sorry`/`axiom` declarations).
- Zero new `axiom` declarations introduced.
- No vacuous definitions introduced.

### Note on final full-tree build

A concurrent, unrelated task (454, "consolidate Chronicle PointInsertion Bimodal/Temporal")
was actively editing `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/
Since.lean` and related Foundations/Temporal Chronicle files in the same working tree during
this implementation. A final whole-repo `lake build` run after Phase 4 intermittently failed
in that unrelated Bimodal file due to task 454's in-progress (uncommitted) edits -- confirmed
unrelated to task 392 because: (1) `Since.lean` has no import dependency on any Propositional
module, (2) the dedicated full-tree `lake build` (3189/3189 jobs), `lake test`, and
`lake exe lint-style` all passed cleanly immediately after Phase 4's edits and before
committing, and (3) a scoped rebuild of exactly the 26 Phase-4 files plus `CslibTests.Propositional`
passed cleanly on retry after the transient Bimodal breakage appeared. No task-392 file was
implicated in the failure.

## Plan Deviations

None. All 4 phases were implemented exactly as planned; the Phase 1 conservative fallback for
`Classical/Completeness.lean` (defer `mem_extendMany_of_mem`/`hintikka_inv_mono` if task 317
WIP conflicts) was NOT triggered -- re-verification at implement time showed 0 external refs,
no adjacent sorry, and no working-tree conflict, so both were deleted as the primary plan.

## Follow-up Note (flagged, out of scope)

`height_modus_ponens_left` / `height_modus_ponens_right` in
`Cslib/Logics/Propositional/ProofSystem/Derivation.lean` remain snake_case after the Phase 4
constructor rename, creating a minor naming inconsistency (`modusPonens` vs
`height_modus_ponens_*`). This was explicitly out of scope for task 392; a follow-up task
could rename these two helper lemmas to `heightModusPonensLeft`/`heightModusPonensRight`.

## Artifacts

- `specs/392_remove_deadcode_fix_naming/plans/01_deadcode-and-naming-fixes.md` (all 4 phases
  marked [COMPLETED])
- `specs/392_remove_deadcode_fix_naming/summaries/01_deadcode-and-naming-fixes-summary.md`
  (this file)
- 38 modified `.lean` files across `Cslib/Logics/Propositional/` and `Cslib/Foundations/`
  (see git log for the 4 phase commits: `task 392 phase 1..4`)
