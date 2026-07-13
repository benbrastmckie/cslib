# Implementation Summary: Task #461 — omit annotations for unused section variables

- **Task**: 461 - Add omit [...] annotations for unused section variables in tableau proofs
- **Plan**: specs/461_vet_299_unused_section_vars/plans/01_omit-unused-section-vars.md
- **Status**: Implemented (module-scoped); full-library CI deferred
- **Commit**: e04a2894 -- "task 461: silence unusedSectionVars via omit clauses (Modal Tableau)"

## What Was Done

Inserted 15 `omit [...] in` clauses immediately above the docstring block of each flagged
lemma, matching the existing idiom used throughout the Modal Tableau modules:

- `Cslib/Logics/Modal/Tableau/Branch.lean` (2 insertions):
  - `modalNextWorld_gt` -- `omit [DecidableEq Atom] [Hashable Atom] in`
  - `label_le_modalMaxWorld` -- `omit [DecidableEq Atom] [Hashable Atom] in`
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` (1 insertion):
  - `modalClosed_unsat` -- `omit [Hashable Atom] in`
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (12 insertions):
  - `extractModel_atom_sat_iff`, `extractModel_bot_false`, `openBranch_noTBot`,
    `openBranch_noContradiction`, `hintikka_box_pos`, `hintikka_box_neg`,
    `modalApplyOne_eq_prop_of_applicable`, `modalStepBranch_none_saturated` --
    `omit [Hashable Atom] in`
  - `modalAndOf?_eq`, `modalOrOf?_eq`, `modalImpOf?_eq`, `modalNegOf?_eq` --
    `omit [DecidableEq Atom] [Hashable Atom] in`

Zero semantic changes; purely additive `omit ... in` lines.

## Plan Deviations

1. **`label_le_modalMaxWorld` clause corrected**: the plan specified
   `omit [DecidableEq Atom] in` only, but the live build showed `[Hashable Atom]` was also
   unused in this lemma. Used `omit [DecidableEq Atom] [Hashable Atom] in` to fully silence
   the warning (see Phase 1 task annotation in the plan file).
2. **Cascading linter-batching artifact discovered and NOT chased**: after the 12
   Completeness.lean insertions, `lake build` exposed 3 additional `unusedSectionVars`
   warnings on neighboring lemmas (`extractModel_atomPos_sat`, `modalApplyOne_imp_pos`,
   `modalApplyOne_imp_neg`) that were invisible in the pre-fix baseline. Root cause: the
   linter reports only the last lemma of a maximal run of consecutive declarations sharing
   the same unused-variable status, so fixing one boundary lemma exposes the next lemma
   behind it. A trial fix of these 3 cascaded further into `modalTruthLemma` and
   `modalApplyOne_fst_eq_of_not_box`, indicating the true footprint extends well beyond the
   plan's comprehensive-scope count of 15. Per the explicitly authorized 15-insertion scope,
   these were left untouched and reverted from the trial fix. Flagged here as a follow-up
   candidate (a dedicated vet/lint task) rather than expanded into this task.
3. **Full-library CI deferred**: `lake test`, `lake exe checkInitImports`,
   `lake exe lint-style`, and `lake shake` were NOT run this pass. Task 317
   (`specs/317_propositional_tableau_completeness/`) has concurrent, uncommitted
   in-progress edits to `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
   (unrelated territory to this task) that transiently break a whole-library build/test
   through no fault of this change. Per explicit coordinator instruction, verification for
   this mechanical fix was scoped to a module-level `lake build` of the three touched
   files (`Branch.lean`, `SoundnessStep.lean`, `Completeness.lean`), which passed cleanly
   (exit 0, zero warnings among all 15 targeted lemmas). Full-library CI should be run in a
   follow-up pass once task 317 reaches a stable/committed state, before this task is
   promoted to PR-ready.

## Verification Evidence

- `lake build Cslib.Logics.Modal.Tableau.Branch Cslib.Logics.Modal.Tableau.SoundnessStep Cslib.Logics.Modal.Tableau.Completeness`
  -- exit 0, 480 jobs, zero `unusedSectionVars` warnings for any of the 15 targeted lemmas.
- Verified via `git stash`/baseline comparison that the 4 remaining unrelated warnings
  (1 in `SoundnessStep.lean`, 3 in `Completeness.lean`) are either pre-existing baseline
  warnings or the linter-batching artifact described in deviation 2 above -- none are
  targets of this task.
- `git diff --stat` confirms exactly 15 additive lines across the 3 files, no other changes.
- No sorries, no new axioms, no vacuous definitions introduced.

## Out of Scope (Confirmed Untouched)

- `classicalStepBranch_mem_preserved` (item 6) -- already fixed by task 460, not re-touched.
- Unused-`simp`-argument and deprecated-`push_neg` warnings -- separate lint categories,
  left untouched.
- All files under `Propositional/`, `Intuitionistic/`, `Minimal/`, and `Scheme.lean` --
  task 317's active territory; not read for editing purposes beyond the CI-blocker check.

## Follow-Up Recommendations

1. Run the deferred full-library CI pipeline (`lake test`, `checkInitImports`,
   `lint-style`, `shake`) once task 317's Scheme.lean WIP is committed/stable.
2. Consider a dedicated follow-up lint task to address the cascading
   `unusedSectionVars` warnings identified in deviation 2 (`extractModel_atomPos_sat`,
   `modalApplyOne_imp_pos`, `modalApplyOne_imp_neg`, and beyond) -- the true scope appears
   larger than the 15 handled here and deserves its own research/plan pass rather than
   ad hoc expansion.
