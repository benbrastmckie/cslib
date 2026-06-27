# Implementation Summary: Task #365

- **Task**: 365 - Docstring/comment-only hygiene pass over the Propositional metatheory
- **Status**: Implemented
- **Session**: sess_1782538677_f01f15_365
- **Phases Completed**: 2 of 2

## Outcome

All 7 target files updated (6 required + 1 optional). ZERO code, proof, signature, or
sorry-count changes. Build passes for all modified modules. lint-style passes. No task-number
leaks remain in the modified files.

## Phase 1: Rewrite stale "Notes on sorry" in Tableau tree [COMPLETED]

Files modified:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`: Rewrote "Notes on sorry"
  from "key lemmas are marked sorry" to "This module is sorry-free. All three key lemmas
  (`classicalRule_preserves_sat`, `classically_closed_unsatisfiable`,
  `classicalTableau_sound`) are fully proved."
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`: Rewrote header "Notes on
  sorry" and the inline `NOTE:` inside the `minimalTableau_sound` docstring to reflect that
  `intExpandBranches_closed_unsat` is now proved and the module is sorry-free.
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean`: Rewrote to note
  that soundness is sorry-free; only the one completeness sorry remains.
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean`: Rewrote to
  note that `intuitionisticTableau_sound` is sorry-free; completeness still has 4 sorries.
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (optional): Softened
  the "Proved" claim for `minimalTableau_complete` to note the 4 remaining completeness
  sorries.

## Phase 2: Remove internal task-number leaks [COMPLETED]

Files modified:
- `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean`: Replaced "This bridge is
  the subject of task 308." with "This bridge is established by `brouwerianEmbeddingLemma`
  in `FreeJoinCompletion.lean`."
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`: Replaced
  "see task 332" in header docstring (line 22) with named obligation reference
  (`reduceRoot_decreases_normMeasure` h_8 case). Replaced `TODO(task 332, Phase 3)` inline
  comment (line 1325) with `TODO(reduceRoot_decreases_normMeasure, h_8 case)`. The `.bak`
  file-path reference at line 1332 was deliberately left untouched.

## Verification

- `lake build` for all modified modules: PASS (Classical.Completeness build failure is
  pre-existing and unrelated to this task).
- `lake exe lint-style`: PASS (no output).
- `git diff` confirmed ONLY comment/docstring lines changed in all 7 files.
- No `sorry` tokens added or removed in any file.
- No `leave_unchanged` files appear in the diff.
- task-number leak grep returns 0 matches.

## Plan Deviations

None. All required tasks executed as specified. The optional Minimal/DecisionProcedure.lean
softening was also applied.
