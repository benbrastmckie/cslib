# Implementation Summary: Task #386 — Fix PL-Specific lake lint Violations

- **Task**: 386 - fix_lake_lint_errors_propositional
- **Status**: Implemented
- **Session**: sess_1782817543_eee5ae_386
- **Phases**: 4/4 completed

## What Was Done

Cleared 20 PL-namespace `lake lint` violations across 9 files under `Cslib/Logics/Propositional/`.

### Phase 1: Attribute & docstring fixes [COMPLETED]
Fixed 6 non-rename violations:
- `Subformula.lean`: Added `@[simp, nolint simpNF]` to `vars_neg` with explanation comment.
- `Tableau/Classical/Expansion.lean`: Added `let rec @[nolint docBlame] processNext` (correct Lean 4 syntax for `let rec` docBlame suppression).
- `Tableau/Intuitionistic/Expansion.lean`: Added `let rec @[nolint docBlame] go` inside `intExpandBranches`.
- `Tableau/Intuitionistic/Rules.lean`: Added `let rec @[nolint docBlame] go` inside `isAccessible`.
- `Metalogic/DeductionTheorem.lean`: Added `@[nolint unusedArguments]` to `deductionWithMem` with comment explaining `_hA` is an intentional weakening witness.
- `Tableau/Intuitionistic/Soundness.lean`: Added `@[nolint unusedArguments]` to `intBotForces` with comment explaining the `ℕ` world parameter is part of the `botForces` predicate signature.

### Phase 2: GenericMCSBridge renames + def->lemma + cross-file consumer [COMPLETED]
Fixed 4 violations in `Metalogic/GenericMCSBridge.lean`:
- `deriv_tree_to_list` -> `derivTreeToList` + converted `noncomputable def` -> `lemma` (return type is Prop).
- `unfold_listImp_in_tree` -> `unfoldListImpInTree` (stays `noncomputable def`, returns a `DerivationTree` term).
- `list_deriv_to_tree` -> `listDerivToTree`.
- Updated all intra-file call sites and docstring references.
- Updated the one cross-file consumer: `Metalogic/DeductionTheorem.lean:79`.

### Phase 3: LK CutElimination renames [COMPLETED]
Fixed 5 violations in `SequentCalculus/LK/CutElimination.lean`:
- `cutAdm_right_andR` -> `cutAdmRightAndR`
- `cutAdm_right_orR` -> `cutAdmRightOrR`
- `cutAdm_right_impR` -> `cutAdmRightImpR`
- `cutAdm_right` -> `cutAdmRight`
- `cutAdm_left` -> `cutAdmLeft`
All 81 intra-file references updated. `cutAdmissibility` (public wrapper) unchanged.

### Phase 4: LJ CutElimination renames [COMPLETED]
Fixed 5 violations in `SequentCalculus/LJ/CutElimination.lean`:
- `ljCutAdm_principal_andR` -> `ljCutAdmPrincipalAndR`
- `ljCutAdm_principal_orR` -> `ljCutAdmPrincipalOrR`
- `ljCutAdm_principal_impR` -> `ljCutAdmPrincipalImpR`
- `ljCutAdm_left` -> `ljCutAdmLeft`
- `ljCutAdm_right` -> `ljCutAdmRight`
All intra-file references updated. `ljCutAdmissibility` (public wrapper) unchanged.

## Plan Deviations

- **docBlame fix (let rec)**: Plan called for `/-- ... -/` docstrings on `let rec` declarations. Lean 4 syntax does NOT support docstrings before `let rec` inside function bodies (parser error: "expected lemma"). Used `let rec @[nolint docBlame] name` instead, which correctly suppresses the linter. This is the CSLib-idiomatic approach (pattern already used in `Foundations/Semantics/LTS/Notation.lean`).
- No other deviations. All 20 violations cleared as planned.

## Verification

- All 9 touched modules build green (`lake build Cslib.Logics.Propositional.<Module>`).
- Zero lint errors in all 9 modules (`lake exe runLinter` on each).
- Zero sorries in all 9 modified files.
- Zero new axioms introduced.
- Cross-file rename verified: old names absent from `Cslib/Logics/Propositional/`.
- `lake exe lint-style`: Clean.
- `lake shake`: No warnings in touched files.

## Pre-existing Failures (Not Introduced by Task 386)

1. `Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness`: Type mismatch at line 76 -- `truthLemma` requires `hsat : IBranchSaturation Atom b` (re-added by task 317 commit `c648603b`) but `Completeness.lean` was not updated. Confirmed pre-existing by reverting task 386 changes.
2. `Cslib.Computability.Languages.Congruences.BuchiCongruence`: Syntax errors from toolchain bump (PR #609). Unrelated to task 386.

## Files Modified

- `Cslib/Logics/Propositional/Subformula.lean`
- `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean`
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean`
