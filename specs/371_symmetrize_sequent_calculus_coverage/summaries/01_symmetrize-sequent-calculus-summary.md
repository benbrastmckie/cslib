# Implementation Summary: Task 371 — Symmetrize Sequent Calculus Coverage

**Status**: implemented
**Phases completed**: 4/4
**Build**: green (0 errors, 0 sorry)

## What Was Done

Three new Lean 4 files were added to complete LJ/LK coverage parity:

### Phase 1 (pre-existing)
- `/Cslib/Logics/Propositional/SequentCalculus/LJ/SubformulaProperty.lean`
  - LJ subformula property using CutFreeLJProof

### Phase 2 (pre-existing, with bug fixes applied in Phase 4)
- `/Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean`
  - Decidability of LK provability via deduction theorem + classical tableau
  - Fixed three pre-existing type errors: `Finset.Subset.refl` missing `_` arguments (×2) and wrong `hR` subset proof in `lkListDeductionBwd`

### Phase 3 (this dispatch)
- `/Cslib/Logics/Propositional/SequentCalculus/LK/CutFreeCompleteness.lean`
  - `lkCutFreeCompleteness`: every tautology has a cut-free LK proof (composition of `lk_iff_tautology.mp` and `LKProof.cutElim`)
  - `lkCutFreeIffTautology`: biconditional strengthening of `lk_iff_tautology` using cut-free proofs

### Phase 4 (this dispatch)
- Updated barrel files: `LJ.lean` and `LK.lean` with new public imports
- Ran `lake exe mk_all --module` to add all three modules to `Cslib.lean`
- All CI checks passed on new files (lint-style, shake, lake lint, Init imports, 0 sorry, 0 new axioms)

## Plan Deviations

- Fixed Decidability.lean build errors (Phase 2 file had pre-existing type mismatches); these were not part of Phase 3/4 scope but were necessary for CI to pass.
- `checkInitImports` could not be run globally due to pre-existing Bimodal module failures; verified Init imports manually for all three new files.

## Verification

- Scoped builds: green for all three modules individually
- `lake lint`, `lake exe lint-style`, `lake shake`: no new warnings in modified files
- sorry_count: 0
- axiom_count introduced: 0
