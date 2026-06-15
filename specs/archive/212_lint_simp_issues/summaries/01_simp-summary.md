# Implementation Summary: Fix 25 simpNF Lint Errors

- **Task**: 212
- **Status**: Implemented
- **Date**: 2026-06-15
- **Duration**: ~15 minutes

## What Was Done

Removed `@[simp]` attribute from 25 declarations across 6 files in the Bimodal logic subsystem.
All 25 declarations triggered simpNF lint errors because they stated equalities whose LHS was
a derived connective defined via `abbrev`, which unfolds transparently under simp. This caused
the primitive-constructor simp lemmas to fire first, preventing the derived-lemma LHS from
being recognized.

## Files Modified

| File | Declarations Fixed |
|------|-------------------|
| `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` | 2 (`toBimodal_neg`, `toBimodal_diamond`) |
| `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` | 1 (`toBimodal_neg`) |
| `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` | 1 (`toBimodal_neg`) |
| `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` | 9 (`embedFormula_neg/and/or/diamond/someFuture/somePast/allFuture/allPast/always`) |
| `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` | 4 (`int_truth_allPast/allFuture/and/top`) |
| `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` | 8 (`subst_neg/and/or/diamond/someFuture/somePast/allFuture/allPast`) |

## Verification Results

- `lake build` (scoped to 6 modified modules): PASSED
- `lake lint` (simpNF check): 0 simpNF errors on the 25 affected declarations, 0 total in codebase
- `lake test`: Pre-existing failures in `Instances.lean`, `HierarchyDefs.lean`, `IntHelpers.lean`,
  `MaximalConsistent.lean` (from other tasks' work-in-progress); no new failures from task 212 changes.
  None of these files were touched by this task.

## Plan Deviations

None. The implementation followed the plan exactly as specified.

## Impact

- 25 simpNF lint errors eliminated from the global simp set
- No downstream code affected: all usages of the removed lemmas are via explicit `rw`,
  `simp only [...]`, or `.mp`/`.mpr` calls, confirmed by grep during research phase
- No axioms introduced; no sorries present
