# Implementation Summary: Fix 28 Unused Argument Lint Errors

- **Task**: 213
- **Status**: Implemented
- **Date**: 2026-06-15
- **Duration**: ~45 minutes

## Outcome

All 28 "does not use the following hypothesis in its type" lint warnings fixed across 3 files in `Cslib/Logics/Bimodal/Metalogic/Separation/`. Zero new warnings introduced.

## Changes Made

### Phase 1: Explicit-Signature Declarations (3 warnings)

**`Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean`**

- `exists_n_fresh_atoms`: Removed `[DecidableEq Atom]` from signature; added `haveI : DecidableEq Atom := Classical.decEq Atom` at proof start

**`Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean`**

- `Int.exists_least_above`: Removed `[DecidablePred pred]` from signature; added `haveI : DecidablePred pred := Classical.decPred pred`
- `Int.exists_greatest_below`: Same fix
- `Int.exists_least_above'` and `Int.exists_greatest_below'`: Converted from full theorem bodies with `haveI + exact` to `alias` declarations (since the unprimed versions became classical)

### Phase 2: Section-Variable Declarations (25 warnings)

**`Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean`**

- `count_U_zero_iff_U_free` (line 328): Added `omit [DecidableEq Atom] in` prefix
- Junction-depth block (10 theorems, lines 532-588): Wrapped in `section NoDecEqJD` / `end NoDecEqJD` with `omit [DecidableEq Atom]`
- Separability block (14+ declarations, lines 779-995): Wrapped in `section NoDecEqSep` / `end NoDecEqSep` with `omit [DecidableEq Atom]`
- `u_free_separable_with_type` (inside `NoDecEqSep`): Required `haveI : DecidableEq Atom := Classical.decEq Atom` in proof body because it calls `separated_imp_separable` which was compiled with `[DecidableEq Atom]` as an implicit parameter
- Removed `set_option linter.unusedSectionVars false` (no longer needed)

## Plan Deviations

| Task | Deviation |
|------|-----------|
| Phase 1: alias primed versions | Used `alias X := Y` instead of `theorem X := @Y` (the `theorem X := @Y` syntax causes style linter errors) |
| Phase 2: `u_free_separable_with_type` | Added `haveI` in proof body in addition to wrapping in `NoDecEqSep`; the research report did not anticipate that `separated_imp_separable` requires `DecidableEq Atom` even though it's not in `u_free_separable_with_type`'s type |

## Verification Results

| Check | Result | Notes |
|-------|--------|-------|
| `lake build` | Pass | All Separation files build cleanly |
| `lake build 2>&1 | grep "does not use"` | 0 matches | All 28 warnings eliminated |
| `lake exe lint-style` | Pass | No new style issues |
| `lake exe mk_all --module` | "No update necessary" | No new files created |
| Downstream callers (DedekindZ/QLemma, Cases, HierarchyCaseSep, HierarchyCompletion) | Pass | All still compile |
| Sorry count in modified files | 0 | No sorries added |
| New axioms | 0 | No axioms introduced |
| `lake exe checkInitImports` | Pre-existing failure | MaximalConsistent.olean missing from pre-existing ProofSystem/Instances.lean build error (unrelated to task 213) |
| `lake test` | Pre-existing failure | BXCanonical/Chronicle/PointInsertion was already failing before these changes |

## Files Modified

1. `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` -- 2 lines changed
2. `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean` -- 29 lines changed
3. `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean` -- 13 lines changed
