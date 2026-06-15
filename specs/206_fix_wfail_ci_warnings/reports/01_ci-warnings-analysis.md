# CI Warnings Analysis: Bimodal/, Temporal/, Modal/

## Metadata
- **Task**: 206
- **Type**: research
- **Date**: 2026-06-15
- **Session**: sess_1781534511_11ef67
- **CI Run**: https://github.com/benbrastmckie/cslib/actions/runs/27551734921/job/81439622369
- **Lean Toolchain**: leanprover/lean4:v4.31.0-rc2

## Executive Summary

The CI run (27551734921) produced **70 warnings across 10 files**. However, this is misleading -- the CI uses incremental builds with caching, so only 10 of 2980 modules were freshly compiled. A clean build would reveal **significantly more warnings**, estimated at 250-350 total across approximately 50 files in the target directories.

The warnings break down into well-defined categories, all with known mechanical fixes. The primary risk factor is **unused simp args removal**, which requires per-case verification that the proof still compiles after removing the argument.

## Warning Categories (From CI Run)

### Currently Active Warnings (70 total, 10 files)

| Category | Count | Files | Risk | Fix Strategy |
|----------|-------|-------|------|-------------|
| Module docstring placement | 17 | 6 | None | Move `set_option` after `/-!` |
| Flexible simp | 18 | 2 | Low | Add `set_option linter.flexible false` or convert to `simp only` |
| Unused simp arguments | 18 | 3 | Medium | Remove unused arg from simp call |
| push_neg deprecation | 9 | 3 | None | Replace `push_neg` with `push Not` |
| Unused hypothesis in type | 4 | 3 | Low | Remove `[DecidablePred]`/`[DecidableEq]` from signature |
| Try this: intro merge | 2 | 1 | None | Combine separate `intro` calls |
| Unscoped linter.flexible | 1 | 1 | None | Scope with `in` or suppress |
| Auto-included section var | 1 | 1 | None | Add `omit` annotation |
| **TOTAL** | **70** | **10** | | |

### Latent Warnings (Would Fire on Clean Build)

| Category | Est. Count | Files | Notes |
|----------|-----------|-------|-------|
| Unscoped `linter.flexible false` | 24 | 24 | All 24 files with file-level suppression |
| Unscoped `maxHeartbeats` | 16 | 12 | 16 occurrences across 12 files |
| Module docstring ordering | ~26 | 13 | Some files fire multiple times per set_option line |
| push_neg deprecation | ~138 | 22 | All occurrences across all 22 files |
| Flexible simp (unsuppressed) | ~20-40 | unknown | Files without `linter.flexible false` |
| **Estimated total** | **~250-350** | **~50** | |

## Detailed File-by-File Analysis

### Files with Current CI Warnings

#### 1. `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` (16 warnings)
- **2x** Module docstring: `set_option` at line 11 before `/-!` at line 13
- **4x** Flexible simp: lines 178, 183, 255, 260 -- `simp [Formula.swapTemporal, ...]`
- **10x** Unused simp args: lines 354-386 -- unused `Formula.neg`, `Formula.and`, `Formula.or` args
- **Fix**: Move set_option after docstring; either add `linter.flexible false` or convert to `simp only`; remove unused args from simp calls

#### 2. `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` (14 warnings)
- **14x** Flexible simp: lines 238-351 -- various `simp [embedFormula, ...]` calls modifying hypotheses/goals
- **Fix**: Add `set_option linter.flexible false` to file header (already has emptyLine/longLine suppression)

#### 3. `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean` (12 warnings)
- **5x** Module docstring: `set_option` lines 12-15 before `/-!` at line 17
- **1x** Unscoped `linter.flexible`: line 15
- **4x** Unused simp args at line 281: `Formula.allFuture`, `Formula.neg`, `Formula.someFuture`, `Formula.top`
- **2x** Unused simp args: lines 364 (`junctionDepthU`), 394 (`junctionDepthS`)
- **Fix**: Move set_options after docstring; scope or suppress `linter.flexible`; remove unused simp args

#### 4. `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean` (8 warnings)
- **2x** Module docstring placement
- **6x** push_neg deprecation: lines 56, 65, 77, 129, 138, 150
- **Fix**: Move set_option after docstring; replace `push_neg` with `push Not`

#### 5. `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean` (6 warnings)
- **2x** Module docstring placement
- **2x** push_neg deprecation: lines 124, 166
- **2x** Try this (intro merge): lines 113, 155
- **Fix**: Move set_option after docstring; replace `push_neg` with `push Not`; merge intro calls

#### 6. `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean` (4 warnings)
- **2x** Module docstring placement
- **2x** Unused hypothesis: `[DecidablePred pred]` unused in `Int.exists_least_above` (line 53) and `Int.exists_greatest_below` (line 80)
- **Fix**: Move set_option after docstring; remove `[DecidablePred pred]` from signatures

#### 7. `Cslib/Logics/Modal/Denotation.lean` (3 warnings)
- **1x** push_neg deprecation: line 62
- **2x** Unused simp args: line 59 (`Proposition.neg`), line 67 (`Proposition.denotation`)
- **Fix**: Replace `push_neg` with `push Not`; remove unused simp args

#### 8. `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` (3 warnings)
- **2x** Module docstring placement
- **1x** Unused hypothesis: `[DecidableEq Atom]` unused in `exists_n_fresh_atoms` (line 183)
- **Fix**: Move set_option after docstring; remove `[DecidableEq Atom]` or make it a local open

#### 9. `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` (2 warnings)
- **1x** Auto-included section variable: `[DecidableEq Atom]` unused in `f_nesting_depth_nonneg` (line 34)
- **1x** Unused hypothesis: same as above
- **Fix**: Add `omit [DecidableEq Atom] in` before the theorem

#### 10. `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` (2 warnings)
- **2x** Module docstring placement
- **Fix**: Move set_option after docstring

### Files with Latent Warnings (Not in CI but would fire on clean build)

#### Unscoped `linter.flexible false` (24 files)

These files all have `set_option linter.flexible false` at file level, which the setOption linter flags:

**Bimodal/** (16 files):
- `Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` (66 decls)
- `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` (47 decls)
- `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` (17 decls)
- `Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` (18 decls)
- `Metalogic/BXCanonical/Chronicle/PointInsertion.lean` (97 decls)
- `Metalogic/BXCanonical/Completeness/Dense.lean` (2 decls)
- `Metalogic/Completeness.lean` (12 decls)
- `Metalogic/Core/DeductionTheorem.lean` (4 decls)
- `Metalogic/Core/MaximalConsistent.lean` (13 decls)
- `Metalogic/Core/MCSProperties.lean` (15 decls)
- `Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` (15 decls)
- `Metalogic/Separation/Hierarchy/HierarchyCompletion.lean` (23 decls)
- `Metalogic/Separation/Hierarchy/HierarchyDefs.lean` (75 decls)
- `Metalogic/Separation/Hierarchy/HierarchyInduction.lean` (63 decls)
- `Metalogic/Separation/SeparationThm.lean` (28 decls)
- `Metalogic/Separation/TemporalClosure.lean` (30 decls) -- already has CI warning

**Temporal/** (8 files):
- `Metalogic/Chronicle/ChronicleConstruction.lean` (64 decls)
- `Metalogic/Chronicle/ChronicleToCountermodel.lean` (5 decls)
- `Metalogic/Chronicle/CounterexampleElimination.lean` (15 decls)
- `Metalogic/Chronicle/PointInsertion.lean` (96 decls)
- `Metalogic/Chronicle/TruthLemma.lean` (8 decls)
- `Metalogic/DeductionTheorem.lean` (4 decls)
- `Metalogic/DenseMCS.lean` (25 decls)
- `Metalogic/MCS.lean` (19 decls)

**Recommended Fix**: The existing Temporal pattern of `set_option linter.style.setOption false` is viable but creates circular suppression. The better approach is to use `attribute [local instance]` and scoped `set_option ... in` where possible, but for files with 60+ declarations, the pragmatic fix is adding `set_option linter.style.setOption false` alongside the existing `linter.flexible false`.

#### Unscoped `maxHeartbeats` (16 occurrences in 12 files)

All of these need `in` suffix to scope to the next declaration:

| File | Line | Value |
|------|------|-------|
| `Temporal/Metalogic/CompletenessHelpers.lean` | 29 | 3200000 |
| `Bimodal/Metalogic/Algebraic/BooleanStructure.lean` | 31 | 400000 |
| `Temporal/Metalogic/Completeness.lean` | 46 | 3200000 |
| `Temporal/Metalogic/Soundness.lean` | 32 | 1600000 |
| `Temporal/Metalogic/DenseSoundness.lean` | 32 | 1600000 |
| `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` | 31 | 800000 |
| `Temporal/Metalogic/DenseMCS.lean` | 42 | 3200000 |
| `Temporal/Metalogic/GeneralizedNecessitation.lean` | 24 | 400000 |
| `Temporal/Metalogic/DenseCompleteness.lean` | 34 | 3200000 |
| `Temporal/Metalogic/Chronicle/RRelation.lean` | 29 | 1600000 |
| `Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` | 38 | 1600000 |
| `Temporal/Metalogic/WitnessSeed.lean` | 26 | 800000 |
| `Temporal/Metalogic/MCS.lean` | 36 | 1600000 |
| `Temporal/Metalogic/Chronicle/Frame.lean` | 26 | 800000 |
| `Temporal/Metalogic/Chronicle/TruthLemma.lean` | 39 | 3200000 |
| `Temporal/Metalogic/Chronicle/PointInsertion.lean` | 41 | 3200000 |

**Recommended Fix**: Add `in` suffix to all 16 occurrences. This is mechanical and safe -- it scopes the heartbeat limit to the next declaration, which is the intended behavior anyway.

#### Module Docstring Ordering (13 files)

All files where `set_option` appears before `/-!`:

| File | set_option line | docstring line |
|------|----------------|----------------|
| `Separation/Duality.lean` | 11 | 13 |
| `Separation/NegationEquiv.lean` | 13 | ~15 |
| `Separation/Eliminations.lean` | 14 | ~18 |
| `Separation/IntHelpers.lean` | 12 | ~14 |
| `Separation/NormalForm.lean` | 13 | ~17 |
| `Separation/Distributivity.lean` | 11 | ~13 |
| `Separation/FormulaOps.lean` | 12 | ~14 |
| `Separation/TemporalClosure.lean` | 12 | ~17 |
| `Separation/Defs.lean` | 12 | ~14 |
| `Separation/DedekindZ/QLemma.lean` | 13 | ~17 |
| `Separation/DedekindZ/Cases.lean` | 11 | ~14 |
| `Separation/Hierarchy/HierarchyDefs.lean` | 14 | ~18 |
| `Separation/Hierarchy/HierarchyCaseSep.lean` | 11 | ~15 |

**Recommended Fix**: Swap the `set_option` block and `/-!` block in each file. This is purely structural and cannot break proofs.

#### push_neg Deprecation (138 occurrences in 22 files)

All `push_neg` calls need to be replaced with `push Not`. Complete file list with occurrence counts:

| File | Count |
|------|-------|
| `Bimodal/Metalogic/Separation/NegationEquiv.lean` | 6 |
| `Bimodal/Metalogic/Separation/Distributivity.lean` | 2 |
| `Bimodal/Metalogic/Separation/Eliminations.lean` | 8 |
| `Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` | 14 |
| `Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` | 12 |
| `Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` | 4 |
| `Bimodal/Metalogic/Separation/Hierarchy/HierarchyCompletion.lean` | 2 |
| `Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean` | 2 |
| `Bimodal/Metalogic/Core/MaximalConsistent.lean` | 6 |
| `Bimodal/Metalogic/Core/RestrictedMCS.lean` | 4 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` | 16 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` | 10 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 4 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` | 6 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 10 |
| `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` | 6 |
| `Bimodal/Metalogic/Soundness/DenseValidity.lean` | 2 |
| `Bimodal/Metalogic/Soundness/FrameClassVariants.lean` | 4 |
| `Bimodal/Metalogic/Decidability/CountermodelExtraction.lean` | 2 |
| `Modal/Denotation.lean` | 1 |
| `Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` | 12 |
| `Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` | 4 |

**Recommended Fix**: Global search-and-replace `push_neg` with `push Not`. Both `push_neg` and `push Not` handle the same `at h` and `at *` syntax, so this is a purely mechanical rename. The `push_neg` tactic is defined as `push_neg := push Not` under the hood.

**Risk**: None for the tactic call itself. However, if any `push_neg` is followed by `at h` and the result of the push changes the hypothesis name or structure, the subsequent tactics might need adjustment. This is extremely unlikely since `push Not` is the same implementation.

## Fix Risk Assessment

### Zero Risk (Purely Structural)
- **Module docstring reordering** (13 files): Cannot affect proofs
- **push_neg -> push Not** (22 files, 138 occurrences): Same underlying implementation
- **intro merging** (1 file, 2 occurrences): Same semantics
- **omit annotation** (1 file): Only affects type signature generalization

### Low Risk (Needs Compilation Check)
- **Unused simp args removal** (3 files, 18 occurrences): Each removal could theoretically break a proof if the arg was actually needed indirectly. However, the linter specifically confirms these args are unused, so removal is safe. Needs `lake build` verification.
- **Unused hypothesis removal** (3 files, 4 occurrences): Removing `[DecidablePred]`/`[DecidableEq]` from signatures means callers must provide classical decidability. Since these files `open Classical`, the proofs work the same way. But downstream callers that explicitly pass decidability instances may need adjustment.
- **maxHeartbeats scoping** (12 files, 16 occurrences): Adding `in` scopes the limit to the next declaration. If there are multiple declarations that need the higher limit, only the first will get it. However, each `set_option maxHeartbeats N` is typically placed right before the declaration that needs it.

### Medium Risk (Requires Interactive Verification)
- **Flexible simp fixes** (2 files, 18 occurrences): Converting `simp [...]` to `simp only [...]` requires running `simp?` to get the exact lemma list. This is safe but time-consuming and requires LSP interaction.
- **linter.flexible scoping** (24 files): The pragmatic fix (adding `linter.style.setOption false`) is safe but adds technical debt. The proper fix (converting all flexible simps) is a large effort.

## Recommended Implementation Strategy

### Phase 1: Zero-Risk Mechanical Fixes (All Directories)
1. **push_neg -> push Not**: Global regex replacement across all 22 files
2. **Module docstring reordering**: Swap set_option and /-! blocks in 13 files
3. **intro merging**: Combine intro calls in Distributivity.lean

### Phase 2: Low-Risk Targeted Fixes
4. **Unused simp args**: Remove specific args in Duality.lean, TemporalClosure.lean, Denotation.lean
5. **Unused hypotheses**: Remove DecidablePred/DecidableEq in IntHelpers.lean, FormulaOps.lean, NestingDepth.lean
6. **maxHeartbeats scoping**: Add `in` to 16 occurrences across 12 files

### Phase 3: Unscoped linter.flexible Resolution
7. **For files with few declarations** (< 10): Convert to `set_option linter.flexible false in` per declaration
8. **For files with many declarations** (> 10): Add `set_option linter.style.setOption false` as file-level suppression (matching existing Temporal/ pattern)

### Phase 4: Flexible Simp Fixes (Optional / Future)
9. **ExtFormula.lean**: Add `set_option linter.flexible false` (14 warnings)
10. **Duality.lean**: Add `set_option linter.flexible false` (4 warnings)

### Phase 5: Verification
11. Run `lake build` to verify no regressions
12. Run CI pipeline to confirm zero warnings

## Files NOT Requiring Changes

The following warning categories are NOT active in CI and should NOT be fixed:
- **`open Classical`** (8 files): `linter.style.openClassical` is disabled by default
- **`show` tactic misuse**: `linter.style.show` is disabled by default
- **sorry declarations** (22+ occurrences): These are blocked on upstream tasks (36, 37) and cannot be removed

## Parallelization Guidance

The fixes can be parallelized by directory:
- **Agent 1**: All `Cslib/Logics/Bimodal/Metalogic/Separation/` files (Defs, Duality, NegationEquiv, Distributivity, IntHelpers, FormulaOps, TemporalClosure, Eliminations, NormalForm, DedekindZ/, Hierarchy/)
- **Agent 2**: All `Cslib/Logics/Bimodal/Metalogic/Core/` + `BXCanonical/` + `Algebraic/` files
- **Agent 3**: All `Cslib/Logics/Temporal/` + `Cslib/Logics/Modal/` files + remaining Bimodal files

No dependencies exist between files for these fixes (warning fixes are local to each file).
