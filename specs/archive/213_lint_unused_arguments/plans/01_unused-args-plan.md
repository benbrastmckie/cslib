# Implementation Plan: Fix Unused Argument Lint Errors in Bimodal/Separation

- **Task**: 213 - Fix 28 unused argument lint errors across 3 files in Bimodal/Metalogic/Separation/
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/213_lint_unused_arguments/reports/01_unused-args-research.md
- **Artifacts**: plans/01_unused-args-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix 28 "does not use the following hypothesis in its type" lint warnings across 3 files in `Cslib/Logics/Bimodal/Metalogic/Separation/`. The warnings fall into two categories: (a) 3 declarations with explicit typeclass instances in their signatures that should be moved to `haveI` in the proof body, and (b) 25 declarations inside a section that inherits `[DecidableEq Atom]` which they do not need, fixable via `omit [DecidableEq Atom]` subsections. All fixes are type-level only -- no proof logic changes.

### Research Integration

Research report `01_unused-args-research.md` provides a complete enumeration of all 28 warnings with line numbers, caller impact analysis, and verified fix strategies. Key findings:
- All warnings involve `DecidableEq` or `DecidablePred` instances present in types but only used in proof bodies
- All callers have the instances available in their own scopes, so removing from types is strictly less restrictive
- The `omit` keyword is already used in 11 places across 5 CSLib files, establishing precedent

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances repository hygiene and CI cleanliness, supporting the ongoing BimodalLogic-to-CSLib port by reducing lint noise in the Bimodal Separation module.

## Goals & Non-Goals

**Goals**:
- Eliminate all 28 "unused hypothesis" lint warnings in the 3 Separation files
- Maintain identical proof behavior and caller compatibility
- Follow established CSLib patterns for `omit` and `haveI` usage

**Non-Goals**:
- Fix other lint warning categories (unused simp arguments, tactic suggestions, etc.)
- Refactor section structure beyond adding `omit` subsections
- Remove the primed versions (`exists_least_above'`, `exists_greatest_below'`) -- keep as aliases for backward compatibility

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `haveI` placement breaks proof | L | L | Instance is already used in body; `Classical.decEq`/`Classical.decPred` are always available |
| `omit` subsection boundary misplaced | L | L | Research precisely identified which declarations need/don't need DecidableEq |
| Callers break from type change | M | L | Research verified all callers have instances in own scope; changes are strictly less restrictive |
| Existing `set_option linter.unusedSectionVars false` interacts | L | L | Check if it can be removed after fixes |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Fix Explicit-Signature Declarations (3 warnings) [COMPLETED]

**Goal**: Remove unused typeclass instances from explicit theorem signatures in FormulaOps.lean and IntHelpers.lean, introducing them via `haveI` in proof bodies instead.

**Tasks**:
- [ ] In `FormulaOps.lean` line ~183: Remove `[DecidableEq Atom]` from `exists_n_fresh_atoms` signature; add `haveI : DecidableEq Atom := Classical.decEq Atom` at start of proof body
- [ ] In `IntHelpers.lean` line ~53: Remove `[DecidablePred pred]` from `Int.exists_least_above` signature; add `haveI : DecidablePred pred := Classical.decPred pred` at start of proof body
- [ ] In `IntHelpers.lean` line ~80: Remove `[DecidablePred pred]` from `Int.exists_greatest_below` signature; add `haveI : DecidablePred pred := Classical.decPred pred` at start of proof body
- [ ] Convert primed versions (`Int.exists_least_above'` at line ~109, `Int.exists_greatest_below'` at line ~119) to aliases: `theorem Int.exists_least_above' := @Int.exists_least_above` (and similarly for greatest_below)
- [ ] Build and verify these 2 files compile: `lake build Cslib.Logics.Bimodal.Metalogic.Separation.FormulaOps Cslib.Logics.Bimodal.Metalogic.Separation.IntHelpers`

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` - Remove `[DecidableEq Atom]` from `exists_n_fresh_atoms`
- `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean` - Remove `[DecidablePred pred]` from 2 theorems, alias primed versions

**Verification**:
- `lake build` on both files produces no "unused hypothesis" warnings for these 3 declarations
- Downstream callers in `DedekindZ/QLemma.lean` and `DedekindZ/Cases.lean` still compile

---

### Phase 2: Fix Section-Variable Declarations via `omit` (25 warnings) [COMPLETED]

**Goal**: Add `omit [DecidableEq Atom]` subsections in HierarchyDefs.lean to exclude the inherited section variable from 25 declarations that do not use it.

**Tasks**:
- [ ] At line ~328: Add `omit [DecidableEq Atom] in` before `count_U_zero_iff_U_free` (isolated declaration between DecidableEq-dependent theorems)
- [ ] At line ~532: Open `section NoDecEqJD` with `omit [DecidableEq Atom]` before the junction-depth block; close with `end NoDecEqJD` after `jd_snce_le_right` (~line 583). This covers 10 theorems: `junction_depth_bounds`, `junction_depth_le_jdU`, `junction_depth_le_jdS`, `jd_imp_le_left`, `jd_imp_le_right`, `jd_box_le`, `jd_untl_le_left`, `jd_untl_le_right`, `jd_snce_le_left`, `jd_snce_le_right`
- [ ] At line ~775: Open `section NoDecEqSep` with `omit [DecidableEq Atom]` before the separability block; close with `end NoDecEqSep` after `is_separable_with_U_type_replace_args` (~line 985). This covers 14 declarations including `isSeparableWithUType`, `separable_with_type_imp_separable`, `is_separable_with_U_type_of_equiv`, `imp_separable_with_type`, `u_free_separable_with_type`, `untl_s_free_separable_with_type`, `or_separable_with_U_type`, `and_separable_with_U_type`, `neg_separable_with_U_type`, `replaceUntlArgs`, `replace_untl_args_has_single_U_type`, `replace_untl_args_u_free_eq`, `replace_untl_args_preserves_S_free`, `replace_untl_args_preserves_separated`, `replace_untl_args_equiv`, `is_separable_with_U_type_replace_args`
- [ ] Check if the existing `set_option linter.unusedSectionVars false` in HierarchyDefs.lean can be removed now that all warnings are addressed
- [ ] Build and verify: `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyDefs`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean` - Add `omit` subsections for 25 declarations

**Verification**:
- `lake build` on HierarchyDefs.lean produces no "unused hypothesis" warnings
- Downstream files `HierarchyCaseSep.lean` and `HierarchyCompletion.lean` still compile

## Testing & Validation

- [ ] `lake build 2>&1 | grep "does not use the following hypothesis"` returns 0 matches in Separation files
- [ ] Full CI pipeline passes: `lake build && lake exe checkInitImports && lake exe lint-style && lake test`
- [ ] No new warnings introduced by the changes

## Artifacts & Outputs

- `specs/213_lint_unused_arguments/plans/01_unused-args-plan.md` (this file)
- `specs/213_lint_unused_arguments/summaries/01_unused-args-summary.md` (after implementation)

## Rollback/Contingency

All changes are additive (`haveI` insertions, `omit` annotations) or subtractive (removing unused binders). If any change breaks compilation, revert the individual file via `git checkout -- <file>`. The changes are independent across the 3 files, so partial rollback is straightforward.
