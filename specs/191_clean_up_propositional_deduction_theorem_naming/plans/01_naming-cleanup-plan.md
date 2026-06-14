# Implementation Plan: Clean Up Propositional Deduction Theorem Naming

- **Task**: 191 - Clean up propositional deduction theorem naming and dead code
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/191_clean_up_propositional_deduction_theorem_naming/reports/01_naming-cleanup-research.md
- **Artifacts**: plans/01_naming-cleanup-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Clean up naming and dead code in the Propositional/ directory by deleting the unused `cl_prop_has_deduction_theorem`, renaming 6 `_h_` witness theorems to namespace-qualified form, and renaming `prop_has_deduction_theorem` to `hasDeductionTheorem`. All changes are mechanical renames with zero semantic impact. The implementation is ordered to minimize intermediate build breakage: definition-side changes first, then call-site updates, then build verification.

### Research Integration

The research report confirmed:
- `cl_prop_has_deduction_theorem` has zero references outside its own definition (safe to delete)
- 6 `_h_` witness theorems have 24 call sites across StrongCompleteness.lean, IntLindenbaum.lean, and MinLindenbaum.lean
- `prop_has_deduction_theorem` has 5 active call sites across MCS.lean, IntLindenbaum.lean, and MinLindenbaum.lean
- No symmetric wrappers are needed (confirmed)
- The broader snake_case prefix pattern (60+ declarations) is explicitly out of scope

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is a code quality cleanup within the Propositional module. It does not directly advance any ROADMAP.md items (which focus on porting remaining completeness results for Bimodal and Temporal modules). However, it improves the naming quality of shared infrastructure used by Modal, Temporal, and Bimodal metalogic.

## Goals & Non-Goals

**Goals**:
- Delete the unused `cl_prop_has_deduction_theorem` dead code
- Rename 6 `_h_` witness theorems to namespace-qualified `mem_` form
- Rename `prop_has_deduction_theorem` to `hasDeductionTheorem`
- All call sites updated with zero breakage
- Pass `lake build` and `lake exe lint-style`

**Non-Goals**:
- Renaming the broader 60+ `prop_`/`int_`/`min_` snake_case declarations
- Adding symmetric wrappers (e.g., `int_has_deduction_theorem`)
- Introducing a `HasImplyKS` typeclass

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missed call site causes build failure | L | L | Grep for old names after rename; lake build catches any miss |
| Downstream files outside Propositional/ reference these names | M | L | Research confirmed no external references; grep entire codebase to verify |
| Name collision with existing `mem_implyK` in namespace | M | L | Grep for target names before creating them |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Definition-Side Changes [COMPLETED]

**Goal**: Rename/delete declarations at their definition sites (Axioms.lean, DeductionTheorem.lean)

**Tasks**:
- [ ] Delete `cl_prop_has_deduction_theorem` (DeductionTheorem.lean lines 210-217, including the section comment at line 210)
- [ ] Rename `prop_has_deduction_theorem` to `hasDeductionTheorem` at its definition (DeductionTheorem.lean line 198)
- [ ] Update the module docstring reference in DeductionTheorem.lean line 24 (`prop_has_deduction_theorem` -> `hasDeductionTheorem`)
- [ ] Rename `prop_h_implyK` to `PropositionalAxiom.mem_implyK` (Axioms.lean line 184)
- [ ] Rename `prop_h_implyS` to `PropositionalAxiom.mem_implyS` (Axioms.lean line 190)
- [ ] Rename `int_h_implyK` to `IntPropAxiom.mem_implyK` (Axioms.lean line 196)
- [ ] Rename `int_h_implyS` to `IntPropAxiom.mem_implyS` (Axioms.lean line 202)
- [ ] Rename `min_h_implyK` to `MinPropAxiom.mem_implyK` (Axioms.lean line 208)
- [ ] Rename `min_h_implyS` to `MinPropAxiom.mem_implyS` (Axioms.lean line 214)

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - Delete dead code, rename definition, update docstring
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` - Rename 6 witness theorem definitions

**Verification**:
- All old definition names removed from definition files
- New names follow namespace-qualified conventions

---

### Phase 2: Call-Site Updates [COMPLETED]

**Goal**: Update all 29 call sites across 4 files to use the new names

**Tasks**:
- [ ] Update `prop_h_implyK` -> `PropositionalAxiom.mem_implyK` in StrongCompleteness.lean (all occurrences)
- [ ] Update `prop_h_implyS` -> `PropositionalAxiom.mem_implyS` in StrongCompleteness.lean (all occurrences)
- [ ] Update `int_h_implyK` -> `IntPropAxiom.mem_implyK` in IntLindenbaum.lean (lines 110, 145, 148)
- [ ] Update `int_h_implyS` -> `IntPropAxiom.mem_implyS` in IntLindenbaum.lean (lines 110, 145, 148)
- [ ] Update `min_h_implyK` -> `MinPropAxiom.mem_implyK` in MinLindenbaum.lean (lines 93, 128, 131)
- [ ] Update `min_h_implyS` -> `MinPropAxiom.mem_implyS` in MinLindenbaum.lean (lines 93, 128, 131)
- [ ] Update `prop_has_deduction_theorem` -> `hasDeductionTheorem` in MCS.lean (lines 78, 92, 105)
- [ ] Update `prop_has_deduction_theorem` -> `hasDeductionTheorem` in IntLindenbaum.lean (line 110)
- [ ] Update `prop_has_deduction_theorem` -> `hasDeductionTheorem` in MinLindenbaum.lean (line 93)
- [ ] Grep entire codebase for any remaining old names: `prop_h_implyK`, `prop_h_implyS`, `int_h_implyK`, `int_h_implyS`, `min_h_implyK`, `min_h_implyS`, `prop_has_deduction_theorem`, `cl_prop_has_deduction_theorem`

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - Update ~16 call sites for prop witnesses
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - Update 3 call sites for int witnesses + 1 for hasDeductionTheorem
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - Update 3 call sites for min witnesses + 1 for hasDeductionTheorem
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - Update 3 call sites for hasDeductionTheorem

**Verification**:
- Grep for old names returns zero results across entire codebase
- All call sites use new namespace-qualified names

---

### Phase 3: Build Verification [IN PROGRESS]

**Goal**: Verify all changes compile cleanly and pass CI checks

**Tasks**:
- [ ] Run `lake build` and confirm zero errors
- [ ] Run `lake exe lint-style` and confirm zero style violations
- [ ] Run `lake exe checkInitImports` and confirm import consistency
- [ ] Run `lake test` to verify test suite passes

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` exits 0
- `lake exe lint-style` exits 0
- `lake exe checkInitImports` exits 0
- `lake test` exits 0

## Testing & Validation

- [ ] `lake build` compiles without errors
- [ ] `lake exe lint-style` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake test` passes
- [ ] Grep for all old names returns zero matches across entire repository
- [ ] No new `sorry` introduced

## Artifacts & Outputs

- plans/01_naming-cleanup-plan.md (this file)
- summaries/01_naming-cleanup-summary.md (post-implementation)

## Rollback/Contingency

All changes are mechanical renames within a single commit. Rollback is trivial via `git revert`. If a missed call site causes build failure, grep for the old name and update the remaining reference.
