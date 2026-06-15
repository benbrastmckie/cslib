# Implementation Summary: Clean Up Propositional Deduction Theorem Naming

- **Task**: 191 - Clean up propositional deduction theorem naming and dead code
- **Status**: Implemented
- **Date**: 2026-06-14
- **Duration**: ~30 minutes

## What Was Done

All changes are mechanical renames and one deletion with zero semantic impact.

### Phase 1: Definition-Side Changes

**Axioms.lean** (`Cslib/Logics/Propositional/ProofSystem/Axioms.lean`):
- Replaced 6 flat `_h_` theorem names with namespace-qualified `mem_` names using explicit `namespace` blocks:
  - `prop_h_implyK` -> `PropositionalAxiom.mem_implyK`
  - `prop_h_implyS` -> `PropositionalAxiom.mem_implyS`
  - `int_h_implyK` -> `IntPropAxiom.mem_implyK`
  - `int_h_implyS` -> `IntPropAxiom.mem_implyS`
  - `min_h_implyK` -> `MinPropAxiom.mem_implyK`
  - `min_h_implyS` -> `MinPropAxiom.mem_implyS`

**DeductionTheorem.lean** (`Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`):
- Renamed `prop_has_deduction_theorem` -> `hasDeductionTheorem` at its definition (line 198)
- Updated module docstring reference from old to new name
- Deleted `cl_prop_has_deduction_theorem` (lines 210-217, dead code with 0 call sites)

### Phase 2: Call-Site Updates

All 29 call sites updated across 4 files:
- **StrongCompleteness.lean** (18 occurrences): `prop_h_implyK`/`prop_h_implyS` -> `PropositionalAxiom.mem_implyK`/`PropositionalAxiom.mem_implyS`
- **IntLindenbaum.lean** (4 occurrences): 3 int witness renames + 1 `hasDeductionTheorem` rename
- **MinLindenbaum.lean** (4 occurrences): 3 min witness renames + 1 `hasDeductionTheorem` rename
- **MCS.lean** (3 occurrences): `prop_has_deduction_theorem` -> `hasDeductionTheorem`

Line-length fixes applied: the longer qualified names caused 13 lines to exceed the 100-character limit. These were reformatted by wrapping the argument list onto the next line.

### Phase 3: Build Verification

All CI checks passed:
- `lake build` (scoped module builds): passed, no errors
- `lake exe checkInitImports`: passed
- `lake exe lint-style`: passed (exit 0)
- `lake test`: passed (exit 0)
- Zero sorries in Propositional/ directory
- Zero new axioms introduced (axiom count stable at 18)

## Plan Deviations

None. All phases executed exactly as planned. One secondary effect was anticipated in the risk table (longer names exceeding 100-char limit) and resolved with line-wrapping.

## Files Modified

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/MCS.lean`
