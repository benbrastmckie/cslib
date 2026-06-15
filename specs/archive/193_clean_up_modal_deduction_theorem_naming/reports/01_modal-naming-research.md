# Research Report: Modal Deduction Theorem Naming Cleanup

**Task**: 193 -- Clean up modal deduction theorem naming
**Session**: sess_1781458686_d856d6
**Date**: 2026-06-14

## 1. s5_has_deduction_theorem -- Confirmed Dead Code

**Declaration** (lines 209-213 of `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`):
```lean
theorem s5_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (modalDerivationSystem (@ModalAxiom Atom)) :=
  modal_has_deduction_theorem
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
```

**References**: Zero references outside the definition file. The only two hits are:
- Line 29 (docstring mention in module header)
- Line 209 (the definition itself)

**Conclusion**: Safe to delete. This is a backward-compatibility wrapper that was never used.

## 2. modal_has_deduction_theorem -- 3 External Call Sites

**Declaration** (lines 194-204 of `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`):
```lean
theorem modal_has_deduction_theorem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))) :
    Metalogic.HasDeductionTheorem (modalDerivationSystem Axioms) := by
  ...
```

**All external references** (3 call sites, all in `Cslib/Logics/Modal/Metalogic/MCS.lean`):

| Line | Declaration | Exact Text |
|------|-------------|------------|
| 78 | `modal_closed_under_derivation` | `(modal_has_deduction_theorem h_implyK h_implyS)` |
| 92 | `modal_implication_property` | `(modal_has_deduction_theorem h_implyK h_implyS)` |
| 105 | `modal_negation_complete` | `(modal_has_deduction_theorem h_implyK h_implyS)` |

**Internal references** (within DeductionTheorem.lean):
- Line 23: docstring mention
- Line 194: definition itself
- Line 211: used by `s5_has_deduction_theorem` (which will be deleted)

## 3. Namespace Analysis -- No Conflict

- `modal_has_deduction_theorem` is in namespace `Cslib.Logic.Modal` (line 39)
- Propositional `hasDeductionTheorem` is in namespace `Cslib.Logic.PL` (line 42 of propositional file)

Renaming to `hasDeductionTheorem` will produce:
- `Cslib.Logic.Modal.hasDeductionTheorem` (modal)
- `Cslib.Logic.PL.hasDeductionTheorem` (propositional)

These are distinct fully-qualified names. No conflict.

## 4. Other Naming Inconsistencies in Modal/Metalogic

The task description specifically asks about `hasDeductionTheorem` naming. Beyond the two
declarations in scope, I identified several other `snake_case` declarations in the
Modal/Metalogic directory that follow the same pre-cleanup pattern. These are **out of scope**
for this task but noted for completeness:

**MCS.lean snake_case declarations** (all in `Cslib.Logic.Modal` namespace):
- `modal_lindenbaum` (line 59)
- `modal_closed_under_derivation` (line 67)
- `modal_implication_property` (line 82)
- `modal_negation_complete` (line 96)
- `mcs_mp_axiom` (line 111)
- `mcs_bot_not_mem` (line 128)
- `mcs_box_closure` (line 139)
- `mcs_box_box` (line 151)
- `mcs_box_diamond` (line 164)
- `mcs_box_mp` (line 177)
- `mcs_neg_of_not_mem` (line 194)
- `mcs_not_mem_of_neg` (line 206)
- `mcs_mem_iff_neg_not_mem` (line 218)
- `mcs_box_witness` (line 360)

**Temporal side** has similar patterns: `temporal_has_deduction_theorem` (in
`Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean`, line 167) and
`temporal_has_deduction_theorem_fc` (in `DenseMCS.lean`, line 261).

**Note**: The propositional side still uses `prop_lindenbaum`, `prop_closed_under_derivation`,
etc. in MCS.lean, so the broader snake_case-to-camelCase migration is not yet done across
the codebase. Only the `hasDeductionTheorem` name was cleaned up on the propositional side
in task 191.

## 5. Implementation Plan

### Phase 1: DeductionTheorem.lean (2 edits + docstring updates)

1. **Delete** `s5_has_deduction_theorem` (lines 206-213, including the section header on line 206 and preceding blank line)
2. **Rename** `modal_has_deduction_theorem` to `hasDeductionTheorem` (line 194)
3. **Update docstrings**: Fix the module header (lines 22-29) to reflect the new name and remove the backward-compatibility section

### Phase 2: MCS.lean (3 call-site renames)

1. Line 78: `modal_has_deduction_theorem` -> `hasDeductionTheorem`
2. Line 92: `modal_has_deduction_theorem` -> `hasDeductionTheorem`
3. Line 105: `modal_has_deduction_theorem` -> `hasDeductionTheorem`

### Verification

- `lake build Cslib.Logics.Modal.Metalogic.DeductionTheorem`
- `lake build Cslib.Logics.Modal.Metalogic.MCS`
- Full `lake build` to verify no downstream breakage

### Risk Assessment

**Very low risk**. The rename is purely lexical within a single namespace (`Cslib.Logic.Modal`).
Only 2 files are affected, with exactly 3 external call sites. The propositional cleanup
(task 191) established the exact pattern being mirrored here.
