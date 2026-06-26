/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.GenericMCSBridge
public import Cslib.Foundations.Logic.Metalogic.GenericMCS

/-! # Deduction Theorem for Temporal Logic BX

This module proves the deduction theorem for the temporal BX Hilbert system:
if `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

## Main Results

- `deductionTheorem`: The core metatheorem, routed via the `temporal_deriv_iff_algebraic`
  bridge to `algebraic_has_deduction_theorem`.
- `temporal_has_deduction_theorem`: The `HasDeductionTheorem` instance for the generic
  MCS framework.

## Implementation

The proof delegates to the generic `algebraic_has_deduction_theorem` via the
bidirectional `temporal_deriv_iff_algebraic` bridge:

```
d : DerivationTree FrameClass.Base (A :: Γ) B
  --(⟨d⟩)-->  temporalDerivationSystem.Deriv (A :: Γ) B
  --(bridge.mp)-->  temporalAlgDS.Deriv (A :: Γ) B
  --(algebraic_has_deduction_theorem)-->  temporalAlgDS.Deriv Γ (A → B)
  --(bridge.mpr)-->  temporalDerivationSystem.Deriv Γ (A → B)
  --(.some)-->  DerivationTree FrameClass.Base Γ (A → B)
```

This eliminates the hand-written well-founded recursion and `deductionWithMem` helper
without changing the public signature.

## References

* Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean — provides `temporal_deriv_iff_algebraic`
* Cslib/Foundations/Logic/Metalogic/GenericMCS.lean — provides `algebraic_has_deduction_theorem`
* Cslib/Foundations/Logic/Metalogic/Consistency.lean
-/

set_option linter.style.setOption false

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic
open Cslib.Logic.Metalogic.GenericMCS

variable {Atom : Type*}

/-! ## Main Deduction Theorem -/

/-- **Deduction Theorem**: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

Proof via the `temporal_deriv_iff_algebraic` bridge to `algebraic_has_deduction_theorem`:
the bridge converts tree derivability to the algebraic (list-implication) level where
the deduction theorem is provable generically from `MinimalHilbert`, then converts back. -/
noncomputable def deductionTheorem (Γ : Context Atom) (A B : Formula Atom)
    (d : DerivationTree FrameClass.Base (A :: Γ) B) :
    DerivationTree FrameClass.Base Γ (A → B) :=
  (temporal_deriv_iff_algebraic.mpr
    (algebraic_has_deduction_theorem
      (temporal_deriv_iff_algebraic.mp ⟨d⟩))).some

/-! ## HasDeductionTheorem Instance -/

/-- The deduction theorem wrapped for the generic MCS framework. -/
theorem temporal_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (@temporalDerivationSystem Atom) := by
  intro Γ φ ψ h
  exact temporal_deriv_iff_algebraic.mpr
    (algebraic_has_deduction_theorem
      (temporal_deriv_iff_algebraic.mp h))

end Cslib.Logic.Temporal
