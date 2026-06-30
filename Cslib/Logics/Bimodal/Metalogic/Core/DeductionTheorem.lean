/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Foundations.Data.ListHelpers
public import Cslib.Foundations.Logic.Metalogic.DeductionHelpers
public import Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge
public import Cslib.Foundations.Logic.Metalogic.GenericMCS

/-!
# Deduction Theorem for Bimodal TM Logic

This module proves the deduction theorem for the bimodal TM Hilbert system,
at an arbitrary frame class `fc : FrameClass`.

## Main Results

- `bimodalHilbertTree`: `HasHilbertTree` for bimodal logic (fc-parameterized tree witnesses)
- `deductionTheorem`: If `A :: Γ ⊢[fc] B` then `Γ ⊢[fc] A → B` (seam-routed)
- `deductionWithMem`: Thin `removeAll`-aware wrapper over `deductionTheorem`
- `bimodalHasDeductionTheorem`: `HasDeductionTheorem` for `bimodalDerivationSystem`
  (Base-only, for the generic MCS framework)

## Implementation (Option A — seam routing)

`deductionTheorem` and `deductionWithMem` are **fc-polymorphic**: they work for any
`fc : FrameClass`. They route through the `bimodal_deriv_iff_algebraic_fc` bridge
(from `GenericMCSBridge.lean`) to `algebraic_has_deduction_theorem` in `GenericMCS.lean`.
The bridge is supported by `MinimalHilbert (HilbertTMFc fc)`, which is constructible
because the K and S axioms (`.imp_s`, `.imp_k`) have `minFrameClass = .Base ≤ fc`.
No well-founded recursion on derivation height is required.

The Base-specific `bimodalHasDeductionTheorem` similarly routes through the fixed-fc
bridge `bimodal_deriv_iff_algebraic`.

`deductionWithMem` is a load-bearing thin wrapper (not a candidate for deletion):
it is called from `Core/MaximalConsistent.lean` and `Core/MCSProperties.lean`, where
removing-all-occurrences is the required shape for Lindenbaum-style elimination.

## References

* `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — D1 architecture docstring;
  `algebraic_has_deduction_theorem`, `HilbertTMFc` bridge pattern
* `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — fc-parameterized bridge
* `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` — parallel fc deduction theorem (R2)
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Core

open Cslib.Logic
open Cslib.Logic.Bimodal
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## HasHilbertTree Instance -/

/-- `HasHilbertTree` for bimodal logic, parameterized by frame class.
Since the bimodal deduction theorem is polymorphic in `fc`, this is defined as
a function rather than an instance. Use `letI` to bring it into scope.
Note: Bimodal uses swapped axiom names -- `.imp_s` is K and `.imp_k` is S. -/
@[reducible] def bimodalHilbertTree (fc : FrameClass) : HasHilbertTree (Formula Atom) where
  Tree := fun Γ φ => DerivationTree fc Γ φ
  implyK := fun φ ψ => .axiom [] _ (.imp_s φ ψ) trivial
  implyS := fun φ ψ χ => .axiom [] _ (.imp_k φ ψ χ) trivial
  assumption := fun h => .assumption _ _ h
  mp := fun d₁ d₂ => .modus_ponens _ _ _ d₁ d₂
  weakening := fun d h => .weakening _ _ _ d h

/-! ## Main Deduction Theorem -/

/--
The Deduction Theorem: If `A :: Γ ⊢[fc] B` then `Γ ⊢[fc] A → B`.

This fundamental metatheorem allows converting derivations with assumptions
into implicational theorems.

Proof via the `bimodal_deriv_iff_algebraic_fc` bridge to
`algebraic_has_deduction_theorem`: the bridge converts tree derivability at
arbitrary `fc` to the algebraic (list-implication) level where the deduction
theorem is provable generically from `MinimalHilbert (HilbertTMFc fc)`,
then converts back. No well-founded recursion on derivation height is needed.
-/
noncomputable def deductionTheorem {fc : FrameClass} (Γ : Context Atom) (A B : Formula Atom)
    (h : DerivationTree fc (A :: Γ) B) :
    DerivationTree fc Γ (A.imp B) :=
  (bimodal_deriv_iff_algebraic_fc.mpr
    (Cslib.Logic.Metalogic.GenericMCS.algebraic_has_deduction_theorem
      (bimodal_deriv_iff_algebraic_fc.mp ⟨h⟩))).some

/--
Deduction theorem for contexts where A appears in the middle.

If `Γ' ⊢[fc] φ` and `A ∈ Γ'`, then `(removeAll Γ' A) ⊢[fc] A → φ`.

Implemented via `deductionTheorem` with a single weakening step that embeds
`Γ'` into `A :: removeAll Γ' A`. This is a thin `removeAll`-aware wrapper over
the seam-routed `deductionTheorem`, kept because removing-all-occurrences is the
shape required by Lindenbaum/consistency elimination in callers
(`Core/MaximalConsistent.lean`, `Core/MCSProperties.lean`, etc.).
-/
-- `_hA : A ∈ Γ'` is retained to match the generic-MCS helper signature even though
-- the implementation routes through `deductionTheorem` and doesn't use it directly.
@[nolint unusedArguments]
noncomputable def deductionWithMem {fc : FrameClass} (Γ' : Context Atom)
    (A φ : Formula Atom)
    (h : DerivationTree fc Γ' φ) (_hA : A ∈ Γ') :
    DerivationTree fc (removeAll Γ' A) (A.imp φ) :=
  deductionTheorem (removeAll Γ' A) A φ
    (.weakening Γ' (A :: removeAll Γ' A) φ h fun x hx =>
      if h_eq : x = A then List.mem_cons.mpr (Or.inl h_eq)
      else List.mem_cons.mpr (Or.inr (mem_removeAll_of_mem_of_ne hx h_eq)))

/-! ## Generic MCS Framework Connection -/

/--
The bimodal deduction theorem wrapped for the generic MCS framework.

This witnesses that `bimodalDerivationSystem` satisfies the `HasDeductionTheorem`
property, enabling use of generic MCS closure properties (closed_under_derivation,
implication_property, negation_complete) from `Consistency.lean`.

Proof via the `bimodal_deriv_iff_algebraic` bridge to `algebraic_has_deduction_theorem`:
the bridge converts tree derivability to the algebraic (list-implication) level where
the deduction theorem is provable generically from `MinimalHilbert`, then converts back. -/
lemma bimodalHasDeductionTheorem :
    Metalogic.HasDeductionTheorem (bimodalDerivationSystem (Atom := Atom)) := by
  intro Γ φ ψ h
  exact Cslib.Logic.Bimodal.Metalogic.Core.bimodal_deriv_iff_algebraic.mpr
    (Cslib.Logic.Metalogic.GenericMCS.algebraic_has_deduction_theorem
      (Cslib.Logic.Bimodal.Metalogic.Core.bimodal_deriv_iff_algebraic.mp h))

end -- noncomputable section

end Cslib.Logic.Bimodal.Metalogic.Core
