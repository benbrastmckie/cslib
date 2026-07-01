/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.GenericMCSBridge
public import Cslib.Foundations.Logic.Metalogic.GenericMCS
public import Cslib.Foundations.Data.ListHelpers

/-! # Deduction Theorem for Normal Modal Logics

This module proves the deduction theorem parameterized over an axiom predicate
`Axioms : Proposition Atom -> Prop`: if `A :: Gamma |- B` then `Gamma |- A -> B`,
provided `Axioms` includes `implyK` and `implyS`.

## Main Results

- `deductionTheorem`: The core metatheorem, parameterized over `Axioms`.
- `deductionWithMem`: Helper for the weakening case.
- `hasDeductionTheorem`: The `HasDeductionTheorem` instance for any
  `Axioms` including implyK and implyS.

## Implementation

All results are re-routed through the algebraic deduction theorem
(`algebraic_has_deduction_theorem`) via the `modal_deriv_iff_algebraic` bridge
from `GenericMCSBridge.lean`. The bridge instantiates `ClosedHilbert (DerivationTree
Axioms)` as a `MinimalHilbert` system whenever `HasMinimalAxioms Axioms` holds, which is
synthesised inline from the explicit `h_implyK`/`h_implyS` witnesses.
`deductionWithMem` is implemented via `deductionTheorem` with a single weakening
step.

## References

* `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — D1 architecture docstring;
  `algebraic_has_deduction_theorem`, `HasMinimalAxioms`, predicate→type bridge pattern
* `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — bridge used here
* `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — MCS framework
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Helpers
open Cslib.Logic.Metalogic.GenericMCS
open Cslib.Logic.Metalogic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Main Deduction Theorem (parameterized) -/

/-- **Deduction Theorem**: If `A :: Gamma |- B` then `Gamma |- A -> B`.

Parameterized over `Axioms` with explicit proofs that `Axioms` includes
implyK and implyS. Proved by routing through `algebraic_has_deduction_theorem`
via the `modal_deriv_iff_algebraic` bridge. -/
noncomputable def deductionTheorem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (Γ : List (Proposition Atom)) (A B : Proposition Atom)
    (d : DerivationTree Axioms (A :: Γ) B) :
    DerivationTree Axioms Γ (A → B) := by
  haveI : HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩
  exact listDerivToTree
    (algebraic_has_deduction_theorem
      (modal_deriv_iff_algebraic.mp ⟨d⟩))

/-! ## Core: deductionWithMem -/

/-- If `Γ' ⊢ φ` and `A ∈ Γ'`, then `removeAll Γ' A ⊢ A → φ`.

Thin `removeAll`-aware wrapper over the seam-routed `deductionTheorem`. Kept because
removing-all-occurrences is the shape required by Lindenbaum-style elimination in its
1 external caller: `Modal/Metalogic/Completeness.lean:542`. -/
-- `_hA : A ∈ Γ'` is retained to match the generic-MCS helper signature even though
-- the implementation routes through `deductionTheorem` and doesn't use it directly.
@[nolint unusedArguments]
noncomputable def deductionWithMem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (Γ' : List (Proposition Atom)) (A φ : Proposition Atom)
    (d : DerivationTree Axioms Γ' φ) (_hA : A ∈ Γ') :
    DerivationTree Axioms (removeAll Γ' A) (A → φ) :=
  deductionTheorem h_implyK h_implyS (removeAll Γ' A) A φ
    (.weakening Γ' (A :: removeAll Γ' A) φ d fun x hx =>
      if h_eq : x = A then List.mem_cons.mpr (Or.inl h_eq)
      else List.mem_cons.mpr (Or.inr (mem_removeAll_of_mem_of_ne hx h_eq)))

/-! ## HasDeductionTheorem Instance (parameterized) -/

/-- The deduction theorem wrapped for the generic MCS framework.

Parameterized over `Axioms` with explicit proofs that `Axioms` includes
implyK and implyS. -/
theorem hasDeductionTheorem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))) :
    Metalogic.HasDeductionTheorem (modalDerivationSystem Axioms) := by
  haveI : HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩
  intro Γ φ ψ h
  exact modal_deriv_iff_algebraic.mpr
    (algebraic_has_deduction_theorem
      (modal_deriv_iff_algebraic.mp h))

end Cslib.Logic.Modal
