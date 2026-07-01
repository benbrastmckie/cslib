/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.GenericMCSBridge
public import Cslib.Logics.Propositional.ProofSystem.Axioms
public import Cslib.Foundations.Logic.Metalogic.GenericMCS
public import Cslib.Foundations.Data.ListHelpers

/-! # Deduction Theorem for Propositional Logic

This module proves the deduction theorem for the propositional Hilbert system:
if `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

## Main Results

- `deductionTheorem`: The core metatheorem, parameterized over `Axioms`.
- `deductionWithMem`: Thin `removeAll`-aware wrapper over `deductionTheorem`.
  **Load-bearing**: has 4 callers — `IntLindenbaum.lean:148`,
  `MinLindenbaum.lean:131`, `StrongCompleteness.lean:447`,
  `Semantics/SemanticConsequence.lean:159`. Do not delete.
- `hasDeductionTheorem`: The `HasDeductionTheorem` instance for the generic MCS
  framework.

## Implementation

All results are re-routed through the algebraic deduction theorem
(`algebraic_has_deduction_theorem`) via the `pl_deriv_iff_algebraic` bridge
from `GenericMCSBridge.lean`. The bridge instantiates `ClosedHilbert (PL.DerivationTree
Axioms)` as a `MinimalHilbert` system whenever `HasMinimalAxioms Axioms` holds, which is
synthesised inline from the explicit `h_implyK`/`h_implyS` witnesses.
`deductionWithMem` wraps `deductionTheorem` with a single weakening step,
using `removeAll` to clear all occurrences of the discharged hypothesis from
the context (the precise shape required by Lindenbaum-style callers).

## References

* `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — D1 architecture docstring;
  `algebraic_has_deduction_theorem`, `HasMinimalAxioms`, predicate→type bridge pattern
* `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` — bridge used here
* `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — MCS framework
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers
open Cslib.Logic.Metalogic.GenericMCS
open Cslib.Logic.Metalogic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Main Deduction Theorem -/

/-- **Deduction Theorem**: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

Parameterized over `Axioms` with explicit proofs that `Axioms` includes
implyK and implyS. Proved by routing through `algebraic_has_deduction_theorem`
via the `pl_deriv_iff_algebraic` bridge.

See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.4.3. -/
noncomputable def deductionTheorem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (Γ : List (PL.Proposition Atom)) (A B : PL.Proposition Atom)
    (d : DerivationTree Axioms (A :: Γ) B) :
    DerivationTree Axioms Γ (A → B) := by
  haveI : HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩
  exact listDerivToTree
    (algebraic_has_deduction_theorem
      (pl_deriv_iff_algebraic.mp ⟨d⟩))

/-! ## Core: deductionWithMem -/

/-- If `Γ' ⊢ φ` and `A ∈ Γ'`, then `removeAll Γ' A ⊢ A → φ`.

Thin `removeAll`-aware wrapper over the seam-routed `deductionTheorem`. Kept because
removing-all-occurrences is the shape required by Lindenbaum-style elimination in its
4 callers: `IntLindenbaum.lean:148`, `MinLindenbaum.lean:131`,
`StrongCompleteness.lean:447`, `Semantics/SemanticConsequence.lean:159`. -/
-- `_hA : A ∈ Γ'` is an intentional weakening witness in the API signature.
@[nolint unusedArguments]
noncomputable def deductionWithMem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (Γ' : List (PL.Proposition Atom)) (A φ : PL.Proposition Atom)
    (d : DerivationTree Axioms Γ' φ) (_hA : A ∈ Γ') :
    DerivationTree Axioms (removeAll Γ' A) (A → φ) :=
  deductionTheorem h_implyK h_implyS (removeAll Γ' A) A φ
    (.weakening Γ' (A :: removeAll Γ' A) φ d fun x hx =>
      if h_eq : x = A then List.mem_cons.mpr (Or.inl h_eq)
      else List.mem_cons.mpr (Or.inr (mem_removeAll_of_mem_of_ne hx h_eq)))

/-! ## HasDeductionTheorem Instance -/

/-- The deduction theorem wrapped for the generic MCS framework.

Parameterized over `Axioms` with explicit proofs that `Axioms` includes
implyK and implyS. -/
theorem hasDeductionTheorem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))) :
    Metalogic.HasDeductionTheorem (propDerivationSystem Axioms) := by
  haveI : HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩
  intro Γ φ ψ h
  exact pl_deriv_iff_algebraic.mpr
    (algebraic_has_deduction_theorem
      (pl_deriv_iff_algebraic.mp h))

end Cslib.Logic.PL
