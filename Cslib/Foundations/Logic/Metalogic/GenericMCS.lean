/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Metalogic.ListDeduction
public import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # Algebraic Derivation System with Free Deduction Theorem

This module builds a `DerivationSystem` from `ListDeriv` and proves
`HasDeductionTheorem` for it. The deduction theorem is a trivial consequence
of the `list_deduction_theorem` from `ListDeduction.lean`.

This bridges the algebraic `listImp` infrastructure to CSLib's existing
`Consistency.lean` framework, making all existing MCS lemmas
(`closed_under_derivation`, `implication_property`, `negation_complete`)
available for ANY logic with `MinimalHilbert`.

## References

* Isabelle `Propositional_Logic_Class.thy` -- `list_deduction_logic` interpretation
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.GenericMCS

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction
open Cslib.Logic.Metalogic

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

/-! ## Algebraic Derivation System -/

/-- The algebraic derivation system: contextual derivation defined via `ListDeriv`
(i.e., provability of the list-implication). This construction works for ANY
`MinimalHilbert` proof system, giving a `DerivationSystem` for free. -/
def algebraicDerivationSystem : DerivationSystem F where
  Deriv := ListDeriv (S := S)
  weakening := fun hd hsub => list_deriv_monotonic hsub hd
  assumption := fun hmem => list_deriv_reflection hmem
  mp := fun h1 h2 => list_deriv_mp h1 h2

/-! ## Free Deduction Theorem -/

/-- The algebraic derivation system automatically has the deduction theorem.
This follows directly from `list_deduction_theorem`, which is proved once
generically using the flip lemmas. No per-logic induction on proof trees needed. -/
theorem algebraic_has_deduction_theorem :
    HasDeductionTheorem (algebraicDerivationSystem (S := S) (F := F)) := by
  intro Γ φ ψ h
  exact (list_deduction_theorem φ ψ Γ).mp h

/-! ## Convenience Wrappers -/

/-- MCS closed under derivation (algebraic version). Follows from
`SetMaximalConsistent.closed_under_derivation` with the free deduction theorem. -/
theorem algebraic_mcs_closed_under_derivation
    {G : Set F} (h_mcs : SetMaximalConsistent (algebraicDerivationSystem (S := S)) G)
    {L : List F} (h_sub : ∀ ψ ∈ L, ψ ∈ G) {φ : F}
    (h_deriv : ListDeriv (S := S) L φ) : φ ∈ G :=
  SetMaximalConsistent.closed_under_derivation
    algebraicDerivationSystem algebraic_has_deduction_theorem h_mcs h_sub h_deriv

/-- MCS implication property (algebraic version). -/
theorem algebraic_mcs_implication_property
    {G : Set F} (h_mcs : SetMaximalConsistent (algebraicDerivationSystem (S := S)) G)
    {φ ψ : F} (h_imp : HasImp.imp φ ψ ∈ G) (h_phi : φ ∈ G) : ψ ∈ G :=
  SetMaximalConsistent.implication_property
    algebraicDerivationSystem algebraic_has_deduction_theorem h_mcs h_imp h_phi

/-- MCS negation completeness (algebraic version). -/
theorem algebraic_mcs_negation_complete
    {G : Set F} (h_mcs : SetMaximalConsistent (algebraicDerivationSystem (S := S)) G)
    (φ : F) : φ ∈ G ∨ HasImp.imp φ HasBot.bot ∈ G :=
  SetMaximalConsistent.negation_complete
    algebraicDerivationSystem algebraic_has_deduction_theorem h_mcs φ

end Cslib.Logic.Metalogic.GenericMCS
