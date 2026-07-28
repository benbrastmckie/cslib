/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Metalogic.GenericMCS

/-! # Generic MCS Properties

This module provides bot/negation/membership lemmas for maximally consistent sets
(MCS) over the algebraic derivation system. These are proved ONCE generically
for ANY `MinimalHilbert` proof system, eliminating the need for per-logic
re-proofs.

## Main Results

- `mcs_bot_not_mem`: `⊥ ∉ S` for MCS `S`
- `mcs_neg_of_not_mem`: `φ ∉ S → (φ → ⊥) ∈ S`
- `mcs_not_mem_of_neg`: `(φ → ⊥) ∈ S → φ ∉ S`
- `mcs_mem_iff_neg_not_mem`: `φ ∈ S ↔ (φ → ⊥) ∉ S`
- `mcs_mp_axiom`: derive `ψ ∈ S` from `φ ∈ S` and `⊢ φ → ψ`
- `mcs_theorem_in_mcs`: any theorem belongs to every MCS

All lemmas are parameterized over `MinimalHilbert S` and use the
`algebraicDerivationSystem` from `GenericMCS.lean`.
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.MCSProperties

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction
open Cslib.Logic.Metalogic.GenericMCS
open Cslib.Logic.Metalogic

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

/-- Abbreviation for MCS over the algebraic derivation system. -/
abbrev AlgebraicMCS (G : Set F) : Prop :=
  SetMaximalConsistent (algebraicDerivationSystem (S := S) (F := F)) G

/-! ## Bot Not in MCS -/

/-- `⊥ ∉ S` for any MCS `S` over the algebraic derivation system. -/
theorem mcs_bot_not_mem {G : Set F}
    (h_mcs : AlgebraicMCS (S := S) G) :
    HasBot.bot ∉ G := by
  intro h_bot
  exact h_mcs.1 [HasBot.bot]
    (fun x hx => by
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h_bot
      · simp at hx)
    (list_deriv_reflection (List.mem_cons.mpr (Or.inl rfl)))

/-! ## Negation Lemmas -/

/-- If `φ ∉ S` (MCS), then `(φ → ⊥) ∈ S`. -/
theorem mcs_neg_of_not_mem {G : Set F}
    (h_mcs : AlgebraicMCS (S := S) G)
    {φ : F} (h_not : φ ∉ G) : HasImp.imp φ HasBot.bot ∈ G := by
  rcases algebraic_mcs_negation_complete h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

/-- If `(φ → ⊥) ∈ S` (MCS), then `φ ∉ S`. -/
theorem mcs_not_mem_of_neg {G : Set F}
    (h_mcs : AlgebraicMCS (S := S) G)
    {φ : F} (h_neg : HasImp.imp φ HasBot.bot ∈ G) : φ ∉ G := by
  intro h_phi
  exact mcs_bot_not_mem h_mcs
    (algebraic_mcs_implication_property h_mcs h_neg h_phi)

/-- `φ ∈ S ↔ (φ → ⊥) ∉ S` for MCS `S`. -/
theorem mcs_mem_iff_neg_not_mem {G : Set F}
    (h_mcs : AlgebraicMCS (S := S) G)
    {φ : F} : φ ∈ G ↔ HasImp.imp φ HasBot.bot ∉ G := by
  constructor
  · intro h hn
    exact mcs_bot_not_mem h_mcs
      (algebraic_mcs_implication_property h_mcs hn h)
  · intro h
    rcases algebraic_mcs_negation_complete h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## Theorem Membership -/

/-- If `⊢ φ → ψ` and `φ ∈ S` (MCS), then `ψ ∈ S`. -/
theorem mcs_mp_axiom {G : Set F}
    (h_mcs : AlgebraicMCS (S := S) G)
    {φ ψ : F} (h_mem : φ ∈ G)
    (h_ax : InferenceSystem.DerivableIn S (HasImp.imp φ ψ)) : ψ ∈ G := by
  apply algebraic_mcs_closed_under_derivation h_mcs
    (L := [HasImp.imp φ ψ, φ])
    (fun x hx => by
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- Need: (φ → ψ) ∈ G. Use closed_under_derivation with empty list.
        apply algebraic_mcs_closed_under_derivation h_mcs
          (L := []) (fun _ hx => by simp at hx)
        exact h_ax
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact h_mem
        · simp at hx)
  exact list_deriv_mp
    (list_deriv_reflection (List.mem_cons.mpr (Or.inl rfl)))
    (list_deriv_reflection (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-- Any theorem (derivable from empty context) belongs to every MCS. -/
theorem mcs_theorem_in_mcs {G : Set F}
    (h_mcs : AlgebraicMCS (S := S) G)
    {φ : F} (h_thm : InferenceSystem.DerivableIn S φ) : φ ∈ G := by
  apply algebraic_mcs_closed_under_derivation h_mcs
    (L := []) (fun _ hx => by simp at hx)
  exact h_thm

end Cslib.Logic.Metalogic.MCSProperties
