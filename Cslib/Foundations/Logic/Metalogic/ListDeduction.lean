/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Metalogic.ListImplication
public import Mathlib.Tactic.Attr.Core

/-! # Algebraic List-Level Deduction

This module defines `ListDeriv` (algebraic contextual derivation via `listImp`) and proves:

- `list_deduction_theorem`: `ListDeriv (φ :: Γ) ψ ↔ ListDeriv Γ (φ → ψ)`
- `list_deriv_reflection`: `φ ∈ Γ → ListDeriv Γ φ`
- `list_deriv_mp`: contextual modus ponens
- `list_deriv_monotonic`: derivation is monotone in the context
- `list_deriv_cut`: the cut rule
- `list_deriv_weaken`: weakening by appending

The deduction theorem is structural (follows from the flip lemmas in `ListImplication.lean`),
not requiring induction on proof trees. This is the key advantage of the `listImp` approach.

## References

* Isabelle `Propositional_Logic_Class.thy` -- `list_deduction`
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.ListDeduction

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Metalogic.ListImplication

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

/-! ## Algebraic Contextual Derivation -/

/-- Algebraic contextual derivation: `ListDeriv Γ φ` holds when `⊢_S listImp Γ φ`.
This encoding makes the deduction theorem structural rather than requiring
induction on proof trees. -/
def ListDeriv (Γ : List F) (φ : F) : Prop :=
  InferenceSystem.DerivableIn S (listImp Γ φ)

/-! ## Deduction Theorem -/

/-- **Deduction Theorem** (algebraic): `ListDeriv (φ :: Γ) ψ ↔ ListDeriv Γ (φ → ψ)`.
The forward direction uses `list_flip_implication1`, the backward uses
`list_flip_implication2`. This is proved ONCE generically, not per-logic. -/
theorem list_deduction_theorem (φ ψ : F) (Γ : List F) :
    ListDeriv (S := S) (φ :: Γ) ψ ↔
    ListDeriv (S := S) Γ (HasImp.imp φ ψ) := by
  unfold ListDeriv
  constructor
  · intro h
    exact ModusPonens.mp (list_flip_implication1 φ ψ Γ) h
  · intro h
    exact ModusPonens.mp (list_flip_implication2 φ ψ Γ) h

/-! ## Reflection -/

/-- Reflection: if `φ ∈ Γ`, then `ListDeriv Γ φ`. -/
theorem list_deriv_reflection {Γ : List F} {φ : F}
    (h : φ ∈ Γ) : ListDeriv (S := S) Γ φ := by
  induction Γ with
  | nil => simp at h
  | cons ψ Ψ ih =>
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · -- φ = ψ, need ListDeriv (φ :: Ψ) φ
      unfold ListDeriv
      grind [listImp_axiom_k]
    · -- φ ∈ Ψ, use ih and then weaken
      exact ModusPonens.mp HasAxiomImplyK.implyK (ih h)

/-! ## Contextual Modus Ponens -/

/-- Contextual modus ponens: from `ListDeriv Γ (φ → ψ)` and `ListDeriv Γ φ`,
    derive `ListDeriv Γ ψ`. Uses `listImp_axiom_s`. -/
theorem list_deriv_mp {Γ : List F} {φ ψ : F}
    (h1 : ListDeriv (S := S) Γ (HasImp.imp φ ψ))
    (h2 : ListDeriv (S := S) Γ φ) :
    ListDeriv (S := S) Γ ψ := by
  unfold ListDeriv at *
  exact ModusPonens.mp (ModusPonens.mp (listImp_axiom_s φ ψ Γ) h1) h2

/-! ## Monotonicity -/

/-- Monotonicity: if `∀ x ∈ Σ, x ∈ Γ`, then `ListDeriv Σ φ → ListDeriv Γ φ`.
The proof goes by induction on Σ generalizing φ, peeling off elements and
using the deduction theorem + reflection. -/
theorem list_deriv_monotonic {Sigma Γ : List F} {φ : F}
    (h_sub : ∀ x ∈ Sigma, x ∈ Γ)
    (h : ListDeriv (S := S) Sigma φ) :
    ListDeriv (S := S) Γ φ := by
  induction Sigma generalizing φ with
  | nil =>
    unfold ListDeriv at *
    exact ModusPonens.mp (listImp_axiom_k φ Γ) h
  | cons ψ Ψ ih =>
    -- h : ListDeriv (ψ :: Ψ) φ
    -- By DT: ListDeriv Ψ (ψ → φ)
    have h' := (list_deduction_theorem ψ φ Ψ).mp h
    have hΨ : ∀ x ∈ Ψ, x ∈ Γ := fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx))
    -- By IH (with φ := ψ → φ): ListDeriv Γ (ψ → φ)
    have h_imp := ih hΨ h'
    -- By reflection: ListDeriv Γ ψ
    have hψ : ψ ∈ Γ := h_sub ψ (List.mem_cons.mpr (Or.inl rfl))
    have h_ψ : ListDeriv (S := S) Γ ψ := list_deriv_reflection hψ
    -- By MP: ListDeriv Γ φ
    exact list_deriv_mp h_imp h_ψ

/-! ## Weakening -/

/-- Weakening by appending: `ListDeriv Γ φ → ListDeriv (Γ ++ Δ) φ`. -/
theorem list_deriv_weaken {Γ Δ : List F} {φ : F}
    (h : ListDeriv (S := S) Γ φ) :
    ListDeriv (S := S) (Γ ++ Δ) φ :=
  list_deriv_monotonic (fun _ hx => List.mem_append.mpr (Or.inl hx)) h

/-! ## Cut Rule -/

/-- Cut rule: from `ListDeriv (φ :: Γ) ψ` and `ListDeriv Δ φ`,
    derive `ListDeriv (Γ ++ Δ) ψ`. -/
theorem list_deriv_cut {φ ψ : F} {Γ Δ : List F}
    (h1 : ListDeriv (S := S) (φ :: Γ) ψ)
    (h2 : ListDeriv (S := S) Δ φ) :
    ListDeriv (S := S) (Γ ++ Δ) ψ := by
  have h_imp := (list_deduction_theorem φ ψ Γ).mp h1
  have h_imp' := list_deriv_weaken (Δ := Δ) h_imp
  have h2' : ListDeriv (S := S) (Γ ++ Δ) φ :=
    list_deriv_monotonic (fun x hx => List.mem_append.mpr (Or.inr hx)) h2
  exact list_deriv_mp h_imp' h2'

/-! ## Lifting Theorems to Contexts -/

/-- Any theorem (derivable from empty context) holds in any context. -/
theorem list_deriv_of_theorem {Γ : List F} {φ : F}
    (h : ListDeriv (S := S) [] φ) :
    ListDeriv (S := S) Γ φ :=
  list_deriv_monotonic (fun _ hx => by simp at hx) h

end Cslib.Logic.Metalogic.ListDeduction
