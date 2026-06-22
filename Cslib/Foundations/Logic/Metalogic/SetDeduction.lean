/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Metalogic.ListDeduction
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Insert

/-! # Set-Level Algebraic Deduction

This module lifts list-level algebraic derivation (`ListDeriv`) to set-level
derivation (`SetDeriv`), providing the interface used by the MCS machinery.

- `SetDeriv`: set-level contextual derivation via witness lists
- `set_deduction_theorem`: `SetDeriv (insert φ Γ) ψ ↔ SetDeriv Γ (φ → ψ)`
- `set_deriv_monotonic`: monotonicity in the context
- `set_deriv_reflection`: assumption rule
- `set_deriv_cut`: cut rule
- `set_deriv_mp`: contextual modus ponens

## References

* Isabelle `Propositional_Logic_Class.thy` -- set-level deduction
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.SetDeduction

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

/-! ## Set-Level Derivation -/

/-- Set-level algebraic derivation: `SetDeriv Γ φ` holds when there exists a
finite list of formulas from `Γ` from which `φ` is list-derivable. -/
def SetDeriv (Γ : Set F) (φ : F) : Prop :=
  ∃ L : List F, (∀ x ∈ L, x ∈ Γ) ∧ ListDeriv (S := S) L φ

/-! ## Reflection -/

/-- Reflection: if `φ ∈ Γ`, then `SetDeriv Γ φ`. -/
theorem set_deriv_reflection {Γ : Set F} {φ : F}
    (h : φ ∈ Γ) : SetDeriv (S := S) Γ φ :=
  ⟨[φ], fun x hx => by
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h
    · simp at hx,
   list_deriv_reflection (List.mem_cons.mpr (Or.inl rfl))⟩

/-! ## Monotonicity -/

omit [HasBot F] [MinimalHilbert S (F := F)] in
/-- Monotonicity: if `Σ ⊆ Γ`, then `SetDeriv Σ φ → SetDeriv Γ φ`. -/
theorem set_deriv_monotonic {Sigma Γ : Set F} {φ : F}
    (h_sub : Sigma ⊆ Γ)
    (h : SetDeriv (S := S) Sigma φ) :
    SetDeriv (S := S) Γ φ := by
  obtain ⟨L, hL, hd⟩ := h
  exact ⟨L, fun x hx => h_sub (hL x hx), hd⟩

/-! ## Contextual Modus Ponens -/

/-- Contextual modus ponens at the set level. -/
theorem set_deriv_mp {Γ : Set F} {φ ψ : F}
    (h1 : SetDeriv (S := S) Γ (HasImp.imp φ ψ))
    (h2 : SetDeriv (S := S) Γ φ) :
    SetDeriv (S := S) Γ ψ := by
  obtain ⟨L1, hL1, hd1⟩ := h1
  obtain ⟨L2, hL2, hd2⟩ := h2
  refine ⟨L1 ++ L2, fun x hx => ?_, ?_⟩
  · rcases List.mem_append.mp hx with h | h
    · exact hL1 x h
    · exact hL2 x h
  · -- Weaken both to L1 ++ L2, then apply list_deriv_mp
    have hd1' := list_deriv_weaken (Δ := L2) hd1
    have hd2' : ListDeriv (S := S) (L1 ++ L2) φ :=
      list_deriv_monotonic (fun _ hx => List.mem_append.mpr (Or.inr hx)) hd2
    exact list_deriv_mp hd1' hd2'

/-! ## Deduction Theorem -/

/-- **Set-Level Deduction Theorem**: `SetDeriv (insert φ Γ) ψ ↔ SetDeriv Γ (φ → ψ)`. -/
theorem set_deduction_theorem {Γ : Set F} (φ ψ : F) :
    SetDeriv (S := S) (insert φ Γ) ψ ↔
    SetDeriv (S := S) Γ (HasImp.imp φ ψ) := by
  constructor
  · -- Forward: SetDeriv (insert φ Γ) ψ → SetDeriv Γ (φ → ψ)
    intro ⟨L, hL, hd⟩
    -- Split L into: elements equal to φ, and elements in Γ
    -- Strategy: weaken to φ :: L_Γ where L_Γ ⊆ Γ, then apply list DT
    classical
    let L_Γ := L.filter (fun x => decide (x ≠ φ) = true)
    have hL_Γ_sub : ∀ x ∈ L_Γ, x ∈ Γ := by
      intro x hx
      simp only [L_Γ, List.mem_filter, decide_eq_true_eq] at hx
      rcases Set.mem_insert_iff.mp (hL x hx.1) with rfl | hxΓ
      · exact absurd rfl hx.2
      · exact hxΓ
    have hL_sub_cons : ∀ x ∈ L, x ∈ φ :: L_Γ := by
      intro x hx
      by_cases hxφ : x = φ
      · exact List.mem_cons.mpr (Or.inl hxφ)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L_Γ, List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxφ⟩))
    -- Weaken L derivation to φ :: L_Γ
    have hd' := list_deriv_monotonic hL_sub_cons hd
    -- Apply list deduction theorem
    have hdt := (list_deduction_theorem φ ψ L_Γ).mp hd'
    exact ⟨L_Γ, hL_Γ_sub, hdt⟩
  · -- Backward: SetDeriv Γ (φ → ψ) → SetDeriv (insert φ Γ) ψ
    intro ⟨L, hL, hd⟩
    -- hd : ListDeriv L (φ → ψ)
    -- By list DT backward: ListDeriv (φ :: L) ψ
    have hd' := (list_deduction_theorem φ ψ L).mpr hd
    refine ⟨φ :: L, fun x hx => ?_, hd'⟩
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hL x hx)

/-! ## Cut Rule -/

/-- Cut rule at the set level. -/
theorem set_deriv_cut {Γ : Set F} {φ ψ : F}
    (h1 : SetDeriv (S := S) (insert φ Γ) ψ)
    (h2 : SetDeriv (S := S) Γ φ) :
    SetDeriv (S := S) Γ ψ := by
  -- By set DT: SetDeriv Γ (φ → ψ)
  have h_imp := (set_deduction_theorem φ ψ).mp h1
  -- By MP: SetDeriv Γ ψ
  exact set_deriv_mp h_imp h2

end Cslib.Logic.Metalogic.SetDeduction
