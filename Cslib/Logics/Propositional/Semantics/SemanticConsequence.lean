/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Std.Tactic.BVDecide.Normalize

/-! # Set-Based Derivability and Semantic Consequence

This module defines set-based syntactic derivability and semantic consequence
for classical, intuitionistic, and minimal propositional logic. These are the
foundations needed for strong completeness theorems.

## Main Definitions

- `SetDerivable Axioms Γ φ`: `φ` is derivable from a finite subset of `Γ`.
- `SemanticEntails Γ φ`: Classical semantic consequence (bivalent).
- `ISemanticEntails Γ φ`: Intuitionistic Kripke semantic consequence.
- `MSemanticEntails Γ φ`: Minimal Kripke semantic consequence.

## Basic Lemmas

- `SetDerivable_of_mem`: Any member of `Γ` is set-derivable from `Γ`.
- `SetDerivable_weakening`: Set-derivability is monotone in the premise set.
- `SetDerivable_of_Derivable`: Theorems are set-derivable from any set.
- `SetDerivable_empty_iff`: Set-derivability from `∅` is the same as derivability.
- `SetDerivable_mp`: Modus ponens is closed under set-derivability.

## References

* CZ Theorem 1.16 (compactness for classical logic)
* CZ Theorem 2.43 (compactness for intuitionistic/minimal logic)
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Set-Based Derivability -/

/-- `φ` is set-derivable from `Γ` if there exists a finite list `L ⊆ Γ`
such that `L ⊢ φ` in the given proof system.

This is the "finitary" or "compact" version of derivability: derivations
only use finitely many assumptions, even when `Γ` is infinite. -/
def SetDerivable (Axioms : PL.Proposition Atom → Prop)
    (Γ : Set (PL.Proposition Atom)) (φ : PL.Proposition Atom) : Prop :=
  ∃ L : List (PL.Proposition Atom),
    (∀ x ∈ L, x ∈ Γ) ∧ (propDerivationSystem Axioms).Deriv L φ

/-! ## Basic SetDerivable Lemmas -/

/-- Any member of `Γ` is set-derivable from `Γ`. -/
theorem SetDerivable_of_mem {Axioms : PL.Proposition Atom → Prop}
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : φ ∈ Γ) : SetDerivable Axioms Γ φ :=
  ⟨[φ],
   fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h,
   (propDerivationSystem Axioms).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- Set-derivability is monotone: if `Γ ⊆ Δ` and `φ` is set-derivable from `Γ`,
then `φ` is set-derivable from `Δ`. -/
theorem SetDerivable_weakening {Axioms : PL.Proposition Atom → Prop}
    {Γ Δ : Set (PL.Proposition Atom)} (h_sub : Γ ⊆ Δ)
    {φ : PL.Proposition Atom} (h : SetDerivable Axioms Γ φ) :
    SetDerivable Axioms Δ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  exact ⟨L, fun x hx => h_sub (hL_sub x hx), hL_deriv⟩

/-- Any theorem (derivable from the empty context) is set-derivable from any set. -/
theorem SetDerivable_of_Derivable {Axioms : PL.Proposition Atom → Prop}
    {φ : PL.Proposition Atom} (h : Derivable Axioms φ)
    (Γ : Set (PL.Proposition Atom)) : SetDerivable Axioms Γ φ :=
  ⟨[], fun _ hx => by simp only [List.mem_nil_iff] at hx, by
    obtain ⟨d⟩ := h
    exact ⟨d⟩⟩

/-- Set-derivability from the empty set is equivalent to ordinary derivability. -/
theorem SetDerivable_empty_iff {Axioms : PL.Proposition Atom → Prop}
    {φ : PL.Proposition Atom} :
    SetDerivable Axioms ∅ φ ↔ Derivable Axioms φ := by
  constructor
  · intro ⟨L, hL_sub, hL_deriv⟩
    have hL_nil : L = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L h
      exact absurd (hL_sub a ha) (fun h => h)
    rw [hL_nil] at hL_deriv
    exact hL_deriv
  · intro h
    exact SetDerivable_of_Derivable h ∅

/-- Modus ponens is closed under set-derivability: if `Γ ⊢_S φ → ψ` and `Γ ⊢_S φ`,
then `Γ ⊢_S ψ`. -/
theorem SetDerivable_mp {Axioms : PL.Proposition Atom → Prop}
    {Γ : Set (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (h_imp : SetDerivable Axioms Γ (φ.imp ψ))
    (h_phi : SetDerivable Axioms Γ φ) :
    SetDerivable Axioms Γ ψ := by
  obtain ⟨L₁, hL₁_sub, hL₁_deriv⟩ := h_imp
  obtain ⟨L₂, hL₂_sub, hL₂_deriv⟩ := h_phi
  exact ⟨L₁ ++ L₂,
    fun x hx => by
      rw [List.mem_append] at hx
      exact hx.elim (hL₁_sub x) (hL₂_sub x),
    (propDerivationSystem Axioms).mp
      ((propDerivationSystem Axioms).weakening hL₁_deriv
        (fun x hx => List.mem_append.mpr (Or.inl hx)))
      ((propDerivationSystem Axioms).weakening hL₂_deriv
        (fun x hx => List.mem_append.mpr (Or.inr hx)))⟩

/-! ## Classical Semantic Consequence -/

/-- Classical (bivalent) semantic consequence: `φ` is a semantic consequence of `Γ`
if every valuation satisfying all formulas in `Γ` also satisfies `φ`. -/
def SemanticEntails (Γ : Set (PL.Proposition Atom))
    (φ : PL.Proposition Atom) : Prop :=
  ∀ (v : Valuation Atom),
    (∀ ψ ∈ Γ, Evaluate v ψ) → Evaluate v φ

/-! ## Intuitionistic Kripke Semantic Consequence -/

/-- Intuitionistic Kripke semantic consequence: `φ` is an intuitionistic consequence
of `Γ` if for every intuitionistic Kripke model (with `bot_forces = fun _ => False`)
and every world where all formulas in `Γ` are forced, `φ` is also forced. -/
def ISemanticEntails (Γ : Set (PL.Proposition Atom))
    (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type u) [Preorder World] (val : World → Atom → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    ∀ (w : World),
      (∀ ψ ∈ Γ, IForces val (fun _ => False) w ψ) →
      IForces val (fun _ => False) w φ

/-! ## Minimal Kripke Semantic Consequence -/

/-- Minimal Kripke semantic consequence: `φ` is a minimal consequence of `Γ`
if for every minimal Kripke model (with arbitrary upward-closed `bot_forces`)
and every world where all formulas in `Γ` are forced, `φ` is also forced. -/
def MSemanticEntails (Γ : Set (PL.Proposition Atom))
    (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type u) [Preorder World] (val : World → Atom → Prop)
    (bot_forces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → bot_forces w → bot_forces w') →
    ∀ (w : World),
      (∀ ψ ∈ Γ, IForces val bot_forces w ψ) →
      IForces val bot_forces w φ

/-! ## Entailment from Validity -/

/-- Classical tautologies are classical semantic consequences of any set. -/
theorem SemanticEntails_of_Tautology {φ : PL.Proposition Atom}
    (h : Tautology φ) (Γ : Set (PL.Proposition Atom)) :
    SemanticEntails Γ φ :=
  fun v _ => h v

/-- Intuitionistic valid formulas are intuitionistic semantic consequences of any set. -/
theorem ISemanticEntails_of_IValid {φ : PL.Proposition Atom}
    (h : IValid.{u, u} φ) (Γ : Set (PL.Proposition Atom)) :
    ISemanticEntails Γ φ :=
  fun World _ val v_uc w _ => h World val v_uc w

/-- Minimally valid formulas are minimal semantic consequences of any set. -/
theorem MSemanticEntails_of_MValid {φ : PL.Proposition Atom}
    (h : MValid.{u, u} φ) (Γ : Set (PL.Proposition Atom)) :
    MSemanticEntails Γ φ :=
  fun World _ val bot_forces v_uc bf_uc w _ => h World val bot_forces v_uc bf_uc w

end Cslib.Logic.PL
