/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Syntax.Formula
public import Mathlib.Data.Set.Finite.Basic

/-! # GNBA Closure — Subformulas and Fischer-Ladner Closure

This module defines the subformula set and the Fischer-Ladner closure of an LTL formula,
together with the basic membership lemmas used by the atom predicate.

## Contents

- `Formula.subformulas`: the set of all subformulas of a formula
- `Formula.closure`: the Fischer-Ladner closure (subformulas + their negations + next-until rules)
- Membership lemmas: `subformula_mem_closure`, `neg_subformula_mem_closure`, `next_untl_mem_closure`
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {Atom : Type*}

/-! ## Subformulas -/

/-- The set of all subformulas of an LTL formula (including the formula itself).

Defined recursively: `atom p` and `bot` have only themselves; `imp`, `next`, `untl`
include the formula plus all subformulas of the immediate subformulas. -/
def Formula.subformulas : Formula Atom → Set (Formula Atom)
  | .atom p => {.atom p}
  | .bot => {.bot}
  | .imp φ ψ => {.imp φ ψ} ∪ Formula.subformulas φ ∪ Formula.subformulas ψ
  | .next φ => {.next φ} ∪ Formula.subformulas φ
  | .untl φ ψ => {.untl φ ψ} ∪ Formula.subformulas φ ∪ Formula.subformulas ψ

/-- Every formula is a subformula of itself. -/
lemma Formula.self_mem_subformulas (φ : Formula Atom) : φ ∈ Formula.subformulas φ := by
  cases φ <;> simp [Formula.subformulas, Set.mem_insert_iff, Set.mem_union]

/-- The subformula set is finite. -/
lemma Formula.subformulas_finite (φ : Formula Atom) : Set.Finite (Formula.subformulas φ) := by
  induction φ with
  | atom p => simp [Formula.subformulas]
  | bot => simp [Formula.subformulas]
  | imp φ ψ ihφ ihψ =>
    simp only [Formula.subformulas]
    exact ((Set.finite_singleton _).union ihφ).union ihψ
  | next φ ihφ =>
    simp only [Formula.subformulas]
    exact (Set.finite_singleton _).union ihφ
  | untl φ ψ ihφ ihψ =>
    simp only [Formula.subformulas]
    exact ((Set.finite_singleton _).union ihφ).union ihψ

/-! ## Fischer-Ladner Closure -/

/-- The Fischer-Ladner closure of an LTL formula.

The closure contains, for each subformula `ψ`:
- `ψ` itself
- `imp ψ bot` (the negation of `ψ` in CSLib's encoding `¬ψ = imp ψ bot`)

Additionally, for each Until subformula `untl ψ₁ ψ₂`, the closure contains:
- `next (untl ψ₁ ψ₂)` (Fischer-Ladner closure rule 5)

This is the minimal set closed under the tableau rules that makes the atom predicate
well-defined without double-negation complications. -/
def Formula.closure (φ : Formula Atom) : Set (Formula Atom) :=
  (⋃ ψ ∈ Formula.subformulas φ, ({ψ, .imp ψ .bot} : Set (Formula Atom))) ∪
  (⋃ ψ ∈ Formula.subformulas φ, match ψ with
    | .untl ψ₁ ψ₂ => ({.next (.untl ψ₁ ψ₂)} : Set (Formula Atom))
    | _ => ∅)

/-- Every formula is a member of its own closure. -/
lemma Formula.self_mem_closure (φ : Formula Atom) : φ ∈ Formula.closure φ := by
  unfold Formula.closure
  apply Set.mem_union_left
  apply Set.mem_iUnion₂.mpr
  exact ⟨φ, Formula.self_mem_subformulas φ, Set.mem_insert φ _⟩

/-- Helper: the set of negations of subformulas, `{ imp ψ bot | ψ ∈ subformulas φ }`. -/
private def Formula.negSubformulas (φ : Formula Atom) : Set (Formula Atom) :=
  (fun ψ => Formula.imp ψ Formula.bot) '' Formula.subformulas φ

/-- Helper: the set of `next`-images of subformulas, `{ next ψ | ψ ∈ subformulas φ }`. -/
private def Formula.nextSubformulas (φ : Formula Atom) : Set (Formula Atom) :=
  Formula.next '' Formula.subformulas φ

/-- The closure is finite. -/
lemma Formula.closure_finite (φ : Formula Atom) : Set.Finite (Formula.closure φ) := by
  -- The closure is a subset of subformulas ∪ negSubformulas ∪ nextSubformulas,
  -- all of which are finite.
  apply Set.Finite.subset
  · exact (Formula.subformulas_finite φ).union
      (((Formula.subformulas_finite φ).image (fun ψ => Formula.imp ψ Formula.bot)).union
       ((Formula.subformulas_finite φ).image Formula.next))
  intro x hx
  simp only [Formula.closure, Set.mem_union, Set.mem_iUnion] at hx
  rcases hx with ⟨ψ, hψ, hx⟩ | ⟨ψ, hψ, hx⟩
  · -- x ∈ { ψ, imp ψ bot }
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_union_left _ hψ
    · exact Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_image_of_mem _ hψ))
  · -- x ∈ match ψ with | untl ψ₁ ψ₂ => { next (untl ψ₁ ψ₂) } | _ => ∅
    cases ψ with
    | untl ψ₁ ψ₂ =>
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_union_right _
        (Set.mem_union_right _ (Set.mem_image_of_mem _ hψ))
    | atom p => simp at hx
    | bot => simp at hx
    | imp ψ₁ ψ₂ => simp at hx
    | next ψ => simp at hx

/-! ## Subformula membership in closure -/

/-- If `ψ` is a subformula of `φ`, then `ψ ∈ φ.closure`. -/
lemma Formula.subformula_mem_closure {φ ψ : Formula Atom}
    (h : ψ ∈ Formula.subformulas φ) : ψ ∈ Formula.closure φ := by
  unfold Formula.closure
  apply Set.mem_union_left
  apply Set.mem_iUnion₂.mpr
  exact ⟨ψ, h, Set.mem_insert ψ _⟩

/-- If `ψ` is a subformula of `φ`, then `imp ψ bot ∈ φ.closure`. -/
lemma Formula.neg_subformula_mem_closure {φ ψ : Formula Atom}
    (h : ψ ∈ Formula.subformulas φ) : .imp ψ .bot ∈ Formula.closure φ := by
  unfold Formula.closure
  apply Set.mem_union_left
  apply Set.mem_iUnion₂.mpr
  exact ⟨ψ, h, Set.mem_insert_iff.mpr (Or.inr rfl)⟩

/-- If `untl ψ₁ ψ₂` is a subformula of `φ`, then `next (untl ψ₁ ψ₂) ∈ φ.closure`. -/
lemma Formula.next_untl_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.subformulas φ) :
    Formula.next (Formula.untl ψ₁ ψ₂) ∈ Formula.closure φ := by
  unfold Formula.closure
  apply Set.mem_union_right
  apply Set.mem_iUnion₂.mpr
  exact ⟨.untl ψ₁ ψ₂, h, by simp⟩

end Cslib.Logic.LTL

end
