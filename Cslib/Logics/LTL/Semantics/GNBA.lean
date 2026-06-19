/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.Satisfies
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.Finite.Lattice

/-! # GNBA Tableau Construction for LTL Omega-Regularity

This module implements the standard Generalized Nondeterministic Büchi Automaton (GNBA)
tableau construction for LTL formulas, following Baier-Katoen Chapter 5 / Vardi-Wolper 1986.
The construction provides the missing `untl` case for `Formula.isRegular`.

## Overview

The construction proceeds in five phases:

1. **Closure and Atoms** (this file, Phase 1): Fischer-Ladner closure `Formula.closure` and
   the atom predicate `Formula.IsAtom` (maximally consistent subsets of the closure).

2. **Canonical Atoms** (Phase 2): Canonical atoms `canonicalAtom v i φ = { ψ ∈ cl(φ) | v,i ⊨ ψ }`
   and their semantic properties.

3. **GNBA Construction** (Phase 3): Transition relation, initial states, acceptance sets, and
   GNBA-to-NBA conversion via cycling counter.

4. **Correctness** (Phase 4): Language equality `language (gnbaNBA φ) = φ.omegaLanguage`.

5. **Integration** (Phase 5): Proof of `Formula.isRegular_untl` removing the `sorry` from
   `Formula.isRegular`.

## Closure Convention

Following Option B from the research report: the Fischer-Ladner closure of `φ` contains,
for each subformula `ψ`:
- `ψ` itself
- its negation `imp ψ bot` (CSLib encodes `¬ψ = imp ψ bot`)

Plus, for each Until subformula `untl ψ₁ ψ₂` in `φ`:
- `next (untl ψ₁ ψ₂)` (Fischer-Ladner rule 5)

This avoids double-negation issues since `neg` is an abbreviation for `imp _ bot`.

## References

* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008]
* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
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

/-! ## Atom predicate -/

/-- A set `B` is an atom for formula `φ` if it is a maximally consistent subset of `φ.closure`.

The conditions are:
1. `B ⊆ φ.closure` (subset condition)
2. Propositional consistency: for all `ψ ∈ φ.closure`, `ψ ∈ B ↔ imp ψ bot ∉ B`
3. Bot consistency: `bot ∉ B`
4. Imp closure: for all `imp ψ₁ ψ₂ ∈ φ.closure`, `imp ψ₁ ψ₂ ∈ B ↔ (ψ₁ ∉ B ∨ ψ₂ ∈ B)`
5. Until local consistency (right): `untl ψ₁ ψ₂ ∈ φ.closure` and `ψ₂ ∈ B` implies
   `untl ψ₁ ψ₂ ∈ B`
6. Until local consistency (left): `untl ψ₁ ψ₂ ∈ φ.closure` and `untl ψ₁ ψ₂ ∈ B` and
   `ψ₂ ∉ B` implies `ψ₁ ∈ B`

Note: conditions 2-6 only apply to formulas that are members of `φ.closure`. -/
structure Formula.IsAtom (φ : Formula Atom) (B : Set (Formula Atom)) : Prop where
  /-- B is a subset of the closure. -/
  subset : B ⊆ Formula.closure φ
  /-- Propositional consistency: ψ ∈ B iff ¬ψ ∉ B. -/
  propConsistent : ∀ ψ ∈ Formula.closure φ, ψ ∈ B ↔ .imp ψ .bot ∉ B
  /-- Bot consistency: ⊥ ∉ B. -/
  botConsistent : .bot ∉ B
  /-- Imp closure: imp ψ₁ ψ₂ ∈ B iff ψ₁ ∉ B or ψ₂ ∈ B. -/
  impClosure : ∀ ψ₁ ψ₂ : Formula Atom, .imp ψ₁ ψ₂ ∈ Formula.closure φ →
    (.imp ψ₁ ψ₂ ∈ B ↔ (ψ₁ ∉ B ∨ ψ₂ ∈ B))
  /-- Until local consistency: ψ₂ ∈ B implies untl ψ₁ ψ₂ ∈ B. -/
  untlRight : ∀ ψ₁ ψ₂ : Formula Atom, .untl ψ₁ ψ₂ ∈ Formula.closure φ →
    ψ₂ ∈ B → .untl ψ₁ ψ₂ ∈ B
  /-- Until local consistency: untl ψ₁ ψ₂ ∈ B and ψ₂ ∉ B implies ψ₁ ∈ B. -/
  untlLeft : ∀ ψ₁ ψ₂ : Formula Atom, .untl ψ₁ ψ₂ ∈ Formula.closure φ →
    .untl ψ₁ ψ₂ ∈ B → ψ₂ ∉ B → ψ₁ ∈ B

/-! ## Finiteness of atoms -/

/-- The set of all atoms of `φ` is finite.

Atoms are subsets of `φ.closure`, which is finite. The set of all subsets of a finite set
is finite, so the collection of atoms (a subcollection of all subsets) is finite. -/
lemma Formula.atoms_finite (φ : Formula Atom) :
    Set.Finite {B | Formula.IsAtom φ B} := by
  apply Set.Finite.subset (Set.Finite.finite_subsets (Formula.closure_finite φ))
  intro B hB
  exact hB.subset

end Cslib.Logic.LTL

end
