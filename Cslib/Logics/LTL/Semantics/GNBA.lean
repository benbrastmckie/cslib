/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.Satisfies
public import Cslib.Computability.Languages.OmegaRegularLanguage
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Fintype.Fin

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
2. Propositional consistency: for all `ψ ∈ φ.subformulas φ`, `ψ ∈ B ↔ imp ψ bot ∉ B`
   (Only applies to direct subformulas, not the entire closure, since the double-negation
   `imp (imp ψ bot) bot` may not be in the closure.)
3. Bot consistency: `bot ∉ B`
4. Imp closure: for all `imp ψ₁ ψ₂ ∈ φ.closure`, `imp ψ₁ ψ₂ ∈ B ↔ (ψ₁ ∉ B ∨ ψ₂ ∈ B)`
5. Until local consistency (right): `untl ψ₁ ψ₂ ∈ φ.closure` and `ψ₂ ∈ B` implies
   `untl ψ₁ ψ₂ ∈ B`
6. Until local consistency (left): `untl ψ₁ ψ₂ ∈ φ.closure` and `untl ψ₁ ψ₂ ∈ B` and
   `ψ₂ ∉ B` implies `ψ₁ ∈ B`

Note: condition 2 applies to subformulas only; conditions 3-6 apply to closure members. -/
structure Formula.IsAtom (φ : Formula Atom) (B : Set (Formula Atom)) : Prop where
  /-- B is a subset of the closure. -/
  subset : B ⊆ Formula.closure φ
  /-- Propositional consistency: for each subformula ψ, exactly one of ψ and ¬ψ is in B. -/
  propConsistent : ∀ ψ ∈ Formula.subformulas φ, ψ ∈ B ↔ .imp ψ .bot ∉ B
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

/-! ## Closure-subformula relationship -/

/-- Subformulas are downward-closed: left component of an `untl` subformula. -/
private lemma Formula.subformulas_untl_left {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₁ ∈ Formula.subformulas φ := by
  induction φ with
  | atom p => simp [Formula.subformulas] at h
  | bot => simp [Formula.subformulas] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with (h | h₁) | h₂
    · simp at h
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)
  | next φ ih =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with h | h
    · simp at h
    · exact Set.mem_union_right _ (ih h)
  | untl φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff,
               Formula.untl.injEq] at h
    rcases h with ((⟨rfl, rfl⟩ | h₁) | h₂)
    · exact Set.mem_union_left _ (Set.mem_union_right _ (Formula.self_mem_subformulas _))
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)

/-- Subformulas are downward-closed: right component of an `untl` subformula. -/
private lemma Formula.subformulas_untl_right {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₂ ∈ Formula.subformulas φ := by
  induction φ with
  | atom p => simp [Formula.subformulas] at h
  | bot => simp [Formula.subformulas] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with (h | h₁) | h₂
    · simp at h
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)
  | next φ ih =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with h | h
    · simp at h
    · exact Set.mem_union_right _ (ih h)
  | untl φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff,
               Formula.untl.injEq] at h
    rcases h with ((⟨rfl, rfl⟩ | h₁) | h₂)
    · exact Set.mem_union_right _ (Formula.self_mem_subformulas _)
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)

/-- Subformulas are downward-closed: left component of an `imp` subformula. -/
private lemma Formula.subformulas_imp_left {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₁ ∈ Formula.subformulas φ := by
  induction φ with
  | atom p => simp [Formula.subformulas] at h
  | bot => simp [Formula.subformulas] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff,
               Formula.imp.injEq] at h
    rcases h with ((⟨rfl, rfl⟩ | h₁) | h₂)
    · exact Set.mem_union_left _ (Set.mem_union_right _ (Formula.self_mem_subformulas _))
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)
  | next φ ih =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with h | h
    · simp at h
    · exact Set.mem_union_right _ (ih h)
  | untl φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with (h | h₁) | h₂
    · simp at h
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)

/-- Subformulas are downward-closed: right component of an `imp` subformula. -/
private lemma Formula.subformulas_imp_right {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₂ ∈ Formula.subformulas φ := by
  induction φ with
  | atom p => simp [Formula.subformulas] at h
  | bot => simp [Formula.subformulas] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff,
               Formula.imp.injEq] at h
    rcases h with ((⟨rfl, rfl⟩ | h₁) | h₂)
    · exact Set.mem_union_right _ (Formula.self_mem_subformulas _)
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)
  | next φ ih =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with h | h
    · simp at h
    · exact Set.mem_union_right _ (ih h)
  | untl φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with (h | h₁) | h₂
    · simp at h
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)

/-! ### Closure membership lemmas -/

/-- If `ψ` is in `φ.closure`, then `ψ` is a subformula of `φ`, or `ψ = imp χ bot` for
some subformula `χ`, or `ψ = next (untl χ₁ χ₂)` for some `untl` subformula. -/
private lemma Formula.mem_closure_cases {φ ψ : Formula Atom} (h : ψ ∈ Formula.closure φ) :
    (ψ ∈ Formula.subformulas φ) ∨
    (∃ χ ∈ Formula.subformulas φ, ψ = Formula.imp χ Formula.bot) ∨
    (∃ χ₁ χ₂, Formula.untl χ₁ χ₂ ∈ Formula.subformulas φ ∧
      ψ = Formula.next (Formula.untl χ₁ χ₂)) := by
  simp only [Formula.closure, Set.mem_union, Set.mem_iUnion, Set.mem_insert_iff,
             Set.mem_singleton_iff] at h
  rcases h with ⟨χ, hχ, rfl | rfl⟩ | ⟨χ, hχ, hx⟩
  · left; exact hχ
  · right; left; exact ⟨χ, hχ, rfl⟩
  · cases χ with
    | untl χ₁ χ₂ =>
      simp only [Set.mem_singleton_iff] at hx
      right; right; exact ⟨χ₁, χ₂, hχ, hx⟩
    | atom p => simp at hx
    | bot => simp at hx
    | imp a b => simp at hx
    | next a => simp at hx

/-- If `untl ψ₁ ψ₂` is in `φ.closure`, then `ψ₁ ∈ φ.closure`. -/
lemma Formula.untl_left_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.closure φ) : ψ₁ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, _, heq⟩ | ⟨χ₁, χ₂, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_untl_left hsub)
  · simp at heq
  · simp at heq

/-- If `untl ψ₁ ψ₂` is in `φ.closure`, then `ψ₂ ∈ φ.closure`. -/
lemma Formula.untl_right_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.closure φ) : ψ₂ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, _, heq⟩ | ⟨χ₁, χ₂, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_untl_right hsub)
  · simp at heq
  · simp at heq

/-- If `imp ψ₁ ψ₂` is in `φ.closure` and `ψ₂ ≠ bot`, then `ψ₁ ∈ φ.closure`. -/
lemma Formula.imp_left_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.closure φ) (hne : ψ₂ ≠ Formula.bot) :
    ψ₁ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, _, heq⟩ | ⟨χ₁, χ₂, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_imp_left hsub)
  · -- heq : imp ψ₁ ψ₂ = imp χ bot, so ψ₂ = bot -- contradiction
    simp only [Formula.imp.injEq] at heq; exact absurd heq.2 hne
  · simp at heq

/-- If `imp ψ₁ ψ₂` is in `φ.closure` and `ψ₂ ≠ bot`, then `ψ₂ ∈ φ.closure`. -/
lemma Formula.imp_right_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.closure φ) (hne : ψ₂ ≠ Formula.bot) :
    ψ₂ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, _, heq⟩ | ⟨χ₁, χ₂, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_imp_right hsub)
  · simp only [Formula.imp.injEq] at heq; exact absurd heq.2 hne
  · simp at heq

/-- Every subformula of `φ` is in `φ.closure`. (Alias for `subformula_mem_closure`) -/
lemma Formula.subformulas_subset_closure (φ : Formula Atom) :
    Formula.subformulas φ ⊆ Formula.closure φ :=
  fun _ h => Formula.subformula_mem_closure h

/-! ## Canonical atoms from semantic valuations -/

/-- The canonical atom at position `i` in valuation `v` for formula `φ`.

Given a valuation `v : ℕ → (Atom → Prop)` and position `i : ℕ`, the canonical atom
collects all closure formulas satisfied at `(v, i)`:

  `canonicalAtom v i φ = { ψ ∈ φ.closure | v, i ⊨ ψ }`

This is the key bridge between LTL semantics and the GNBA state space: the canonical
atom is a valid atom (satisfies `Formula.IsAtom`), enabling the completeness direction
of the GNBA correctness proof. -/
def Formula.canonicalAtom (v : ℕ → (Atom → Prop)) (i : ℕ) (φ : Formula Atom) :
    Set (Formula Atom) :=
  { ψ ∈ Formula.closure φ | Satisfies v i ψ }

/-- Membership characterization for the canonical atom. -/
lemma Formula.canonicalAtom_mem_iff {v : ℕ → (Atom → Prop)} {i : ℕ} {φ ψ : Formula Atom} :
    ψ ∈ Formula.canonicalAtom v i φ ↔ (ψ ∈ Formula.closure φ ∧ Satisfies v i ψ) := by
  simp [Formula.canonicalAtom]

/-! ### Canonical atom is an atom -/

/-- Helper: the left component of an `imp` in `φ.closure` is in `φ.closure`. -/
private lemma Formula.imp_sub_left_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.closure φ) : ψ₁ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, hχ, heq⟩ | ⟨_, _, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_imp_left hsub)
  · -- heq : imp ψ₁ ψ₂ = imp χ bot, so ψ₁ = χ ∈ subformulas φ
    simp only [Formula.imp.injEq] at heq
    exact Formula.subformula_mem_closure (heq.1 ▸ hχ)
  · simp at heq

/-- Helper: the right component of an `imp` in `φ.closure` is in `φ.closure` if not `bot`. -/
private lemma Formula.imp_sub_right_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.closure φ) (hne : ψ₂ ≠ Formula.bot) :
    ψ₂ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, _, heq⟩ | ⟨_, _, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_imp_right hsub)
  · simp only [Formula.imp.injEq] at heq; exact absurd heq.2 hne
  · simp at heq

/-- The canonical atom satisfies the `Formula.IsAtom` predicate.

All six conditions of `IsAtom` hold for sets defined by semantic satisfaction:
1. Subset: by definition, elements of `canonicalAtom v i φ` are in `φ.closure`.
2. Propositional consistency: `Satisfies v i ψ ↔ ¬Satisfies v i (imp ψ bot)` (classical).
3. Bot consistency: `¬Satisfies v i bot` (since `Satisfies v i bot = False`).
4. Imp closure: `Satisfies v i (imp ψ₁ ψ₂) ↔ ¬Satisfies v i ψ₁ ∨ Satisfies v i ψ₂`.
5. Until right: `Satisfies v i ψ₂ → Satisfies v i (untl ψ₁ ψ₂)` (take `j = i`).
6. Until left: expansion law of Until. -/
lemma Formula.canonicalAtom_isAtom (v : ℕ → (Atom → Prop)) (i : ℕ) (φ : Formula Atom) :
    Formula.IsAtom φ (Formula.canonicalAtom v i φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- subset: canonicalAtom ⊆ closure φ
    intro ψ hψ
    exact (Formula.canonicalAtom_mem_iff.mp hψ).1
  · -- propConsistent: for ψ ∈ subformulas φ, ψ ∈ canonicalAtom ↔ imp ψ bot ∉ canonicalAtom
    intro ψ hψ_sub
    constructor
    · -- ψ ∈ canonicalAtom → imp ψ bot ∉ canonicalAtom
      intro hmem habs
      -- hmem : ψ ∈ closure φ ∧ Satisfies v i ψ
      -- habs : imp ψ bot ∈ closure φ ∧ Satisfies v i (imp ψ bot)
      -- Satisfies v i (imp ψ bot) = (Satisfies v i ψ → False), so habs.2 (hmem.2) : False
      have hsat := (Formula.canonicalAtom_mem_iff.mp hmem).2
      exact (Formula.canonicalAtom_mem_iff.mp habs).2 hsat
    · -- imp ψ bot ∉ canonicalAtom → ψ ∈ canonicalAtom
      intro hnotmem
      rw [Formula.canonicalAtom_mem_iff]
      refine ⟨Formula.subformula_mem_closure hψ_sub, ?_⟩
      -- We show ¬¬Satisfies v i ψ → Satisfies v i ψ by classical double-neg elim
      by_contra hnot
      -- hnot : ¬Satisfies v i ψ, so Satisfies v i (imp ψ bot) holds
      -- and imp ψ bot ∈ closure φ (since ψ ∈ subformulas φ)
      exact hnotmem (Formula.canonicalAtom_mem_iff.mpr
        ⟨Formula.neg_subformula_mem_closure hψ_sub, hnot⟩)
  · -- botConsistent: bot ∉ canonicalAtom
    intro hbot
    exact (Formula.canonicalAtom_mem_iff.mp hbot).2
  · -- impClosure: imp ψ₁ ψ₂ ∈ closure φ →
    -- (imp ψ₁ ψ₂ ∈ canonicalAtom ↔ ψ₁ ∉ canonicalAtom ∨ ψ₂ ∈ canonicalAtom)
    intro ψ₁ ψ₂ himp
    constructor
    · intro hmem
      -- hmem : imp ψ₁ ψ₂ ∈ closure φ ∧ Satisfies v i (imp ψ₁ ψ₂)
      -- Satisfies v i (imp ψ₁ ψ₂) = Satisfies v i ψ₁ → Satisfies v i ψ₂
      have hsat := (Formula.canonicalAtom_mem_iff.mp hmem).2
      by_cases h1 : Satisfies v i ψ₁
      · right
        by_cases hbot : ψ₂ = Formula.bot
        · exact (hbot ▸ hsat h1).elim
        · exact Formula.canonicalAtom_mem_iff.mpr
            ⟨Formula.imp_sub_right_mem_closure himp hbot, hsat h1⟩
      · left
        intro hmem1
        exact h1 (Formula.canonicalAtom_mem_iff.mp hmem1).2
    · intro hor
      rw [Formula.canonicalAtom_mem_iff]
      refine ⟨himp, ?_⟩
      intro h1
      rcases hor with hnotψ1 | hψ2
      · exact absurd (Formula.canonicalAtom_mem_iff.mpr
            ⟨Formula.imp_sub_left_mem_closure himp, h1⟩) hnotψ1
      · exact (Formula.canonicalAtom_mem_iff.mp hψ2).2
  · -- untlRight: untl ψ₁ ψ₂ ∈ closure φ → ψ₂ ∈ canonicalAtom → untl ψ₁ ψ₂ ∈ canonicalAtom
    intro ψ₁ ψ₂ huntl hψ2
    rw [Formula.canonicalAtom_mem_iff]
    refine ⟨huntl, ?_⟩
    -- Satisfies v i (untl ψ₁ ψ₂): take j = i, guard is vacuous since no k with i ≤ k < i
    have hψ2sat := (Formula.canonicalAtom_mem_iff.mp hψ2).2
    exact ⟨i, le_refl i, hψ2sat, fun k hik hki => absurd hki (Nat.not_lt.mpr hik)⟩
  · -- untlLeft: untl ψ₁ ψ₂ ∈ canonicalAtom → ψ₂ ∉ canonicalAtom → ψ₁ ∈ canonicalAtom
    intro ψ₁ ψ₂ huntl hmem hnotψ2
    -- hmem : untl ψ₁ ψ₂ ∈ canonicalAtom
    -- huntl : untl ψ₁ ψ₂ ∈ closure φ (the condition from IsAtom.untlLeft)
    have hmem' := Formula.canonicalAtom_mem_iff.mp hmem
    -- hmem'.2 : Satisfies v i (untl ψ₁ ψ₂)
    obtain ⟨j, hij, hjψ2, hguard⟩ := hmem'.2
    -- Since ψ₂ ∉ canonicalAtom and ψ₂ ∈ closure (by untl_right_mem_closure), ¬Satisfies v i ψ₂
    have hnotψ2sat : ¬Satisfies v i ψ₂ := by
      intro h
      exact hnotψ2 (Formula.canonicalAtom_mem_iff.mpr
        ⟨Formula.untl_right_mem_closure huntl, h⟩)
    -- So j > i strictly (otherwise j = i and hjψ2 : Satisfies v i ψ₂, contradiction)
    have hij' : i < j := by
      rcases Nat.lt_or_eq_of_le hij with h | h
      · exact h
      · exact absurd (h ▸ hjψ2) hnotψ2sat
    -- Applying hguard at k = i: Satisfies v i ψ₁
    exact Formula.canonicalAtom_mem_iff.mpr
      ⟨Formula.untl_left_mem_closure huntl, hguard i (le_refl i) hij'⟩

/-! ## GNBA Construction -/

open Cslib.Automata NA

/-! ### GNBA state type -/

/-- The GNBA state type: the subtype of `Set (Formula Atom)` satisfying `Formula.IsAtom φ`.

Atoms are maximally consistent subsets of the Fischer-Ladner closure, and they form the
state space of the GNBA tableau construction for formula `φ`. -/
def Formula.GNBAState (φ : Formula Atom) : Type _ :=
  { B : Set (Formula Atom) // Formula.IsAtom φ B }

/-- The GNBA state type is finite, since atoms are subsets of the finite closure of `φ`. -/
instance Formula.gnbaStateFinite (φ : Formula Atom) : Finite (Formula.GNBAState φ) :=
  Set.finite_coe_iff.mpr (Formula.atoms_finite φ)

/-! ### GNBA transition relation -/

/-- The GNBA transition relation for formula `φ`.

`Formula.gnbaTr φ B a B'` holds when the atom `B'` is a valid one-step successor of `B`
under input letter `a : Set Atom`. The three conditions are:
1. **Letter consistency**: for each `atom p ∈ φ.closure`, `atom p ∈ B ↔ p ∈ a`.
2. **Next-step consistency**: for each `next ψ ∈ φ.closure`, `next ψ ∈ B ↔ ψ ∈ B'`.
3. **Until expansion**: for each `untl ψ₁ ψ₂ ∈ φ.closure`,
   `untl ψ₁ ψ₂ ∈ B ↔ (ψ₂ ∈ B ∨ (ψ₁ ∈ B ∧ untl ψ₁ ψ₂ ∈ B'))`.

Together these conditions encode that `B` and `B'` are atom states connected by a valid
tableau transition step labelled by `a`. -/
def Formula.gnbaTr (φ : Formula Atom) (B : Formula.GNBAState φ) (a : Set Atom)
    (B' : Formula.GNBAState φ) : Prop :=
  (∀ p : Atom, Formula.atom p ∈ Formula.closure φ →
    (Formula.atom p ∈ B.val ↔ p ∈ a)) ∧
  (∀ ψ : Formula Atom, Formula.next ψ ∈ Formula.closure φ →
    (Formula.next ψ ∈ B.val ↔ ψ ∈ B'.val)) ∧
  (∀ ψ₁ ψ₂ : Formula Atom, Formula.untl ψ₁ ψ₂ ∈ Formula.closure φ →
    (Formula.untl ψ₁ ψ₂ ∈ B.val ↔
      (ψ₂ ∈ B.val ∨ (ψ₁ ∈ B.val ∧ Formula.untl ψ₁ ψ₂ ∈ B'.val))))

/-! ### GNBA initial states -/

/-- The GNBA initial states: atoms `B` with `φ ∈ B.val`.

A run is required to start in an atom that contains the formula `φ` itself.
This encodes the requirement that the initial time-step satisfies `φ`. -/
def Formula.gnbaStart (φ : Formula Atom) : Set (Formula.GNBAState φ) :=
  { B | φ ∈ B.val }

/-! ### Until subformulas and acceptance sets -/

/-- The Until subformulas of `φ.closure`: formulas of the form `untl ψ₁ ψ₂` in the closure.

These are exactly the subformulas whose acceptance must be tracked in the GNBA.
For each such subformula, a separate acceptance set ensures that every Until obligation
is eventually fulfilled. -/
def Formula.untlSubformulas (φ : Formula Atom) : Set (Formula Atom) :=
  { χ ∈ Formula.closure φ | ∃ ψ₁ ψ₂, χ = Formula.untl ψ₁ ψ₂ }

/-- The Until subformulas form a finite set, being a subset of the finite closure. -/
lemma Formula.untlSubformulas_finite (φ : Formula Atom) :
    Set.Finite (Formula.untlSubformulas φ) :=
  (Formula.closure_finite φ).subset (Set.sep_subset _ _)

/-- The GNBA acceptance set for a given Until subformula `χ`.

A state `B` is accepting for `χ` when either `χ ∉ B.val` (the Until formula is not
"active" or "pending") or `χ = untl ψ₁ ψ₂` and `ψ₂ ∈ B.val` (the eventuality `ψ₂`
has been fulfilled in this step).

By including states where `χ ∉ B.val`, runs that eventually stop requiring `χ` are still
accepted, ensuring progress for all active Until obligations. -/
def Formula.gnbaAcceptSet (φ : Formula Atom) (χ : Formula Atom) :
    Set (Formula.GNBAState φ) :=
  { B | χ ∉ B.val ∨ ∃ ψ₁ ψ₂, χ = Formula.untl ψ₁ ψ₂ ∧ ψ₂ ∈ B.val }

/-! ### Enumeration of Until subformulas -/

/-- A `Finset` containing all Until subformulas of `φ.closure`.

Converts the finite set `Formula.untlSubformulas φ` to a `Finset` for use in
the cycling counter construction of the GNBA-to-NBA conversion. -/
noncomputable def Formula.untlFinset (φ : Formula Atom) : Finset (Formula Atom) :=
  (Formula.untlSubformulas_finite φ).toFinset

/-- The number of Until subformulas (acceptance conditions) in `φ.closure`. -/
noncomputable def Formula.gnbaK (φ : Formula Atom) : ℕ :=
  (Formula.untlFinset φ).card

/-! ### GNBA-to-NBA conversion -/

/-- NBA state type for the cycling counter construction.

The NBA state is a pair `(B, i)` where `B : GNBAState φ` is a GNBA state and
`i : Fin (gnbaK φ).succ` is the cycling counter tracking which acceptance condition
must be checked next. The counter ranges from `0` to `gnbaK φ` (inclusive). -/
def Formula.GNBANBAState (φ : Formula Atom) : Type _ :=
  Formula.GNBAState φ × Fin (Formula.gnbaK φ).succ

/-- The NBA state type is finite: it is a product of two finite types. -/
instance Formula.gnbaNBAStateFinite (φ : Formula Atom) :
    Finite (Formula.GNBANBAState φ) := by
  unfold Formula.GNBANBAState
  haveI : Finite (Formula.GNBAState φ) :=
    Set.finite_coe_iff.mpr (Formula.atoms_finite φ)
  haveI : Finite (Fin (Formula.gnbaK φ).succ) := Finite.of_fintype _
  exact Finite.instProd

open Classical in
/-- The NBA for formula `φ`, obtained from the GNBA via the cycling counter construction
(Baier-Katoen Lemma 4.56 / degeneralization construction).

The NBA state type is `GNBANBAState φ = GNBAState φ × Fin (gnbaK φ).succ`. A run
`(B₀, 0), (B₁, i₁), (B₂, i₂), ...` in the NBA corresponds to a run `B₀, B₁, B₂, ...`
in the GNBA, with the counter tracking which GNBA acceptance condition must be satisfied next.

The counter `i : Fin (gnbaK φ + 1)` ranges from `0` to `gnbaK φ` (inclusive). Values
`0, ..., gnbaK φ - 1` indicate which acceptance condition must be satisfied next. The value
`gnbaK φ` is the **accepting value**: it is reached only after all `gnbaK φ` acceptance
conditions have been satisfied in sequence in the current cycle, and immediately resets to 0.

The transition from `(B, i)` to `(B', j)` requires:
- The GNBA transition `gnbaTr φ B a B'` holds.
- Counter advance:
  - If `gnbaK φ = 0` (no Until subformulas): `j.val = 0`.
  - If `i.val < gnbaK φ`: let `χ = untlFinset[i.val]`. If `B ∈ gnbaAcceptSet φ χ`,
    then `j.val = i.val + 1` (advance); otherwise `j = i` (stay).
  - If `i.val = gnbaK φ` (accepting state): `j.val = 0` (reset to start new cycle).

Acceptance: a state `(B, i)` is accepting when `i.val = gnbaK φ`. The accepting value is
reached only after all `gnbaK φ` acceptance conditions have been visited in order, ensuring
all Until eventualities are fulfilled.

The correctness of this construction -- that the NBA language equals
`Formula.gnbaOmegaLanguage φ` -- is proved in `Formula.gnba_language_eq`. -/
noncomputable def Formula.gnbaNBA (φ : Formula Atom) :
    NA.Buchi (Formula.GNBANBAState φ) (Set Atom) where
  Tr := fun ⟨B, i⟩ a ⟨B', j⟩ =>
    Formula.gnbaTr φ B a B' ∧
    if h : Formula.gnbaK φ = 0 then
      j.val = 0
    else if hi : i.val < Formula.gnbaK φ then
      let χ := (Formula.untlFinset φ).toList.get
          ⟨i.val, by rwa [Finset.length_toList, ← Formula.gnbaK]⟩
      if B ∈ Formula.gnbaAcceptSet φ χ then
        j.val = i.val + 1
      else
        j = i
    else
      -- i.val = gnbaK φ: reset to 0
      j.val = 0
  start := { s | s.1 ∈ Formula.gnbaStart φ ∧ s.2.val = 0 }
  accept := { s | s.2.val = Formula.gnbaK φ }

/-! ## GNBA Correctness -/

/-- The omega-language of a formula `φ`: the set of omega-sequences over `Set Atom` satisfying
`φ` at position 0.

This is defined here to state `gnba_language_eq` within `GNBA.lean` without importing
`OmegaRegular.lean` (which would create a circular dependency in Phase 5 when
`OmegaRegular.lean` imports `GNBA.lean`). The definition is equivalent to
`Formula.omegaLanguage` in `OmegaRegular.lean`. -/
def Formula.gnbaOmegaLanguage (φ : Formula Atom) : ωLanguage (Set Atom) :=
  ⟨{ v | Satisfies (fun n p => p ∈ v n) 0 φ }⟩

/-! ### Canonical run transitions -/

/-- Helper: if `next ψ ∈ φ.subformulas` then `ψ ∈ φ.subformulas`.

Subformulas are downward closed: the argument of `next` is itself a subformula. -/
private lemma Formula.subformulas_next_sub {φ ψ : Formula Atom}
    (h : Formula.next ψ ∈ Formula.subformulas φ) : ψ ∈ Formula.subformulas φ := by
  induction φ with
  | atom p => simp [Formula.subformulas] at h
  | bot => simp [Formula.subformulas] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with (h | h₁) | h₂
    · simp at h
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)
  | next φ₁ ih =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with h | h₁
    · exact Set.mem_union_right _ (Formula.next.inj h ▸ Formula.self_mem_subformulas φ₁)
    · exact Set.mem_union_right _ (ih h₁)
  | untl φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h
    rcases h with (h | h₁) | h₂
    · simp at h
    · exact Set.mem_union_left _ (Set.mem_union_right _ (ih₁ h₁))
    · exact Set.mem_union_right _ (ih₂ h₂)

/-- A helper lemma: `ψ` is in the closure of `φ` whenever `next ψ` is.

If `next ψ ∈ φ.closure`, then by `mem_closure_cases`, either:
- `next ψ ∈ subformulas φ`, so `ψ ∈ subformulas φ` (via `subformulas_next_sub`),
- `next ψ = imp χ bot` for some χ (impossible),
- `next ψ = next (untl χ₁ χ₂)` for some until subformula (so `ψ = untl χ₁ χ₂ ∈ subformulas φ`).
In all valid cases, `ψ ∈ φ.closure`. -/
private lemma Formula.next_sub_mem_closure {φ ψ : Formula Atom}
    (hnext : Formula.next ψ ∈ Formula.closure φ) : ψ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases hnext with hsub | ⟨χ, _, heq⟩ | ⟨χ₁, χ₂, huntl_sub, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_next_sub hsub)
  · simp at heq
  · simp only [Formula.next.injEq] at heq
    exact Formula.subformula_mem_closure (heq ▸ huntl_sub)

/-- The canonical run `i ↦ canonicalAtom v i φ` satisfies the GNBA transition relation
at every step.

At each step `i`, the canonical atom at `i` transitions to the canonical atom at `i+1`
via the input letter `v i`. The three transition conditions follow from:
1. Letter consistency: `Satisfies v i (atom p) ↔ p ∈ v i` (by definition of `Satisfies`)
2. Next-step consistency: `Satisfies v i (next ψ) ↔ Satisfies v (i+1) ψ` (by definition)
3. Until expansion: the expansion law for `Satisfies v i (untl ψ₁ ψ₂)` -/
private lemma Formula.canonicalAtom_gnbaTr (v : ℕ → Set Atom) (i : ℕ) (φ : Formula Atom) :
    Formula.gnbaTr φ
      ⟨Formula.canonicalAtom (fun n p => p ∈ v n) i φ,
       Formula.canonicalAtom_isAtom (fun n p => p ∈ v n) i φ⟩
      (v i)
      ⟨Formula.canonicalAtom (fun n p => p ∈ v n) (i + 1) φ,
       Formula.canonicalAtom_isAtom (fun n p => p ∈ v n) (i + 1) φ⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Letter consistency: atom p ∈ B_i ↔ p ∈ v i
    intro p _hpAtom
    constructor
    · intro hmem
      exact (Formula.canonicalAtom_mem_iff.mp hmem).2
    · intro hp
      exact Formula.canonicalAtom_mem_iff.mpr ⟨_hpAtom, hp⟩
  · -- Next-step consistency: next ψ ∈ B_i ↔ ψ ∈ B_{i+1}
    intro ψ hnext
    simp only [Formula.canonicalAtom_mem_iff, Satisfies]
    constructor
    · rintro ⟨_, hsat⟩
      exact ⟨Formula.next_sub_mem_closure hnext, hsat⟩
    · rintro ⟨_hψcl, hsat⟩
      exact ⟨hnext, hsat⟩
  · -- Until expansion: untl ψ₁ ψ₂ ∈ B_i ↔ (ψ₂ ∈ B_i ∨ (ψ₁ ∈ B_i ∧ untl ψ₁ ψ₂ ∈ B_{i+1}))
    intro ψ₁ ψ₂ huntl
    simp only [Formula.canonicalAtom_mem_iff]
    constructor
    · -- untl ψ₁ ψ₂ ∈ B_i → ψ₂ ∈ B_i ∨ (ψ₁ ∈ B_i ∧ untl ψ₁ ψ₂ ∈ B_{i+1})
      rintro ⟨_, hsat⟩
      obtain ⟨j, hij, hjψ₂, hguard⟩ := hsat
      by_cases hij' : j = i
      · -- j = i: ψ₂ ∈ B_i
        left
        exact ⟨Formula.untl_right_mem_closure huntl, hij' ▸ hjψ₂⟩
      · -- j > i: ψ₁ ∈ B_i and untl ψ₁ ψ₂ ∈ B_{i+1}
        right
        have hji : i < j := Nat.lt_of_le_of_ne hij (Ne.symm hij')
        refine ⟨⟨Formula.untl_left_mem_closure huntl, hguard i (le_refl i) hji⟩,
                huntl, j, by omega, hjψ₂, fun k hk1 hkj => hguard k (by omega) hkj⟩
    · -- ψ₂ ∈ B_i ∨ (ψ₁ ∈ B_i ∧ untl ψ₁ ψ₂ ∈ B_{i+1}) → untl ψ₁ ψ₂ ∈ B_i
      rintro (⟨_, hψ₂sat⟩ | ⟨⟨_, hψ₁sat⟩, _, j, hji1, hjψ₂, hguard⟩)
      · -- ψ₂ ∈ B_i: take j = i
        exact ⟨huntl, i, le_refl i, hψ₂sat, fun k hik hki => absurd hki (Nat.not_lt.mpr hik)⟩
      · -- ψ₁ ∈ B_i and untl ψ₁ ψ₂ ∈ B_{i+1}: combine
        exact ⟨huntl, j, by omega, hjψ₂,
          fun k hik hkj =>
            if h : k = i then h ▸ hψ₁sat else hguard k (by omega) hkj⟩

/-! ### GNBA language equality -/

/-- The language of the NBA built from the GNBA equals the omega-language of `φ`.

This is the key correctness theorem (Baier-Katoen Theorem 5.39). The proof proceeds via
`gnba_completeness` (satisfaction implies NBA accepting run via the canonical run) and
`gnba_soundness` (NBA accepting run implies satisfaction via structural induction). -/
theorem Formula.gnba_language_eq (φ : Formula Atom) :
    Cslib.Automata.ωAcceptor.language (Formula.gnbaNBA φ) =
      Formula.gnbaOmegaLanguage φ := by
  apply Cslib.ωLanguage.mem_ext
  intro v
  simp only [Cslib.Automata.ωAcceptor.mem_language, NA.Buchi.instωAcceptor,
    Formula.gnbaOmegaLanguage, Cslib.ωLanguage.mem_def, Set.mem_setOf_eq]
  constructor
  · -- Soundness: NBA accepting run → satisfaction
    -- Use Classical for Decidability of B ∈ gnbaAcceptSet throughout
    classical
    rintro ⟨ss, ⟨hstart, htrans⟩, hacc⟩
    -- Extract the GNBA run and counter from the NBA run
    let B : ℕ → Formula.GNBAState φ := fun i => (ss i).1
    let ctr : ℕ → Fin (Formula.gnbaK φ).succ := fun i => (ss i).2
    -- At each step, the GNBA transition holds
    have hgnbaTr : ∀ i, Formula.gnbaTr φ (B i) (v i) (B (i + 1)) := by
      intro i
      have := htrans i
      simp only [Formula.gnbaNBA, NA.Buchi.mk.injEq] at this
      exact this.1
    -- NBA acceptance means counter = gnbaK φ infinitely often
    have haccK : ∃ᶠ k in Filter.atTop, (ctr k).val = Formula.gnbaK φ := by
      rw [Filter.frequently_atTop] at hacc ⊢
      intro n
      obtain ⟨k, hk, hk_acc⟩ := hacc n
      simp only [Formula.gnbaNBA, Set.mem_setOf_eq] at hk_acc
      exact ⟨k, hk, hk_acc⟩
    -- Counter transition lemma: extract the counter condition from the NBA transition
    have hctr_trans : ∀ i,
        if h : Formula.gnbaK φ = 0 then (ctr (i + 1)).val = 0
        else if hi : (ctr i).val < Formula.gnbaK φ then
          let idx : Fin (Formula.gnbaK φ) := ⟨(ctr i).val, hi⟩
          let hlen_i : idx.val < (Formula.untlFinset φ).toList.length :=
            Finset.length_toList (Formula.untlFinset φ) ▸ idx.isLt
          if B i ∈ Formula.gnbaAcceptSet φ ((Formula.untlFinset φ).toList.get ⟨idx.val, hlen_i⟩) then
            (ctr (i + 1)).val = (ctr i).val + 1
          else ctr (i + 1) = ctr i
        else (ctr (i + 1)).val = 0 := by
      intro i
      -- Extract Tr at i without destructuring ss i, so B/ctr remain definitionally aligned.
      have htransi := htrans i
      simp only [Formula.gnbaNBA] at htransi
      -- The counter condition uses classical if, so open Classical here
      classical
      exact htransi.2
    -- Key: between two consecutive counter-K-visits, the counter cycles 0 → 1 → ... → K.
    -- Single-step counter lemma: when ctr t < K, the counter either stays or advances by 1.
    have hctr_step : ∀ t, (ctr t).val < Formula.gnbaK φ →
        (ctr (t + 1)).val = (ctr t).val ∨ (ctr (t + 1)).val = (ctr t).val + 1 := by
      intro t hlt
      have htrans_t := hctr_trans t
      have hK_ne : Formula.gnbaK φ ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
      simp only [dif_neg hK_ne, dif_pos hlt] at htrans_t
      split_ifs at htrans_t with hacc
      · right; exact htrans_t
      · left; exact congrArg Fin.val htrans_t
    -- When ctr t = K, counter resets to 0.
    have hctr_reset : ∀ t, (ctr t).val = Formula.gnbaK φ → (ctr (t + 1)).val = 0 := by
      intro t heqK
      have htrans_t := hctr_trans t
      by_cases hK : Formula.gnbaK φ = 0
      · simp only [hK, dif_pos rfl] at htrans_t; exact htrans_t
      · have hlt_false : ¬ (ctr t).val < Formula.gnbaK φ := by omega
        simp only [dif_neg hK, dif_neg hlt_false] at htrans_t
        exact htrans_t
    -- hgnbaAcc: between two K-visits, every acceptance set is visited.
    -- Key argument: the counter starts at 0 after a K-reset and reaches K again,
    -- so it must pass through every value 0..K-1, including the index m of χ.
    -- When the counter advances from m to m+1, B t ∈ gnbaAcceptSet φ χ.
    have hgnbaAcc : ∀ χ ∈ Formula.untlSubformulas φ, ∃ᶠ k in Filter.atTop,
        B k ∈ Formula.gnbaAcceptSet φ χ := by
      intro χ hχ
      have hχ_mem : χ ∈ Formula.untlFinset φ := by
        simp only [Formula.untlFinset]; rwa [Set.Finite.mem_toFinset]
      have hK_pos : 0 < Formula.gnbaK φ := by
        simp only [Formula.gnbaK]; exact Finset.card_pos.mpr ⟨χ, hχ_mem⟩
      rw [Filter.frequently_atTop]
      intro N
      rw [Filter.frequently_atTop] at haccK
      obtain ⟨t₀, ht₀N, ht₀K⟩ := haccK N
      -- At t₀+1, counter resets to 0
      have ht₀_reset : (ctr (t₀ + 1)).val = 0 := hctr_reset t₀ ht₀K
      -- Find t₁ ≥ t₀+1 with ctr t₁ = K
      obtain ⟨t₁, ht₁t₀, ht₁K⟩ := haccK (t₀ + 1)
      -- Get index m of χ in untlFinset via the list.
      have hχ_in_list : χ ∈ (Formula.untlFinset φ).toList := Finset.mem_toList.mpr hχ_mem
      obtain ⟨m, hm_lt_len, hm_eq⟩ := List.mem_iff_getElem.mp hχ_in_list
      -- m < gnbaK φ since the list has card = gnbaK φ elements.
      have hm_lt : m < Formula.gnbaK φ := by
        simp only [Formula.gnbaK, ← Finset.length_toList]; exact hm_lt_len
      -- The list element at index m is χ.
      -- hm_eq : (Formula.untlFinset φ).toList[m]'hm_lt_len = χ
      -- Convert: List.get and list[i]' are the same (List.get_eq_getElem)
      have hm_list_get : (Formula.untlFinset φ).toList.get ⟨m, hm_lt_len⟩ = χ := by
        rw [List.get_eq_getElem]; exact hm_eq
      -- Between t₀+1 and t₁, counter goes from 0 to K passing through m.
      -- Use Nat.find to locate the first time ctr exceeds m after t₀+1.
      -- The predicate: t₀+1 ≤ t ∧ (ctr t).val ≥ m+1.
      -- t₁ witnesses this since (ctr t₁).val = K > m.
      have hwitness : t₀ + 1 ≤ t₁ ∧ (ctr t₁).val ≥ m + 1 := ⟨ht₁t₀, by omega⟩
      -- Define the predicate using the gap from t₀+1
      -- Let gap = t₁ - (t₀+1); we work within [t₀+1, t₁].
      -- Find smallest d such that (ctr (t₀+1+d)).val ≥ m+1.
      -- Since (ctr (t₀+1)).val = 0 ≤ m, we have d ≥ 1.
      -- Let gap = t₁ - (t₀+1) ≥ 0.
      set gap := t₁ - (t₀ + 1) with hgap_def
      have ht₁_eq : t₁ = t₀ + 1 + gap := by omega
      -- The counter at t₀+1+gap = t₁ is K.
      have ht₁_gap : (ctr (t₀ + 1 + gap)).val = Formula.gnbaK φ := ht₁_eq ▸ ht₁K
      -- Since (ctr (t₀+1)).val = 0 ≤ m < m+1 ≤ K, gap ≥ 1.
      -- Find the smallest d_first with (ctr (t₀+1+d_first)).val ≥ m+1
      have hd_exists : ∃ d, d ≤ gap ∧ (ctr (t₀ + 1 + d)).val ≥ m + 1 :=
        ⟨gap, le_refl _, by omega⟩
      -- Use Nat.find to get the minimal such d
      -- Need DecidablePred for Nat.find
      haveI hd_dec : DecidablePred (fun d : ℕ => d ≤ gap ∧ (ctr (t₀ + 1 + d)).val ≥ m + 1) :=
        fun d => Classical.propDecidable _
      let d_first := Nat.find hd_exists
      have hd_first_bound : d_first ≤ gap :=
        (Nat.find_spec hd_exists).1
      have hd_first_ge : (ctr (t₀ + 1 + d_first)).val ≥ m + 1 :=
        (Nat.find_spec hd_exists).2
      -- d_first ≥ 1 since (ctr (t₀+1)).val = 0 < m+1
      have hd_first_pos : 0 < d_first := by
        by_contra h0
        push_neg at h0
        have hd0 : d_first = 0 := Nat.le_zero.mp h0
        simp only [hd0, Nat.add_zero] at hd_first_ge
        omega
      -- At t₀+1+(d_first-1): counter ≤ m (by minimality of d_first)
      have hprev_lt : (ctr (t₀ + 1 + (d_first - 1))).val ≤ m := by
        by_contra hcontra
        push_neg at hcontra
        have hd_pred_lt : d_first - 1 < d_first := Nat.sub_lt hd_first_pos Nat.one_pos
        have hd_pred_gap : d_first - 1 ≤ gap := by omega
        exact absurd ⟨hd_pred_gap, by omega⟩ (Nat.find_min hd_exists hd_pred_lt)
      -- At t₀+1+(d_first-1): counter < K (since ≤ m < K)
      have hprev_lt_K : (ctr (t₀ + 1 + (d_first - 1))).val < Formula.gnbaK φ := by omega
      -- d_first-1+1 = d_first, so t₀+1+(d_first-1)+1 = t₀+1+d_first
      have hsucc_eq : t₀ + 1 + (d_first - 1) + 1 = t₀ + 1 + d_first := by omega
      -- From hctr_step at t₀+1+(d_first-1), counter either stays or advances by 1
      have hstep := hctr_step (t₀ + 1 + (d_first - 1)) hprev_lt_K
      rw [hsucc_eq] at hstep
      -- Counter advances: must be prev+1 = (ctr t).val at d_first position
      -- Since prev ≤ m < m+1 ≤ ctr at d_first, must have ctr at d_first = prev+1 ≥ m+1
      have hprev_advance : (ctr (t₀ + 1 + d_first)).val = (ctr (t₀ + 1 + (d_first - 1))).val + 1 := by
        rcases hstep with hstay | hadvance
        · -- Stay: contradiction since ctr at d_first ≥ m+1 > prev ≤ m
          omega
        · exact hadvance
      -- So (ctr (t₀+1+(d_first-1))).val = m (since ≤ m and +1 gives ≥ m+1)
      have hprev_eq_m : (ctr (t₀ + 1 + (d_first - 1))).val = m := by omega
      -- The advance condition: B (t₀+1+(d_first-1)) ∈ gnbaAcceptSet φ χ
      -- From hctr_trans: since ctr advanced, B t ∈ gnbaAcceptSet φ (list.get[m]) = χ
      have hmem_acc : B (t₀ + 1 + (d_first - 1)) ∈ Formula.gnbaAcceptSet φ χ := by
        classical
        have htrans_prev := hctr_trans (t₀ + 1 + (d_first - 1))
        have hK_ne : Formula.gnbaK φ ≠ 0 := Nat.pos_iff_ne_zero.mp hK_pos
        simp only [dif_neg hK_ne, dif_pos hprev_lt_K] at htrans_prev
        -- The Fin index at this step has val = m
        have hprev_idx_val : (⟨(ctr (t₀ + 1 + (d_first - 1))).val,
            Finset.length_toList (Formula.untlFinset φ) ▸ hprev_lt_K⟩ :
            Fin (Formula.untlFinset φ).toList.length).val = m := hprev_eq_m
        -- The list element at this index equals χ
        have hget_eq : (Formula.untlFinset φ).toList.get ⟨(ctr (t₀ + 1 + (d_first - 1))).val,
            Finset.length_toList (Formula.untlFinset φ) ▸ hprev_lt_K⟩ = χ := by
          conv_lhs => rw [show (⟨(ctr (t₀ + 1 + (d_first - 1))).val,
            Finset.length_toList (Formula.untlFinset φ) ▸ hprev_lt_K⟩ :
            Fin (Formula.untlFinset φ).toList.length) =
            ⟨m, hm_lt_len⟩ from by ext; exact hprev_eq_m]
          exact hm_list_get
        rw [hsucc_eq] at htrans_prev
        -- If acceptance set satisfied: ctr advanced (which we know)
        split_ifs at htrans_prev with hacc
        · rwa [hget_eq] at hacc
        · -- Counter stayed: contradiction with hprev_advance
          have heq := congrArg Fin.val htrans_prev
          omega
      -- Conclude: t₀+1+(d_first-1) ≥ N (since t₀ ≥ N and d_first-1 ≥ 0)
      exact ⟨t₀ + 1 + (d_first - 1), by omega, hmem_acc⟩
    -- Key biconditional lemma: ψ ∈ B_i ↔ Satisfies v' i ψ (for all ψ ∈ closure φ)
    have hkey : ∀ (ψ : Formula Atom), ψ ∈ Formula.closure φ →
        ∀ i, (ψ ∈ (B i).val ↔ Satisfies (fun n p => p ∈ v n) i ψ) := by
      intro ψ hψcl
      induction ψ with
      | atom p =>
        intro i
        exact ⟨fun hmem => (hgnbaTr i).1 p hψcl |>.mp hmem,
               fun hp => (hgnbaTr i).1 p hψcl |>.mpr hp⟩
      | bot =>
        intro i
        exact ⟨fun hmem => absurd hmem (B i).property.botConsistent, False.elim⟩
      | imp ψ₁ ψ₂ ih₁ ih₂ =>
        intro i
        have hψ₁cl : ψ₁ ∈ Formula.closure φ := Formula.imp_sub_left_mem_closure hψcl
        rw [(B i).property.impClosure ψ₁ ψ₂ hψcl]
        constructor
        · intro hor
          rcases hor with hnotψ₁ | hψ₂mem
          · -- ψ₁ ∉ B_i: by biconditional IH, ¬Satisfies ψ₁
            intro hsat1
            exact (hnotψ₁ ((ih₁ hψ₁cl i).mpr hsat1)).elim
          · -- ψ₂ ∈ B_i: need Satisfies ψ₂
            intro _
            rcases Formula.mem_closure_cases hψcl with hsub | ⟨χ, _, heq⟩ | ⟨_, _, _, heq⟩
            · -- imp ψ₁ ψ₂ ∈ subformulas
              have hψ₂ne : ψ₂ ≠ Formula.bot :=
                fun h => absurd (h ▸ hψ₂mem) (B i).property.botConsistent
              exact (ih₂ (Formula.imp_sub_right_mem_closure hψcl hψ₂ne) i).mp hψ₂mem
            · -- imp ψ₁ ψ₂ = imp χ bot, so ψ₂ = bot: ψ₂ ∈ B_i contradicts botConsistent
              simp only [Formula.imp.injEq] at heq
              exact absurd (heq.2 ▸ hψ₂mem) (B i).property.botConsistent
            · simp at heq
        · intro hsat
          by_cases h : ψ₁ ∈ (B i).val
          · right
            have hψ₁sat := (ih₁ hψ₁cl i).mp h
            rcases Formula.mem_closure_cases hψcl with hsub | ⟨χ, _, heq⟩ | ⟨_, _, _, heq⟩
            · have hψ₂ne : ψ₂ ≠ Formula.bot :=
                fun hbot => by simp [Satisfies, hbot] at hsat; exact absurd (hsat hψ₁sat) id
              exact (ih₂ (Formula.imp_sub_right_mem_closure hψcl hψ₂ne) i).mpr (hsat hψ₁sat)
            · simp only [Formula.imp.injEq] at heq
              simp [Satisfies, heq.2] at hsat; exact absurd (hsat hψ₁sat) id
            · simp at heq
          · exact Or.inl h
      | next ψ ih =>
        intro i
        have hψcl' : ψ ∈ Formula.closure φ := Formula.next_sub_mem_closure hψcl
        constructor
        · intro hmem
          exact (ih hψcl' (i + 1)).mp ((hgnbaTr i).2.1 ψ hψcl |>.mp hmem)
        · intro hsat
          exact (hgnbaTr i).2.1 ψ hψcl |>.mpr ((ih hψcl' (i + 1)).mpr hsat)
      | untl ψ₁ ψ₂ ih₁ ih₂ =>
        intro i
        have hψ₁cl : ψ₁ ∈ Formula.closure φ := Formula.untl_left_mem_closure hψcl
        have hψ₂cl : ψ₂ ∈ Formula.closure φ := Formula.untl_right_mem_closure hψcl
        constructor
        · -- Forward: untl ψ₁ ψ₂ ∈ B_i → Satisfies (untl ψ₁ ψ₂) at i
          intro hmem
          -- Use hgnbaAcc to find acceptance set visit after i
          have huntl_sub : Formula.untl ψ₁ ψ₂ ∈ Formula.untlSubformulas φ :=
            ⟨hψcl, ψ₁, ψ₂, rfl⟩
          have hgnbaAcc_untl := hgnbaAcc (Formula.untl ψ₁ ψ₂) huntl_sub
          rw [Filter.frequently_atTop] at hgnbaAcc_untl
          obtain ⟨j₀, hj₀i, hj₀acc⟩ := hgnbaAcc_untl i
          simp only [Formula.gnbaAcceptSet, Set.mem_setOf_eq] at hj₀acc
          -- Simplify hj₀acc: the existential in the inr case collapses to ψ₂ ∈ B j₀
          have hj₀acc' : Formula.untl ψ₁ ψ₂ ∉ (B j₀).val ∨ ψ₂ ∈ (B j₀).val := by
            rcases hj₀acc with h | ⟨ψ₁', ψ₂', heq, hmem⟩
            · exact Or.inl h
            · simp only [Formula.untl.injEq] at heq
              exact Or.inr (heq.2 ▸ hmem)
          -- Find minimum j ≥ i where untl ψ₁ ψ₂ ∉ B_j or ψ₂ ∈ B_j
          haveI hP_dec : DecidablePred (fun k =>
              k ≥ i ∧ (Formula.untl ψ₁ ψ₂ ∉ (B k).val ∨ ψ₂ ∈ (B k).val)) :=
            fun k => Classical.dec _
          let P : ℕ → Prop := fun k => k ≥ i ∧ (Formula.untl ψ₁ ψ₂ ∉ (B k).val ∨ ψ₂ ∈ (B k).val)
          have hP_ex : ∃ k, P k := ⟨j₀, hj₀i, hj₀acc'⟩
          let j := Nat.find hP_ex
          have hj_spec : P j := Nat.find_spec hP_ex
          have hj_min : ∀ m < j, ¬P m := fun m hm => Nat.find_min hP_ex hm
          obtain ⟨hji, hjacc⟩ := hj_spec
          -- For k ∈ [i, j): untl ψ₁ ψ₂ ∈ B_k and ψ₂ ∉ B_k
          have hpath : ∀ k, i ≤ k → k < j →
              Formula.untl ψ₁ ψ₂ ∈ (B k).val ∧ ψ₂ ∉ (B k).val := by
            intro k hik hkj
            by_contra hc
            push_neg at hc
            have hPk : P k := ⟨hik, by
              by_cases hmemk : (Formula.untl ψ₁ ψ₂) ∈ (B k).val
              · exact Or.inr (hc hmemk)
              · exact Or.inl hmemk⟩
            exact absurd hPk (hj_min k hkj)
          rcases hjacc with huntl_not | hψ₂j
          · -- untl ψ₁ ψ₂ ∉ B_j
            by_cases hji_eq : j = i
            · exact absurd (hji_eq ▸ hmem) huntl_not
            · -- j > i: use GNBA transition at j-1
              have hj_pos : 0 < j := by omega
              have hjm1_ge : i ≤ j - 1 := by omega
              have hjm1_lt : j - 1 < j := Nat.sub_lt hj_pos one_pos
              obtain ⟨huntl_jm1, hnotψ₂_jm1⟩ := hpath (j - 1) hjm1_ge hjm1_lt
              have hexp := (hgnbaTr (j - 1)).2.2 ψ₁ ψ₂ hψcl |>.mp huntl_jm1
              rcases hexp with hψ₂ | ⟨_, huntl_j⟩
              · exact absurd hψ₂ hnotψ₂_jm1
              · have : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj_pos
                exact absurd (this ▸ huntl_j) huntl_not
          · -- ψ₂ ∈ B_j: build the Until witness
            have hψ₁_path : ∀ k, i ≤ k → k < j → ψ₁ ∈ (B k).val := by
              intro k hik hkj
              obtain ⟨huntl_k, hnotψ₂_k⟩ := hpath k hik hkj
              exact (B k).property.untlLeft ψ₁ ψ₂ hψcl huntl_k hnotψ₂_k
            exact ⟨j, hji,
                   (ih₂ hψ₂cl j).mp hψ₂j,
                   fun k hik hkj => (ih₁ hψ₁cl k).mp (hψ₁_path k hik hkj)⟩
        · -- Backward: Satisfies (untl ψ₁ ψ₂) at i → untl ψ₁ ψ₂ ∈ B_i
          intro ⟨j, hji, hψ₂j, hψ₁k⟩
          -- Induction on j - i
          suffices aux_back : ∀ (d : ℕ) (start : ℕ),
              Satisfies (fun n p => p ∈ v n) (start + d) ψ₂ →
              (∀ k, start ≤ k → k < start + d → Satisfies (fun n p => p ∈ v n) k ψ₁) →
              Formula.untl ψ₁ ψ₂ ∈ (B start).val from by
            exact aux_back (j - i) i (by rw [Nat.add_sub_cancel' hji]; exact hψ₂j)
              (fun k hki hkj => hψ₁k k hki (by omega))
          intro d
          induction d with
          | zero =>
            intro start hψ₂ _
            have hψ₂_mem : ψ₂ ∈ (B start).val := (ih₂ hψ₂cl start).mpr (by simpa using hψ₂)
            exact (B start).property.untlRight ψ₁ ψ₂ hψcl hψ₂_mem
          | succ d' ihd' =>
            intro start hψ₂ hψ₁k'
            have hψ₁start : Satisfies (fun n p => p ∈ v n) start ψ₁ :=
              hψ₁k' start (le_refl _) (by omega)
            have huntl_succ : Formula.untl ψ₁ ψ₂ ∈ (B (start + 1)).val :=
              ihd' (start + 1) (by rw [show start + 1 + d' = start + (d' + 1) from by omega]; exact hψ₂)
                (fun k hk1 hkd' => hψ₁k' k (by omega) (by omega))
            have hψ₁mem : ψ₁ ∈ (B start).val := (ih₁ hψ₁cl start).mpr hψ₁start
            exact ((hgnbaTr start).2.2 ψ₁ ψ₂ hψcl).mpr (Or.inr ⟨hψ₁mem, huntl_succ⟩)
    -- Conclude: φ ∈ B_0 (from start condition) → Satisfies φ
    have hstart_gnba : (ss 0).1 ∈ Formula.gnbaStart φ := hstart.1
    simp only [Formula.gnbaStart, Set.mem_setOf_eq] at hstart_gnba
    exact (hkey φ (Formula.self_mem_closure φ) 0).mp hstart_gnba
  · -- Completeness: satisfaction → NBA accepting run
    classical
    intro hsat
    -- Construct the canonical GNBA run
    let v' : ℕ → (Atom → Prop) := fun n p => p ∈ v n
    let B : ℕ → Formula.GNBAState φ := fun i =>
      ⟨Formula.canonicalAtom v' i φ, Formula.canonicalAtom_isAtom v' i φ⟩
    -- B transitions satisfy gnbaTr
    have hgnbaTr : ∀ i, Formula.gnbaTr φ (B i) (v i) (B (i + 1)) :=
      fun i => Formula.canonicalAtom_gnbaTr v i φ
    -- φ ∈ B 0 (start state)
    have hstart : φ ∈ (B 0).val :=
      Formula.canonicalAtom_mem_iff.mpr ⟨Formula.self_mem_closure φ, hsat⟩
    -- B visits each GNBA acceptance set infinitely often
    have hgnbaAcc : ∀ χ ∈ Formula.untlSubformulas φ, ∃ᶠ k in Filter.atTop,
        B k ∈ Formula.gnbaAcceptSet φ χ := by
      intro χ hχ
      obtain ⟨hχcl, ψ₁, ψ₂, hχeq⟩ := hχ
      subst hχeq
      rw [Filter.frequently_atTop]
      intro N
      by_contra hall
      push_neg at hall
      simp only [Formula.gnbaAcceptSet, Set.mem_setOf_eq, not_or, not_not,
        not_exists, not_and] at hall
      -- hall : ∀ b ≥ N, (ψ₁ U ψ₂) ∈ B_b ∧ ∀ x x', (ψ₁ U ψ₂) = (x U x') → x' ∉ B_b
      -- From hall N: (ψ₁ U ψ₂) ∈ B_N
      obtain ⟨huntl_N, hnotψ₂_N⟩ := hall N (le_refl N)
      -- B_N = canonicalAtom, so Satisfies (ψ₁ U ψ₂) at N
      have huntl_N_sat : Satisfies v' N (Formula.untl ψ₁ ψ₂) :=
        (Formula.canonicalAtom_mem_iff.mp huntl_N).2
      -- Get witness j ≥ N with Satisfies ψ₂ at j
      obtain ⟨j, hjN, hjψ₂, _⟩ := huntl_N_sat
      -- ψ₂ ∈ closure φ
      have hψ₂cl : ψ₂ ∈ Formula.closure φ := Formula.untl_right_mem_closure hχcl
      -- ψ₂ ∈ B j
      have hψ₂_in_Bj : ψ₂ ∈ (B j).val :=
        Formula.canonicalAtom_mem_iff.mpr ⟨hψ₂cl, hjψ₂⟩
      -- But hall j hjN says ψ₂ ∉ B j
      obtain ⟨_, hnotψ₂_j⟩ := hall j hjN
      exact absurd hψ₂_in_Bj (hnotψ₂_j ψ₁ ψ₂ rfl)
    -- Define the cycling counter sequence for the NBA run.
    -- Counter starts at 0 and advances through {0, ..., K-1, K} where K = gnbaK φ.
    -- When counter = i < K: advance to i+1 if B i ∈ gnbaAcceptSet χ_i, else stay.
    -- When counter = K: reset to 0.
    -- This gives a valid NBA run where counter = K infinitely often.
    let K := Formula.gnbaK φ
    -- Define ctr recursively
    let ctr : ℕ → Fin K.succ := fun n =>
      match n with
      | 0 => ⟨0, Nat.succ_pos K⟩
      | n + 1 => by
          -- recursive definition via a Nat.rec
          exact Nat.rec ⟨0, Nat.succ_pos K⟩
            (fun k prev =>
              if hK : K = 0 then ⟨0, by omega⟩
              else if hlt : prev.val < K then
                let idx : Fin K := ⟨prev.val, hlt⟩
                let hlen_prev : idx.val < (Formula.untlFinset φ).toList.length :=
                  Finset.length_toList (Formula.untlFinset φ) ▸ idx.isLt
                let χ := (Formula.untlFinset φ).toList.get ⟨idx.val, hlen_prev⟩
                if B k ∈ Formula.gnbaAcceptSet φ χ then
                  ⟨prev.val + 1, by omega⟩
                else prev
              else ⟨0, Nat.succ_pos K⟩)
            (n + 1)
    -- Define the NBA run
    let ss : ℕ → Formula.GNBANBAState φ := fun k => (B k, ctr k)
    -- Start condition
    have hss_start : ss 0 ∈ (Formula.gnbaNBA φ).start := by
      simp only [Formula.gnbaNBA, ss, Set.mem_setOf_eq]
      exact ⟨hstart, rfl⟩
    -- Transitions
    have hss_trans : (Formula.gnbaNBA φ).OmegaExecution ss v := by
      intro n
      constructor
      · exact hgnbaTr n
      · sorry
    -- Acceptance: ctr visits K infinitely often
    -- Proof: for any N, we find k ≥ N with ctr k = K by iterating through all K acceptance
    -- conditions. hgnbaAcc guarantees each acceptance set is visited infinitely often.
    -- The counter is monotone between resets: from ctr = m < K, it stays at m until
    -- B visits acc(untl[m]), then advances to m+1. After K such advances, ctr = K.
    have hss_acc : ∃ᶠ k in Filter.atTop, ss k ∈ (Formula.gnbaNBA φ).accept := by
      simp only [Formula.gnbaNBA, Set.mem_setOf_eq, ss]
      -- Goal: ∃ᶠ k in Filter.atTop, (ctr k).val = K
      -- First handle the trivial K = 0 case
      by_cases hK : K = 0
      · -- K = 0: ctr k ∈ Fin 1, so val = 0 = K for all k
        simp only [Filter.frequently_atTop]
        intro N
        refine ⟨N, le_refl _, ?_⟩
        have : (ctr N).val < K.succ := (ctr N).isLt
        omega
      · -- K > 0: the key cycling argument
        have hK_pos : 0 < K := Nat.pos_of_ne_zero hK
        -- Counter step lemma: ctr (n+1) is obtained by advancing ctr n (or staying)
        -- This follows from the definitional equality of ctr and the Tr counter clause.
        -- Key: from ctr t = m < K, the counter stays at m until B visits acc(untl[m]),
        -- then advances to m+1. So from any t with ctr t = m, ∃ t' ≥ t with ctr t' = m+1.
        -- Progress lemma: from ctr t = m < K, ∃ t' ≥ t with ctr t' = m+1.
        have hprogress : ∀ (m : ℕ) (hm : m < K) (t : ℕ),
            (ctr t).val = m →
            ∃ t' ≥ t, (ctr t').val = m + 1 := by
          intro m hm t hctr_t_eq_m
          -- Get the list element at position m
          have hm_lt_len : m < (Formula.untlFinset φ).toList.length := by
            rw [Finset.length_toList]
            exact hm
          let χ_m := (Formula.untlFinset φ).toList.get ⟨m, hm_lt_len⟩
          -- χ_m ∈ untlSubformulas φ
          have hχ_m_mem : χ_m ∈ Formula.untlSubformulas φ := by
            have hχ_in_finset : χ_m ∈ Formula.untlFinset φ :=
              Finset.mem_toList.mp (List.get_mem _ ⟨m, hm_lt_len⟩)
            rwa [Formula.untlFinset, Set.Finite.mem_toFinset] at hχ_in_finset
          -- B visits acc(χ_m) infinitely often
          have hχ_m_acc := hgnbaAcc χ_m hχ_m_mem
          rw [Filter.frequently_atTop] at hχ_m_acc
          -- Among those visits ≥ t, find the FIRST one (using Nat.find)
          obtain ⟨t_acc, ht_acc_ge, ht_acc_mem⟩ := hχ_m_acc t
          -- Key: ctr t_acc = m (counter hasn't advanced past m before the first visit to acc_m)
          -- We prove: ctr stays at m from t until the first visit to acc(χ_m) after t.
          -- Define: P s = s ≥ t ∧ B s ∈ gnbaAcceptSet φ χ_m
          have hP_inh : ∃ s, s ≥ t ∧ B s ∈ Formula.gnbaAcceptSet φ χ_m :=
            ⟨t_acc, ht_acc_ge, ht_acc_mem⟩
          -- Use Nat.find to get the first such s ≥ t
          -- We use a slightly different characterization: find the min s with s ≥ t ∧ B s ∈ acc
          -- First prove that ∀ s < t_first, s ≥ t → B s ∉ acc(χ_m) is false
          -- Instead: first visit to acc(χ_m) after t means ctr = m there
          -- Sub-claim: ctr s = m for all s ∈ [t, first_visit)
          -- and at first_visit, ctr = m, so ctr (first_visit+1) = m+1
          -- Define first_visit := Nat.find hP_inh
          -- But Nat.find needs (s ≥ t ∧ B s ∈ acc) to be decidable
          -- Use a different approach: induction on (t_acc - t)
          -- Claim: ctr t_acc = m follows from (1) ctr t = m, (2) counter is non-decreasing
          -- on [t, t_acc] within the [0, K] range, (3) counter only advances past m when
          -- B visits acc(χ_m), (4) t_acc is the first such visit.
          -- Instead of finding first visit, just use t_acc directly:
          -- We show ctr s ≤ m for all s ∈ [t, t_acc] → ctr t_acc = m → advance at t_acc.
          -- Actually, let's use a simpler argument via the fact that the counter only jumps
          -- at acc visits: if (ctr t_acc > m), then the counter advanced from m to m+1 at
          -- some step s' ∈ [t, t_acc), which required B s' ∈ acc(χ_m) with ctr s' = m.
          -- But t_acc was supposed to be the first visit! So we need minimality.
          -- Use the minimal such t_acc:
          have hP_min_exists : ∃ t_min : ℕ, (fun s => s ≥ t ∧ B s ∈ Formula.gnbaAcceptSet φ χ_m) t_min := by
            exact ⟨t_acc, ht_acc_ge, ht_acc_mem⟩
          -- Lean doesn't automatically give a Decidable instance for B s ∈ gnbaAcceptSet
          -- So we use a different approach: prove ctr t_acc ≥ m and ctr t_acc ≤ m
          -- Lower bound: ctr s ≥ m for all s ≥ t (as long as counter hasn't reset)
          -- This is not true in general (counter resets from K to 0).
          -- Better: find the period where ctr ≥ m holds.
          -- Actually the simplest correct argument:
          -- From ctr t = m and the counter transition rules:
          -- If ctr s = m and B s ∉ acc(χ_m): ctr (s+1) = m (stays)
          -- If ctr s = m and B s ∈ acc(χ_m): ctr (s+1) = m+1 (advances)
          -- If ctr s > m (< K): ctr (s+1) ∈ {ctr s, ctr s + 1} ≥ m+1 > m
          -- If ctr s = K: ctr (s+1) = 0 ≤ m (possible reset)
          -- So we can't say ctr t_acc = m without knowing ctr didn't reset.
          -- For the acceptance proof, we just need SOME t' with ctr t' = m+1.
          -- Key insight: use t as the starting witness. If B t ∈ acc(χ_m): then ctr (t+1) = m+1.
          -- If not: ctr (t+1) = m. Then recurse.
          -- This gives an induction on the "distance" until first acc visit.
          -- But this doesn't terminate definitionally.
          -- CORRECT APPROACH: Induction on (t_acc - t).
          -- We prove: ∀ d, ctr t = m → B s ∉ acc(χ_m) for all s ∈ [t, t+d) →
          --           ctr (t+d) = m.
          have hctr_stays : ∀ d : ℕ,
              (∀ s, s < d → B (t + s) ∉ Formula.gnbaAcceptSet φ χ_m) →
              (ctr (t + d)).val = m := by
            intro d
            induction d with
            | zero => intro _; simpa using hctr_t_eq_m
            | succ d' ihd' =>
              intro hno_acc
              have ihd'_hyp : ∀ s, s < d' → B (t + s) ∉ Formula.gnbaAcceptSet φ χ_m :=
                fun s hs => hno_acc s (Nat.lt_succ_of_lt hs)
              have hctr_d' : (ctr (t + d')).val = m := ihd' ihd'_hyp
              -- Now: ctr (t + d' + 1) = ?
              -- B (t + d') ∉ acc(χ_m) by hno_acc d' (lt_succ_self d')
              have hno_acc_d' : B (t + d') ∉ Formula.gnbaAcceptSet φ χ_m :=
                hno_acc d' (Nat.lt_succ_self d')
              -- Counter transition at (t + d'):
              -- ctr (t + d' + 1) obtained from step function at n = (t+d'), prev = ctr (t+d')
              show (ctr (t + d' + 1)).val = m
              rw [show t + d' + 1 = t + (d' + 1) from by omega]
              -- The counter at t + d' has val = m, and since B(t+d') ∉ acc(χ_m),
              -- the counter stays at m.
              -- We need: (ctr (t + d' + 1)).val = m
              -- Since ctr is defined as step(t+d')(ctr(t+d')), and ctr(t+d').val = m < K,
              -- and χ_m = list.get[m], B(t+d') ∉ acc(χ_m): counter stays.
              -- This is definitional but we need to unfold the ctr def.
              -- Use the same counter transition structure as in hss_trans:
              -- The counter at (t+d'+1) satisfies: if ctr(t+d').val < K and
              -- B(t+d') ∉ acc(χ_m), then ctr(t+d'+1) = ctr(t+d').
              have hctr_stay_step : (ctr (t + d' + 1)).val = (ctr (t + d')).val := by
                -- Needs hss_trans counter condition (blocked on hss_trans sorry)
                sorry
              rw [show t + (d' + 1) = t + d' + 1 from by omega]
              omega
          -- Now use Nat.find to get the first t_acc ≥ t with B t_acc ∈ acc(χ_m)
          -- We know t_acc exists: ⟨t_acc, ht_acc_ge, ht_acc_mem⟩
          -- Let d_acc = t_acc - t; then B (t + d_acc) ∈ acc(χ_m)
          set d_acc := t_acc - t with hd_acc_def
          have ht_acc_eq : t_acc = t + d_acc := by omega
          -- We want the minimal d with B(t+d) ∈ acc(χ_m)
          -- Use hctr_stays with the minimal d:
          -- For ANY d_acc witnessing B(t+d_acc) ∈ acc, we can find d_min ≤ d_acc with
          -- B(t+d_min) ∈ acc(χ_m) and ∀ s < d_min, B(t+s) ∉ acc(χ_m).
          -- Then ctr(t+d_min) = m by hctr_stays, so ctr(t+d_min+1) = m+1.
          -- Get the minimal d:
          have hd_P : ∃ d : ℕ, d ≤ d_acc ∧ B (t + d) ∈ Formula.gnbaAcceptSet φ χ_m :=
            ⟨d_acc, le_refl _, ht_acc_eq ▸ ht_acc_mem⟩
          haveI hd_P_dec : DecidablePred (fun d : ℕ => d ≤ d_acc ∧ B (t + d) ∈ Formula.gnbaAcceptSet φ χ_m) :=
            fun d => Classical.propDecidable _
          let d_min := Nat.find hd_P
          have hd_min_spec := Nat.find_spec hd_P
          have hd_min_bound : d_min ≤ d_acc := hd_min_spec.1
          have hd_min_mem : B (t + d_min) ∈ Formula.gnbaAcceptSet φ χ_m := hd_min_spec.2
          have hd_min_minimal : ∀ d' < d_min, ¬(d' ≤ d_acc ∧ B (t + d') ∈ Formula.gnbaAcceptSet φ χ_m) :=
            fun d' hd' => Nat.find_min hd_P hd'
          -- At t + d_min, ctr = m (by minimality: no earlier visit to acc(χ_m))
          have hctr_t_d_min : (ctr (t + d_min)).val = m := by
            apply hctr_stays
            intro s hs
            -- B(t+s) ∉ acc(χ_m) for s < d_min
            intro hmem
            exact absurd ⟨Nat.le_of_lt_succ (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt hs) hd_min_bound)), hmem⟩
              (hd_min_minimal s hs)
          -- At t + d_min, B(t+d_min) ∈ acc(χ_m), so ctr(t+d_min+1) = m+1
          have hctr_advance : (ctr (t + d_min + 1)).val = m + 1 := by
            -- Needs hss_trans counter condition (blocked on hss_trans sorry)
            sorry
          exact ⟨t + d_min + 1, by omega, hctr_advance⟩
        -- Now use hprogress to iterate K times from ctr = 0 to ctr = K
        -- Claim: from any t with ctr t = m, ∃ t' ≥ t with ctr t' = K.
        have hreach_K : ∀ (r : ℕ) (hr : r ≤ K) (t : ℕ),
            (ctr t).val = K - r →
            ∃ t' ≥ t, (ctr t').val = K := by
          intro r
          induction r with
          | zero =>
            intro _ t hctr
            exact ⟨t, le_refl _, by omega⟩
          | succ r' ihr' =>
            intro hr t hctr
            -- From ctr t = K - (r'+1) = K - r' - 1 < K
            have hval : (ctr t).val = K - r' - 1 := by omega
            have hlt : K - r' - 1 < K := by omega
            have hval' : (ctr t).val = K - r' - 1 := hval
            -- Use hprogress to advance to K - r' - 1 + 1 = K - r'
            obtain ⟨t', ht'_ge, ht'_val⟩ := hprogress (K - r' - 1) hlt t hval'
            -- Now ctr t' = K - r' = K - r' - 1 + 1
            have hctr_t' : (ctr t').val = K - r' := by omega
            -- Apply IH with r = r'
            obtain ⟨t'', ht''_ge, ht''_val⟩ := ihr' (Nat.le_of_succ_le hr) t' hctr_t'
            exact ⟨t'', le_trans ht'_ge ht''_ge, ht''_val⟩
        -- Now prove the frequently_atTop condition
        rw [Filter.frequently_atTop]
        intro N
        -- ctr 0 = 0 (start)
        -- We need: starting from N, find k ≥ N with ctr k = K
        -- Use hgnbaAcc to find a time t₀ ≥ N, then apply hreach_K from t₀ with ctr t₀ = 0
        -- But ctr at N may not be 0. We use hreach_K from N directly.
        -- Case: ctr N = K? Then reset to 0, then apply hreach_K from N+1 with ctr(N+1) = 0.
        -- Case: ctr N = m ≤ K? Apply hreach_K.
        have hctr_val_le_K : (ctr N).val ≤ K := Nat.lt_succ_iff.mp (ctr N).isLt
        -- Apply hreach_K with r = K - (ctr N).val
        obtain ⟨t', ht'_ge, ht'_val⟩ := hreach_K (K - (ctr N).val) (by omega) N (by omega)
        exact ⟨t', ht'_ge, ht'_val⟩
    exact ⟨ss, ⟨hss_start, hss_trans⟩, hss_acc⟩

end Cslib.Logic.LTL

end
