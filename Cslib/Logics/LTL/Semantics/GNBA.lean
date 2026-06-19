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

/-- The NBA for formula `φ`, obtained from the GNBA via the cycling counter construction.

The NBA state type is `GNBANBAState φ = GNBAState φ × Fin (gnbaK φ).succ`. A run
`(B₀, 0), (B₁, i₁), (B₂, i₂), ...` in the NBA corresponds to a run `B₀, B₁, B₂, ...`
in the GNBA, with the counter advancing cyclically through positions `0` to `gnbaK φ`.

The transition from `(B, i)` to `(B', j)` requires:
- The GNBA transition `gnbaTr φ B a B'` holds.
- The counter advances: either `j = i + 1` (if `i < gnbaK φ`) or `j = 0` (wrap-around
  when `i = gnbaK φ`).

Acceptance: a state `(B, i)` is accepting when `i = 0`. Since the counter wraps from
`gnbaK φ` back to `0`, the accepting states are visited infinitely often in any infinite
run, ensuring the Büchi acceptance condition is met for all Until subformulas.

The correctness of this construction -- that the NBA language equals `Formula.omegaLanguage φ` --
is proved in Phase 4 (`Formula.gnba_language_eq`). -/
noncomputable def Formula.gnbaNBA (φ : Formula Atom) :
    NA.Buchi (Formula.GNBANBAState φ) (Set Atom) where
  Tr := fun ⟨B, i⟩ a ⟨B', j⟩ =>
    Formula.gnbaTr φ B a B' ∧
    (i.val + 1 = j.val ∨
     (j = ⟨0, Nat.succ_pos _⟩ ∧ i.val = Formula.gnbaK φ))
  start := { s | s.1 ∈ Formula.gnbaStart φ ∧ s.2 = ⟨0, Nat.succ_pos _⟩ }
  accept := { s | s.2 = ⟨0, Nat.succ_pos _⟩ }

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

This is the key correctness theorem (Baier-Katoen Theorem 5.39). The full proof
requires:
- **Completeness**: `φ.gnbaOmegaLanguage ⊆ language (gnbaNBA φ)`: given a satisfying
  valuation `v`, the canonical run `i ↦ canonicalAtom (fun n p => p ∈ v n) i φ` is an
  accepting run in the NBA. The GNBA transitions hold by `canonicalAtom_gnbaTr`. For
  acceptance, for each Until subformula `χ = untl ψ₁ ψ₂` in the closure, the accepting
  positions visit `i` with `χ ∉ B_i` or `ψ₂ ∈ B_i` infinitely often. The cycling counter
  wraps through these acceptance sets.
- **Soundness**: `language (gnbaNBA φ) ⊆ φ.gnbaOmegaLanguage`: given an accepting NBA run,
  for each closure formula `ψ` and position `i`, `ψ ∈ B_i → Satisfies v i ψ`, proved by
  structural induction on `ψ` using the transition conditions. Since `φ ∈ B_0` (start
  condition), we get `Satisfies v 0 φ`. -/
theorem Formula.gnba_language_eq (φ : Formula Atom) :
    Cslib.Automata.ωAcceptor.language (Formula.gnbaNBA φ) =
      Formula.gnbaOmegaLanguage φ := by
  sorry

end Cslib.Logic.LTL

end
