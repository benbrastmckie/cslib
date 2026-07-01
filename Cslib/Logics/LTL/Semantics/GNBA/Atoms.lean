/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.GNBA.Closure
public import Cslib.Foundations.Data.OmegaSequence.Init
public import Cslib.Logics.LTL.Semantics.Satisfies

/-! # GNBA Atoms — Atom Predicate and Canonical Atoms

This module defines the atom predicate for the GNBA tableau construction and establishes
the canonical atom construction from semantic valuations.

## Contents

- `Formula.IsAtom`: the maximally-consistent-subset predicate for atoms
- `Formula.atoms_finite`: the collection of atoms for a formula is finite
- Closure-subformula relationship lemmas (`subformulas_trans`, `mem_closure_cases`, etc.)
- `Formula.canonicalAtom`: the canonical atom for a formula at a given position
- `Formula.canonicalAtom_isAtom`: the canonical atom satisfies the atom predicate
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {Atom : Type*}

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

/-- Subformula membership is transitive: if `χ` is a subformula of `ψ` and `ψ` is a
subformula of `φ`, then `χ` is a subformula of `φ`. -/
lemma Formula.subformulas_trans {χ ψ φ : Formula Atom}
    (h1 : χ ∈ Formula.subformulas ψ) (h2 : ψ ∈ Formula.subformulas φ) :
    χ ∈ Formula.subformulas φ := by
  induction φ with
  | atom p => simp only [Formula.subformulas, Set.mem_singleton_iff] at h2; subst h2; exact h1
  | bot => simp only [Formula.subformulas, Set.mem_singleton_iff] at h2; subst h2; exact h1
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with (rfl | h₁) | h₂
    · exact h1
    · exact Or.inl (Or.inr (ih₁ h₁))
    · exact Or.inr (ih₂ h₂)
  | next φ₁ ih =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with rfl | h₁
    · exact h1
    · exact Or.inr (ih h₁)
  | untl φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with (rfl | h₁) | h₂
    · exact h1
    · exact Or.inl (Or.inr (ih₁ h₁))
    · exact Or.inr (ih₂ h₂)

/-- Subformulas are downward-closed: left component of an `untl` subformula. -/
private lemma Formula.subformulas_untl_left {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₁ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans
    (Set.mem_union_left _ (Set.mem_union_right _ (Formula.self_mem_subformulas _))) h

/-- Subformulas are downward-closed: right component of an `untl` subformula. -/
private lemma Formula.subformulas_untl_right {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₂ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans
    (Set.mem_union_right _ (Formula.self_mem_subformulas _)) h

/-- Subformulas are downward-closed: left component of an `imp` subformula. -/
private lemma Formula.subformulas_imp_left {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₁ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans
    (Set.mem_union_left _ (Set.mem_union_right _ (Formula.self_mem_subformulas _))) h

/-- Subformulas are downward-closed: right component of an `imp` subformula. -/
private lemma Formula.subformulas_imp_right {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₂ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans
    (Set.mem_union_right _ (Formula.self_mem_subformulas _)) h

/-! ### Closure membership lemmas -/

/-- If `ψ` is in `φ.closure`, then `ψ` is a subformula of `φ`, or `ψ = imp χ bot` for
some subformula `χ`, or `ψ = next (untl χ₁ χ₂)` for some `untl` subformula.

De-privatized for use in `GNBA.Correctness`. -/
lemma Formula.mem_closure_cases {φ ψ : Formula Atom} (h : ψ ∈ Formula.closure φ) :
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


/-- Every subformula of `φ` is in `φ.closure`. (Alias for `subformula_mem_closure`) -/
lemma Formula.subformulas_subset_closure (φ : Formula Atom) :
    Formula.subformulas φ ⊆ Formula.closure φ :=
  fun _ h => Formula.subformula_mem_closure h

/-! ## Canonical atoms from semantic valuations -/

/-- The canonical atom at position `i` in valuation `v` for formula `φ`.

Given an ω-sequence of letter sets `v : ωSequence (Set Atom)` and position `i : ℕ`,
the canonical atom collects all closure formulas satisfied at the `i`-th position:

  `canonicalAtom v i φ = { ψ ∈ φ.closure | v.drop i, ⊨ ψ }`

This is the key bridge between LTL semantics and the GNBA state space: the canonical
atom is a valid atom (satisfies `Formula.IsAtom`), enabling the completeness direction
of the GNBA correctness proof. -/
def Formula.canonicalAtom (v : ωSequence (Set Atom)) (i : ℕ) (φ : Formula Atom) :
    Set (Formula Atom) :=
  { ψ ∈ Formula.closure φ | Satisfies (fun p s => p ∈ s) (v.drop i) ψ }

/-- Membership characterization for the canonical atom. -/
lemma Formula.canonicalAtom_mem_iff {v : ωSequence (Set Atom)} {i : ℕ} {φ ψ : Formula Atom} :
    ψ ∈ Formula.canonicalAtom v i φ ↔
    (ψ ∈ Formula.closure φ ∧ Satisfies (fun p s => p ∈ s) (v.drop i) ψ) := by
  simp [Formula.canonicalAtom]

/-! ### Canonical atom is an atom -/

/-- Helper: the left component of an `imp` in `φ.closure` is in `φ.closure`.

De-privatized for use in `GNBA.Correctness`. -/
lemma Formula.imp_sub_left_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.closure φ) : ψ₁ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, hχ, heq⟩ | ⟨_, _, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_imp_left hsub)
  · -- heq : imp ψ₁ ψ₂ = imp χ bot, so ψ₁ = χ ∈ subformulas φ
    simp only [Formula.imp.injEq] at heq
    exact Formula.subformula_mem_closure (heq.1 ▸ hχ)
  · simp at heq

/-- Helper: the right component of an `imp` in `φ.closure` is in `φ.closure` if not `bot`.

De-privatized for use in `GNBA.Correctness`. -/
lemma Formula.imp_sub_right_mem_closure {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.imp ψ₁ ψ₂ ∈ Formula.closure φ) (hne : ψ₂ ≠ Formula.bot) :
    ψ₂ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases h with hsub | ⟨χ, _, heq⟩ | ⟨_, _, _, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_imp_right hsub)
  · simp only [Formula.imp.injEq] at heq; exact absurd heq.2 hne
  · simp at heq

/-- The canonical atom satisfies the `Formula.IsAtom` predicate.

All six conditions of `IsAtom` hold for sets defined by semantic satisfaction:
1. Subset: by definition, elements of `canonicalAtom v i φ` are in `φ.closure`.
2. Propositional consistency: satisfaction of ψ and ¬ψ cannot both hold.
3. Bot consistency: `Satisfies val (v.drop i) bot = False`.
4. Imp closure: unfolding `Satisfies` for `imp`.
5. Until right: `Satisfies val (v.drop i) ψ₂ → Satisfies val (v.drop i) (untl ψ₁ ψ₂)`
   (take `j = 0`, the guard condition is vacuous).
6. Until left: expansion law of Until. -/
lemma Formula.canonicalAtom_isAtom (v : ωSequence (Set Atom)) (i : ℕ) (φ : Formula Atom) :
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
      -- hmem : imp ψ₁ ψ₂ ∈ closure φ ∧ Satisfies val (v.drop i) (imp ψ₁ ψ₂)
      -- = Satisfies val (v.drop i) ψ₁ → Satisfies val (v.drop i) ψ₂
      have hsat := (Formula.canonicalAtom_mem_iff.mp hmem).2
      by_cases h1 : Satisfies (fun p s => p ∈ s) (v.drop i) ψ₁
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
    -- Satisfies val (v.drop i) (untl ψ₁ ψ₂): take j = 0, guard is vacuous (∀ k < 0)
    have hψ2sat := (Formula.canonicalAtom_mem_iff.mp hψ2).2
    simp only [Satisfies]
    exact ⟨0, by simpa using hψ2sat, fun k hk => absurd hk (Nat.not_lt.mpr (Nat.zero_le k))⟩
  · -- untlLeft: untl ψ₁ ψ₂ ∈ canonicalAtom → ψ₂ ∉ canonicalAtom → ψ₁ ∈ canonicalAtom
    intro ψ₁ ψ₂ huntl hmem hnotψ2
    -- hmem : untl ψ₁ ψ₂ ∈ canonicalAtom
    -- huntl : untl ψ₁ ψ₂ ∈ closure φ (the condition from IsAtom.untlLeft)
    have hmem' := Formula.canonicalAtom_mem_iff.mp hmem
    -- hmem'.2 : Satisfies val (v.drop i) (untl ψ₁ ψ₂)
    -- = ∃ j', Satisfies val (v.drop (i+j')) ψ₂ ∧ ∀ k < j', Satisfies val (v.drop (i+k)) ψ₁
    simp only [Satisfies, ωSequence.drop_drop] at hmem'
    obtain ⟨j', hj'ψ2, hguard⟩ := hmem'.2
    -- Since ψ₂ ∉ canonicalAtom and ψ₂ ∈ closure (by untl_right_mem_closure),
    -- ¬Satisfies val (v.drop i) ψ₂
    have hnotψ2sat : ¬Satisfies (fun p s => p ∈ s) (v.drop i) ψ₂ := by
      intro h
      exact hnotψ2 (Formula.canonicalAtom_mem_iff.mpr
        ⟨Formula.untl_right_mem_closure huntl, h⟩)
    -- So j' > 0 strictly (otherwise j' = 0 and hj'ψ2 : Satisfies val (v.drop i) ψ₂)
    have hj'_pos : 0 < j' := by
      by_contra h0
      push Not at h0
      have hj'0 : j' = 0 := Nat.le_zero.mp h0
      simp only [hj'0, Nat.add_zero] at hj'ψ2
      exact absurd hj'ψ2 hnotψ2sat
    -- Applying hguard at k = 0: Satisfies val (v.drop (i+0)) ψ₁ = Satisfies val (v.drop i) ψ₁
    have h0_sat := hguard 0 hj'_pos
    simp only [Nat.add_zero] at h0_sat
    exact Formula.canonicalAtom_mem_iff.mpr
      ⟨Formula.untl_left_mem_closure huntl, h0_sat⟩

end Cslib.Logic.LTL

end
