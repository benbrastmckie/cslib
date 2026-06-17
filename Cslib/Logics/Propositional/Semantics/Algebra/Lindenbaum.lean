/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules
public import Cslib.Logics.Propositional.Semantics.Algebra
public import Mathlib.Order.Heyting.Regular

/-! # Lindenbaum Quotient Algebra

This module constructs the **Lindenbaum quotient algebra** for propositional logic: the
quotient of `Proposition Atom` by T-equivalence (`Theory.propositionSetoid`).

## Main Definitions

- `LindenbaumAlgebra T`: The quotient `Proposition Atom ⧸ T.propositionSetoid`.
- `lindenbaumMk T A`: Quotient map; `[A]T`.
- `GeneralizedHeytingAlgebra` instance for any theory T.
- `HeytingAlgebra` instance for intuitionistic T (`[IsIntuitionistic T]`).
- `BooleanAlgebra` instance for classical theories (`[IsIntuitionistic T] [IsClassical T]`).

## Main Results

- `lindenbaumMk_le_mk`: `[A]T ≤ [B]T ↔ DerivableIn T ({A} ⊢ B)`.
- `lindenbaumMk_sup`: `[A ∨ B]T = [A]T ⊔ [B]T`.
- `lindenbaumMk_inf`: `[A ∧ B]T = [A]T ⊓ [B]T`.
- `lindenbaumMk_himp`: `[A → B]T = [A]T ⇨ [B]T`.
- `nontrivialOfConsistent`: Consistent T gives nontrivial quotient.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Heyting

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

/-! ## The Lindenbaum Quotient Type -/

/-- The Lindenbaum algebra of a theory `T`. -/
abbrev LindenbaumAlgebra (T : Theory Atom) : Type u :=
  Quotient (T.propositionSetoid)

/-- The quotient map `Proposition Atom → LindenbaumAlgebra T`. -/
def lindenbaumMk (T : Theory Atom) (A : Proposition Atom) : LindenbaumAlgebra T :=
  Quotient.mk T.propositionSetoid A

/-! ## Order on the quotient -/

/-- `[A]T ≤ [B]T` iff `T ⊢ {A} ⊢ B`. Well-defined by T-equivalence. -/
def lindenbaumLe (T : Theory Atom) (x y : LindenbaumAlgebra T) : Prop :=
  Quotient.liftOn₂ x y
    (fun A B => DerivableIn T ({A} ⊢ B))
    (fun A B A' B' hA hB => propext ⟨
      fun h => by
        have step1 : DerivableIn T (({A'} ∪ ∅) ⊢ B) := DerivableIn.cut (Equiv.mpr hA) h
        have step2 : DerivableIn T ({A'} ⊢ B) := DerivableIn.weakCtx (by simp) step1
        have step3 : DerivableIn T (({A'} ∪ ∅) ⊢ B') := DerivableIn.cut step2 (Equiv.mp hB)
        exact DerivableIn.weakCtx (by simp) step3,
      fun h => by
        have step1 : DerivableIn T (({A} ∪ ∅) ⊢ B') := DerivableIn.cut (Equiv.mp hA) h
        have step2 : DerivableIn T ({A} ⊢ B') := DerivableIn.weakCtx (by simp) step1
        have step3 : DerivableIn T (({A} ∪ ∅) ⊢ B) := DerivableIn.cut step2 (Equiv.mpr hB)
        exact DerivableIn.weakCtx (by simp) step3⟩)

/-- The order on `LindenbaumAlgebra` reduces to derivability on representatives. -/
@[simp]
theorem lindenbaumLe_mk (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumLe T (lindenbaumMk T A) (lindenbaumMk T B) ↔ DerivableIn T ({A} ⊢ B) :=
  Iff.rfl

/-! ## Operations on the quotient -/

/-- Join: `[A] ⊔ [B] = [A ∨ B]`. -/
def lindenbaumSup (T : Theory Atom) (x y : LindenbaumAlgebra T) : LindenbaumAlgebra T :=
  Quotient.lift₂
    (fun A B => lindenbaumMk T (.or A B))
    (fun _ _ _ _ hA hB => Quotient.sound (Equiv.or_congr hA hB)) x y

/-- Meet: `[A] ⊓ [B] = [A ∧ B]`. -/
def lindenbaumInf (T : Theory Atom) (x y : LindenbaumAlgebra T) : LindenbaumAlgebra T :=
  Quotient.lift₂
    (fun A B => lindenbaumMk T (.and A B))
    (fun _ _ _ _ hA hB => Quotient.sound (Equiv.and_congr hA hB)) x y

/-- Heyting implication: `[A] ⇨ [B] = [A → B]`. -/
def lindenbaumHimp (T : Theory Atom) (x y : LindenbaumAlgebra T) : LindenbaumAlgebra T :=
  Quotient.lift₂
    (fun A B => lindenbaumMk T (.imp A B))
    (fun _ _ _ _ hA hB => Quotient.sound (Equiv.imp_congr hA hB)) x y

@[simp]
theorem lindenbaumSup_mk (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumSup T (lindenbaumMk T A) (lindenbaumMk T B) = lindenbaumMk T (.or A B) := rfl

@[simp]
theorem lindenbaumInf_mk (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumInf T (lindenbaumMk T A) (lindenbaumMk T B) = lindenbaumMk T (.and A B) := rfl

@[simp]
theorem lindenbaumHimp_mk (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumHimp T (lindenbaumMk T A) (lindenbaumMk T B) = lindenbaumMk T (.imp A B) := rfl

/-! ## GHA axiom lemmas (proved as standalone theorems) -/

theorem lindenbaumLe_refl (T : Theory Atom) (x : LindenbaumAlgebra T) :
    lindenbaumLe T x x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  change DerivableIn T ({A} ⊢ A)
  exact ⟨Derivation.ass (Finset.mem_singleton_self _)⟩

theorem lindenbaumLe_trans (T : Theory Atom) (x y z : LindenbaumAlgebra T)
    (hxy : lindenbaumLe T x y) (hyz : lindenbaumLe T y z) : lindenbaumLe T x z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  -- hxy : DerivableIn T ({A} ⊢ B), hyz : DerivableIn T ({B} ⊢ C)
  -- goal : DerivableIn T ({A} ⊢ C)
  change DerivableIn T ({A} ⊢ C)
  have hxy' : DerivableIn T ({A} ⊢ B) := hxy
  have hyz' : DerivableIn T ({B} ⊢ C) := hyz
  -- Use cut_away: reduce {A} ∪ {B} ⊢ C to {A} ⊢ C by eliminating B using hxy'
  apply DerivableIn.cut_away (Γ' := {B})
  · intro X hX
    simp only [Finset.mem_singleton] at hX; subst hX; exact hxy'
  · exact DerivableIn.weakCtx Finset.subset_union_right hyz'

theorem lindenbaumLe_antisymm (T : Theory Atom) (x y : LindenbaumAlgebra T)
    (hxy : lindenbaumLe T x y) (hyx : lindenbaumLe T y x) : x = y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  have hxy' : DerivableIn T ({A} ⊢ B) := hxy
  have hyx' : DerivableIn T ({B} ⊢ A) := hyx
  exact Quotient.sound (Theory.equiv_iff.mpr ⟨hxy', hyx'⟩)

theorem lindenbaumLe_sup_left (T : Theory Atom) (x y : LindenbaumAlgebra T) :
    lindenbaumLe T x (lindenbaumSup T x y) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  change DerivableIn T ({A} ⊢ .or A B)
  exact ⟨Derivation.orI1 {A} (Derivation.ass (Finset.mem_singleton_self _))⟩

theorem lindenbaumLe_sup_right (T : Theory Atom) (x y : LindenbaumAlgebra T) :
    lindenbaumLe T y (lindenbaumSup T x y) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  change DerivableIn T ({B} ⊢ .or A B)
  exact ⟨Derivation.orI2 {B} (Derivation.ass (Finset.mem_singleton_self _))⟩

theorem lindenbaumSup_le (T : Theory Atom) (x y z : LindenbaumAlgebra T)
    (hxz : lindenbaumLe T x z) (hyz : lindenbaumLe T y z) :
    lindenbaumLe T (lindenbaumSup T x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  change DerivableIn T ({.or A B} ⊢ C)
  have hAC : DerivableIn T ({A} ⊢ C) := hxz
  have hBC : DerivableIn T ({B} ⊢ C) := hyz
  -- orE uses G = {A ∨ B}, DA needs context insert A G = insert A {A ∨ B}
  -- weaken {A} ⊆ insert A {A ∨ B} and {B} ⊆ insert B {A ∨ B}
  have hDA : DerivableIn T (insert A {.or A B} ⊢ C) :=
    DerivableIn.weakCtx (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self A _)) hAC
  have hDB : DerivableIn T (insert B {.or A B} ⊢ C) :=
    DerivableIn.weakCtx (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self B _)) hBC
  obtain ⟨dA⟩ := hDA; obtain ⟨dB⟩ := hDB
  exact ⟨Derivation.orE {.or A B}
      (Derivation.ass (Finset.mem_singleton_self _)) dA dB⟩

theorem lindenbaumInf_le_left (T : Theory Atom) (x y : LindenbaumAlgebra T) :
    lindenbaumLe T (lindenbaumInf T x y) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  change DerivableIn T ({.and A B} ⊢ A)
  exact ⟨Derivation.andE1 {.and A B} (Derivation.ass (Finset.mem_singleton_self _))⟩

theorem lindenbaumInf_le_right (T : Theory Atom) (x y : LindenbaumAlgebra T) :
    lindenbaumLe T (lindenbaumInf T x y) y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  change DerivableIn T ({.and A B} ⊢ B)
  exact ⟨Derivation.andE2 {.and A B} (Derivation.ass (Finset.mem_singleton_self _))⟩

theorem lindenbaumLe_inf (T : Theory Atom) (x y z : LindenbaumAlgebra T)
    (hxy : lindenbaumLe T x y) (hxz : lindenbaumLe T x z) :
    lindenbaumLe T x (lindenbaumInf T y z) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  change DerivableIn T ({A} ⊢ .and B C)
  have hAB : DerivableIn T ({A} ⊢ B) := hxy
  have hAC : DerivableIn T ({A} ⊢ C) := hxz
  exact ⟨Derivation.andI {A} (Classical.choice hAB) (Classical.choice hAC)⟩

/-- The deduction theorem for the quotient: `x ≤ y ⇨ z ↔ x ⊓ y ≤ z`. -/
theorem lindenbaumLe_himp_iff (T : Theory Atom) (x y z : LindenbaumAlgebra T) :
    lindenbaumLe T x (lindenbaumHimp T y z) ↔ lindenbaumLe T (lindenbaumInf T x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  -- goal: DerivableIn T ({A} ⊢ B → C) ↔ DerivableIn T ({A ∧ B} ⊢ C)
  constructor
  · -- Forward: T ⊢ {A} ⊢ B → C  →  T ⊢ {A ∧ B} ⊢ C
    intro ⟨dImp⟩
    -- Build the proof that {A ∧ B} ⊢ C:
    -- 1. From {A ∧ B}: extract A by andE1, extract B by andE2
    -- 2. Weaken dImp from {A} to {A ∧ B} (since A ∈ {A ∧ B} is false... need another approach)
    -- Better: use impE on the weakened dImp
    -- Context: {A ∧ B}
    -- andE1: {A ∧ B} ⊢ A
    -- Weaken dImp to {A ∧ B}: A ∧ B context is fine since dImp needs {A}
    -- Wait: {A} is not a subset of {A ∧ B}. Use cut instead.
    -- cut (andE1 ...) (dImp weakened to insert A {A ∧ B}): gives {A ∧ B} ∪ Δ ⊢ B→C
    -- Hmm, let me use DerivableIn operations cleanly.
    -- Strategy: impE (andE1-based) (andE2-based) — work directly at DerivableIn level
    let AB : Proposition Atom := .and A B
    let G := ({AB} : Finset (Proposition Atom))
    -- andE1 gives G ⊢ A; andE2 gives G ⊢ B
    have hGA : DerivableIn T (G ⊢ A) :=
      ⟨Derivation.andE1 G (Derivation.ass (Finset.mem_singleton_self _))⟩
    have hGB : DerivableIn T (G ⊢ B) :=
      ⟨Derivation.andE2 G (Derivation.ass (Finset.mem_singleton_self _))⟩
    -- cut A from G: {A ∧ B} ⊢ A, and insert A Δ ⊢ B → C (i.e., {A} ⊢ B → C = dImp with Δ = ∅)
    -- cut gives G ∪ ∅ = G ⊢ B → C
    have hGImp : DerivableIn T (G ⊢ .imp B C) := by
      apply DerivableIn.cut_away (Γ' := {A})
      · intro X hX; simp only [Finset.mem_singleton] at hX; subst hX; exact hGA
      · exact ⟨dImp.weakCtx (Finset.singleton_subset_iff.mpr (Finset.mem_union_right G
            (Finset.mem_singleton_self _)))⟩
    -- Now impE: G ⊢ B → C and G ⊢ B gives G ⊢ C
    exact ⟨Derivation.impE (Classical.choice hGImp) (Classical.choice hGB)⟩
  · -- Backward: T ⊢ {A ∧ B} ⊢ C  →  T ⊢ {A} ⊢ B → C
    intro ⟨dAndBC⟩
    -- Use impI: from insert B {A} derive C
    refine ⟨Derivation.impI {A} ?_⟩
    -- context: insert B {A}; derive A ∧ B via andI, then cut with dAndBC
    have hAndI : DerivableIn T (insert B {A} ⊢ .and A B) :=
      ⟨Derivation.andI (insert B {A})
        (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_singleton_self A)))
        (Derivation.ass (Finset.mem_insert_self B {A}))⟩
    -- cut: T⊢(insert B {A}) ⊢ A∧B and T⊢(insert (A∧B) ∅ = {A∧B}) ⊢ C
    -- → T⊢(insert B {A}) ∪ ∅ ⊢ C = T⊢ insert B {A} ⊢ C
    -- Note: dAndBC has type Nonempty (T.Derivation {A∧B} C)
    -- and DerivableIn.cut needs DerivableIn T ((insert (A∧B) Δ) ⊢ C)
    -- Use DerivableIn T ({A∧B} ⊢ C) which is the same since {A∧B} = insert (A∧B) ∅
    have hAndBC : DerivableIn T ({.and A B} ⊢ C) := ⟨dAndBC⟩
    have hCut := DerivableIn.cut (Γ := insert B {A}) (Δ := ∅) hAndI hAndBC
    simp only [Finset.union_empty] at hCut
    exact Classical.choice hCut

theorem lindenbaumLe_top (T : Theory Atom) (x : LindenbaumAlgebra T) :
    lindenbaumLe T x (lindenbaumMk T (.imp .bot .bot)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  change DerivableIn T ({A} ⊢ .imp .bot .bot)
  exact ⟨Derivation.impI {A} (Derivation.ass (Finset.mem_insert_self _ _))⟩

/-! ## The main GHA instance -/

/-- The Lindenbaum algebra is a `GeneralizedHeytingAlgebra`.

This is the central result of the module. All sub-instances (PartialOrder, Lattice,
DistribLattice) are derived automatically from `le_himp_iff`. -/
instance : GeneralizedHeytingAlgebra (LindenbaumAlgebra T) where
  le := lindenbaumLe T
  top := lindenbaumMk T (.imp .bot .bot)
  sup := lindenbaumSup T
  inf := lindenbaumInf T
  himp := lindenbaumHimp T
  le_refl := lindenbaumLe_refl T
  le_trans := fun x y z => lindenbaumLe_trans T x y z
  le_antisymm := fun x y => lindenbaumLe_antisymm T x y
  le_sup_left := lindenbaumLe_sup_left T
  le_sup_right := lindenbaumLe_sup_right T
  sup_le := fun x y z => lindenbaumSup_le T x y z
  inf_le_left := lindenbaumInf_le_left T
  inf_le_right := lindenbaumInf_le_right T
  le_inf := fun x y z => lindenbaumLe_inf T x y z
  le_himp_iff := fun x y z => lindenbaumLe_himp_iff T x y z
  le_top := lindenbaumLe_top T

/-! ## Simp lemmas for the operations -/

/-- `[A]T ≤ [B]T ↔ T ⊢ {A} ⊢ B`. -/
@[simp]
theorem lindenbaumMk_le_mk (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumMk T A ≤ lindenbaumMk T B ↔ DerivableIn T ({A} ⊢ B) :=
  lindenbaumLe_mk T A B

/-- `[A ∨ B]T = [A]T ⊔ [B]T`. -/
@[simp]
theorem lindenbaumMk_sup (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumMk T (.or A B) = lindenbaumMk T A ⊔ lindenbaumMk T B :=
  (lindenbaumSup_mk T A B).symm

/-- `[A ∧ B]T = [A]T ⊓ [B]T`. -/
@[simp]
theorem lindenbaumMk_inf (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumMk T (.and A B) = lindenbaumMk T A ⊓ lindenbaumMk T B :=
  (lindenbaumInf_mk T A B).symm

/-- `[A → B]T = [A]T ⇨ [B]T`. -/
@[simp]
theorem lindenbaumMk_himp (T : Theory Atom) (A B : Proposition Atom) :
    lindenbaumMk T (.imp A B) = lindenbaumMk T A ⇨ lindenbaumMk T B :=
  (lindenbaumHimp_mk T A B).symm

/-- Top in the Lindenbaum algebra is `[⊥ → ⊥]T`. -/
theorem lindenbaumTop (T : Theory Atom) :
    (⊤ : LindenbaumAlgebra T) = lindenbaumMk T (.imp .bot .bot) := rfl

/-! ## Heyting Algebra (Intuitionistic Theories) -/

/-- Bottom: `⊥ = [⊥]T` (only for intuitionistic theories). -/
instance [IsIntuitionistic T] : Bot (LindenbaumAlgebra T) where
  bot := lindenbaumMk T .bot

/-- `⊥` in the HA instance is `[⊥]T`. -/
theorem lindenbaumBot [IsIntuitionistic T] :
    (⊥ : LindenbaumAlgebra T) = lindenbaumMk T .bot := rfl

theorem lindenbaumBot_le [IsIntuitionistic T] (x : LindenbaumAlgebra T) :
    lindenbaumLe T (lindenbaumMk T .bot) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  change DerivableIn T ({.bot} ⊢ A)
  exact ⟨Derivation.botE (Derivation.ass (Finset.mem_singleton_self _))⟩

/-- The Lindenbaum algebra of an intuitionistic theory is a `HeytingAlgebra`. -/
instance [IsIntuitionistic T] : HeytingAlgebra (LindenbaumAlgebra T) where
  bot_le x := lindenbaumBot_le x
  compl x := x ⇨ ⊥
  himp_bot _ := rfl

/-! ## Boolean Algebra (Classical Theories) -/

-- For classical theories with explosion, we use BooleanAlgebra.ofRegular.
-- The key: for a classical theory T with [IsIntuitionistic T] and [IsClassical T],
-- excluded middle is provable, so [A ∨ ¬A]T = ⊤.

/-- In a classical Lindenbaum algebra, excluded middle holds: `[A ∨ (A → ⊥)]T = ⊤`. -/
lemma lindenbaumEM [IsIntuitionistic T] [IsClassical T] (A : Proposition Atom) :
    lindenbaumMk T A ⊔ (lindenbaumMk T A ⇨ (⊥ : LindenbaumAlgebra T)) = ⊤ := by
  apply le_antisymm le_top
  rw [lindenbaumBot, ← lindenbaumMk_himp, ← lindenbaumMk_sup, lindenbaumTop, lindenbaumMk_le_mk]
  -- Goal: DerivableIn T ({⊥ → ⊥} ⊢ A ∨ (A → ⊥))
  -- Strategy: use DNE applied to ¬¬(A ∨ ¬A).
  -- We work in the context Γ₀ = {⊥ → ⊥}.
  -- Step 1: Suppose ¬(A ∨ ¬A), i.e., Γ₁ = insert (A ∨ ¬A → ⊥) Γ₀
  -- Step 2: From Γ₁, derive ¬A by: suppose A, then orI1 A gives A ∨ ¬A, contradicting ¬(A ∨ ¬A)
  -- Step 3: From Γ₁, derive ⊥ by: orI2 ¬A gives A ∨ ¬A, contradicting ¬(A ∨ ¬A)
  -- Step 4: So impI gives ¬(A ∨ ¬A) → ⊥ from Γ₀, i.e., ¬¬(A ∨ ¬A) derivable from Γ₀
  -- Step 5: DNE gives A ∨ ¬A from Γ₀
  let G₀ : Finset (Proposition Atom) := {.imp .bot .bot}
  let negEM := (.imp (.or A (.imp A .bot)) .bot : Proposition Atom)
  let G₁ : Finset (Proposition Atom) := insert negEM G₀
  -- Step 2: derive ¬A from G₁
  let negA : T.Derivation G₁ (.imp A .bot) :=
    Derivation.impI G₁
      (Derivation.impE
        -- ¬EM ∈ insert A G₁: mem_insert_of_mem (mem_insert_self negEM G₀)
        (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        -- orI1 produces A ∨ ¬A from A ∈ insert A G₁
        (Derivation.orI1 (insert A G₁)
          (Derivation.ass (Finset.mem_insert_self _ _))))
  -- Step 3: derive ⊥ from G₁ using negA
  let botFromNeg : T.Derivation G₁ .bot :=
    Derivation.impE
      -- ¬EM ∈ G₁: mem_insert_self negEM G₀
      (Derivation.ass (Finset.mem_insert_self _ _))
      -- orI2 produces A ∨ ¬A from ¬A
      (Derivation.orI2 G₁ negA)
  -- Step 4: derive ¬¬EM from G₀
  let dblNeg : T.Derivation G₀ (.imp negEM .bot) :=
    Derivation.impI G₀ botFromNeg
  -- Step 5: apply DNE
  exact ⟨Derivation.dne dblNeg⟩

/-- In a classical Lindenbaum algebra (with explosion), every `x ⊔ xᶜ` is regular. -/
lemma lindenbaumRegular [IsIntuitionistic T] [IsClassical T]
    (x : LindenbaumAlgebra T) : IsRegular (x ⊔ xᶜ) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  -- x = ⟦A⟧ = lindenbaumMk T A (definitionally)
  have hcompl : (lindenbaumMk T A)ᶜ = lindenbaumMk T A ⇨ ⊥ := himp_bot _
  have hEM : lindenbaumMk T A ⊔ (lindenbaumMk T A ⇨ (⊥ : LindenbaumAlgebra T)) = ⊤ :=
    lindenbaumEM A
  have hTop : lindenbaumMk T A ⊔ (lindenbaumMk T A)ᶜ = ⊤ := hcompl ▸ hEM
  have : (⟦A⟧ : LindenbaumAlgebra T) ⊔ (⟦A⟧)ᶜ = ⊤ := hTop
  rw [this]
  exact isRegular_top

/-- For classical theories with explosion, the Lindenbaum algebra is a `BooleanAlgebra`. -/
noncomputable instance [IsIntuitionistic T] [IsClassical T] :
    BooleanAlgebra (LindenbaumAlgebra T) :=
  BooleanAlgebra.ofRegular lindenbaumRegular

/-! ## Nontriviality -/

/-- If T does not derive `⊥`, the Lindenbaum algebra is nontrivial. -/
theorem nontrivialOfConsistent [IsIntuitionistic T]
    (hCons : ¬ DerivableIn T (⊥ : Proposition Atom)) :
    Nontrivial (LindenbaumAlgebra T) := by
  refine ⟨⊤, ⊥, ?_⟩
  simp only [lindenbaumTop, lindenbaumBot]
  intro h
  -- h : [⊥ → ⊥]T = [⊥]T
  have heq : (.imp .bot .bot : Proposition Atom) ≡[T] .bot := Quotient.exact h
  -- heq.mp: T ⊢ {⊥ → ⊥} ⊢ ⊥
  have hbot : DerivableIn T ({.imp .bot .bot} ⊢ .bot) := Equiv.mp heq
  apply hCons
  -- Cut with derivationTop (which proves ⊥ → ⊥) to get T ⊢ (∅ ∪ ∅) ⊢ ⊥
  have hcut : DerivableIn T ((∅ ∪ ∅) ⊢ .bot) :=
    DerivableIn.cut ⟨Theory.derivationTop⟩ hbot
  exact DerivableIn.weakCtx (by simp) hcut

end Cslib.Logic.PL
