/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Foundations.Order.BrouwerianSemilattice
public import Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerian
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates
public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
public import Mathlib.Order.UpperLower.Principal

/-! # Nonempty Lower Sets: A Bot-Preserving Heyting Algebra Completion

This module constructs a **bot-preserving Heyting algebra completion** of any pointed
Brouwerian semilattice `[BrouwerianSemilattice B] [OrderBot B]`.

The construction is `NonemptyLowerSet B`: the type of lower sets in `B` that contain the
bottom element `(⊥ : B)`. This is a sublattice of `LowerSet B` with the crucial property
that the principal downset embedding `LowerSet.Iic : B → NonemptyLowerSet B` preserves `⊥`.

## Key Facts

- `LowerSet.Iic (⊥ : B) = {⊥} = (⊥ : NonemptyLowerSet B)` — bot is preserved.
- `NonemptyLowerSet B` is a `HeytingAlgebra`.
- The embedding `iicNonemptyLowerSet : B → NonemptyLowerSet B` is a BSL+OrderBot homomorphism.
- For or-free formulas: `AlgEvaluate (iicNonemptyLowerSet ∘ v) ⊥ φ = iicNonemptyLowerSet (PBE v φ)`.

## Why This Construction

`(⊥ : LowerSet B) = ∅` while `LowerSet.Iic (⊥ : B) = {⊥}`, so `LowerSet.Iic` does NOT
preserve `⊥` in the free join completion. The subtype of nonempty lower sets (those containing
`⊥`) fixes this: its bottom element is `{⊥} = Iic ⊥`.

## Main Definitions

- `NonemptyLowerSet B`: lower sets in `B` that contain `⊥`
- `iicNonemptyLowerSet`: the bot-preserving embedding `B → NonemptyLowerSet B`

## Main Results

- `instHeytingAlgebraNonemptyLowerSet`: `HeytingAlgebra (NonemptyLowerSet B)`
- `iicNonemptyLowerSet_bot`: `iicNonemptyLowerSet (⊥ : B) = ⊥`
- `iicNonemptyLowerSet_inf`: preserves `⊓`
- `iicNonemptyLowerSet_himp`: preserves `⇨`
- `iicNonemptyLowerSet_top`: preserves `⊤`
- `iicNonemptyLowerSet_eq_top_iff`: `iicNonemptyLowerSet x = ⊤ ↔ x = ⊤`
- `nonemptyLowerSet_evaluate_commutes`: or-free commutation with `PointedBrouwerianEvaluate`

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {B : Type*} [BrouwerianSemilattice B] [OrderBot B]

/-! ## Definition -/

/-- `NonemptyLowerSet B` is the type of lower sets in `B` that contain the bottom element.
The name reflects that every such set is nonempty (it contains `⊥`). -/
abbrev NonemptyLowerSet (B : Type*) [BrouwerianSemilattice B] [OrderBot B] : Type _ :=
  {S : LowerSet B // (⊥ : B) ∈ S}

namespace NonemptyLowerSet

/-! ## Closure Properties for the HeytingAlgebra Instance -/

/-- Intersection of lower sets containing `⊥` also contains `⊥`. -/
theorem bot_mem_inf (S T : LowerSet B) (hS : (⊥ : B) ∈ S) (hT : (⊥ : B) ∈ T) :
    (⊥ : B) ∈ S ⊓ T :=
  LowerSet.mem_inf_iff.mpr ⟨hS, hT⟩

/-- Union of lower sets: if `⊥ ∈ S` then `⊥ ∈ S ⊔ T`. -/
theorem bot_mem_sup_left (S T : LowerSet B) (hS : (⊥ : B) ∈ S) :
    (⊥ : B) ∈ S ⊔ T :=
  LowerSet.mem_sup_iff.mpr (Or.inl hS)

/-- The Heyting implication `S ⇨ T` contains `⊥` if `T` does.

The Heyting implication in `LowerSet B` satisfies `a ⊓ (S ⇨ T) ≤ T` by adjunction.
We prove `⊥ ∈ S ⇨ T` by showing `Iic ⊥ ≤ S ⇨ T`: by `le_himp_iff`, it suffices to show
`Iic ⊥ ⊓ S ≤ T`. Any element of `Iic ⊥ ⊓ S` is `≤ ⊥`, hence equals `⊥`, which lies in `T`
by downward closure of `T` and `hT`. -/
theorem bot_mem_himp (S T : LowerSet B) (hT : (⊥ : B) ∈ T) :
    (⊥ : B) ∈ S ⇨ T := by
  -- T ≤ S ⇨ T (since T ⊓ S ≤ T by inf_le_left), so T.carrier ⊆ (S ⇨ T).carrier.
  have hle : (T : Set B) ⊆ (S ⇨ T : LowerSet B) :=
    LowerSet.coe_subset_coe.mpr (le_himp_iff.mpr inf_le_left)
  exact hle hT

/-- The top element (the whole set) contains `⊥`. -/
theorem bot_mem_top : (⊥ : B) ∈ (⊤ : LowerSet B) :=
  LowerSet.mem_top

/-- The principal downset `Iic ⊥ = {x | x ≤ ⊥}` contains `⊥`. -/
theorem bot_mem_iic_bot : (⊥ : B) ∈ LowerSet.Iic (⊥ : B) :=
  LowerSet.mem_Iic_iff.mpr le_rfl

/-- For any `a : B`, the downset `Iic a` contains `⊥` (since `⊥ ≤ a`). -/
theorem bot_mem_iic (a : B) : (⊥ : B) ∈ LowerSet.Iic a :=
  LowerSet.mem_Iic_iff.mpr bot_le

/-! ## Typeclass Instance: HeytingAlgebra -/

/-- `NonemptyLowerSet B` is a `HeytingAlgebra`.

We build all instances by lifting from `LowerSet B`. The key is that the subtype
`{S : LowerSet B // ⊥ ∈ S}` is closed under all HA operations:
- `⊓`: closed (if `⊥ ∈ S` and `⊥ ∈ T`, then `⊥ ∈ S ⊓ T`)
- `⊔`: closed (if `⊥ ∈ S`, then `⊥ ∈ S ⊔ T`)
- `⇨`: closed (if `⊥ ∈ T`, then `⊥ ∈ S ⇨ T`)
- `⊤`: closed (`⊥ ∈ ⊤`)
- `⊥`: is `Iic ⊥` (the minimum nonempty lower set, with `⊥ ∈ Iic ⊥`)
- `compl`: `compl x = x ⇨ ⊥ : NonemptyLowerSet B`, where `⊥ ∈ x.val ⇨ Iic ⊥` by `bot_mem_himp`
-/
instance instHeytingAlgebraNonemptyLowerSet :
    HeytingAlgebra (NonemptyLowerSet B) where
  le x y := x.val ≤ y.val
  le_refl x := le_refl x.val
  le_trans x y z h₁ h₂ := le_trans h₁ h₂
  le_antisymm x y h₁ h₂ := Subtype.ext (le_antisymm h₁ h₂)
  sup x y := ⟨x.val ⊔ y.val, bot_mem_sup_left x.val y.val x.2⟩
  le_sup_left x y := le_sup_left (α := LowerSet B)
  le_sup_right x y := le_sup_right (α := LowerSet B)
  sup_le x y z h₁ h₂ := sup_le h₁ h₂
  inf x y := ⟨x.val ⊓ y.val, bot_mem_inf x.val y.val x.2 y.2⟩
  inf_le_left x y := inf_le_left (α := LowerSet B)
  inf_le_right x y := inf_le_right (α := LowerSet B)
  le_inf x y z h₁ h₂ := le_inf h₁ h₂
  top := ⟨⊤, bot_mem_top⟩
  le_top x := le_top (α := LowerSet B)
  himp x y := ⟨x.val ⇨ y.val, bot_mem_himp x.val y.val y.2⟩
  le_himp_iff x y z := by
    constructor
    · intro h
      exact (inf_le_inf_right y.val h).trans (himp_inf_le (α := LowerSet B))
    · intro h
      exact le_himp_iff.mpr h
  bot := ⟨LowerSet.Iic (⊥ : B), bot_mem_iic_bot⟩
  bot_le x := by
    change LowerSet.Iic (⊥ : B) ≤ x.val
    rw [LowerSet.Iic_le]
    exact x.2
  compl x := ⟨x.val ⇨ LowerSet.Iic (⊥ : B), bot_mem_himp x.val _ bot_mem_iic_bot⟩
  himp_bot x := rfl

/-! ## The Embedding: B → NonemptyLowerSet B -/

/-- The principal downset embedding, sending `a ↦ ↓a`.
This preserves `⊥`: `iicNonemptyLowerSet ⊥ = ⊥ : NonemptyLowerSet B`. -/
def iicNonemptyLowerSet (a : B) : NonemptyLowerSet B :=
  ⟨LowerSet.Iic a, bot_mem_iic a⟩

@[simp]
theorem iicNonemptyLowerSet_val (a : B) :
    (iicNonemptyLowerSet a).val = LowerSet.Iic a := rfl

/-! ## Embedding Preserves Operations -/

/-- `iicNonemptyLowerSet` preserves meet. -/
theorem iicNonemptyLowerSet_inf (a b : B) :
    iicNonemptyLowerSet (a ⊓ b) = iicNonemptyLowerSet a ⊓ iicNonemptyLowerSet b := by
  apply Subtype.ext
  simp only [iicNonemptyLowerSet_val]
  exact LowerSet.Iic_inf a b

/-- `iicNonemptyLowerSet` preserves Heyting implication. -/
theorem iicNonemptyLowerSet_himp (a b : B) :
    iicNonemptyLowerSet (a ⇨ b) = iicNonemptyLowerSet a ⇨ iicNonemptyLowerSet b := by
  apply Subtype.ext
  simp only [iicNonemptyLowerSet_val]
  exact iicHimp a b

/-- `iicNonemptyLowerSet` preserves `⊥`. -/
@[simp]
theorem iicNonemptyLowerSet_bot :
    iicNonemptyLowerSet (⊥ : B) = (⊥ : NonemptyLowerSet B) := rfl

/-- `iicNonemptyLowerSet` preserves `⊤`. -/
@[simp]
theorem iicNonemptyLowerSet_top :
    iicNonemptyLowerSet (⊤ : B) = (⊤ : NonemptyLowerSet B) := by
  apply Subtype.ext
  simp only [iicNonemptyLowerSet_val]
  exact LowerSet.Iic_top

/-- `iicNonemptyLowerSet x = ⊤` iff `x = ⊤`. -/
theorem iicNonemptyLowerSet_eq_top_iff {x : B} :
    iicNonemptyLowerSet x = ⊤ ↔ x = ⊤ := by
  constructor
  · intro h
    have h' : (iicNonemptyLowerSet x).val = (⊤ : NonemptyLowerSet B).val :=
      congrArg Subtype.val h
    simp only [iicNonemptyLowerSet_val] at h'
    rw [show (⊤ : NonemptyLowerSet B).val = ⊤ from rfl] at h'
    exact LowerSet.Iic_injective (h'.trans LowerSet.Iic_top.symm)
  · intro h
    rw [h, iicNonemptyLowerSet_top]

/-! ## Or-Free Commutation Lemma -/

/-- For or-free formulas, `iicNonemptyLowerSet` commutes with pointed Brouwerian evaluation:
`iicNonemptyLowerSet (PointedBrouwerianEvaluate v φ) = AlgEvaluate (iicNonemptyLowerSet ∘ v) ⊥ φ`

The key distinction from the plain `LowerSet` commutation: at the `bot` case, both sides
equal `⊥ : NonemptyLowerSet B = Iic (⊥ : B)`. In the plain `LowerSet`, `Iic ⊥ ≠ ⊥ = ∅`. -/
theorem nonemptyLowerSet_evaluate_commutes
    {Atom : Type*} {B : Type*} [BrouwerianSemilattice B] [OrderBot B]
    (v : Atom → B) (φ : PL.Proposition Atom) (hφ : φ.IsOrFree = true) :
    iicNonemptyLowerSet (PointedBrouwerianEvaluate v φ) =
    AlgEvaluate (iicNonemptyLowerSet ∘ v) (⊥ : NonemptyLowerSet B) φ := by
  induction φ with
  | atom x => rfl
  | bot =>
    simp [AlgEvaluate_bot, iicNonemptyLowerSet_bot]
  | imp a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hφ
    simp only [PointedBrouwerianEvaluate_imp, AlgEvaluate_imp,
               iicNonemptyLowerSet_himp, iha hφ.1, ihb hφ.2]
  | and a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hφ
    simp only [PointedBrouwerianEvaluate_and, AlgEvaluate_and,
               iicNonemptyLowerSet_inf, iha hφ.1, ihb hφ.2]
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hφ

end NonemptyLowerSet

end Cslib.Logic.PL

end
