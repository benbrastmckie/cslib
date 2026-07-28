/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5

/-! # Total-`r` birelational models cannot refute `IS5` non-theorems

Under the `BForces` box clause `w ⊩ □φ ↔ ∀ w' ≥ w, ∀ u, r w' u → u ⊩ φ`
(`Semantics/Birelational.lean`), a **total** modal accessibility relation `r` makes the
quantification world-independent: box degenerates to a global modality, `w ⊩ □φ ↔ ∀ u, u ⊩ φ`.
A meta-level classical case split on `∀ u, val u a` then forces the excluded-middle instance
`□a ∨ ¬□a` at *every* world of *every* total-`r` model (`bforces_boxEm_of_total`) — no frame
condition and no monotonicity of the valuation is even needed. Yet `□a ∨ ¬□a` is **not**
`IS5`-derivable (`boxEm_not_derivable`): the two-world chain `w₀ ≤ w₁` with `r := Eq` is an
`is5FC` model refuting both disjuncts at `w₀`, and `is5_soundness_derivable` converts the
countermodel into underivability.

Consequently total-`r` models cannot separate `IS5` non-theorems from theorems: any
construction requiring, for every pair `(H, A)` with `A ∉ modalDeductiveClosure IS5ModalAxiom
H`, a total-`r` countermodel forcing `H` and refuting `A`, is refuted outright at the instance
`H := ∅`, `A := □a ∨ ¬□a` (`is5TotalCountermodelSupply_false`). This closes the product-model
route toward `CS5PairSeedRightExclusion` (`Constructive/CS5Completeness.lean`), whose product
construction is only sound when the base accessibility relation is total — totality is the only
admissible fix for `≤`-closure of the product carrier, and totality is exactly what this module
shows to be fatal. The `≤`-mediated delicacy of birelational frame conditions that makes such
collapses possible is discussed in [MarinMoralesStrassburger2021], Sections 7–8.

## Main Definitions

- `boxEm`: the separating formula `□a ∨ ¬□a` (with `¬φ := φ → ⊥`).
- `IS5TotalCountermodel`: bundled model data — a total-`r` birelational model with monotone
  valuation and worlds `u ⊩ H`, `v ⊮ A`, `r u v` — the supply a total-model countermodel
  construction would need for the pair `(H, A)`.
- `IS5TotalCountermodelSupply`: the statement that such a countermodel exists for every
  `(H, A)` with `A ∉ modalDeductiveClosure IS5ModalAxiom H`.

## Main Results

- `bforces_boxEm_of_total`: total-`r` models force `□a ∨ ¬□a` at every world.
- `boxEm_not_derivable`: `□a ∨ ¬□a` is not derivable from `IS5ModalAxiom` (fully constructive —
  the classical case split is only needed on the validity side).
- `is5TotalCountermodelSupply_false`: the total-countermodel supply is false for every atom
  type with a distinguished element.

## References

* [M. Marin, S. Morales, L. Straßburger, *A fully labelled proof system for intuitionistic
  modal logics*][MarinMoralesStrassburger2021], Sections 7–8 (birelational frame-condition
  interaction with the intuitionistic preorder).
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational semantics, `IS5` frame class).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The separating formula and its total-model validity -/

/-- The separating formula `□a ∨ ¬□a` (with `¬φ := φ → ⊥`): an instance of excluded middle at
a boxed atom. Total-`r` models force it everywhere (`bforces_boxEm_of_total`); `IS5` does not
derive it (`boxEm_not_derivable`). -/
abbrev boxEm (a : Atom) : Proposition Atom :=
  (Proposition.box (Proposition.atom a)).or
    ((Proposition.box (Proposition.atom a)).imp Proposition.bot)

/-- **Total-model validity of `□a ∨ ¬□a`.** In any birelational model whose modal relation `r`
is total, `□a ∨ ¬□a` is forced at every world. Neither the `is5FC` frame conditions nor
`≤`-monotonicity of `val` is needed: totality alone degenerates the box clause to the
world-independent `∀ u, val u a`, and the meta-level classical case split on that proposition
decides the disjunction. -/
theorem bforces_boxEm_of_total {World : Type v} [Preorder World]
    (r : World → World → Prop) (total : ∀ x y, r x y)
    (val : World → Atom → Prop) (a : Atom) (w : World) :
    BForces r val (fun _ => False) w (boxEm a) := by
  by_cases h : ∀ u : World, val u a
  · -- Left disjunct: `□a` holds since every `r`-successor of every `≤`-successor forces `a`.
    exact Or.inl fun w' _ u _ => h u
  · -- Right disjunct: some `u₀` fails `a`, and totality makes `u₀` an `r`-successor of every
    -- world, so no `≤`-successor of `w` forces `□a` — `¬□a` holds vacuously.
    obtain ⟨u₀, hu₀⟩ := not_forall.mp h
    exact Or.inr fun w' _ hbox => hu₀ (hbox w' (le_refl w') u₀ (total w' u₀))

/-! ## `□a ∨ ¬□a` is not `IS5`-derivable

Countermodel: the two-world chain `w₀ ≤ w₁` with `r := Eq` (identity is an equivalence, so
`is5FC` holds; `f1`/`f2` hold with witnesses `w'`/`u'`), `a` true at `w₁` only (monotone).
At `w₀`: `□a` fails (instantiate the box at `w₀` itself, whose unique `Eq`-successor `w₀`
fails `a`), and `¬□a` fails (the `≤`-successor `w₁` forces `□a`, since every `≤`-successor of
`w₁` is `w₁` and its unique `Eq`-successor `w₁` forces `a`). -/

/-- The two-world chain carrying the countermodel for `boxEm_not_derivable`. -/
inductive BoxEmWorld where
  /-- Bottom world: `a` false here. -/
  | w0
  /-- Top world: `a` true here. -/
  | w1

/-- Chain order: `x ≤ y` iff `x = y` or `y` is the top world. -/
instance : Preorder BoxEmWorld where
  le x y := x = y ∨ y = BoxEmWorld.w1
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    cases hxy with
    | inl h => exact h ▸ hyz
    | inr h => cases hyz with
      | inl h2 => exact Or.inr (h2 ▸ h)
      | inr h2 => exact Or.inr h2

/-- Every `≤`-successor of the top world is the top world. -/
theorem BoxEmWorld.eq_w1_of_w1_le {x : BoxEmWorld} (h : BoxEmWorld.w1 ≤ x) :
    x = BoxEmWorld.w1 := by
  cases h with
  | inl h => exact h.symm
  | inr h => exact h

/-- The valuation "true exactly at `w₁`" is `≤`-monotone. -/
theorem BoxEmWorld.eq_w1_of_le {x y : BoxEmWorld} (h : x ≤ y) (hx : x = BoxEmWorld.w1) :
    y = BoxEmWorld.w1 := by
  cases h with
  | inl h => exact h ▸ hx
  | inr h => exact h

/-- **Underivability of `□a ∨ ¬□a`.** `□a ∨ ¬□a` is not derivable from `IS5ModalAxiom`, by
`is5_soundness_derivable` and the two-world chain countermodel (`BoxEmWorld`, `r := Eq`,
`a` true at `w₁` only). Fully constructive: no classical axiom enters this direction. -/
theorem boxEm_not_derivable (a : Atom) : ¬ Derivable IS5ModalAxiom (boxEm a) := by
  intro h
  have hvalid := is5_soundness_derivable (Atom := Atom) h
  have hforce := hvalid BoxEmWorld (fun x y => x = y)
    ⟨fun _ => rfl, fun h1 h2 => h1.trans h2, fun h1 => h1.symm⟩
    (fun {_ w' _} hle hr => ⟨w', rfl, hr ▸ hle⟩)
    (fun {_ _ u'} hr hle => ⟨u', hr.symm ▸ hle, rfl⟩)
    (fun x (_ : Atom) => x = BoxEmWorld.w1)
    (fun _ hle hx => BoxEmWorld.eq_w1_of_le hle hx)
    BoxEmWorld.w0
  cases hforce with
  | inl hbox =>
    -- `w₀ ⊩ □a` instantiated at `w' := w₀`, `u := w₀` gives `val w₀ a`, i.e. `w₀ = w₁`.
    exact BoxEmWorld.noConfusion (hbox BoxEmWorld.w0 (le_refl _) BoxEmWorld.w0 rfl)
  | inr himp =>
    -- `w₀ ⊩ ¬□a` applied to the `≤`-successor `w₁`, which forces `□a`.
    exact himp BoxEmWorld.w1 (Or.inr rfl)
      (fun w'' hle u hru => hru ▸ BoxEmWorld.eq_w1_of_w1_le hle)

/-! ## Refutation of the total-countermodel supply -/

/-- The model data a total-model countermodel construction needs for a pair `(H, A)`: a
total-`r` birelational model (with monotone valuation, hence an `is5FC` model — totality
trivially gives reflexivity, transitivity, symmetry, and both frame conditions) containing
worlds `u ⊩ H` and `v ⊮ A` with `r u v`. Bundled as a structure to keep the existential
telescope readable. -/
structure IS5TotalCountermodel (Atom : Type u) (H : Set (Proposition Atom))
    (A : Proposition Atom) where
  /-- The world carrier. -/
  World : Type v
  /-- The intuitionistic preorder. -/
  [instPreorder : Preorder World]
  /-- The modal accessibility relation. -/
  r : World → World → Prop
  /-- The totality requirement on `r`. -/
  total : ∀ x y, r x y
  /-- The valuation. -/
  val : World → Atom → Prop
  /-- `≤`-monotonicity of the valuation. -/
  val_mono : ∀ {x y : World} (p : Atom), x ≤ y → val x p → val y p
  /-- The world forcing the seed. -/
  u : World
  /-- The world refuting the target. -/
  v : World
  /-- `u` forces every member of `H`. -/
  seed_forced : ∀ φ ∈ H, BForces r val (fun _ => False) u φ
  /-- `v` refutes `A`. -/
  target_refuted : ¬ BForces r val (fun _ => False) v A
  /-- The cross-relation requirement. -/
  rel : r u v

/-- **The total-countermodel supply**: for every `(H, A)` with
`A ∉ modalDeductiveClosure IS5ModalAxiom H`, a total-`r` countermodel exists. This is the model
supply a product-model construction toward `CS5PairSeedRightExclusion` would need; it is false
(`is5TotalCountermodelSupply_false`). -/
def IS5TotalCountermodelSupply (Atom : Type u) : Prop :=
  ∀ (H : Set (Proposition Atom)) (A : Proposition Atom),
    A ∉ modalDeductiveClosure IS5ModalAxiom H →
    Nonempty (IS5TotalCountermodel.{u, v} Atom H A)

/-- Bridge: non-derivability places `□a ∨ ¬□a` outside
`modalDeductiveClosure IS5ModalAxiom ∅` (the closure's witness list over `∅` is forced empty,
and derivability from the empty list is `Derivable`). -/
theorem boxEm_not_mem_empty_closure (a : Atom) :
    boxEm a ∉ modalDeductiveClosure IS5ModalAxiom (∅ : Set (Proposition Atom)) := by
  rintro ⟨L, hL, hd⟩
  have hLnil : L = [] := by
    cases L with
    | nil => rfl
    | cons x xs => exact absurd (hL x (List.mem_cons_self ..)) (fun hx => hx)
  subst hLnil
  exact boxEm_not_derivable a hd

/-- **Refutation of the total-countermodel supply.** `IS5TotalCountermodelSupply` is false for
every atom type with a distinguished element: at the instance `H := ∅`, `A := □a ∨ ¬□a`, the
side condition holds (`boxEm_not_derivable` + `boxEm_not_mem_empty_closure`), yet by
`bforces_boxEm_of_total` no total-`r` model refutes `□a ∨ ¬□a` at any world. -/
theorem is5TotalCountermodelSupply_false (a : Atom) :
    ¬ IS5TotalCountermodelSupply.{u, v} Atom := by
  intro hsupply
  obtain ⟨M⟩ := hsupply ∅ (boxEm a) (boxEm_not_mem_empty_closure a)
  letI := M.instPreorder
  exact M.target_refuted (bforces_boxEm_of_total M.r M.total M.val a M.v)

end Cslib.Logic.Modal
