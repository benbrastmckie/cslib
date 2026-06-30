/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.BotProperties
public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
public import Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerian

/-! # Free-Bot Brouwerian Evaluator and Bridge Lemmas

This module defines the **free-bot Brouwerian evaluator** `BrouwerianBotEvaluate`, which
generalizes both `BrouwerianEvaluate` (bot → ⊤) and `PointedBrouwerianEvaluate` (bot → ⊥)
by treating the bottom value as a free parameter `bot_val : H`.

The two bridge lemmas recover the specialized evaluators as special cases:
- `brouwerianEvaluate_eq_botTop`: `BrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊤ φ`
- `pointedBrouwerianEvaluate_eq_botBot`:
  `PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ`

## Main Definitions

- `BrouwerianBotEvaluate`: free-bot Brouwerian evaluator (`bot ↦ bot_val`, `or ↦ ⊤`).
- `BrouwerianBotValid`: validity in all Brouwerian semilattices under all `bot_val` choices.

## Main Results

- `iicBrouwerianBotEvaluateEqAlgEvaluate`: commutation of `LowerSet.Iic` with the
  free-bot evaluator on or-free formulas.
- `brouwerianBotEmbeddingLemma`: `BrouwerianBotEvaluate v bot_val φ = ⊤` iff
  `AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ = ⊤` for or-free `φ`.
- `brouwerianEvaluate_eq_botTop`: bridge recovering `BrouwerianEvaluate` at `bot_val = ⊤`.
- `pointedBrouwerianEvaluate_eq_botBot`: bridge recovering `PointedBrouwerianEvaluate` at
  `bot_val = ⊥`.

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type*}

/-! ## Free-Bot Brouwerian Algebraic Evaluator -/

/-- Evaluate a proposition in a Brouwerian semilattice `H` with a free distinguished element
`bot_val` for `⊥`.

The evaluator is parameterized by `v : Atom → H` (atom assignment) and `bot_val : H`
(free bottom value). Connectives map as follows:
- `atom x` → `v x`
- `⊥` → `bot_val` (a free element; not required to be the least element)
- `φ → ψ` → `BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ`
- `φ ∧ ψ` → `BrouwerianBotEvaluate v bot_val φ ⊓ BrouwerianBotEvaluate v bot_val ψ`
- `φ ∨ ψ` → `⊤` (default; no join in BSL)

This differs from `PointedBrouwerianEvaluate` in that `bot_val` is free (no `OrderBot`
constraint) and from `BrouwerianEvaluate` in that `bot ↦ bot_val` rather than `⊤`. -/
def BrouwerianBotEvaluate {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val
  | .imp a b => BrouwerianBotEvaluate v bot_val a ⇨ BrouwerianBotEvaluate v bot_val b
  | .and a b => BrouwerianBotEvaluate v bot_val a ⊓ BrouwerianBotEvaluate v bot_val b
  | .or _ _ => ⊤

@[simp]
theorem BrouwerianBotEvaluate_atom {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (x : Atom) :
    BrouwerianBotEvaluate v bot_val (.atom x) = v x := rfl

/-- The `bot` case maps to the free `bot_val`. -/
@[simp]
theorem BrouwerianBotEvaluate_bot {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) :
    BrouwerianBotEvaluate v bot_val .bot = bot_val := rfl

@[simp]
theorem BrouwerianBotEvaluate_imp {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (a b : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val (.imp a b) =
    BrouwerianBotEvaluate v bot_val a ⇨ BrouwerianBotEvaluate v bot_val b := rfl

@[simp]
theorem BrouwerianBotEvaluate_and {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (a b : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val (.and a b) =
    BrouwerianBotEvaluate v bot_val a ⊓ BrouwerianBotEvaluate v bot_val b := rfl

@[simp]
theorem BrouwerianBotEvaluate_or {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (a b : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val (.or a b) = ⊤ := rfl

/-! ## Free-Bot Brouwerian Validity -/

/-- A proposition is **free-bot Brouwerian valid** if it evaluates to `⊤` in every Brouwerian
semilattice under every variable assignment and every choice of the free bottom element.

This is the semantic counterpart of derivability in `ConjImpBotMinAxiom` for or-free formulas.
Unlike `PointedBrouwerianValid`, no `OrderBot` constraint is imposed — `bot_val` ranges freely
over the entire algebra, matching the absence of ex falso in `ConjImpBotMinAxiom`. -/
def BrouwerianBotValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [BrouwerianSemilattice H] (v : Atom → H) (bot_val : H),
    BrouwerianBotEvaluate v bot_val φ = ⊤

/-! ## Free-Bot Commutation Lemma -/

/-- For or-free formulas, `LowerSet.Iic` commutes with the free-bot evaluator:
`AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ =
  LowerSet.Iic (BrouwerianBotEvaluate v bot_val φ)`.

The proof is by structural induction:
- **atom**: both sides equal `LowerSet.Iic (v x)`.
- **bot**: both sides equal `LowerSet.Iic bot_val` — closes by `rfl`.
- **imp**: apply `(iicHimp _ _).symm` and the inductive hypothesis.
- **and**: apply `(LowerSet.Iic_inf _ _).symm` and the inductive hypothesis.
- **or**: excluded by `IsOrFree`. -/
theorem iicBrouwerianBotEvaluateEqAlgEvaluate {B : Type*} [BrouwerianSemilattice B]
    (v : Atom → B) (bot_val : B) (φ : Proposition Atom) (hφ : φ.IsOrFree = true) :
    AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ =
      LowerSet.Iic (BrouwerianBotEvaluate v bot_val φ) := by
  induction φ with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hφ
    simp only [AlgEvaluate_imp, BrouwerianBotEvaluate_imp, iha hφ.1, ihb hφ.2]
    exact (iicHimp _ _).symm
  | and a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hφ
    simp only [AlgEvaluate_and, BrouwerianBotEvaluate_and, iha hφ.1, ihb hφ.2]
    exact (LowerSet.Iic_inf _ _).symm
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hφ

/-! ## Free-Bot Embedding Lemma -/

/-- **Free-bot embedding lemma** (or-free): `BrouwerianBotEvaluate v bot_val φ = ⊤` iff
`AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ = ⊤`.

This is the bridge between free-bot Brouwerian semilattice semantics and Heyting algebra
semantics on the or-free fragment. The proof uses `iicBrouwerianBotEvaluateEqAlgEvaluate`,
`LowerSet.Iic_top`, and `LowerSet.Iic_injective`. -/
theorem brouwerianBotEmbeddingLemma {B : Type*} [BrouwerianSemilattice B]
    (v : Atom → B) (bot_val : B) (φ : Proposition Atom) (hφ : φ.IsOrFree = true) :
    BrouwerianBotEvaluate v bot_val φ = ⊤ ↔
      AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ = ⊤ := by
  rw [iicBrouwerianBotEvaluateEqAlgEvaluate v bot_val φ hφ]
  constructor
  · intro h; rw [h, LowerSet.Iic_top]
  · intro h; exact LowerSet.Iic_injective (h.trans LowerSet.Iic_top.symm)

/-! ## Bridge Lemmas -/

/-- `BrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊤ φ`.

Both evaluators map `bot` to `⊤` and agree on all other constructors by `rfl`. -/
theorem brouwerianEvaluate_eq_botTop {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (φ : PL.Proposition Atom) :
    BrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊤ φ := by
  induction φ with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb => simp [BrouwerianEvaluate, BrouwerianBotEvaluate, iha, ihb]
  | and a b iha ihb => simp [BrouwerianEvaluate, BrouwerianBotEvaluate, iha, ihb]
  | or a b iha ihb => rfl

/-- `PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ`.

Both evaluators map `bot` to `⊥` and agree on all other constructors by `rfl`. -/
theorem pointedBrouwerianEvaluate_eq_botBot {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) (φ : PL.Proposition Atom) :
    PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ := by
  induction φ with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb => simp [PointedBrouwerianEvaluate, BrouwerianBotEvaluate, iha, ihb]
  | and a b iha ihb => simp [PointedBrouwerianEvaluate, BrouwerianBotEvaluate, iha, ihb]
  | or a b iha ihb => rfl

/-! ## HasLeastBot Bridge Lemmas

The following lemmas connect the free-bot Brouwerian evaluator to the `HasLeastBot` hierarchy.
They show that the explosion axiom `⊥ → A` evaluates to `⊤` whenever the designated bottom
value is least, placing each evaluator in the semantic property hierarchy:

- `BrouwerianBotEvaluate v ⊤` = `BrouwerianEvaluate v` (free/top bottom, MPL level)
- `BrouwerianBotEvaluate v b` with `HasLeastBot b` ← explosion-sound (IPL level)
- `BrouwerianBotEvaluate v ⊥` = `PointedBrouwerianEvaluate v` (canonical bottom, IPL level) -/

/-- Explosion soundness for the free-bot evaluator with any `HasLeastBot` bottom value:
`BrouwerianBotEvaluate v bot_val (⊥ → A) = ⊤` whenever `bot_val` is the least element.
Uses `BrouwerianSemilattice.himp_eq_top_iff` to reduce to `HasLeastBot.bot_le_val`. -/
lemma brouwerianBotEvaluate_efq_eq_top {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) [HasLeastBot bot_val] (A : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val (.imp .bot A) = ⊤ := by
  simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_bot]
  rw [BrouwerianSemilattice.himp_eq_top_iff]
  exact HasLeastBot.bot_le_val _

/-- Explosion soundness for `PointedBrouwerianEvaluate`: `⊥ → A` evaluates to `⊤` in any
pointed Brouwerian semilattice. Follows via `pointedBrouwerianEvaluate_eq_botBot` and
`brouwerianBotEvaluate_efq_eq_top`, using `HasLeastBot (⊥ : H)` from `instHasLeastBotOrderBot`. -/
lemma pointedBrouwerianEvaluate_efq_eq_top {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) (A : PL.Proposition Atom) :
    PointedBrouwerianEvaluate v (.imp .bot A) = ⊤ := by
  rw [pointedBrouwerianEvaluate_eq_botBot]
  exact brouwerianBotEvaluate_efq_eq_top v ⊥ A

/-! ## HasInitialBot Bridge Lemmas

The following lemmas re-express explosion soundness in terms of the `HasInitialBot` hierarchy,
making the categorical reading explicit: `⊥ → A` evaluates to `⊤` because the designated
bottom is an **initial object** — the unique arrow `bot_val → a` (i.e. `bot_val ≤ a`) exists
for every `a`. These are parallel to the `HasLeastBot` bridge lemmas above, differing only in
which mixin is cited as the witness. -/

/-- Explosion soundness for the free-bot evaluator via the initial-object universal property:
`BrouwerianBotEvaluate v bot_val (⊥ → A) = ⊤` whenever `bot_val` is an initial object
(`HasInitialBot bot_val`). The proof cites `HasInitialBot.initialArrow` — the unique arrow
from the initial object to any target — making the categorical reading explicit. -/
lemma brouwerianBotEvaluate_efq_eq_top_of_initialBot {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) [HasInitialBot bot_val] (A : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val (.imp .bot A) = ⊤ := by
  simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_bot]
  rw [BrouwerianSemilattice.himp_eq_top_iff]
  exact HasInitialBot.initialArrow _

/-- Explosion soundness for `PointedBrouwerianEvaluate` via the initial-object witness:
`⊥ → A` evaluates to `⊤` in any pointed Brouwerian semilattice, because the canonical `⊥`
is an initial object (via `instHasInitialBotOfHasLeastBot` and `instHasLeastBotOrderBot`).
Follows via `pointedBrouwerianEvaluate_eq_botBot` and
`brouwerianBotEvaluate_efq_eq_top_of_initialBot`. -/
lemma pointedBrouwerianEvaluate_efq_eq_top_of_initialBot
    {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) (A : PL.Proposition Atom) :
    PointedBrouwerianEvaluate v (.imp .bot A) = ⊤ := by
  rw [pointedBrouwerianEvaluate_eq_botBot]
  exact brouwerianBotEvaluate_efq_eq_top_of_initialBot v ⊥ A

end Cslib.Logic.PL

end
