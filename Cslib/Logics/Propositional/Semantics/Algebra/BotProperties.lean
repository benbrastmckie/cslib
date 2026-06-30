/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra

/-! # Bottom-Property Hierarchy for Algebraic Propositional Semantics

This module introduces the **bottom-property hierarchy** that mirrors the proof-theoretic
property modules (`IsIntuitionistic`, `IsClassical`) at the semantic (algebraic) level.
It is organized around three levels of constraint on the designated bottom value
`bot_val : H` used by `AlgEvaluate`:

## Property Hierarchy

1. **Designated bottom** (free `bot_val` parameter): the `AlgEvaluate v bot_val` evaluator
   level, where `⊥` maps to any chosen element of the algebra — no semantic constraint on
   its behavior. Used by `GHAValid` (MPL semantics over all bot values).

2. **Least bottom** (`HasLeastBot bot_val`): the designated `bot_val` is less than or equal
   to every element of the algebra. This is the algebraic correlate of the explosion property
   (`IsIntuitionistic` at the proof-theoretic level): for a `GeneralizedHeytingAlgebra H`,
   `HasLeastBot bot_val` holds iff every formula `⊥ → A` evaluates to `⊤` under `bot_val`.

3. **Initial object** (`HasInitialBot bot_val`): a categorical refinement of `HasLeastBot`,
   emphasizing that `bot_val` is an **initial object** in the poset viewed as a category —
   there is a unique arrow `bot_val → a` for every `a`. In a poset the unique morphism from
   `b` to `a` is the inequality `b ≤ a`, so `HasInitialBot` is the literal universal property
   of an initial object. `HasLeastBot` implies `HasInitialBot`; explosion soundness (EFQ)
   is the categorical statement that the initial object admits a unique arrow to every object.

4. **Canonical bottom** (`bot_val = ⊥` from `OrderBot`): the designated bottom is the unique
   algebraic `⊥`. Every `HeytingAlgebra` (and thus `BooleanAlgebra`) satisfies this. Used by
   `HAValid` and `BAValid`, which hardcode `bot_val = ⊥`.

This hierarchy mirrors the proof-theoretic one: **MPL** (no constraint) → **IPL**
(explosion = least bottom) → **CPL** (classicality). The `AlgEvaluate v bot_val` evaluator
is the unified semantic evaluator; the property modules are additive layers.

## Main Definitions

- `HasLeastBot b`: thin `Prop`-mixin asserting `b` is the least element of `H`.
- `instHasLeastBotOrderBot`: every `OrderBot H` makes `⊥ : H` a least bottom.
- `hasLeastBot_himp_eq_top`: explosion soundness — if `HasLeastBot b`, then `b ⇨ a = ⊤`.
- `algEvaluate_imp_bot_eq_top`: `AlgEvaluate v bot_val (⊥ → A) = ⊤` when `HasLeastBot bot_val`.
- `algTValid_ipl_of_hasLeastBot`: any `HasLeastBot`-valuation models `IPL`.
- `HasInitialBot b`: initial-object universal property — the unique arrow `b → a` exists for
  every `a` (as the inequality `b ≤ a`).
- `instHasInitialBotOfHasLeastBot`: `HasLeastBot b` implies `HasInitialBot b`.
- `hasInitialBot_himp_eq_top`: explosion soundness via initial-object witness — `b ⇨ a = ⊤`.
- `algEvaluate_imp_bot_eq_top_of_initialBot`: evaluator-level explosion via `HasInitialBot`.

## Design Notes

`HasLeastBot` does not introduce a new bottom structure (the `bot_val` parameter of
`AlgEvaluate` is retained as-is). It is a **Prop-valued predicate on a specific element**
`b : H`, not a typeclass on the type `H`. This means it can be stated and used without
changing the type of the evaluator or the algebra. The `IsIntuitionistic` ↔ `HasLeastBot`
correspondence is the semantic dual of the proof-theoretic explosion property:
- Proof-theoretic: `IsIntuitionistic T ↔ IPL ⊆ T` (`Defs.lean`)
- Semantic: `HasLeastBot bot_val ↔ ∀ A, AlgEvaluate v bot_val (⊥ → A) = ⊤`

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [A. Rasiowa, R. Sikorski, *The Mathematics of Metamathematics*][RasiowaSikorski1963]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## HasLeastBot: Thin Prop-Mixin for Least-Bottom Property -/

/-- A `Prop`-mixin asserting that an element `b : H` is the least element of `H`, i.e.,
less than or equal to every other element. This is the algebraic correlate of the
explosion property (`IsIntuitionistic` at the proof-theoretic level): in a
`GeneralizedHeytingAlgebra`, `HasLeastBot b` holds iff `b ⇨ a = ⊤` for all `a`,
which is exactly the condition for `⊥ → A` to evaluate to `⊤`.

Note: This is a predicate on a specific element `b`, not a constraint on the algebra type
`H`. The `bot_val` parameter of `AlgEvaluate` is retained; `HasLeastBot bot_val` is the
additive property asserting the bottom is least (the IPL-level constraint). -/
class HasLeastBot {H : Type*} [LE H] (b : H) : Prop where
  /-- The designated bottom element `b` is less than or equal to every element of `H`. -/
  bot_le_val : ∀ a : H, b ≤ a

/-- Every `OrderBot` provides a least-bottom instance for its algebraic `⊥`. The canonical
`⊥` of any `HeytingAlgebra` or `BooleanAlgebra` is automatically a `HasLeastBot` witness. -/
instance instHasLeastBotOrderBot {H : Type*} [Preorder H] [OrderBot H] :
    HasLeastBot (⊥ : H) where
  bot_le_val a := OrderBot.bot_le a

/-! ## Explosion Soundness via HasLeastBot -/

/-- Explosion soundness: when `b` is the least element of a `GeneralizedHeytingAlgebra H`,
`b ⇨ a = ⊤` for every element `a : H`. This is the algebraic content of ex falso quodlibet:
the implication from the designated bottom to any proposition evaluates to the top element.

This connects to `PointedBrouwerianCompleteness` where `bot_le` (from `OrderBot`) is used
to prove the `efq` axiom sound; here we generalize to any `HasLeastBot b` element. -/
lemma hasLeastBot_himp_eq_top {H : Type*} [GeneralizedHeytingAlgebra H]
    (b a : H) [HasLeastBot b] : b ⇨ a = ⊤ := by
  rw [himp_eq_top_iff]
  exact HasLeastBot.bot_le_val a

/-- When `HasLeastBot bot_val`, the formula `⊥ → A` evaluates to `⊤` under `AlgEvaluate`.
This is the semantic content of the explosion property at the evaluator level. -/
lemma algEvaluate_imp_bot_eq_top {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) [HasLeastBot bot_val]
    (A : PL.Proposition Atom) :
    AlgEvaluate v bot_val (.imp .bot A) = ⊤ := by
  simp only [AlgEvaluate_imp, AlgEvaluate_bot]
  exact hasLeastBot_himp_eq_top bot_val (AlgEvaluate v bot_val A)

/-- Every IPL formula `⊥ → A` is in `Theory.IPL`, and any valuation with `HasLeastBot bot_val`
models this axiom. In other words: `HasLeastBot bot_val` implies `v ⊨[bot_val] Theory.IPL`. -/
lemma algTValid_ipl_of_hasLeastBot {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) [HasLeastBot bot_val] :
    v ⊨[bot_val] (Theory.IPL : PL.Theory Atom) := by
  intro B hB
  -- Theory.IPL = Set.range (Proposition.imp ⊥ ·); membership: ∃ A, ⊥ → A = B
  obtain ⟨A, rfl⟩ := hB
  exact algEvaluate_imp_bot_eq_top v bot_val A

/-! ## HasInitialBot: Initial-Object Universal Property -/

/-- A `Prop`-mixin asserting that `b : H` is an **initial object** in the order-theoretic sense:
there is a (unique) morphism from `b` to every element `a`, witnessed by `b ≤ a`. In a poset
viewed as a category, the unique morphism from `b` to `a` is the inequality `b ≤ a`, so
`HasInitialBot` is literally the categorical initial-object universal property.

`HasInitialBot b` and `HasLeastBot b` both assert `∀ a, b ≤ a`; they differ in conceptual
emphasis. `HasLeastBot` is the order-theoretic reading (b is the least element); `HasInitialBot`
is the categorical reading (b is an initial object, with a unique arrow to every object).
`HasLeastBot b` implies `HasInitialBot b` via `instHasInitialBotOfHasLeastBot`.

The connection to explosion (*ex falso quodlibet*): in a `GeneralizedHeytingAlgebra`, the
implication `b ⇨ a = ⊤` for every `a` is exactly the statement that `b` is an initial object.
`HasInitialBot` makes this categorical reading a first-class named artifact. -/
class HasInitialBot {H : Type*} [LE H] (b : H) : Prop where
  /-- The universal arrow: for every object `a`, the unique morphism `b → a` exists
  (realized as the inequality `b ≤ a`). -/
  initialArrow : ∀ a : H, b ≤ a

/-- Every `HasLeastBot b` element is also an initial object: the order-theoretic least element
and the categorical initial object coincide in a poset. The universal arrow is
`HasLeastBot.bot_le_val`. -/
instance instHasInitialBotOfHasLeastBot {H : Type*} [LE H] (b : H) [HasLeastBot b] :
    HasInitialBot b where
  initialArrow := HasLeastBot.bot_le_val

/-- **Explosion soundness via the initial-object universal property**: `b ⇨ a = ⊤` in any
`GeneralizedHeytingAlgebra H` whenever `b` is an initial object (`HasInitialBot b`). This makes
explicit that *ex falso quodlibet* is the categorical universal property of the initial object:
the unique arrow `b → a` exists for every `a`, here witnessed by `HasInitialBot.initialArrow`. -/
lemma hasInitialBot_himp_eq_top {H : Type*} [GeneralizedHeytingAlgebra H]
    (b a : H) [HasInitialBot b] : b ⇨ a = ⊤ := by
  rw [himp_eq_top_iff]
  exact HasInitialBot.initialArrow a

/-- Explosion soundness at the evaluator level via the initial-object universal property:
`AlgEvaluate v bot_val (⊥ → A) = ⊤` whenever `bot_val` is an initial object
(`HasInitialBot bot_val`). Parallel to `algEvaluate_imp_bot_eq_top` for `HasLeastBot`. -/
lemma algEvaluate_imp_bot_eq_top_of_initialBot {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) [HasInitialBot bot_val]
    (A : PL.Proposition Atom) :
    AlgEvaluate v bot_val (.imp .bot A) = ⊤ := by
  simp only [AlgEvaluate_imp, AlgEvaluate_bot]
  exact hasInitialBot_himp_eq_top bot_val (AlgEvaluate v bot_val A)

end Cslib.Logic.PL
