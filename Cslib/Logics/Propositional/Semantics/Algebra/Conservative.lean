/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra
public import Mathlib.Order.WithBot

/-! # Bot-Free Analysis and Validity Subsumption

This module defines the `IsBotFree` predicate for propositions that do not mention `⊥`,
proves that algebraic evaluation of bot-free formulas is independent of `bot_val`,
establishes validity subsumption (`GHAValid → HAValid → BAValid`), and provides the
`WithBot` Heyting algebra construction with its embedding lemma.

These algebraic building blocks are used by the Hilbert-primary conservative extension theorem
`hilbertIplConservativeOverMpl` in `HilbertConservativeGlivenko.lean`. The ND corollary
`ipl_conservative_over_mpl` is also located there, derived via algebraic bridges.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

universe u v

namespace Cslib.Logic.PL

open Proposition

/-! ## Bot-Free Predicate -/

/-- A proposition is bot-free if it does not mention `⊥`. -/
def Proposition.IsBotFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsBotFree && b.IsBotFree
  | .and a b => a.IsBotFree && b.IsBotFree
  | .or a b => a.IsBotFree && b.IsBotFree

/-! ## Bot-Free Independence -/

/-- For bot-free formulas, `AlgEvaluate` is independent of `bot_val`. -/
theorem AlgEvaluate_botFree_independent
    {Atom : Type*} {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (b₁ b₂ : H) (A : Proposition Atom)
    (hA : A.IsBotFree = true) :
    AlgEvaluate v b₁ A = AlgEvaluate v b₂ A := by
  induction A with
  | atom _ => rfl
  | bot => simp [Proposition.IsBotFree] at hA
  | imp a b iha ihb =>
    simp [Proposition.IsBotFree] at hA
    simp [AlgEvaluate_imp, iha hA.1, ihb hA.2]
  | and a b iha ihb =>
    simp [Proposition.IsBotFree] at hA
    simp [AlgEvaluate_and, iha hA.1, ihb hA.2]
  | or a b iha ihb =>
    simp [Proposition.IsBotFree] at hA
    simp [AlgEvaluate_or, iha hA.1, ihb hA.2]

/-! ## Validity Subsumption -/

/-- GHA-validity implies HA-validity: every Heyting algebra is a GHA with `bot_val := ⊥`. -/
theorem GHAValid_implies_HAValid {Atom : Type u} {A : Proposition Atom}
    (h : ∀ (H : Type v) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      AlgEvaluate v bot_val A = ⊤) :
    ∀ (H : Type v) [HeytingAlgebra H] (v : Atom → H),
      AlgEvaluate v (⊥ : H) A = ⊤ :=
  fun H _ v => h H v ⊥

/-- HA-validity implies BA-validity: every Boolean algebra is a Heyting algebra. -/
theorem HAValid_implies_BAValid {Atom : Type u} {A : Proposition Atom}
    (h : ∀ (H : Type v) [HeytingAlgebra H] (v : Atom → H),
      AlgEvaluate v (⊥ : H) A = ⊤) :
    ∀ (H : Type v) [BooleanAlgebra H] (v : Atom → H),
      AlgEvaluate v (⊥ : H) A = ⊤ :=
  fun H _ v => h H v

/-! ## WithBot Heyting Algebra Instance

Given any `GeneralizedHeytingAlgebra G`, adjoining a fresh bottom element via `WithBot G`
yields a `HeytingAlgebra`. The Heyting implication is defined by case analysis:
- `⊥ ⇨ y = ⊤` (bottom implies anything)
- `↑a ⇨ ⊥ = ⊥` (non-bottom implies bottom equals bottom)
- `↑a ⇨ ↑b = ↑(a ⇨ b)` (lift from G) -/

/-- Heyting implication on `WithBot G` for a `GeneralizedHeytingAlgebra G`. -/
noncomputable def withBotHimp {G : Type*} [GeneralizedHeytingAlgebra G] :
    WithBot G → WithBot G → WithBot G
  | ⊥, _ => ⊤
  | (a : G), ⊥ => ⊥
  | (a : G), (b : G) => ((a ⇨ b : G) : WithBot G)

/-- Every `GeneralizedHeytingAlgebra` can be extended to a `HeytingAlgebra` by adjoining
a fresh bottom element via `WithBot`. -/
noncomputable instance instHeytingAlgebraWithBot {G : Type*} [GeneralizedHeytingAlgebra G] :
    HeytingAlgebra (WithBot G) :=
  HeytingAlgebra.ofHImp withBotHimp (by
    intro a b c
    cases a with
    | bot => simp [withBotHimp]
    | coe a' =>
      cases b with
      | bot => simp [withBotHimp]
      | coe b' =>
        cases c with
        | bot =>
          simp only [withBotHimp]
          constructor
          · intro h; exact absurd h (WithBot.not_coe_le_bot _)
          · intro h
            simp only [← WithBot.coe_inf] at h
            exact absurd h (WithBot.not_coe_le_bot _)
        | coe c' =>
          simp only [withBotHimp, WithBot.coe_le_coe, ← WithBot.coe_inf]
          exact le_himp_iff)

/-! ## Embedding Lemma -/

/-- For bot-free formulas, evaluating in `WithBot G` via the lifted valuation equals the
coercion of evaluating in `G`. This is the key embedding lemma for the conservative extension:
bot-free formulas "do not see" the fresh bottom element adjoined by `WithBot`. -/
theorem coe_AlgEvaluate {Atom : Type*} {G : Type*} [GeneralizedHeytingAlgebra G]
    (v : Atom → G) (bot_val : G) (A : Proposition Atom)
    (hBF : A.IsBotFree = true) :
    AlgEvaluate (fun x => (v x : WithBot G)) (⊥ : WithBot G) A =
      ((AlgEvaluate v bot_val A : G) : WithBot G) := by
  induction A with
  | atom _ => rfl
  | bot => simp [Proposition.IsBotFree] at hBF
  | imp a b iha ihb =>
    simp [Proposition.IsBotFree] at hBF
    simp only [AlgEvaluate_imp, iha hBF.1, ihb hBF.2]
    rfl
  | and a b iha ihb =>
    simp [Proposition.IsBotFree] at hBF
    simp only [AlgEvaluate_and, iha hBF.1, ihb hBF.2, ← WithBot.coe_inf]
  | or a b iha ihb =>
    simp [Proposition.IsBotFree] at hBF
    simp only [AlgEvaluate_or, iha hBF.1, ihb hBF.2, ← WithBot.coe_sup]

end Cslib.Logic.PL
