/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Tactic.ToAdditive

/-! # Bot-Free Analysis and Validity Subsumption

This module defines the `IsBotFree` predicate for propositions that do not mention `⊥`,
proves that algebraic evaluation of bot-free formulas is independent of `bot_val`,
and establishes validity subsumption: `GHAValid → HAValid → BAValid`.

The conservative extension theorem (`ipl_conservative_over_mpl`) is stated but left as `sorry`
because the proof requires Dedekind-MacNeille completion of the Lindenbaum algebra (deferred).

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

universe u v

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

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

/-! ## Conservative Extension (Deferred)

The full proof of the conservative extension theorem requires Dedekind-MacNeille completion
of the Lindenbaum algebra to embed the GHA quotient into a Heyting algebra while preserving
evaluation of bot-free formulas. This is deferred to a follow-up task. -/

variable {Atom : Type u} [DecidableEq Atom]

/-- IPL is a conservative extension of MPL for bot-free formulas: if a bot-free formula is
derivable in IPL, then it is already derivable in MPL.

The proof requires Dedekind-MacNeille completion (deferred). -/
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (_hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A := by
  sorry

end Cslib.Logic.PL
