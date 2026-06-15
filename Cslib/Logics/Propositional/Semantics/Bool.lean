/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Basic

/-! # Boolean Evaluation for Propositional Logic

This module defines a computable Boolean evaluation function for propositional logic,
alongside the `Prop`-valued `Evaluate` from `Semantics.Basic`.

## Main Definitions

- `BoolValuation`: A Boolean propositional valuation assigns a `Bool` to each atom.
- `BoolEvaluate`: Evaluate a proposition under a Boolean valuation, returning `Bool`.

## Main Results

- `BoolEvaluate_eq_iff`: Bridge lemma connecting `BoolEvaluate v φ = true` to
  `Evaluate (fun a => v a = true) φ`, enabling decidable evaluation.
- `instDecidableBoolEvaluate`: Decidability of `Evaluate` under Boolean valuations.

## Design Notes

`BoolEvaluate` exists alongside `Evaluate` because DPLL/SAT procedures need computable
`Bool` evaluation, while canonical model construction in strong completeness requires `Prop`
(set membership `fun p => p ∈ S` is not decidable in general). The bridge lemma connects
the two worlds: `Bool` computation to `Prop` metatheory.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-- A Boolean propositional valuation assigns a `Bool` value to each atom. -/
abbrev BoolValuation (Atom : Type*) := Atom → Bool

/-- Computable Boolean evaluation of a proposition; mirrors `Evaluate` with `Bool` instead of
`Prop`. Use `BoolEvaluate_eq_iff` to connect results to `Evaluate`. -/
def BoolEvaluate (v : BoolValuation Atom) : PL.Proposition Atom → Bool
  | .atom x => v x
  | .bot => false
  | .imp a b => !BoolEvaluate v a || BoolEvaluate v b
  | .and a b => BoolEvaluate v a && BoolEvaluate v b
  | .or a b => BoolEvaluate v a || BoolEvaluate v b

@[simp] theorem BoolEvaluate_atom (v : BoolValuation Atom) (x : Atom) :
    BoolEvaluate v (.atom x) = v x := rfl

@[simp] theorem BoolEvaluate_bot (v : BoolValuation Atom) :
    BoolEvaluate v (.bot) = false := rfl

@[simp] theorem BoolEvaluate_imp (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.imp a b) = (!BoolEvaluate v a || BoolEvaluate v b) := rfl

@[simp] theorem BoolEvaluate_and (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.and a b) = (BoolEvaluate v a && BoolEvaluate v b) := rfl

@[simp] theorem BoolEvaluate_or (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.or a b) = (BoolEvaluate v a || BoolEvaluate v b) := rfl

/-- Bridge lemma: `BoolEvaluate v φ = true` iff `Evaluate (fun a => v a = true) φ`.
The `imp` case uses `cases` on `Bool` since `!a || b = true ↔ (a = true → b = true)`
is not automatic from `simp`. -/
theorem BoolEvaluate_eq_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ := by
  induction φ with
  | atom x => simp [BoolEvaluate, Evaluate]
  | bot => simp [BoolEvaluate, Evaluate]
  | imp a b iha ihb =>
    simp only [BoolEvaluate, Evaluate_imp, ← iha, ← ihb]
    cases BoolEvaluate v a <;> cases BoolEvaluate v b <;> simp
  | and a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]
  | or a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]

/-- Negation form of the bridge: `BoolEvaluate v φ = false` iff
`¬ Evaluate (fun a => v a = true) φ`. -/
theorem BoolEvaluate_eq_false_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = false ↔ ¬Evaluate (fun a => v a = true) φ := by
  rw [← BoolEvaluate_eq_iff]
  cases BoolEvaluate v φ <;> simp

/-- Every propositional valuation with decidable atoms factors through `BoolEvaluate`. -/
theorem Evaluate_eq_BoolEvaluate (v : Valuation Atom) [∀ a, Decidable (v a)]
    (φ : PL.Proposition Atom) :
    Evaluate v φ ↔ BoolEvaluate (fun a => decide (v a)) φ = true := by
  rw [BoolEvaluate_eq_iff]
  induction φ with
  | atom x => simp [Evaluate, decide_eq_true_eq]
  | bot => simp [Evaluate]
  | imp a b iha ihb => simp [Evaluate, iha, ihb]
  | and a b iha ihb => simp [Evaluate, iha, ihb]
  | or a b iha ihb => simp [Evaluate, iha, ihb]

/-- `Evaluate` under a Boolean valuation is decidable, via `BoolEvaluate_eq_iff`. -/
instance instDecidableBoolEvaluate (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    Decidable (Evaluate (fun a => v a = true) φ) :=
  decidable_of_iff _ (BoolEvaluate_eq_iff v φ)

end Cslib.Logic.PL
