/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra
public import Cslib.Logics.Propositional.Semantics.Bool

/-! # Bridge Lemmas Between Evaluators

This module connects the generic algebraic evaluator `AlgEvaluate` to the existing
evaluators `Evaluate` (Prop-valued) and `BoolEvaluate` (Bool-valued), showing that
both are special cases of the algebraic framework.

## Main Results

- `prop_evaluate_eq`: `Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ`
  The Prop-valued evaluator is `AlgEvaluate` instantiated at `Prop` (as a Heyting Algebra)
  with `bot_val = False`.
- `bool_evaluate_eq`: `BoolEvaluate v φ = AlgEvaluate (fun a => v a) false φ`
  The Bool-valued evaluator is `AlgEvaluate` instantiated at `Bool` (as a Boolean Algebra)
  with `bot_val = false`.

## Design Notes

`prop_evaluate_eq` is an iff (not equality) because `Prop` does not have decidable equality,
so the two types `Evaluate v φ` and `AlgEvaluate (fun a => v a) False φ` are propositionally
but not definitionally equal for the `imp` case (Prop's `⇨` is `→`, which is definitionally
equal to `Evaluate`'s `imp` case).

`bool_evaluate_eq` is a `Bool` equality. Note that `Bool`'s Heyting implication is
`a ⇨ b = b || !a` while `BoolEvaluate` uses `!a || b`; these are propositionally equal by
`Bool.or_comm` but not definitionally. The proof uses `simp` with `himp_eq` and commutativity.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974] — the algebraic
  framework for propositional logic over generalized Heyting algebras
* [A. Rasiowa, R. Sikorski, *The Mathematics of Metamathematics*][RasiowaSikorski1963] — the
  Lindenbaum-Tarski algebra construction and its use in completeness proofs
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-- The Prop-valued evaluator `Evaluate v φ` is a special case of `AlgEvaluate` at `Prop`
(as a Heyting Algebra) with `bot_val = False`.

Concretely: `Prop`'s `⇨` is `(→)`, `⊓` is `And`, `⊔` is `Or`, and `⊥` is `False`. -/
theorem propEvaluateEq (v : Valuation Atom) (φ : PL.Proposition Atom) :
    Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ := by
  induction φ with
  | atom x => simp [AlgEvaluate, Evaluate]
  | bot => simp [AlgEvaluate, Evaluate]
  | imp a b iha ihb =>
    simp only [AlgEvaluate_imp, Evaluate_imp]
    exact Iff.imp iha ihb
  | and a b iha ihb =>
    simp only [AlgEvaluate_and, Evaluate_and]
    exact Iff.and iha ihb
  | or a b iha ihb =>
    simp only [AlgEvaluate_or, Evaluate_or]
    exact Iff.or iha ihb

/-- The Bool-valued evaluator `BoolEvaluate v φ` is a special case of `AlgEvaluate` at `Bool`
(as a Boolean Algebra) with `bot_val = false`.

Concretely: `Bool`'s `⇨` is `(!· || ·)`, `⊓` is `(· && ·)`, `⊔` is `(· || ·)`, `⊥` is
`false`. Note `a ⇨ b = b || !a` in `Bool`'s algebra, matching `!a || b` up to commutativity. -/
theorem boolEvaluateEq (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = AlgEvaluate (fun a => v a) false φ := by
  induction φ with
  | atom x => simp [AlgEvaluate, BoolEvaluate]
  | bot => simp [AlgEvaluate, BoolEvaluate]
  | imp a b iha ihb =>
    simp only [AlgEvaluate_imp, BoolEvaluate_imp, himp_eq, iha, ihb]
    cases AlgEvaluate (fun a => v a) false a <;> cases AlgEvaluate (fun a => v a) false b <;> decide
  | and a b iha ihb =>
    simp [AlgEvaluate_and, BoolEvaluate_and, iha, ihb]
  | or a b iha ihb =>
    simp [AlgEvaluate_or, BoolEvaluate_or, iha, ihb]

end Cslib.Logic.PL
