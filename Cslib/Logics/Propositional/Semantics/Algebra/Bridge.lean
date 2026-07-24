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

This module is a self-contained development of the three-evaluator correspondence for
propositional logic: it proves that `Evaluate` (Prop-valued) and `BoolEvaluate` (Bool-valued)
are both special cases of the generic algebraic evaluator `AlgEvaluate`. It has no in-tree
consumer; `Bool.lean` maintains its own direct `Evaluate ↔ BoolEvaluate` bridge
(`BoolEvaluate_eq_iff` et al.) for the CPL soundness/decidability chain, and this module is an
independent algebraic reformulation rather than the route that chain uses.

## Evaluators

- **`Evaluate`** (`Prop`, `Valuation = Atom → Prop`):
  Uniformity with Kripke semantics; soundness and completeness are stated here.
  Specializes `AlgEvaluate` at `Prop` with `bot_val = False` (see `propEvaluateEq`).

- **`BoolEvaluate`** (`Bool`, `BoolValuation = Atom → Bool`):
  Computable decision procedure; canonical DPLL/SAT entry point (`instDecidableTautology`).
  Specializes `AlgEvaluate` at `Bool` with `bot_val = false` (see `boolEvaluateEq`).

- **`AlgEvaluate`** (GHA `H`, `Atom → H` + `bot_val : H`):
  Common generalization; tiered soundness-completeness across MPL/IPL/CPL.

`Valuation` stays `Atom → Prop` — the canonical model construction needs it.

## Soundness Chain

```
BoolEvaluate v φ = true
  ↔  (BoolEvaluate_eq_iff)  Evaluate (fun a => v a = true) φ
  ↔  (propEvaluateEq / boolEvaluateEq)  AlgEvaluate · bot_val φ = ⊤
  ↔  SemanticEntails (via Tautology / prop_strong_soundness)
```

`SemanticEntails` and `prop_strong_soundness` are stated in terms of `Evaluate`; the chain
above shows that `BoolEvaluate` is the computable end of this pipeline, while `AlgEvaluate`
unifies the metatheory at all three tiers (GHA/HA/BA).

## Main Results

- `propEvaluateEq`: `Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ`
  The Prop-valued evaluator is `AlgEvaluate` instantiated at `Prop` (as a Heyting Algebra)
  with `bot_val = False`.
- `boolEvaluateEq`: `BoolEvaluate v φ = AlgEvaluate (fun a => v a) false φ`
  The Bool-valued evaluator is `AlgEvaluate` instantiated at `Bool` (as a Boolean Algebra)
  with `bot_val = false`.

## Design Notes

`propEvaluateEq` is an iff (not equality) because `Prop` does not have decidable equality,
so the two types `Evaluate v φ` and `AlgEvaluate (fun a => v a) False φ` are propositionally
but not definitionally equal for the `imp` case (Prop's `⇨` is `→`, which is definitionally
equal to `Evaluate`'s `imp` case).

`boolEvaluateEq` is a `Bool` equality. Note that `Bool`'s Heyting implication is
`a ⇨ b = b || !a` while `BoolEvaluate` uses `!a || b`; these are propositionally equal by
`Bool.or_comm` but not definitionally. The proof uses `simp` with `himp_eq` and commutativity.

## Roadmap

- `baValid_imp_tautology : BAValid φ → Tautology φ` — direct route via
  `prop_soundness_tautology ∘ CPL.hilbert_alg_completeness.mpr`; requires importing
  `Semantics/Algebra/HilbertCompleteness.lean` and
  `Metalogic/Soundness.lean`.
- `tautology_iff_baValid : Tautology φ ↔ BAValid φ` — follows from
  `prop_completeness_iff_tautology.trans CPL.hilbert_alg_completeness`; restricted to
  `BAValid.{u, u}` (same universe for `Atom` and `H`); a universe-polymorphic form
  may need a `ULift`-based argument.

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
