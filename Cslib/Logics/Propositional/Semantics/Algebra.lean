/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Defs
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.BooleanAlgebra.Basic

/-! # Algebraic Semantics for Propositional Logic

This module defines a generic algebraic evaluator for propositional logic, parameterized over
any `GeneralizedHeytingAlgebra`. This generalizes the bivalent `Evaluate` (using `Prop`) and
the Boolean `BoolEvaluate` (using `Bool`), providing a uniform framework for soundness proofs
at each axiom tier.

## Main Definitions

- `AlgEvaluate`: Generic evaluator mapping propositions to elements of a GHA `H`, with an
  explicit `bot_val : H` parameter (since GHA lacks a bottom element).
- `GHAValid`: Validity in all Generalized Heyting Algebras.
- `HAValid`: Validity in all Heyting Algebras (which have a primitive `⊥`).
- `BAValid`: Validity in all Boolean Algebras.

## Design Notes

`AlgEvaluate` takes a primitive `bot_val : H` parameter because `GeneralizedHeytingAlgebra`
does not guarantee a bottom element. At the `HeytingAlgebra` and `BooleanAlgebra` levels,
`bot_val = ⊥` is the canonical choice (and `HAValid`/`BAValid` use it).

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Generic Algebraic Evaluator -/

/-- Evaluate a proposition in an arbitrary Generalized Heyting Algebra `H`.

The evaluator is parameterized by:
- `v : Atom → H`: the assignment of algebra elements to propositional atoms
- `bot_val : H`: the value assigned to `⊥` (explicit since GHA lacks a primitive bottom)

Connectives map to the corresponding algebraic operations:
- `atom x` → `v x`
- `⊥` → `bot_val`
- `φ → ψ` → `AlgEvaluate v bot_val φ ⇨ AlgEvaluate v bot_val ψ` (Heyting implication)
- `φ ∧ ψ` → `AlgEvaluate v bot_val φ ⊓ AlgEvaluate v bot_val ψ` (meet)
- `φ ∨ ψ` → `AlgEvaluate v bot_val φ ⊔ AlgEvaluate v bot_val ψ` (join) -/
def AlgEvaluate {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val
  | .imp a b => AlgEvaluate v bot_val a ⇨ AlgEvaluate v bot_val b
  | .and a b => AlgEvaluate v bot_val a ⊓ AlgEvaluate v bot_val b
  | .or a b => AlgEvaluate v bot_val a ⊔ AlgEvaluate v bot_val b

@[simp] theorem AlgEvaluate_atom {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) (x : Atom) :
    AlgEvaluate v bot_val (.atom x) = v x := rfl

@[simp] theorem AlgEvaluate_bot {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) :
    AlgEvaluate v bot_val (.bot) = bot_val := rfl

@[simp] theorem AlgEvaluate_imp {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) (a b : PL.Proposition Atom) :
    AlgEvaluate v bot_val (.imp a b) =
      (AlgEvaluate v bot_val a ⇨ AlgEvaluate v bot_val b) := rfl

@[simp] theorem AlgEvaluate_and {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) (a b : PL.Proposition Atom) :
    AlgEvaluate v bot_val (.and a b) =
      (AlgEvaluate v bot_val a ⊓ AlgEvaluate v bot_val b) := rfl

@[simp] theorem AlgEvaluate_or {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) (a b : PL.Proposition Atom) :
    AlgEvaluate v bot_val (.or a b) =
      (AlgEvaluate v bot_val a ⊔ AlgEvaluate v bot_val b) := rfl

/-! ## Validity Predicates -/

/-- A proposition is valid in all Generalized Heyting Algebras iff it evaluates to `⊤`
under every GHA `H`, every variable assignment `v : Atom → H`, and every bottom value
`bot_val : H`. -/
def GHAValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
    AlgEvaluate v bot_val φ = ⊤

/-- A proposition is valid in all Heyting Algebras iff it evaluates to `⊤` under every
Heyting Algebra `H` and every variable assignment `v : Atom → H`. Uses `⊥` as the canonical
bottom value. -/
def HAValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [HeytingAlgebra H] (v : Atom → H),
    AlgEvaluate v (⊥ : H) φ = ⊤

/-- A proposition is valid in all Boolean Algebras iff it evaluates to `⊤` under every
Boolean Algebra `H` and every variable assignment `v : Atom → H`. Uses `⊥` as the canonical
bottom value. -/
def BAValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [BooleanAlgebra H] (v : Atom → H),
    AlgEvaluate v (⊥ : H) φ = ⊤


end Cslib.Logic.PL
