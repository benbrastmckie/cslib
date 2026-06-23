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
the Boolean `BoolEvaluate` (using `Bool`), providing a uniform framework for soundness and
completeness proofs at each axiom tier.

The algebraic hierarchy mirrors the proof-theoretic one:
- `GeneralizedHeytingAlgebra` (GHA) = Johansson algebra = semantics for **MPL** (minimal logic)
- `HeytingAlgebra` (HA) = GHA + designated `⊥` = semantics for **IPL** (intuitionistic logic)
- `BooleanAlgebra` (BA) = HA + excluded middle = semantics for **CPL** (classical logic)

A GHA is precisely a Johansson algebra: a bounded distributive lattice with relative
pseudo-complement (Heyting implication `⇨`) but no designated bottom element. The connection
to minimal logic was established by Rasiowa and Sikorski.

## Main Definitions

- `AlgEvaluate`: Generic evaluator mapping propositions to elements of a GHA `H`, with an
  explicit `bot_val : H` parameter (since GHA lacks a bottom element).
- `GHAValid`: Validity in all Generalized Heyting Algebras (quantifies over `bot_val`).
- `HAValid`: Validity in all Heyting Algebras (uses canonical `⊥`).
- `BAValid`: Validity in all Boolean Algebras (uses canonical `⊥`).
- `AlgTValid`: Theory validity — a valuation models a theory `T` if every axiom evaluates
  to `⊤`. Used to state general algebraic completeness via `Theory.alg_complete`.

## Design Notes

`AlgEvaluate` takes `bot_val : H` as an explicit parameter because `GeneralizedHeytingAlgebra`
does not guarantee a bottom element. This parameter is the Johansson "designated constant" —
it can be any element of the algebra. At the `HeytingAlgebra` and `BooleanAlgebra` levels,
`bot_val = ⊥` is the unique canonical choice (and `HAValid`/`BAValid` hardcode it, eliminating
the parameter entirely).

The ND completeness theorem `Theory.alg_complete` unifies the three validity predicates:
a formula `A` is derivable in theory `T` iff `AlgEvaluate v bot_val A = ⊤` for every GHA,
every valuation `v`, every `bot_val`, and every `T`-valid assignment (via `AlgTValid`). The
tier-specific ND results (`MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`)
specialize this by fixing the algebra class and (for HA/BA) setting `bot_val = ⊥`.

The Hilbert-primary completeness theorems (`MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`,
`CPL.hilbert_alg_complete`) are proved independently via the Hilbert Lindenbaum algebra and
do not require `[DecidableEq Atom]`. Conservative extension (`hilbertIplConservativeOverMpl`)
and Glivenko (`hilbertGlivenko`) are proved directly in the Hilbert setting, with their ND
counterparts (`ipl_conservative_over_mpl`, `glivenko`) derived as corollaries via algebraic
bridges. See `HilbertConservativeGlivenko.lean` for the unified Hilbert-primary module.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [A. Rasiowa, R. Sikorski, *The Mathematics of Metamathematics*][RasiowaSikorski1963]
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

/-- A valuation `v` with bottom value `bot_val` models a theory `T` if every axiom of `T`
evaluates to `⊤`. This is Thomas Waring's `v ⊨ T` pattern, parametric in the theory.

This predicate is used to state general algebraic completeness: a formula is derivable in `T`
iff it evaluates to `⊤` in every GHA under every `T`-valid valuation. -/
def AlgTValid {H : Type*} [GeneralizedHeytingAlgebra H]
    (T : PL.Theory Atom) (v : Atom → H) (bot_val : H) : Prop :=
  ∀ B ∈ T, AlgEvaluate v bot_val B = ⊤

end Cslib.Logic.PL
