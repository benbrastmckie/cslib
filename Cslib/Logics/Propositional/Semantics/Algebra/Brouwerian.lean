/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Foundations.Order.BrouwerianSemilattice
public import Cslib.Logics.Propositional.Defs

/-! # Brouwerian Algebraic Semantics for Propositional Logic

This module defines a Brouwerian evaluator for propositional logic, parameterized over any
`BrouwerianSemilattice`. This specializes `AlgEvaluate` (from
`Cslib.Logics.Propositional.Semantics.Algebra`) to the weaker `BrouwerianSemilattice` setting,
where no bottom element or join are available.

The Brouwerian semilattice models the `{⊓, ⇨, ⊤}` fragment of intuitionistic logic. Since
`PL.Proposition` includes `bot` and `or` constructors, `BrouwerianEvaluate` maps these to `⊤`
(the neutral/default value), consistent with the "or-bot-free fragment" convention.

## Main Definitions

- `BrouwerianEvaluate`: maps `PL.Proposition Atom` to an element of a `BrouwerianSemilattice H`
  given a variable assignment `v : Atom → H`. Atoms map to `v x`, `bot` and `or` default to
  `⊤`, `imp` maps to `⇨`, and `and` maps to `⊓`.
- `BrouwerianValid`: validity in all Brouwerian semilattices — a proposition evaluates to `⊤`
  under every Brouwerian semilattice, every variable assignment.

## Design Notes

`BrouwerianEvaluate` differs from `AlgEvaluate` in two ways:
1. It requires only `BrouwerianSemilattice` rather than `GeneralizedHeytingAlgebra`.
2. `bot` and `or` constructors map to `⊤` rather than taking an explicit `bot_val` parameter.

On formulas in the `{⊓, ⇨, ⊤}` fragment (i.e., formulas where `bot` and `or` do not appear),
`BrouwerianEvaluate v A = AlgEvaluate v ⊤ A` when the Brouwerian semilattice instance comes
from a GHA. This bridge is established by `brouwerianEmbeddingLemma` in `FreeJoinCompletion.lean`.

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Brouwerian Algebraic Evaluator -/

/-- Evaluate a proposition in a Brouwerian semilattice `H`.

The evaluator is parameterized by `v : Atom → H`, the assignment of algebra elements to
propositional atoms. Connectives map to the corresponding algebraic operations:
- `atom x` → `v x`
- `⊥` → `⊤` (default value for the or-bot-free fragment; `BrouwerianSemilattice` has no `⊥`)
- `φ → ψ` → `BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ` (Heyting implication)
- `φ ∧ ψ` → `BrouwerianEvaluate v φ ⊓ BrouwerianEvaluate v ψ` (meet)
- `φ ∨ ψ` → `⊤` (default value for the or-bot-free fragment; `BrouwerianSemilattice` has no `⊔`) -/
def BrouwerianEvaluate {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => ⊤
  | .imp a b => BrouwerianEvaluate v a ⇨ BrouwerianEvaluate v b
  | .and a b => BrouwerianEvaluate v a ⊓ BrouwerianEvaluate v b
  | .or _ _ => ⊤

@[simp]
theorem BrouwerianEvaluate_atom {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (x : Atom) :
    BrouwerianEvaluate v (.atom x) = v x := rfl

@[simp]
theorem BrouwerianEvaluate_bot {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) :
    BrouwerianEvaluate v (.bot) = ⊤ := rfl

@[simp]
theorem BrouwerianEvaluate_imp {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    BrouwerianEvaluate v (.imp a b) =
      (BrouwerianEvaluate v a ⇨ BrouwerianEvaluate v b) := rfl

@[simp]
theorem BrouwerianEvaluate_and {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    BrouwerianEvaluate v (.and a b) =
      (BrouwerianEvaluate v a ⊓ BrouwerianEvaluate v b) := rfl

@[simp]
theorem BrouwerianEvaluate_or {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    BrouwerianEvaluate v (.or a b) = ⊤ := rfl

/-! ## Brouwerian Validity -/

/-- A proposition is Brouwerian-valid iff it evaluates to `⊤` under every Brouwerian
semilattice `H` and every variable assignment `v : Atom → H`. -/
def BrouwerianValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [BrouwerianSemilattice H] (v : Atom → H),
    BrouwerianEvaluate v φ = ⊤

end Cslib.Logic.PL
