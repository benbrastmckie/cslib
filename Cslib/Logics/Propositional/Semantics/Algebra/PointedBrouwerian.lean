/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Foundations.Order.BrouwerianSemilattice
public import Cslib.Logics.Propositional.Semantics.Algebra
public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates

/-! # Pointed Brouwerian Algebraic Semantics for IPL⟨∧,→,⊥,⊤⟩

This module defines a **pointed Brouwerian evaluator** for propositional logic, parameterized
over any `BrouwerianSemilattice` with `OrderBot`. This extends `BrouwerianEvaluate` (from
`Brouwerian.lean`) by mapping `⊥` to the algebraic `⊥` rather than `⊤`.

A **pointed Brouwerian semilattice** is a `BrouwerianSemilattice` together with an `OrderBot`
instance — i.e., a structure carrying `⊤`, `⊓`, `⇨`, and `⊥` satisfying the usual axioms.
Every `HeytingAlgebra` is a pointed Brouwerian semilattice via the forgetful path.

## Main Definitions

- `PointedBrouwerianEvaluate`: maps `PL.Proposition Atom` to an element of a pointed
  Brouwerian semilattice `[BrouwerianSemilattice H] [OrderBot H]`. Key difference from
  `BrouwerianEvaluate`: `bot` maps to `⊥` (not `⊤`), and `or` still defaults to `⊤`.
- `PointedBrouwerianValid`: validity in all pointed Brouwerian semilattices.

## Bridge Lemma

For any `HeytingAlgebra H` and any or-free formula `φ`:
  `PointedBrouwerianEvaluate v φ = AlgEvaluate v ⊥ φ`

This bridge is crucial for the conservative extension proof: it shows that HA-validity on
or-free formulas implies pointed Brouwerian validity (since every HA is a pointed BSL).

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type*}

/-! ## Pointed Brouwerian Algebraic Evaluator -/

/-- Evaluate a proposition in a pointed Brouwerian semilattice `H`.

The evaluator is parameterized by `v : Atom → H`, the assignment of algebra elements to
propositional atoms. Connectives map to the corresponding algebraic operations:
- `atom x` → `v x`
- `⊥` → `⊥` (the `OrderBot` bottom; key difference from `BrouwerianEvaluate`)
- `φ → ψ` → `PointedBrouwerianEvaluate v φ ⇨ PointedBrouwerianEvaluate v ψ`
- `φ ∧ ψ` → `PointedBrouwerianEvaluate v φ ⊓ PointedBrouwerianEvaluate v ψ`
- `φ ∨ ψ` → `⊤` (default value for the or-free fragment; no `⊔` in BSL) -/
def PointedBrouwerianEvaluate {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => ⊥
  | .imp a b => PointedBrouwerianEvaluate v a ⇨ PointedBrouwerianEvaluate v b
  | .and a b => PointedBrouwerianEvaluate v a ⊓ PointedBrouwerianEvaluate v b
  | .or _ _ => ⊤

@[simp]
theorem PointedBrouwerianEvaluate_atom {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) (x : Atom) :
    PointedBrouwerianEvaluate v (.atom x) = v x := rfl

@[simp]
theorem PointedBrouwerianEvaluate_bot {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) :
    PointedBrouwerianEvaluate v .bot = ⊥ := rfl

@[simp]
theorem PointedBrouwerianEvaluate_imp {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    PointedBrouwerianEvaluate v (.imp a b) =
    PointedBrouwerianEvaluate v a ⇨ PointedBrouwerianEvaluate v b := rfl

@[simp]
theorem PointedBrouwerianEvaluate_and {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    PointedBrouwerianEvaluate v (.and a b) =
    PointedBrouwerianEvaluate v a ⊓ PointedBrouwerianEvaluate v b := rfl

@[simp]
theorem PointedBrouwerianEvaluate_or {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    PointedBrouwerianEvaluate v (.or a b) = ⊤ := rfl

/-! ## Pointed Brouwerian Validity -/

/-- A proposition is **pointed Brouwerian valid** if it evaluates to `⊤` in every pointed
Brouwerian semilattice under every variable assignment.

This is the semantic counterpart of derivability in the `ConjImpBotAxiom` system for
or-free formulas. -/
def PointedBrouwerianValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H), PointedBrouwerianEvaluate v φ = ⊤

/-! ## Bridge Lemma: HeytingAlgebra → Pointed Brouwerian -/

/-- For or-free formulas in any `HeytingAlgebra H`, the pointed Brouwerian evaluator
agrees with the generic algebraic evaluator at `⊥`:
  `PointedBrouwerianEvaluate v φ = AlgEvaluate v ⊥ φ`

This relies on the forgetful path `HeytingAlgebra → GeneralizedHeytingAlgebra →
BrouwerianSemilattice + OrderBot`, under which `⊥` is preserved.

The bridge is used to show that `HAValid φ → PointedBrouwerianValid φ` for or-free `φ`:
since every HA is a pointed BSL and the evaluators agree on or-free formulas, HA validity
transfers to pointed Brouwerian validity. -/
theorem pointedBrouwerianEvaluate_eq_algEvaluate_orFree
    {H : Type*} [HeytingAlgebra H]
    (v : Atom → H) (φ : PL.Proposition Atom)
    (hφ : φ.IsOrFree = true) :
    PointedBrouwerianEvaluate v φ = AlgEvaluate v ⊥ φ := by
  induction φ with
  | atom x => rfl
  | bot => simp [AlgEvaluate_bot]
  | imp a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hφ
    simp only [PointedBrouwerianEvaluate_imp, AlgEvaluate_imp, iha hφ.1, ihb hφ.2]
  | and a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hφ
    simp only [PointedBrouwerianEvaluate_and, AlgEvaluate_and, iha hφ.1, ihb hφ.2]
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hφ

end Cslib.Logic.PL

end
