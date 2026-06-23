/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Foundations.Order.HilbertAlgebra
public import Cslib.Logics.Propositional.Defs

/-! # Hilbert Algebraic Semantics for Propositional Logic

This module defines a Hilbert evaluator for propositional logic, parameterized over any
`HilbertAlgebra`. This specializes the evaluator to the `{⇨, ⊤}` fragment of
intuitionistic logic — the implication-only fragment — using only `⇨` from the algebra.

The Hilbert algebra models `IPL⟨→,⊤⟩`, the purely implicational fragment. Since
`PL.Proposition` includes `bot`, `and`, and `or` constructors, `HilbertEvaluate` maps
these to `⊤` (the neutral default value), consistent with the fragment convention
established in `BrouwerianEvaluate`.

## Main Definitions

- `HilbertEvaluate`: maps `PL.Proposition Atom` to an element of a `HilbertAlgebra H`
  given a variable assignment `v : Atom → H`. Atoms map to `v x`, implication maps to
  `⇨`, and `bot`, `and`, `or` default to `⊤`.
- `HilbertValid`: validity in all Hilbert algebras — a proposition evaluates to `⊤`
  under every Hilbert algebra and every variable assignment.

## Design Notes

`HilbertEvaluate` uses only `⇨` from the algebra. For formulas in the `{⇨}` fragment
(i.e., formulas built from atoms and `imp` only), `HilbertEvaluate v A` correctly
captures the algebraic semantics for `IPL⟨→,⊤⟩`. The defaulting of `bot`, `and`, `or`
to `⊤` is semantically neutral for such formulas (they never appear in the fragment).

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Hilbert Algebraic Evaluator -/

/-- Evaluate a proposition in a Hilbert algebra `H`.

The evaluator is parameterized by `v : Atom → H`, the assignment of algebra elements to
propositional atoms. Connectives map to the corresponding algebraic operations:
- `atom x` → `v x`
- `⊥` → `⊤` (default value; `HilbertAlgebra` has no `⊥`)
- `φ → ψ` → `HilbertEvaluate v φ ⇨ HilbertEvaluate v ψ` (Hilbert implication)
- `φ ∧ ψ` → `⊤` (default value; `HilbertAlgebra` has no `⊓`)
- `φ ∨ ψ` → `⊤` (default value; `HilbertAlgebra` has no `⊔`) -/
def HilbertEvaluate {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => ⊤
  | .imp a b => HilbertEvaluate v a ⇨ HilbertEvaluate v b
  | .and _ _ => ⊤
  | .or _ _ => ⊤

@[simp]
theorem HilbertEvaluate_atom {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) (x : Atom) :
    HilbertEvaluate v (.atom x) = v x := rfl

@[simp]
theorem HilbertEvaluate_bot {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) :
    HilbertEvaluate v (.bot) = ⊤ := rfl

@[simp]
theorem HilbertEvaluate_imp {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    HilbertEvaluate v (.imp a b) =
      (HilbertEvaluate v a ⇨ HilbertEvaluate v b) := rfl

@[simp]
theorem HilbertEvaluate_and {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    HilbertEvaluate v (.and a b) = ⊤ := rfl

@[simp]
theorem HilbertEvaluate_or {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) (a b : PL.Proposition Atom) :
    HilbertEvaluate v (.or a b) = ⊤ := rfl

/-! ## Hilbert Validity -/

/-- A proposition is Hilbert-valid iff it evaluates to `⊤` under every Hilbert algebra `H`
and every variable assignment `v : Atom → H`. -/
def HilbertValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [HilbertAlgebra H] (v : Atom → H),
    HilbertEvaluate v φ = ⊤

end Cslib.Logic.PL

end
