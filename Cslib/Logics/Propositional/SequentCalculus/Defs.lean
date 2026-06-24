/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.Semantics.Bool
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert

/-! # Sequent Calculus Definitions for Propositional Logic

This module defines the basic structures for classical propositional sequent calculus LK,
following the all-additive Finset-based presentation of Negri and von Plato (2001).

## Main Definitions

- `LKSequent`: A sequent `Γ ⊢ₛ Δ` where both `Γ` (antecedent) and `Δ` (succedent) are
  `Finset`s of propositions over a given atom type.
- `LKSequent.valid`: Semantic validity of a sequent: every valuation that satisfies all
  antecedents satisfies at least one succedent.

## Notation

- `Γ ⊢ₛ Δ` for `LKSequent.mk Γ Δ`

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 2–3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type u} [DecidableEq Atom]

/-- An LK sequent `Γ ⊢ₛ Δ` consists of a finite antecedent `Γ` and a finite succedent `Δ`,
both drawn from `Proposition Atom`. -/
structure LKSequent (Atom : Type u) [DecidableEq Atom] where
  /-- The antecedent (left-hand side) of the sequent -/
  ant : Finset (Proposition Atom)
  /-- The succedent (right-hand side) of the sequent -/
  suc : Finset (Proposition Atom)

/-- Notation for sequents: `Γ ⊢ₛ Δ` means `LKSequent.mk Γ Δ`. -/
scoped notation Γ:60 " ⊢ₛ " Δ:60 => LKSequent.mk Γ Δ

/-- A sequent `Γ ⊢ₛ Δ` is semantically valid if every valuation satisfying all formulas in `Γ`
satisfies at least one formula in `Δ`.

This matches the standard sequent calculus interpretation (Negri and von Plato, 2001, Ch. 2). -/
def LKSequent.valid (seq : LKSequent Atom) : Prop :=
  ∀ (v : Valuation Atom),
    (∀ A ∈ seq.ant, Evaluate v A) → (∃ B ∈ seq.suc, Evaluate v B)

end Cslib.Logic.PL
