/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.Defs
public import Cslib.Foundations.Logic.Tableau.ClosureCondition

/-! # Modal K Tableau Closure

This module instantiates the generic closure condition from the Foundations layer for
the modal K tableau, using classical closure (T(⊥) or T(φ)/F(φ) contradiction at the
same world label).

## Main Definitions

- `ModalClassicalClosure`: The closure instance for modal K tableau branches.
- `isModalClosed`: Convenience predicate wrapping the closure instance.

## Design

Modal K uses the same classical closure condition as classical propositional tableau.
A branch is closed when it contains T(⊥) at any world label, or both T(φ) and F(φ)
at the same world label for any formula φ. The world label is encoded as the `L` type
parameter (here `WorldIndex`), so the Foundations `ClassicalClosure` instance handles
both conditions atomically.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Classical Closure for Modal K -/

/-- The modal K tableau uses classical closure: a branch is closed when it contains T(⊥)
at any world label, or both T(φ) and F(φ) at the same world label. -/
instance instModalClosureCondition :
    ClosureCondition (Proposition Atom) WorldIndex :=
  ClassicalClosure.instClosureConditionOfBEqOfHasBot

/-- Test whether a modal K branch is classically closed.

A branch is closed when it contains T(⊥) at any world, or both T(φ) and F(φ) at the
same world label `w` for any formula φ. -/
def isModalClosed (b : List (SignedFormula (Proposition Atom) WorldIndex)) : Bool :=
  ClosureCondition.isClosed b

end Cslib.Logic.Modal.Tableau

end
