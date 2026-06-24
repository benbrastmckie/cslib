/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.Branch
public import Cslib.Foundations.Logic.Tableau.Closure

/-! # Closure Condition Typeclass

This module defines the `ClosureCondition F L` typeclass, which abstracts the closure
criterion for a tableau calculus over formula type `F` with label type `L`.

Two instances are provided, corresponding to classical and intuitionistic/minimal logic:

| Instance | Logic | Closes when |
|----------|-------|-------------|
| `ClassicalClosure` | Classical | T(bot) at any label, OR T(phi)/F(phi) at the same label |
| `IntuitionisticClosure` | Intuitionistic/Minimal | T(bot) at any label only |

## Design

The key method `findClosure` returns `Option (ClosureReason F L)` rather than `Bool`, so
callers can extract the reason for closure (needed for proof extraction and countermodel
construction).

The minimal tableau uses the same closure criterion as the intuitionistic tableau
(`isMinimallyClosed = Branch.hasContradiction`), computed directly without going through
this typeclass.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-! ## ClosureCondition Typeclass -/

/-- Typeclass for the branch closure criterion of a tableau calculus.

Instances parameterize the closure check, allowing the same tableau algorithm
to be used across classical, intuitionistic, and minimal logics.

The `findClosure` method returns `some r` when the branch is closed (with reason `r`)
and `none` when the branch is open. -/
class ClosureCondition (F : Type*) (L : Type*) where
  /-- Check whether the branch is closed; return the reason if so. -/
  findClosure : Branch F L → Option (ClosureReason F L)

namespace ClosureCondition

/-- `true` when the branch is closed according to the given `ClosureCondition`. -/
def isClosed [ClosureCondition F L] (b : Branch F L) : Bool :=
  (ClosureCondition.findClosure b).isSome

/-- `true` when the branch is open (not closed) according to the given `ClosureCondition`. -/
def isOpen [ClosureCondition F L] (b : Branch F L) : Bool :=
  !(isClosed b)

end ClosureCondition

/-! ## Classical Closure -/

namespace ClassicalClosure

/-- The classical closure condition for tableau calculi.

A branch is classically closed when it contains T(bot) at any label, or both
T(phi) and F(phi) at the same label for any formula phi. -/
instance [BEq F] [BEq L] [HasBot F] :
    ClosureCondition F L where
  findClosure b :=
    match b.find? fun sf => sf.isPos && sf.formula == (HasBot.bot : F) with
    | some sf => some (.botPos sf.label)
    | none =>
      match b.findContradiction with
      | some (phi, l) => some (.contradiction phi l)
      | none => none

end ClassicalClosure

/-! ## Intuitionistic Closure -/

namespace IntuitionisticClosure

/-- The intuitionistic closure condition for tableau calculi.

A branch is intuitionistically closed when it contains T(bot) at any label.
Complementary pairs T(phi)/F(phi) do NOT close a branch in intuitionistic logic. -/
instance [BEq F] [HasBot F] : ClosureCondition F L where
  findClosure b :=
    match b.find? fun sf => sf.isPos && sf.formula == (HasBot.bot : F) with
    | some sf => some (.botPos sf.label)
    | none => none

end IntuitionisticClosure

end Cslib.Logic.Tableau

end
