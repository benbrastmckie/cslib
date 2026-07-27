/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Tableau.Branch
public import Cslib.Foundations.Logic.Tableau.ClosureCondition

/-! # Temporal Tableau Closure

This module defines the closure conditions for the temporal tableau calculus.

## Two Closure Modes

1. **Classical closure**: T(⊥) at any time, or T(φ)/F(φ) at the same time label.
   Inherited from the Foundations `ClassicalClosure` instance.

2. **Eventuality-defect closure**: A saturated branch that is time-subset blocked
   (by `isTemporallyBlocked`) and still has unfulfilled positive Until/Since
   eventualities is closed. This implements the eventuality fulfilment requirement
   from the Reynolds tableau termination argument.

## Design

`TemporalClosureReason Atom` extends the classical case with the new `eventualityDefect`
constructor. `findTemporalClosure` computes the combined closure check.

## References

* Bimodal `Decidability/Saturation.lean` (blocking + eventuality tracking template)
* [R. Reynolds, *An axiomatization of prior's tense logic*][Reynolds1994]
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Temporal Closure Reason -/

/-- An explanation of why a temporal tableau branch is closed.

Three closure modes are supported:
- `botPos t`: Branch contains T(⊥) at time `t` (classical).
- `contradiction φ t`: Branch contains both T(φ) and F(φ) at time `t` (classical).
- `eventualityDefect t`: Branch is time-subset-blocked at time `t` with an unfulfilled
  positive Until or Since eventuality (eventuality-defect closure). -/
inductive TemporalClosureReason (Atom : Type*) where
  /-- Branch contains T(⊥) at time `t`. -/
  | botPos (t : TimeIndex) : TemporalClosureReason Atom
  /-- Branch contains both T(φ) and F(φ) at time `t`. -/
  | contradiction (φ : Formula Atom) (t : TimeIndex) : TemporalClosureReason Atom
  /-- Branch is blocked at time `t` with an unfulfilled eventuality. -/
  | eventualityDefect (t : TimeIndex) : TemporalClosureReason Atom

/-! ## Classical Temporal Closure -/

/-- The temporal tableau uses classical closure: a branch is closed when it contains T(⊥)
at any time label, or both T(φ) and F(φ) at the same time label. -/
instance instTemporalClosureCondition :
    ClosureCondition (Formula Atom) TimeIndex :=
  ClassicalClosure.instClosureConditionOfBEqOfHasBot

/-- Test whether a temporal branch is classically closed. -/
def isClassicallyClosed (b : TBranch Atom) : Bool :=
  ClosureCondition.isClosed b

/-- Find the classical closure reason for a temporal branch, if any. -/
def findClassicalClosure (b : TBranch Atom) : Option (TemporalClosureReason Atom) :=
  match b.find? fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom) with
  | some sf => some (.botPos sf.label)
  | none =>
    match Branch.findContradiction b with
    | some (φ, t) => some (.contradiction φ t)
    | none => none

/-! ## Eventuality-Defect Closure -/

/-- Check if any time on the branch is temporally blocked with an unfulfilled eventuality.
Returns the blocked time if found. -/
def findEventualityDefect (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom) : Option TimeIndex :=
  if !tracker.hasPending then none
  else findBlockedTime b ord tracker

/-- Find a temporal closure reason for a branch, checking both classical and
eventuality-defect closure. Returns `none` if the branch is open. -/
def findTemporalClosure (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom := EventualityTracker.empty) :
    Option (TemporalClosureReason Atom) :=
  match findClassicalClosure b with
  | some r => some r
  | none =>
    match findEventualityDefect b ord tracker with
    | some t => some (.eventualityDefect t)
    | none => none

/-- Test whether a temporal branch is closed (classically or by eventuality-defect). -/
def isTemporalClosed (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom := EventualityTracker.empty) : Bool :=
  (findTemporalClosure b ord tracker).isSome

end Cslib.Logic.Temporal.Tableau

end
