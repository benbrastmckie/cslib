/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Tableau.Rules

/-! # Temporal Tableau Branch Utilities

This module provides:
- `knownTimes`: collect distinct time indices from a branch
- `Eventuality` / `EventualityTracker`: track unfulfilled until/since obligations
- `timeType`, `isSubsetBlocked`, `isTemporallyBlocked`, `findBlockedTime`:
  the time-subset blocking device used for termination

These are ported from the bimodal
`Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean` with the
bimodal `Label.{world,time}` pair collapsed to a bare `Nat` time index.
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Branch Time Index Utilities -/

/-- Collect all distinct time indices appearing on a branch. -/
def knownTimes (b : TBranch Atom) : List TimeIndex :=
  (b.map (·.label)).eraseDups

/-- The maximum time index on a branch (0 if empty). -/
def maxTime (b : TBranch Atom) : TimeIndex :=
  b.foldl (fun acc sf => max acc sf.label) 0

/-! ## Eventuality Tracking -/

variable (Atom) in
/-- An eventuality records a pending obligation from a positive Until or Since formula.
Until eventualities require the event to be witnessed at some future time;
Since eventualities require the event at some past time. -/
structure Eventuality : Type _ where
  /-- The Until/Since formula that generated this eventuality. -/
  formula : Formula Atom
  /-- The time index at which the eventuality was introduced. -/
  label : TimeIndex
  /-- `true` for Until (future-directed), `false` for Since (past-directed). -/
  isUntil : Bool
  deriving DecidableEq

instance : BEq (Eventuality Atom) :=
  ⟨fun a b => decide (a = b)⟩

variable (Atom) in
/-- Tracks pending eventualities on a tableau branch.
Provides operations to add new eventualities and mark them as fulfilled. -/
structure EventualityTracker : Type _ where
  /-- List of pending eventualities. -/
  pending : List (Eventuality Atom)

namespace EventualityTracker

/-- Empty tracker with no pending eventualities. -/
def empty : EventualityTracker Atom := { pending := [] }

/-- Add a new eventuality to track. -/
def add (tracker : EventualityTracker Atom)
    (e : Eventuality Atom) : EventualityTracker Atom :=
  { pending := e :: tracker.pending }

/-- Remove a fulfilled eventuality (by formula and label match). -/
def fulfill (tracker : EventualityTracker Atom)
    (formula : Formula Atom) (label : TimeIndex) :
    EventualityTracker Atom :=
  { pending := tracker.pending.filter fun e =>
      !(e.formula == formula && e.label == label) }

/-- Check if there are any pending eventualities. -/
def hasPending (tracker : EventualityTracker Atom) : Bool :=
  !tracker.pending.isEmpty

/-- Get pending eventualities at a specific time index. -/
def pendingAtTime (tracker : EventualityTracker Atom)
    (t : TimeIndex) : List (Eventuality Atom) :=
  tracker.pending.filter fun e => e.label == t

/-- Check if an eventuality is no longer pending (fulfilled). -/
def isFulfilled (tracker : EventualityTracker Atom)
    (e : Eventuality Atom) : Bool :=
  !tracker.pending.any (· == e)

end EventualityTracker

/-! ## Subset Blocking for Temporal Tableau Termination

Subset blocking prevents infinite temporal chains in tableau expansion.
When a new time point `t'` has signed formulas that are a subset of an
ancestor time point `t`, further expansion from `t'` is blocked. -/

/-- Collect all signed formulas on a branch at a given time index. -/
def formulasAtTime (b : TBranch Atom) (t : TimeIndex) :
    List (TSF Atom) :=
  b.filter fun sf => sf.label == t

/-- Extract the "time type" of a time point: the set of `(sign, formula)` pairs
at that time, deduplicated. -/
def timeType (b : TBranch Atom) (t : TimeIndex) :
    List (Sign × Formula Atom) :=
  ((formulasAtTime b t).map fun sf =>
    (sf.sign, sf.formula)).eraseDups

/-- Check if the time type at `t_new` is a subset of the time type at `t_anc`. -/
def isSubsetBlocked (b : TBranch Atom) (t_new t_anc : TimeIndex) : Bool :=
  let typeNew := timeType b t_new
  let typeAnc := timeType b t_anc
  typeNew.all fun pair => typeAnc.any fun pair' => pair == pair'

/-! ## Ancestor Times (Transitive Closure) -/

/-- Compute the transitive closure of temporal predecessors of a given time
index. Uses fuel to avoid non-termination. -/
def ancestorTimes (ord : TimeOrdering) (t : TimeIndex)
    (fuel : Nat := 100) : List TimeIndex :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let directPredecessors := ord.constraints.filterMap fun (a, b) =>
      if b == t then some a else none
    let transitiveAncestors := directPredecessors.flatMap fun anc =>
      anc :: ancestorTimes ord anc fuel
    transitiveAncestors.eraseDups

/-- Check if all pending eventualities at time `t_new` are also pending at
the blocking ancestor `t_anc` (i.e., not newly introduced at `t_new`). -/
def allEventualitiesFulfilledOrDuplicated
    (tracker : EventualityTracker Atom) (t_new t_anc : TimeIndex) :
    Bool :=
  let pendingAtNew := tracker.pendingAtTime t_new
  pendingAtNew.all fun e =>
    let duplicatedAtAnc := tracker.pending.any fun e' =>
      e'.formula == e.formula && e'.label == t_anc &&
        e'.isUntil == e.isUntil
    duplicatedAtAnc

/-- Check if a given time index is temporally blocked by any ancestor time.
A time `t` is blocked when there is an ancestor `t_anc` such that
the signed formulas at `t` are a subset of those at `t_anc` and all
pending eventualities at `t` are also present at `t_anc`. -/
def isTemporallyBlocked (b : TBranch Atom) (t : TimeIndex)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom :=
      EventualityTracker.empty) : Bool :=
  let ancestors := ancestorTimes ord t
  ancestors.any fun t_anc =>
    isSubsetBlocked b t t_anc &&
      allEventualitiesFulfilledOrDuplicated tracker t_anc t

/-- Check if any active time on the branch is temporally blocked.
Returns the first blocked time found, or `none` if none is blocked. -/
def findBlockedTime (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom :=
      EventualityTracker.empty) : Option TimeIndex :=
  (knownTimes b).find? fun t => isTemporallyBlocked b t ord tracker

end Cslib.Logic.Temporal.Tableau

end
