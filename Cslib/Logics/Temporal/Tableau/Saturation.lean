/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Temporal.Tableau.Closure

/-! # Temporal Tableau Saturation

This module implements the fuel-based saturation loop for the temporal tableau
decision procedure. It defines the main `temporalTableau` entry point and the
`TemporalTableauResult` type.

## Main Definitions

- `TemporalTableauResult Atom`: The result of the temporal tableau (closed or open
  branch + time ordering).
- `temporalExpandBranches`: Fuel-based branch expansion worklist loop.
- `temporalFuel`: Fuel bound derived from formula complexity.
- `temporalTableau`: Entry point for the decision procedure.
- `temporalHintikkaSet`: Saturation predicate for open branches.

## Design

The saturation loop maintains a worklist of `(branch, expandedSet, timeOrd, tracker)`
tuples. Each step picks the first open, unexpanded branch, applies `temporalApplyOne` to
its first unprocessed formula, and either:
- Adds the result to the same branch (linear/persistent), or
- Splits into sub-branches (branching).

The `expandedSet` tracks processed signed formulas. Persistent rules (G/H propagation,
Reynolds co-decomposition) keep the source formula off the expanded set so it re-fires
when new time points are added.

The eventuality tracker is updated when Until/Since witnesses are found. Time-subset
blocking prevents infinite temporal chains.

## References

* Modal `Saturation.lean` (algorithm template)
* Bimodal `Decidability/Saturation.lean` (eventuality + blocking template)
* [R. Reynolds, *An axiomatization of prior's tense logic*][Reynolds1994]
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Tableau Result Type -/

/-- The result of the temporal tableau computation.

- `closed`: Every branch is closed (the formula is temporal-unsatisfiable).
- `openBranch b ord`: An open saturated branch `b` with time ordering `ord`
  exists, from which a finite countermodel can be extracted. -/
inductive TemporalTableauResult (Atom : Type*) : Type _ where
  /-- All branches close: the formula is unsatisfiable. -/
  | closed : TemporalTableauResult Atom
  /-- An open saturated branch exists: a countermodel can be extracted. -/
  | openBranch : TBranch Atom → TimeOrdering → TemporalTableauResult Atom

/-! ## Fuel Bound -/

/-- Fuel bound for the temporal tableau.

Conservative bound based on subformula count. Sufficient for termination under
time-subset blocking: the number of distinct time types is bounded by `2^n` where
`n` is the number of subformulas, so the tableau depth is also bounded. -/
def temporalFuel (φ : Formula Atom) : Nat :=
  let n := subformulaCount φ
  (4 * n + 4) * (n + 2) + 2

/-! ## Eventuality Registration and Fulfilment -/

/-- Register new eventualities introduced by Until/Since rules. When a positive
`Until` or `Since` formula is expanded (event-witness branch or guard-continue
branch), record the eventuality obligation. -/
def registerEventualities (b : TBranch Atom)
    (tracker : EventualityTracker Atom) : EventualityTracker Atom :=
  b.foldl (fun tr sf =>
    match sf.sign with
    | .pos =>
      match asUntl? sf.formula with
      | some _ =>
        let e : Eventuality Atom := {
          formula := sf.formula, label := sf.label, isUntil := true }
        if tr.pending.any (· == e) then tr else tr.add e
      | none =>
        match asSnce? sf.formula with
        | some _ =>
          let e : Eventuality Atom := {
            formula := sf.formula, label := sf.label, isUntil := false }
          if tr.pending.any (· == e) then tr else tr.add e
        | none => tr
    | .neg => tr
  ) tracker

/-- Check which eventualities have been fulfilled on a branch.
An Until eventuality `U(guard,event)@t` is fulfilled if `T(event)@t'` appears
for some `t' > t` (i.e., the witness is found). Since is symmetric with past. -/
def fulfillEventualities (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom) : EventualityTracker Atom :=
  tracker.pending.foldl (fun tr e =>
    if e.isUntil then
      -- Until: look for T(event)@t' where t' is a future of e.label
      let futureTimes := ord.futureOf e.label
      match asUntl? e.formula with
      | some (event, _guard) =>
        if futureTimes.any fun t' => b.any fun sf =>
            sf.sign == .pos && sf.label == t' && sf.formula == event
        then tr.fulfill e.formula e.label
        else tr
      | none => tr
    else
      -- Since: look for T(event)@t' where t' is a past of e.label
      let pastTimes := ord.pastOf e.label
      match asSnce? e.formula with
      | some (event, _guard) =>
        if pastTimes.any fun t' => b.any fun sf =>
            sf.sign == .pos && sf.label == t' && sf.formula == event
        then tr.fulfill e.formula e.label
        else tr
      | none => tr
  ) tracker

/-! ## Branch Step -/

/-- Apply one expansion step to a branch, using the time ordering and eventuality tracker.

Returns `some (newBranches, newExpandedSets, newOrd, newTracker)` if a formula was expanded,
or `none` if the branch is saturated. -/
def temporalStepBranch
    (b : TBranch Atom)
    (expanded : TBranch Atom)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom) :
    Option (List (TBranch Atom) × List (TBranch Atom) × TimeOrdering × EventualityTracker Atom) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      let (result, newOrd) := temporalApplyOne sf b ord
      match result with
      | .linear newForms =>
        let newB := newForms ++ b
        let newTracker :=
          registerEventualities newForms tracker
          |> fulfillEventualities newB newOrd
        some ([newB], [expanded ++ [sf]], newOrd, newTracker)
      | .branching branches =>
        let newBranches := branches.map (· ++ b)
        some (newBranches, newBranches.map (fun _ => expanded ++ [sf]), newOrd, tracker)
      | .persistent newForms =>
        -- Persistent: keep sf on branch (don't add to expanded), add consequences
        let newB := newForms ++ b
        let newTracker :=
          registerEventualities newForms tracker
          |> fulfillEventualities newB newOrd
        some ([newB], [expanded], newOrd, newTracker)
      | .notApplicable => none

/-! ## Main Expansion Loop -/

/-- Fuel-based expansion of a list of temporal tableau branches.

Processes each branch in a worklist:
- If the branch is classically closed (T(⊥) or T/F contradiction), skip it.
- If the branch is time-subset-blocked and has unfulfilled eventualities,
  skip it (eventuality-defect closure).
- If the branch has no more applicable rules (saturated and open), return it as a
  countermodel together with the current time ordering.
- Otherwise apply one expansion step and recurse with remaining fuel. -/
def temporalExpandBranches
    (branches : List (TBranch Atom))
    (expandedSets : List (TBranch Atom))
    (orderings : List TimeOrdering)
    (trackers : List (EventualityTracker Atom))
    (fuel : Nat) : TemporalTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: return first open branch (treat as countermodel)
    match (branches.zip expandedSets |>.zip (orderings.zip trackers)).findSome?
        (fun ((b, _), (ord, tracker)) =>
          if isTemporalClosed b ord tracker then none else some (b, ord)) with
    | some (b, ord) => .openBranch b ord
    | none => .closed
  | fuel' + 1 =>
    let rec processNext
        (pending : List (TBranch Atom))
        (pendingExp : List (TBranch Atom))
        (pendingOrd : List TimeOrdering)
        (pendingTrack : List (EventualityTracker Atom))
        (done : List (TBranch Atom))
        (doneExp : List (TBranch Atom))
        (doneOrd : List TimeOrdering)
        (doneTrack : List (EventualityTracker Atom))
        : TemporalTableauResult Atom :=
      match pending, pendingExp, pendingOrd, pendingTrack with
      | [], _, _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, ord :: restOrds, tracker :: restTracks =>
        if isTemporalClosed b ord tracker then
          -- Branch is closed (classical or eventuality-defect): skip it
          processNext restBs restEs restOrds restTracks
            (done ++ [b]) (doneExp ++ [e]) (doneOrd ++ [ord]) (doneTrack ++ [tracker])
        else
          match temporalStepBranch b e ord tracker with
          | none =>
            -- Branch is saturated and open: return countermodel
            .openBranch b ord
          | some (newBs, newExps, newOrd, newTracker) =>
            -- Expanded: recurse with new branches
            temporalExpandBranches
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              (doneOrd ++ newBs.map (fun _ => newOrd) ++ restOrds)
              (doneTrack ++ newBs.map (fun _ => newTracker) ++ restTracks)
              fuel'
      | _ :: restBs, [], _, _ =>
        processNext restBs [] [] [] done doneExp doneOrd doneTrack
      | _ :: restBs, _, [], _ =>
        processNext restBs [] [] [] done doneExp doneOrd doneTrack
      | _ :: restBs, _, _, [] =>
        processNext restBs [] [] [] done doneExp doneOrd doneTrack
    processNext branches expandedSets orderings trackers [] [] [] []

/-! ## Entry Point -/

/-- The temporal tableau decision procedure.

Given a formula `φ`, runs the signed tableau starting from `F(φ)` at time `0`.
- Returns `closed` iff `φ` is temporal-valid (no model refutes it).
- Returns `openBranch b ord` iff `φ` is not valid; `b` and `ord` encode a
  finite countermodel (see `Completeness.lean`). -/
def temporalTableau (φ : Formula Atom) : TemporalTableauResult Atom :=
  let initialBranch : TBranch Atom := [⟨.neg, φ, 0⟩]
  temporalExpandBranches
    [initialBranch] [[]] [TimeOrdering.empty] [EventualityTracker.empty]
    (temporalFuel φ)

/-! ## Hintikka Set Predicate -/

/-- A temporal Hintikka set: a branch that is open (not closed) and saturated with
respect to all applicable rules, including G/H/F/P and until/since rules using `ord`.

For a branch `b` with time ordering `ord`, this holds when:
1. The branch is not closed (no classical contradiction, no eventuality-defect).
2. For every signed formula `sf` on the branch, the applicable rule's outputs are
   already on the branch:
   - Linear rules: all outputs present.
   - Branching rules: at least one complete branch's outputs present.
   - Persistent rules: all outputs present. -/
def temporalHintikkaSet
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom) : Prop :=
  isTemporalClosed b ord tracker = false ∧
  ∀ sf ∈ b,
    let (result, _) := temporalApplyOne sf b ord
    match result with
    | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
    | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
    | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
    | .notApplicable => True

end Cslib.Logic.Temporal.Tableau

end
