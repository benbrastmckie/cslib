/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

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

/-! ## Branch/Ordering Coupling: Single-Step Preservation -/

omit [Hashable Atom] in
/-- `temporalStepBranch` preserves `InstantStrict` and the `OrdFreshWRT` branch/ordering
coupling invariant: if the current ordering `ord` is `InstantStrict` and fresh with
respect to `b` (every constraint endpoint is `< branchNextTime b`), then whenever one
expansion step succeeds, the resulting ordering `newOrd` is again `InstantStrict`, and
every produced branch `nb ∈ newBs` is `OrdFreshWRT` with `newOrd`.

`temporalStepBranch` only ever updates `ord` via a single call to `temporalApplyOne` on
the found signed formula `sf ∈ b`, so this packages `temporalApplyOne_preserves`
(Rules.lean) as the inductive step for the run-level `InstantStrict` threading proof
below. -/
lemma temporalStepBranch_preserves
    (b expanded : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hIS : TimeOrdering.InstantStrict ord) (hOFW : OrdFreshWRT b ord)
    (newBs newExps : List (TBranch Atom)) (newOrd : TimeOrdering)
    (newTracker : EventualityTracker Atom)
    (h : temporalStepBranch b expanded ord tracker = some (newBs, newExps, newOrd, newTracker)) :
    TimeOrdering.InstantStrict newOrd ∧ ∀ nb ∈ newBs, OrdFreshWRT nb newOrd := by
  unfold temporalStepBranch at h
  obtain ⟨sf, hsfmem, hsfeq⟩ := List.exists_of_findSome?_eq_some h
  by_cases hexp : expanded.any (· == sf) = true
  · rw [if_pos hexp] at hsfeq
    exact absurd hsfeq (by simp)
  · rw [if_neg hexp] at hsfeq
    rcases htA : temporalApplyOne sf b ord with ⟨result, newOrd'⟩
    rw [htA] at hsfeq
    obtain ⟨hISnew, hCase⟩ :=
      temporalApplyOne_preserves sf b ord hIS hOFW hsfmem result newOrd' htA
    cases result with
    | linear newForms =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsfeq
      obtain ⟨rfl, -, rfl, -⟩ := hsfeq
      refine ⟨hISnew, fun nb hnb => ?_⟩
      simp only [List.mem_singleton] at hnb
      subst hnb
      exact hCase newForms (by simp)
    | branching branches =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsfeq
      obtain ⟨rfl, -, rfl, -⟩ := hsfeq
      refine ⟨hISnew, fun nb hnb => ?_⟩
      simp only [List.mem_map] at hnb
      obtain ⟨nf, hnf, rfl⟩ := hnb
      exact hCase nf hnf
    | persistent newForms =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsfeq
      obtain ⟨rfl, -, rfl, -⟩ := hsfeq
      refine ⟨hISnew, fun nb hnb => ?_⟩
      simp only [List.mem_singleton] at hnb
      subst hnb
      exact hCase newForms (by simp)
    | notApplicable =>
      simp only [reduceCtorEq] at hsfeq

/-! ## Main Expansion Loop -/

mutual

/-- Fuel-based expansion of a list of temporal tableau branches.

Processes each branch in a worklist:
- If the branch is classically closed (T(⊥) or T/F contradiction), skip it.
- If the branch is time-subset-blocked and has unfulfilled eventualities,
  skip it (eventuality-defect closure).
- If the branch has no more applicable rules (saturated and open), return it as a
  countermodel together with the current time ordering.
- Otherwise apply one expansion step and recurse with remaining fuel.

Mutually recursive with `processNext`, which drains the current worklist one branch at
a time (structurally on `pending`) before `temporalExpandBranches` is re-entered with
strictly smaller `fuel`. Lifted to a top-level `mutual` block (task #439) so that both
functions get a standalone equation/induction principle -- the previous `let rec`
nesting inside `temporalExpandBranches` had none, blocking the run-level `InstantStrict`
threading proof. -/
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
    processNext branches expandedSets orderings trackers [] [] [] [] fuel'
termination_by (fuel, 0)

/-- Process the pending worklist for one fuel-step of `temporalExpandBranches`,
accumulating already-handled `(branch, expandedSet, ordering, tracker)` tuples in the
`done*` accumulators.

- If `pending` is empty, every branch in this worklist closed: return `.closed`.
- If the head branch is (classically or eventuality-)closed, skip it and continue
  with the tail.
- Otherwise, apply one expansion step (`temporalStepBranch`): if the branch is already
  saturated and open, return it as a countermodel; if it expanded, hand the updated
  worklist back to `temporalExpandBranches` with the decremented fuel `fuel'`.
- The mismatched-length fallback arms (`pendingExp`/`pendingOrd`/`pendingTrack` empty
  while `pending` is not) are defensive: the caller always keeps the four worklists in
  lock-step, so these arms are unreachable in practice but are needed for
  exhaustiveness; they skip the head branch and continue. -/
def processNext
    (pending : List (TBranch Atom))
    (pendingExp : List (TBranch Atom))
    (pendingOrd : List TimeOrdering)
    (pendingTrack : List (EventualityTracker Atom))
    (done : List (TBranch Atom))
    (doneExp : List (TBranch Atom))
    (doneOrd : List TimeOrdering)
    (doneTrack : List (EventualityTracker Atom))
    (fuel' : Nat) : TemporalTableauResult Atom :=
  match pending, pendingExp, pendingOrd, pendingTrack with
  | [], _, _, _ => .closed  -- All branches closed
  | b :: restBs, e :: restEs, ord :: restOrds, tracker :: restTracks =>
    if isTemporalClosed b ord tracker then
      -- Branch is closed (classical or eventuality-defect): skip it
      processNext restBs restEs restOrds restTracks
        (done ++ [b]) (doneExp ++ [e]) (doneOrd ++ [ord]) (doneTrack ++ [tracker]) fuel'
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
    processNext restBs [] [] [] done doneExp doneOrd doneTrack fuel'
  | _ :: restBs, _, [], _ =>
    processNext restBs [] [] [] done doneExp doneOrd doneTrack fuel'
  | _ :: restBs, _, _, [] =>
    processNext restBs [] [] [] done doneExp doneOrd doneTrack fuel'
termination_by (fuel', pending.length)

end

/-! ## Run-Level `InstantStrict` Threading -/

/-- Worklist invariant: parallel lists `bs` (branches) and `ords` (orderings) satisfy,
position-by-position, `InstantStrict` on the ordering and the `OrdFreshWRT` branch/ordering
coupling. Mismatched-length lists are vacuously excluded (`False`) -- by construction,
`temporalExpandBranches`/`processNext` always keep their branch and ordering worklists the
same length, so this never blocks a genuine derivation. -/
def WorklistInv : List (TBranch Atom) → List TimeOrdering → Prop
  | [], [] => True
  | b :: bs, ord :: ords => TimeOrdering.InstantStrict ord ∧ OrdFreshWRT b ord ∧ WorklistInv bs ords
  | _, _ => False

/-- Result invariant: an `.openBranch b ord` result carries an `InstantStrict` ordering;
`.closed` carries no ordering and is vacuously fine. -/
def ResultInv : TemporalTableauResult Atom → Prop
  | .closed => True
  | .openBranch _ ord => TimeOrdering.InstantStrict ord

omit [DecidableEq Atom] [Hashable Atom] in
/-- `WorklistInv` is preserved by list append (paired componentwise). -/
lemma worklistInv_append {l1 l2 : List (TBranch Atom)} {o1 o2 : List TimeOrdering}
    (h1 : WorklistInv l1 o1) (h2 : WorklistInv l2 o2) : WorklistInv (l1 ++ l2) (o1 ++ o2) := by
  induction l1 generalizing o1 with
  | nil =>
    cases o1 with
    | nil => simpa using h2
    | cons _ _ => simp only [WorklistInv] at h1
  | cons b bs ih =>
    cases o1 with
    | nil => simp only [WorklistInv] at h1
    | cons ord os =>
      obtain ⟨hIS, hOFW, hrest⟩ := h1
      exact ⟨hIS, hOFW, ih hrest⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `WorklistInv` holds for a list paired with a constant-ordering replication, given the
ordering is `InstantStrict` and every branch in the list is `OrdFreshWRT` it. -/
lemma worklistInv_map_const (bs : List (TBranch Atom)) (ord : TimeOrdering)
    (hIS : TimeOrdering.InstantStrict ord) (hOFW : ∀ nb ∈ bs, OrdFreshWRT nb ord) :
    WorklistInv bs (bs.map (fun _ => ord)) := by
  induction bs with
  | nil => simp [WorklistInv]
  | cons b bs ih =>
    simp only [List.map_cons, WorklistInv]
    exact ⟨hIS, hOFW b List.mem_cons_self, ih (fun nb hnb => hOFW nb (List.mem_cons_of_mem _ hnb))⟩

omit [Hashable Atom] in
/-- The `fuel = 0` base case: if `WorklistInv` holds for the worklist and the fuel-exhausted
search finds an open branch `(b, ord)`, then `InstantStrict ord`. -/
lemma worklistInv_findSome_zero
    (branches expandedSets : List (TBranch Atom)) (orderings : List TimeOrdering)
    (trackers : List (EventualityTracker Atom)) (b : TBranch Atom) (ord : TimeOrdering)
    (hInv : WorklistInv branches orderings)
    (h : (branches.zip expandedSets |>.zip (orderings.zip trackers)).findSome?
        (fun ((b, _), (ord, tracker)) =>
          if isTemporalClosed b ord tracker then none else some (b, ord)) = some (b, ord)) :
    TimeOrdering.InstantStrict ord := by
  induction branches generalizing expandedSets orderings trackers with
  | nil => simp at h
  | cons bh bt ih =>
    cases expandedSets with
    | nil => simp at h
    | cons eh et =>
      cases orderings with
      | nil => simp only [WorklistInv] at hInv
      | cons oh ot =>
        obtain ⟨hISoh, -, hrest⟩ := hInv
        cases trackers with
        | nil => simp at h
        | cons th tt =>
          simp only [List.zip_cons_cons, List.findSome?_cons] at h
          by_cases hclosed : isTemporalClosed bh oh th
          · simp only [hclosed, if_true] at h
            exact ih et ot tt hrest h
          · simp only [hclosed] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hISoh

/-- Run-level threading target for `temporalExpandBranches`: assuming the branch/ordering
worklist satisfies `WorklistInv`, the result satisfies `ResultInv`. -/
private def P1 (fuel : Nat) : Prop :=
  ∀ (branches expandedSets : List (TBranch Atom)) (orderings : List TimeOrdering)
    (trackers : List (EventualityTracker Atom)),
    WorklistInv branches orderings →
    ResultInv (temporalExpandBranches branches expandedSets orderings trackers fuel)

/-- Run-level threading target for `processNext`: assuming both the pending and the
accumulated (`done`) worklists satisfy `WorklistInv`, the result satisfies `ResultInv`. The
auxiliary `pendingExp`/`pendingTrack` lists carry no invariant requirement: if either is
shorter than `pending`, `processNext`'s defensive length-mismatch arms fire, which
(`processNext_mismatch_closed`) unconditionally drain to `.closed`. -/
private def P2 (fuel' : Nat) : Prop :=
  ∀ (pending pendingExp : List (TBranch Atom)) (pendingOrd : List TimeOrdering)
    (pendingTrack : List (EventualityTracker Atom))
    (done doneExp : List (TBranch Atom)) (doneOrd : List TimeOrdering)
    (doneTrack : List (EventualityTracker Atom)),
    WorklistInv pending pendingOrd → WorklistInv done doneOrd →
    ResultInv (processNext pending pendingExp pendingOrd pendingTrack
      done doneExp doneOrd doneTrack fuel')

omit [Hashable Atom] in
/-- If any of `processNext`'s length-mismatch side conditions holds (`pendingExp`,
`pendingOrd`, or `pendingTrack` is `[]` while `pending` need not be), the defensive fallback
arms fire and propagate the same mismatch until `pending` is drained, always reaching
`.closed` -- `ResultInv .closed` holds unconditionally, with no invariant needed on `pending`,
`pendingOrd`, or `done`. -/
lemma processNext_mismatch_closed
    (pending pendingExp : List (TBranch Atom)) (pendingOrd : List TimeOrdering)
    (pendingTrack : List (EventualityTracker Atom))
    (done doneExp : List (TBranch Atom)) (doneOrd : List TimeOrdering)
    (doneTrack : List (EventualityTracker Atom)) (fuel' : Nat)
    (hmis : pendingExp = [] ∨ pendingOrd = [] ∨ pendingTrack = []) :
    ResultInv (processNext pending pendingExp pendingOrd pendingTrack
      done doneExp doneOrd doneTrack fuel') := by
  induction pending generalizing pendingExp pendingOrd pendingTrack done doneExp doneOrd doneTrack
      with
  | nil => simp only [processNext, ResultInv]
  | cons b restBs ih =>
    cases pendingExp with
    | nil =>
      simp only [processNext]
      exact ih [] [] [] done doneExp doneOrd doneTrack (Or.inl rfl)
    | cons e restEs =>
      cases pendingOrd with
      | nil =>
        simp only [processNext]
        exact ih [] [] [] done doneExp doneOrd doneTrack (Or.inl rfl)
      | cons ord restOrds =>
        cases pendingTrack with
        | nil =>
          simp only [processNext]
          exact ih [] [] [] done doneExp doneOrd doneTrack (Or.inl rfl)
        | cons tracker restTracks =>
          rcases hmis with h | h | h <;> simp_all

omit [Hashable Atom] in
/-- Run-level `InstantStrict` threading: for every `fuel`, `P1 fuel`
holds. Proved by strong induction on `fuel`; the `fuel'+1` step establishes `P2 fuel'` by a
nested structural induction on `pending`, using `temporalStepBranch_preserves` above at
the branch-expansion step and the outer strong-induction hypothesis (at the *same* `fuel'`)
to close the cross-call back into `temporalExpandBranches`. -/
private lemma run_level_P1 : ∀ fuel : Nat, P1 (Atom := Atom) fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    rcases fuel with _ | fuel'
    · -- fuel = 0
      intro branches expandedSets orderings trackers hInv
      show ResultInv (temporalExpandBranches branches expandedSets orderings trackers 0)
      simp only [temporalExpandBranches]
      cases h : (branches.zip expandedSets |>.zip (orderings.zip trackers)).findSome?
          (fun ((b, _), (ord, tracker)) =>
            if isTemporalClosed b ord tracker then none else some (b, ord)) with
      | none => simp [ResultInv]
      | some x =>
        obtain ⟨b, ord⟩ := x
        simp only [ResultInv]
        exact worklistInv_findSome_zero branches expandedSets orderings trackers b ord hInv h
    · -- fuel = fuel' + 1
      have hP1fuel' : P1 fuel' := ih fuel' (Nat.lt_succ_self fuel')
      have hP2fuel' : P2 (Atom := Atom) fuel' := by
        intro pending
        induction pending with
        | nil =>
          intro pendingExp pendingOrd pendingTrack done doneExp doneOrd doneTrack _ _
          simp only [processNext, ResultInv]
        | cons b restBs ihp =>
          intro pendingExp pendingOrd pendingTrack done doneExp doneOrd doneTrack hpInv hdInv
          cases pendingExp with
          | nil =>
            exact processNext_mismatch_closed (b :: restBs) [] pendingOrd pendingTrack
              done doneExp doneOrd doneTrack fuel' (Or.inl rfl)
          | cons e restEs =>
            cases pendingOrd with
            | nil => simp only [WorklistInv] at hpInv
            | cons ord restOrds =>
              cases pendingTrack with
              | nil =>
                exact processNext_mismatch_closed (b :: restBs) (e :: restEs) (ord :: restOrds) []
                  done doneExp doneOrd doneTrack fuel' (Or.inr (Or.inr rfl))
              | cons tracker restTracks =>
                obtain ⟨hIS, hOFW, hpInvRest⟩ := hpInv
                simp only [processNext]
                by_cases hclosed : isTemporalClosed b ord tracker
                · simp only [hclosed, if_true]
                  exact ihp restEs restOrds restTracks (done ++ [b]) (doneExp ++ [e])
                    (doneOrd ++ [ord]) (doneTrack ++ [tracker]) hpInvRest
                    (worklistInv_append hdInv ⟨hIS, hOFW, trivial⟩)
                · simp only [hclosed]
                  cases hstep : temporalStepBranch b e ord tracker with
                  | none => simp only [ResultInv]; exact hIS
                  | some x =>
                    obtain ⟨newBs, newExps, newOrd, newTracker⟩ := x
                    obtain ⟨hISnew, hOFWnew⟩ :=
                      temporalStepBranch_preserves b e ord tracker hIS hOFW
                        newBs newExps newOrd newTracker hstep
                    have hWorklistNew : WorklistInv (done ++ newBs ++ restBs)
                        (doneOrd ++ newBs.map (fun _ => newOrd) ++ restOrds) :=
                      worklistInv_append
                        (worklistInv_append hdInv
                          (worklistInv_map_const newBs newOrd hISnew hOFWnew))
                        hpInvRest
                    exact hP1fuel' (done ++ newBs ++ restBs) (doneExp ++ newExps ++ restEs)
                      (doneOrd ++ newBs.map (fun _ => newOrd) ++ restOrds)
                      (doneTrack ++ newBs.map (fun _ => newTracker) ++ restTracks) hWorklistNew
      intro branches expandedSets orderings trackers hInv
      show ResultInv (temporalExpandBranches branches expandedSets orderings trackers (fuel' + 1))
      simp only [temporalExpandBranches]
      exact hP2fuel' branches expandedSets orderings trackers [] [] [] [] hInv
        (by simp [WorklistInv])

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

omit [Hashable Atom] in
/-- Entry-point corollary of the run-level `InstantStrict` threading above: whenever
`temporalTableau` returns an open branch, its time ordering is `InstantStrict`. This is the
`hInst` hypothesis needed by `openBranch_branchSat`'s order-preservation component in
`Completeness.lean` (`D = ℤ`, `f = ord.instant`). -/
theorem temporalTableau_instantStrict (φ : Formula Atom) (b : TBranch Atom) (ord : TimeOrdering)
    (h : temporalTableau φ = .openBranch b ord) : TimeOrdering.InstantStrict ord := by
  unfold temporalTableau at h
  have hInv : WorklistInv (Atom := Atom)
      [([⟨.neg, φ, 0⟩] : TBranch Atom)] [TimeOrdering.empty] := by
    simp [WorklistInv, TimeOrdering.instantStrict_empty, ordFreshWRT_empty]
  have hResult := run_level_P1 (Atom := Atom) (temporalFuel φ)
    [([⟨.neg, φ, 0⟩] : TBranch Atom)] [[]] [TimeOrdering.empty] [EventualityTracker.empty] hInv
  rw [h] at hResult
  exact hResult

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
