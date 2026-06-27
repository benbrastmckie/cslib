/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Temporal.Tableau.Defs
public import Cslib.Logics.Temporal.Tableau.TimeOrdering

/-! # Temporal Tableau Rules

This module defines `temporalApplyOne`, the procedural core of the temporal tableau
decision procedure, and its supporting helpers.

## Rule Summary

| Rule | Input | Output | Type |
|------|-------|--------|------|
| Propositional | T/F(φ ∧ ψ/φ ∨ ψ/φ → ψ/¬φ) | standard | linear/branching |
| allFuturePos | T(Gφ)@t | T(φ)@t' for each t' in futureOf(t) | persistent |
| allPastPos | T(Hφ)@t | T(φ)@t' for each t' in pastOf(t) | persistent |
| someFuturePos | T(Fφ)@t | create t', T(φ)@t', propagate G/H | linear |
| somePastPos | T(Pφ)@t | create t', T(φ)@t', propagate G/H | linear |
| allFutureNeg | F(Gφ)@t | = T(F¬φ)@t | (by duality) |
| allPastNeg | F(Hφ)@t | = T(P¬φ)@t | (by duality) |
| untlPos | T(U(guard,event))@t | branch: T(event)@t' OR T(guard)@t' + T(U)@t' | branching |
| untlNeg | F(U(guard,event))@t | Reynolds co-decomp at future times | branching |
| sncePos | T(S(guard,event))@t | branch: T(event)@t' OR T(guard)@t' + T(S)@t' | branching |
| snceNeg | F(S(guard,event))@t | Reynolds co-decomp at past times | branching |

## Convention Note (Pnueli)

In the Lean inductive `Formula`, `untl guard event` stores the guard first (Pnueli convention).
So `T(untl guard event)` holds at t iff ∃ s > t, event at s ∧ guard at all r ∈ (t,s).
The `asUntl?` decomposition adapter returns `some (event, guard)` — note the reversed order
for local use; the internal `untl` constructor is always guard-first.

## References

* Bimodal `Decidability/Tableau.lean` (algorithm template, without box/world machinery)
* [R. Reynolds, *An axiomatization of prior's tense logic*][Reynolds1994]
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- Abbreviated type alias for temporal signed formulas at time index. -/
abbrev TSF (Atom : Type*) := SignedFormula (Formula Atom) TimeIndex

/-- Abbreviated type alias for a temporal branch. -/
abbrev TBranch (Atom : Type*) := List (TSF Atom)

/-! ## Helper: Fresh Time from Branch -/

/-- The maximum time index appearing on a branch. -/
def branchMaxTime (b : TBranch Atom) : TimeIndex :=
  b.foldl (fun mx sf => max mx sf.label) 0

/-- A fresh time index not appearing on the branch (one more than max). -/
def branchNextTime (b : TBranch Atom) : TimeIndex :=
  branchMaxTime b + 1

omit [DecidableEq Atom] [Hashable Atom] in
/-- `branchNextTime b` is strictly greater than every time label on `b`. -/
lemma branchNextTime_gt (b : TBranch Atom) (sf : TSF Atom)
    (hmem : sf ∈ b) : sf.label < branchNextTime b := by
  unfold branchNextTime branchMaxTime
  have hkey : ∀ (xs : List (TSF Atom)) (sf0 : TSF Atom),
      sf0 ∈ xs → sf0.label ≤ xs.foldl (fun mx sf' => max mx sf'.label) 0 := by
    intro xs
    induction xs with
    | nil => intro _ hmem'; simp at hmem'
    | cons hd tl ih =>
      intro sf0 hmem'
      simp only [List.mem_cons] at hmem'
      simp only [List.foldl]
      have hmon : ∀ (ys : List (TSF Atom)) (init : Nat),
          init ≤ ys.foldl (fun mx sf' => max mx sf'.label) init := by
        intro ys
        induction ys with
        | nil => intro _; simp
        | cons y rest ihr =>
          intro init
          simp only [List.foldl]
          exact Nat.le_trans (Nat.le_max_left _ _) (ihr _)
      have hmono : ∀ (ys : List (TSF Atom)) (init init' : Nat),
          init ≤ init' →
          ys.foldl (fun mx sf' => max mx sf'.label) init ≤
          ys.foldl (fun mx sf' => max mx sf'.label) init' := by
        intro ys
        induction ys with
        | nil => intro _ _ hle; simpa
        | cons y rest ihr =>
          intro init init' hle
          simp only [List.foldl]
          exact ihr _ _ (by omega)
      cases hmem' with
      | inl heq =>
        subst heq
        -- After `list.foldl max`, init is `max 0 sf0.label = sf0.label`
        -- Need: sf0.label ≤ foldl max (max 0 sf0.label) tl
        have hge : sf0.label ≤ max 0 sf0.label := Nat.le_max_right _ _
        exact Nat.le_trans hge (hmon tl _)
      | inr hmem' =>
        -- sf0 ∈ tl, init becomes `max 0 hd.label`
        -- Need: sf0.label ≤ foldl max (max 0 hd.label) tl
        calc sf0.label ≤ tl.foldl (fun mx sf' => max mx sf'.label) 0 := ih sf0 hmem'
          _ ≤ tl.foldl (fun mx sf' => max mx sf'.label) (max 0 hd.label) :=
              hmono tl _ _ (Nat.zero_le _)
  have hle := hkey b sf hmem
  exact Nat.lt_succ_of_le hle

/-! ## Helper: Propagation Collectors -/

/-- Collect T(Gφ) formulas from the branch at time `t`. -/
def allFuturePosAt (b : TBranch Atom) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .pos && sf.label == t then
      match asAllFuture? sf.formula with
      | some φ => some φ
      | none => none
    else none

/-- Collect T(Hφ) formulas from the branch at time `t`. -/
def allPastPosAt (b : TBranch Atom) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .pos && sf.label == t then
      match asAllPast? sf.formula with
      | some φ => some φ
      | none => none
    else none

/-- Collect F(Fφ) formulas from the branch at time `t`. -/
def someFutureNegAt (b : TBranch Atom) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .neg && sf.label == t then
      match asSomeFuture? sf.formula with
      | some φ => some φ
      | none => none
    else none

/-- Collect F(Pφ) formulas from the branch at time `t`. -/
def somePastNegAt (b : TBranch Atom) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .neg && sf.label == t then
      match asSomePast? sf.formula with
      | some φ => some φ
      | none => none
    else none

/-- Collect F(U(guard,event)) formulas from the branch at time `t`. -/
def untlNegAt (b : TBranch Atom) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .neg && sf.label == t then
      match asUntl? sf.formula with
      | some _ => some sf.formula
      | none => none
    else none

/-- Collect F(S(guard,event)) formulas from the branch at time `t`. -/
def snceNegAt (b : TBranch Atom) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .neg && sf.label == t then
      match asSnce? sf.formula with
      | some _ => some sf.formula
      | none => none
    else none

/-- Generate propagation formulas to a fresh time `t'` from existing universals at `t`.

Propagates:
- T(Gφ)@t → T(φ)@t' (because φ must hold at all future times of t)
- T(Hφ)@t → (not propagated to future)
- F(Fφ)@t → F(φ)@t' (negative someFuture propagates)
- F(U(...))@t → F(U(...))@t' (negative until propagates)
-/
def propagateToFuture (b : TBranch Atom) (t t' : TimeIndex) : List (TSF Atom) :=
  let gProps := (allFuturePosAt b t).filterMap fun φ =>
    let sf : TSF Atom := ⟨.pos, φ, t'⟩
    if b.any (· == sf) then none else some sf
  let fNegProps := (someFutureNegAt b t).filterMap fun φ =>
    let sf : TSF Atom := ⟨.neg, φ, t'⟩
    if b.any (· == sf) then none else some sf
  let untlNegProps := (untlNegAt b t).filterMap fun φ =>
    let sf : TSF Atom := ⟨.neg, φ, t'⟩
    if b.any (· == sf) then none else some sf
  gProps ++ fNegProps ++ untlNegProps

/-- Generate propagation formulas to a fresh past time `t'` from existing universals at `t`.

Propagates:
- T(Hφ)@t → T(φ)@t' (because φ must hold at all past times of t)
- F(Pφ)@t → F(φ)@t' (negative somePast propagates)
- F(S(...))@t → F(S(...))@t' (negative since propagates)
-/
def propagateToPast (b : TBranch Atom) (t t' : TimeIndex) : List (TSF Atom) :=
  let hProps := (allPastPosAt b t).filterMap fun φ =>
    let sf : TSF Atom := ⟨.pos, φ, t'⟩
    if b.any (· == sf) then none else some sf
  let pNegProps := (somePastNegAt b t).filterMap fun φ =>
    let sf : TSF Atom := ⟨.neg, φ, t'⟩
    if b.any (· == sf) then none else some sf
  let snceNegProps := (snceNegAt b t).filterMap fun φ =>
    let sf : TSF Atom := ⟨.neg, φ, t'⟩
    if b.any (· == sf) then none else some sf
  hProps ++ pNegProps ++ snceNegProps

/-! ## Main Rule Application -/

/-- Apply positive temporal rules to a signed formula. -/
def temporalApplyPos
    (sf : TSF Atom)
    (b : TBranch Atom)
    (ord : TimeOrdering) :
    RuleResult (Formula Atom) TimeIndex × TimeOrdering :=
  let t := sf.label
  let φ := sf.formula
  -- T(Gφ)@t → T(φ)@t' for each t' in futureOf(t) [persistent]
  match asAllFuture? φ with
  | some inner =>
    let newForms : List (TSF Atom) :=
      (ord.futureOf t).filterMap fun t' =>
        let sf' : TSF Atom := ⟨.pos, inner, t'⟩
        if b.any (· == sf') then none else some sf'
    if newForms.isEmpty then (.notApplicable, ord)
    else (.persistent newForms, ord)
  | none =>
  -- T(Hφ)@t → T(φ)@t' for each t' in pastOf(t) [persistent]
  match asAllPast? φ with
  | some inner =>
    let newForms : List (TSF Atom) :=
      (ord.pastOf t).filterMap fun t' =>
        let sf' : TSF Atom := ⟨.pos, inner, t'⟩
        if b.any (· == sf') then none else some sf'
    if newForms.isEmpty then (.notApplicable, ord)
    else (.persistent newForms, ord)
  | none =>
  -- T(Fφ)@t → create fresh t', T(φ)@t', propagate universals [linear]
  match asSomeFuture? φ with
  | some inner =>
    let t' := branchNextTime b
    let newOrd := ord.addFuture t t'
    let witness : TSF Atom := ⟨.pos, inner, t'⟩
    let props := propagateToFuture b t t'
    (.linear (witness :: props), newOrd)
  | none =>
  -- T(Pφ)@t → create fresh t', T(φ)@t', propagate universals [linear]
  match asSomePast? φ with
  | some inner =>
    let t' := branchNextTime b
    let newOrd := ord.addPast t t'
    let witness : TSF Atom := ⟨.pos, inner, t'⟩
    let props := propagateToPast b t t'
    (.linear (witness :: props), newOrd)
  | none =>
  -- T(U(guard,event))@t → branch: T(event)@t' | T(guard)@t' + T(U)@t' [branching]
  match asUntl? φ with
  | some (event, guard) =>
    let t' := branchNextTime b
    let newOrd := ord.addFuture t t'
    let props := propagateToFuture b t t'
    let branch1 : List (TSF Atom) := [⟨.pos, event, t'⟩] ++ props
    let branch2 : List (TSF Atom) := [⟨.pos, guard, t'⟩, ⟨.pos, φ, t'⟩] ++ props
    (.branching [branch1, branch2], newOrd)
  | none =>
  -- T(S(guard,event))@t → branch: T(event)@t' | T(guard)@t' + T(S)@t' [branching]
  match asSnce? φ with
  | some (event, guard) =>
    let t' := branchNextTime b
    let newOrd := ord.addPast t t'
    let props := propagateToPast b t t'
    let branch1 : List (TSF Atom) := [⟨.pos, event, t'⟩] ++ props
    let branch2 : List (TSF Atom) := [⟨.pos, guard, t'⟩, ⟨.pos, φ, t'⟩] ++ props
    (.branching [branch1, branch2], newOrd)
  | none =>
  (.notApplicable, ord)

/-- Apply negative temporal rules (Reynolds co-decomposition for Until/Since). -/
def temporalApplyNeg
    (sf : TSF Atom)
    (b : TBranch Atom)
    (ord : TimeOrdering) :
    RuleResult (Formula Atom) TimeIndex × TimeOrdering :=
  let t := sf.label
  let φ := sf.formula
  -- F(U(guard,event))@t → Reynolds co-decomposition at future times [branching]
  match asUntl? φ with
  | some (event, guard) =>
    let futureTimes := ord.futureOf t
    -- Find future times where co-decomposition hasn't been applied
    let unprocessed := futureTimes.filter fun t' =>
      let negEvent : TSF Atom := ⟨.neg, event, t'⟩
      let negGuard : TSF Atom := ⟨.neg, guard, t'⟩
      !b.any (· == negEvent) && !b.any (· == negGuard)
    match unprocessed with
    | t' :: _ =>
      -- Co-decompose at the first unprocessed future time
      let branch1 : List (TSF Atom) := [⟨.neg, event, t'⟩, sf]
      let branch2 : List (TSF Atom) :=
        [⟨.neg, guard, t'⟩, ⟨.neg, φ, t'⟩, sf]
      (.branching [branch1, branch2], ord)
    | [] =>
      -- No unprocessed future times: create fresh one if depth limit allows
      if futureTimes.isEmpty && ord.timeCount > 0 && ord.timeCount < 4 then
        let t' := branchNextTime b
        let newOrd := ord.addFuture t t'
        let props := propagateToFuture b t t'
        let branch1 : List (TSF Atom) := [⟨.neg, event, t'⟩, sf] ++ props
        let branch2 : List (TSF Atom) :=
          [⟨.neg, guard, t'⟩, ⟨.neg, φ, t'⟩, sf] ++ props
        (.branching [branch1, branch2], newOrd)
      else
        (.notApplicable, ord)
  | none =>
  -- F(S(guard,event))@t → Reynolds co-decomposition at past times [branching]
  match asSnce? φ with
  | some (event, guard) =>
    let pastTimes := ord.pastOf t
    let unprocessed := pastTimes.filter fun t' =>
      let negEvent : TSF Atom := ⟨.neg, event, t'⟩
      let negGuard : TSF Atom := ⟨.neg, guard, t'⟩
      !b.any (· == negEvent) && !b.any (· == negGuard)
    match unprocessed with
    | t' :: _ =>
      let branch1 : List (TSF Atom) := [⟨.neg, event, t'⟩, sf]
      let branch2 : List (TSF Atom) :=
        [⟨.neg, guard, t'⟩, ⟨.neg, φ, t'⟩, sf]
      (.branching [branch1, branch2], ord)
    | [] =>
      if pastTimes.isEmpty && ord.timeCount > 0 && ord.timeCount < 4 then
        let t' := branchNextTime b
        let newOrd := ord.addPast t t'
        let props := propagateToPast b t t'
        let branch1 : List (TSF Atom) := [⟨.neg, event, t'⟩, sf] ++ props
        let branch2 : List (TSF Atom) :=
          [⟨.neg, guard, t'⟩, ⟨.neg, φ, t'⟩, sf] ++ props
        (.branching [branch1, branch2], newOrd)
      else
        (.notApplicable, ord)
  | none =>
  (.notApplicable, ord)

/-- Apply the first applicable temporal tableau rule to a signed formula.

Returns `(result, newTimeOrd)` where:
- `result` is the `RuleResult` (linear, branching, persistent, or notApplicable)
- `newTimeOrd` is the updated time ordering (modified only by existential rules)

See `temporalApplyPos` and `temporalApplyNeg` for the rule cases.
-/
def temporalApplyOne
    (sf : TSF Atom)
    (b : TBranch Atom)
    (ord : TimeOrdering) :
    RuleResult (Formula Atom) TimeIndex × TimeOrdering :=
  -- Step 1: Try propositional rules first
  let propResult := tryAllPropRules tempAndOf? tempOrOf? tempImpOf? tempNegOf? sf
  if propResult.isApplicable then
    (propResult, ord)
  else
    match sf.sign with
    | .pos => temporalApplyPos sf b ord
    | .neg => temporalApplyNeg sf b ord

end Cslib.Logic.Temporal.Tableau

end
