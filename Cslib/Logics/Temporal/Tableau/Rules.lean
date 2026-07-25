/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Tableau.Defs
public import Cslib.Logics.Temporal.Tableau.TimeOrdering
public import Cslib.Foundations.Logic.Tableau.PropositionalRules

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

/-- Fuel bound for `TimeOrdering.ancestorTimes` lookups inside `allFuturePosAt`/`allPastPosAt`.
Generous relative to the tiny time counts the tableau ever reaches (bounded by `temporalFuel`);
not itself a termination-critical bound (see `Rules.lean`'s cap-removal history, Phase 7). -/
def ancestorLookupFuel : Nat := 50

/-- Collect T(Gφ) formulas from the branch relevant to propagating into the future of `t`:
either directly at time `t`, or at any time `t_anc` whose forward light-cone
(`ord.ancestorTimes`) transitively reaches `t` -- i.e. `t` is a (possibly indirect) future time
of `t_anc`, so `T(Gφ)@t_anc` constrains `t` too. This is the option-(iii)-a transitive-closure
fix (Finding 2b/2c): the old direct-time-only filter missed propagating `T(Gφ)@t_anc` across a
chain of `someFuture`-created intermediate times (e.g. `𝐆p → 𝐆𝐆p`). -/
def allFuturePosAt (b : TBranch Atom) (ord : TimeOrdering) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .pos &&
        (sf.label == t || (ord.ancestorTimes sf.label ancestorLookupFuel).contains t) then
      match asAllFuture? sf.formula with
      | some φ => some φ
      | none => none
    else none

/-- Collect T(Hφ) formulas from the branch relevant to propagating into the past of `t`:
either directly at time `t`, or at any time `t_anc` in `t`'s own forward light-cone
(`ord.ancestorTimes t`) -- i.e. `t_anc` is a (possibly indirect) future time of `t`, equivalently
`t` is a (possibly indirect) past time of `t_anc`, so `T(Hφ)@t_anc` (which constrains every time
strictly before `t_anc`) constrains `t` too. Note the arguments are reversed relative to
`allFuturePosAt`: `T(Gφ)@t_anc` propagates *forward* to times in `t_anc`'s future, so that
collector asks "is `t` in `t_anc`'s future light-cone"; `T(Hφ)@t_anc` propagates *backward* to
times in `t_anc`'s past, so this collector must ask "is `t_anc` in `t`'s future light-cone"
instead -- checking `t`'s future reachability, not `t_anc`'s. -/
def allPastPosAt (b : TBranch Atom) (ord : TimeOrdering) (t : TimeIndex) : List (Formula Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .pos &&
        (sf.label == t || (ord.ancestorTimes t ancestorLookupFuel).contains sf.label) then
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
def propagateToFuture (b : TBranch Atom) (ord : TimeOrdering) (t t' : TimeIndex) :
    List (TSF Atom) :=
  let gProps := (allFuturePosAt b ord t).filterMap fun φ =>
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
def propagateToPast (b : TBranch Atom) (ord : TimeOrdering) (t t' : TimeIndex) :
    List (TSF Atom) :=
  let hProps := (allPastPosAt b ord t).filterMap fun φ =>
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

/-- Apply positive temporal rules to a signed formula.

`blocked` is `isTemporallyBlocked b sf.label ord tracker`, precomputed by the caller
(`temporalStepBranch`, `Saturation.lean`): `Rules.lean` cannot depend on `Branch.lean` (which
depends on `Rules.lean`), so the blocking fact -- needed only by the seriality arm below -- is
passed in as a plain `Bool` rather than recomputed from an `EventualityTracker`. -/
def temporalApplyPos
    (sf : TSF Atom)
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (blocked : Bool) :
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
    if !newForms.isEmpty then (.persistent newForms, ord)
    else if (ord.futureOf t).isEmpty && !blocked then
      -- Seriality (Deliverable 2, item i): `t` has no future point at all yet, and no
      -- rule creates one on its own (`someFuturePos` only fires on a *positive* `Fφ`).
      -- Force one via addFuture so `NoMaxOrder`-sound rows like `𝐆p → 𝐅p` can close.
      -- Persistent (not linear): `sf` must stay live in case another rule later adds a
      -- *different* future point this arm also needs to propagate to.
      let t' := branchNextTime b
      let newOrd := ord.addFuture t t'
      let props := propagateToFuture b ord t t'
      (.persistent (⟨.pos, inner, t'⟩ :: props), newOrd)
    else (.notApplicable, ord)
  | none =>
  -- T(Hφ)@t → T(φ)@t' for each t' in pastOf(t) [persistent]
  match asAllPast? φ with
  | some inner =>
    let newForms : List (TSF Atom) :=
      (ord.pastOf t).filterMap fun t' =>
        let sf' : TSF Atom := ⟨.pos, inner, t'⟩
        if b.any (· == sf') then none else some sf'
    if !newForms.isEmpty then (.persistent newForms, ord)
    else if (ord.pastOf t).isEmpty && !blocked then
      -- Past-seriality, symmetric to the future case above.
      let t' := branchNextTime b
      let newOrd := ord.addPast t t'
      let props := propagateToPast b ord t t'
      (.persistent (⟨.pos, inner, t'⟩ :: props), newOrd)
    else (.notApplicable, ord)
  | none =>
  -- T(Fφ)@t → create fresh t', T(φ)@t', propagate universals [linear]
  match asSomeFuture? φ with
  | some inner =>
    let t' := branchNextTime b
    let newOrd := ord.addFuture t t'
    let witness : TSF Atom := ⟨.pos, inner, t'⟩
    let props := propagateToFuture b ord t t'
    (.linear (witness :: props), newOrd)
  | none =>
  -- T(Pφ)@t → create fresh t', T(φ)@t', propagate universals [linear]
  match asSomePast? φ with
  | some inner =>
    let t' := branchNextTime b
    let newOrd := ord.addPast t t'
    let witness : TSF Atom := ⟨.pos, inner, t'⟩
    let props := propagateToPast b ord t t'
    (.linear (witness :: props), newOrd)
  | none =>
  -- T(U(guard,event))@t → branch: T(event)@t' | T(guard)@t' + T(U)@t' [branching]
  match asUntl? φ with
  | some (event, guard) =>
    let t' := branchNextTime b
    let newOrd := ord.addFuture t t'
    let props := propagateToFuture b ord t t'
    let branch1 : List (TSF Atom) := [⟨.pos, event, t'⟩] ++ props
    let branch2 : List (TSF Atom) := [⟨.pos, guard, t'⟩, ⟨.pos, φ, t'⟩] ++ props
    (.branching [branch1, branch2], newOrd)
  | none =>
  -- T(S(guard,event))@t → branch: T(event)@t' | T(guard)@t' + T(S)@t' [branching]
  match asSnce? φ with
  | some (event, guard) =>
    let t' := branchNextTime b
    let newOrd := ord.addPast t t'
    let props := propagateToPast b ord t t'
    let branch1 : List (TSF Atom) := [⟨.pos, event, t'⟩] ++ props
    let branch2 : List (TSF Atom) := [⟨.pos, guard, t'⟩, ⟨.pos, φ, t'⟩] ++ props
    (.branching [branch1, branch2], newOrd)
  | none =>
  (.notApplicable, ord)

/-- Apply negative temporal rules: `allFuture`/`allPast` duality (Deliverable 2, item ii) plus
Reynolds co-decomposition for Until/Since.

`blocked` is `isTemporallyBlocked b sf.label ord tracker`, precomputed by the caller -- see
`temporalApplyPos`'s docstring for why it is threaded in as a `Bool`. Used by the `untlNeg`/
`snceNeg` fresh-time-creation arms (Deliverable 3/4, Phase 7) as the dedup-based termination
gate, replacing the old raw `timeCount < 4` numeric cap. -/
def temporalApplyNeg
    (sf : TSF Atom)
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (blocked : Bool) :
    RuleResult (Formula Atom) TimeIndex × TimeOrdering :=
  let t := sf.label
  let φ := sf.formula
  -- F(Gψ)@t → T(F¬ψ)@t [linear]: ¬𝐆ψ ≡ 𝐅¬ψ (the rule table's "allFutureNeg" row,
  -- `Rules.lean`'s module doc), previously missing entirely -- `asAllFuture?`/`asAllPast?`
  -- don't overlap `asUntl?`/`asSnce?`, so a bare `F(Gψ)@t`/`F(Hψ)@t` fell straight through to
  -- `.notApplicable` and was permanently inert. No new time point; the witness time for the
  -- resulting `T(F¬ψ)@t` is created later by the existing `asSomeFuture?` positive rule.
  match asAllFuture? φ with
  | some ψ => (.linear [⟨.pos, Formula.someFuture (Formula.neg ψ), t⟩], ord)
  | none =>
  -- F(Hψ)@t → T(P¬ψ)@t [linear]: ¬𝐇ψ ≡ 𝐏¬ψ ("allPastNeg"), symmetric to the above.
  match asAllPast? φ with
  | some ψ => (.linear [⟨.pos, Formula.somePast (Formula.neg ψ), t⟩], ord)
  | none =>
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
      -- No unprocessed future times: create fresh one unless `t` is already dedup-blocked
      -- (Deliverable 3/4, Phase 7): the old raw `0 < timeCount < 4` cap is replaced by the same
      -- `isTemporallyBlocked` subset-blocking device the seriality arm already uses
      -- (`temporalApplyPos`), now wired here as a fresh-time *suppressor* per the research
      -- report's Finding 4 (dedup device existed but was previously consulted only at closure
      -- time, never here).
      if futureTimes.isEmpty && !blocked then
        let t' := branchNextTime b
        let newOrd := ord.addFuture t t'
        let props := propagateToFuture b ord t t'
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
      -- Symmetric to the `untlNeg` case above (Deliverable 3/4, Phase 7).
      if pastTimes.isEmpty && !blocked then
        let t' := branchNextTime b
        let newOrd := ord.addPast t t'
        let props := propagateToPast b ord t t'
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

`blocked` is `isTemporallyBlocked b sf.label ord tracker`; see `temporalApplyPos`'s docstring
for why it is threaded in as a `Bool` rather than an `EventualityTracker`. Only the positive
seriality arm reads it.

See `temporalApplyPos` and `temporalApplyNeg` for the rule cases.
-/
def temporalApplyOne
    (sf : TSF Atom)
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (blocked : Bool) :
    RuleResult (Formula Atom) TimeIndex × TimeOrdering :=
  -- Step 1: Try propositional rules first
  let propResult := tryAllPropRules tempAndOf? tempOrOf? tempImpOf? tempNegOf? sf
  if propResult.isApplicable then
    (propResult, ord)
  else
    match sf.sign with
    | .pos => temporalApplyPos sf b ord blocked
    | .neg => temporalApplyNeg sf b ord blocked

/-! ## OrdFreshWRT: Constraint-Endpoint Freshness Invariant

This section defines and proves properties of the `OrdFreshWRT` invariant, which is used to
thread `InstantStrict` through the saturation loop.

The key idea: every constraint endpoint in `ord` is strictly below `branchNextTime b`, ensuring
that the next fresh time `branchNextTime b` introduced by a rule application is truly fresh with
respect to all existing constraints. This makes the freshness side-conditions in
`instantStrict_addFuture` and `instantStrict_addPast` discharge automatically. -/

/-- Every constraint endpoint in `ord` is strictly less than `branchNextTime b`.
This ensures `branchNextTime b` is truly fresh when the next temporal rule fires at branch `b`.

Combined with `InstantStrict ord`, this is the loop invariant for the completeness threading
argument: if both hold for each (branch, ordering) pair in the worklist, then after one
expansion step, both hold for the new (branch, ordering) pairs. -/
def OrdFreshWRT (b : TBranch Atom) (ord : TimeOrdering) : Prop :=
  ∀ a c, (a, c) ∈ ord.constraints → a < branchNextTime b ∧ c < branchNextTime b

omit [DecidableEq Atom] [Hashable Atom] in
/-- `OrdFreshWRT` holds vacuously for the empty ordering: no constraints exist. -/
lemma ordFreshWRT_empty (b : TBranch Atom) : OrdFreshWRT b TimeOrdering.empty := by
  intro a c h
  simp [TimeOrdering.empty] at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- From `OrdFreshWRT`, each constraint endpoint differs from `branchNextTime b`. -/
lemma ordFreshWRT_ne (b : TBranch Atom) (ord : TimeOrdering) (h : OrdFreshWRT b ord) :
    ∀ a c, (a, c) ∈ ord.constraints → a ≠ branchNextTime b ∧ c ≠ branchNextTime b := by
  intro a c hmem
  obtain ⟨ha, hc⟩ := h a c hmem
  exact ⟨Nat.ne_of_lt ha, Nat.ne_of_lt hc⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `branchNextTime` is monotone: prepending formulas cannot decrease the next fresh time. -/
lemma branchNextTime_le_append (nf b : TBranch Atom) :
    branchNextTime b ≤ branchNextTime (nf ++ b) := by
  simp only [branchNextTime, branchMaxTime, Nat.add_le_add_iff_right]
  -- Need: foldl max 0 b ≤ foldl max 0 (nf ++ b)
  -- foldl max 0 (nf ++ b) = foldl max (foldl max 0 nf) b ≥ foldl max 0 b
  rw [List.foldl_append]
  have h0 : 0 ≤ nf.foldl (fun mx sf => max mx sf.label) 0 := Nat.zero_le _
  have hmono : ∀ (ys : List (TSF Atom)) (init init' : Nat),
      init ≤ init' →
      ys.foldl (fun mx sf' => max mx sf'.label) init ≤
      ys.foldl (fun mx sf' => max mx sf'.label) init' := by
    intro ys
    induction ys with
    | nil => intro _ _ hle; simpa
    | cons y rest ih =>
      intro init init' hle
      simp only [List.foldl]
      exact ih _ _ (by omega)
  exact hmono b 0 _ h0

omit [DecidableEq Atom] [Hashable Atom] in
/-- `OrdFreshWRT` is preserved when the branch grows (orderings unchanged). -/
lemma ordFreshWRT_append_left (nf b : TBranch Atom) (ord : TimeOrdering)
    (h : OrdFreshWRT b ord) : OrdFreshWRT (nf ++ b) ord := by
  intro a c hmem
  obtain ⟨ha, hc⟩ := h a c hmem
  exact ⟨Nat.lt_of_lt_of_le ha (branchNextTime_le_append nf b),
         Nat.lt_of_lt_of_le hc (branchNextTime_le_append nf b)⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `OrdFreshWRT` is preserved by `addFuture t t'` when `t = sf.label ∈ b`,
`t' = branchNextTime b`, and some formula in `nf` has label `t'`.

This is the core invariant-preservation lemma for future-creating rules
(someFuturePos, untlPos). -/
lemma ordFreshWRT_addFuture_of_witness (b : TBranch Atom) (ord : TimeOrdering) (t : Nat)
    (sf : TSF Atom) (hmem_sf : sf ∈ b) (ht : sf.label = t) (h : OrdFreshWRT b ord)
    (nf : List (TSF Atom)) (ht'_in_nf : ∃ sf' ∈ nf, sf'.label = branchNextTime b) :
    OrdFreshWRT (nf ++ b) (ord.addFuture t (branchNextTime b)) := by
  intro a c hmem
  simp only [TimeOrdering.addFuture, List.mem_cons] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | hmem_old
  · -- New constraint: (t, branchNextTime b)
    constructor
    · -- t < branchNextTime (nf ++ b)
      exact ht ▸ branchNextTime_gt (nf ++ b) sf (List.mem_append_right _ hmem_sf)
    · -- branchNextTime b < branchNextTime (nf ++ b)
      obtain ⟨sf', hsf'_mem, hsf'_lab⟩ := ht'_in_nf
      rw [← hsf'_lab]
      exact branchNextTime_gt (nf ++ b) sf' (List.mem_append_left _ hsf'_mem)
  · -- Old constraint: both endpoints < branchNextTime b < branchNextTime (nf ++ b)
    obtain ⟨ha, hc⟩ := h a c hmem_old
    obtain ⟨sf', hsf'_mem, hsf'_lab⟩ := ht'_in_nf
    have ht'_lt : branchNextTime b < branchNextTime (nf ++ b) := by
      rw [← hsf'_lab]
      exact branchNextTime_gt (nf ++ b) sf' (List.mem_append_left _ hsf'_mem)
    exact ⟨Nat.lt_trans ha ht'_lt, Nat.lt_trans hc ht'_lt⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `OrdFreshWRT` is preserved by `addPast t t'` when `t = sf.label ∈ b`,
`t' = branchNextTime b`, and some formula in `nf` has label `t'`.

Symmetric to `ordFreshWRT_addFuture_of_witness`. -/
lemma ordFreshWRT_addPast_of_witness (b : TBranch Atom) (ord : TimeOrdering) (t : Nat)
    (sf : TSF Atom) (hmem_sf : sf ∈ b) (ht : sf.label = t) (h : OrdFreshWRT b ord)
    (nf : List (TSF Atom)) (ht'_in_nf : ∃ sf' ∈ nf, sf'.label = branchNextTime b) :
    OrdFreshWRT (nf ++ b) (ord.addPast t (branchNextTime b)) := by
  intro a c hmem
  simp only [TimeOrdering.addPast, List.mem_cons] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | hmem_old
  · -- New constraint: (branchNextTime b, t)
    constructor
    · -- branchNextTime b < branchNextTime (nf ++ b)
      obtain ⟨sf', hsf'_mem, hsf'_lab⟩ := ht'_in_nf
      rw [← hsf'_lab]
      exact branchNextTime_gt (nf ++ b) sf' (List.mem_append_left _ hsf'_mem)
    · -- t < branchNextTime (nf ++ b)
      exact ht ▸ branchNextTime_gt (nf ++ b) sf (List.mem_append_right _ hmem_sf)
  · -- Old constraint: both endpoints < branchNextTime b < branchNextTime (nf ++ b)
    obtain ⟨ha, hc⟩ := h a c hmem_old
    obtain ⟨sf', hsf'_mem, hsf'_lab⟩ := ht'_in_nf
    have ht'_lt : branchNextTime b < branchNextTime (nf ++ b) := by
      rw [← hsf'_lab]
      exact branchNextTime_gt (nf ++ b) sf' (List.mem_append_left _ hsf'_mem)
    exact ⟨Nat.lt_trans ha ht'_lt, Nat.lt_trans hc ht'_lt⟩

/-! ## temporalApplyPos/Neg Preservation Lemmas -/

omit [Hashable Atom] in
/-- `temporalApplyPos` preserves `InstantStrict` and `OrdFreshWRT`.

For every case of `temporalApplyPos sf b ord`:
- The new ordering is `InstantStrict`
- Every output branch `bi = nf ++ b` satisfies `OrdFreshWRT bi newOrd` -/
lemma temporalApplyPos_preserves (sf : TSF Atom) (b : TBranch Atom) (ord : TimeOrdering)
    (blocked : Bool)
    (hIS : TimeOrdering.InstantStrict ord) (hOFW : OrdFreshWRT b ord) (hmem : sf ∈ b)
    (result : RuleResult (Formula Atom) TimeIndex) (newOrd : TimeOrdering)
    (h : temporalApplyPos sf b ord blocked = (result, newOrd)) :
    TimeOrdering.InstantStrict newOrd ∧
    ∀ nf ∈ (match result with
      | .linear newForms => [newForms]
      | .branching brs => brs
      | .persistent newForms => [newForms]
      | .notApplicable => []),
      OrdFreshWRT (nf ++ b) newOrd := by
  simp only [temporalApplyPos] at h
  -- `asAllFuture?`/`asAllPast?` are now primitive-constructor matches (task #180); the previous
  -- `rcases X with _ | y` idiom does not propagate into `h` (it only generalizes the goal
  -- target, not the hypothesis), so every subsequent `simp only at h` silently made no
  -- progress. `split at h` correctly case-splits on the `match`/`if` inside `h` itself;
  -- chained via `<;>` it fully unfolds the 11-way case tree (mirroring the source's bullet
  -- structure, now including the two new seriality sub-cases) regardless of branch depth.
  split at h <;> try split at h <;> try split at h <;> try split at h <;> try split at h <;>
    try split at h <;> try split at h
  -- 1. allFuture, fresh future obligations already pending: persistent, ord unchanged
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by
      simp only [List.mem_singleton] at hnf; subst hnf
      exact ordFreshWRT_append_left _ b ord hOFW⟩
  -- 2. allFuture, no obligations pending, seriality fires: persistent, addFuture
  · rename_i _x inner _heq _hne1 _hne2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addFuture ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · intro a c hac; exact ordFreshWRT_ne b ord hOFW a c hac
    · simp only [List.mem_singleton] at hnf; subst hnf
      exact ordFreshWRT_addFuture_of_witness b ord sf.label sf hmem rfl hOFW _
        ⟨⟨.pos, inner, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 3. allFuture, no obligations pending, seriality blocked: notApplicable
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by simp at hnf⟩
  -- 4. allPast, fresh past obligations already pending: persistent, ord unchanged
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by
      simp only [List.mem_singleton] at hnf; subst hnf
      exact ordFreshWRT_append_left _ b ord hOFW⟩
  -- 5. allPast, no obligations pending, past-seriality fires: persistent, addPast
  · rename_i _x1 _heq1 _x2 inner _heq2 _hne1 _hne2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addPast ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · intro a c hac; exact ordFreshWRT_ne b ord hOFW a c hac
    · simp only [List.mem_singleton] at hnf; subst hnf
      exact ordFreshWRT_addPast_of_witness b ord sf.label sf hmem rfl hOFW _
        ⟨⟨.pos, inner, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 6. allPast, no obligations pending, past-seriality blocked: notApplicable
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by simp at hnf⟩
  -- 7. someFuturePos: addFuture, linear result
  · rename_i inner heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addFuture ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · -- t ≠ t' (sf.label ≠ branchNextTime b): sf ∈ b so sf.label < branchNextTime b
      exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · -- hfresh: all constraint endpoints ≠ branchNextTime b
      intro a c hac
      exact ordFreshWRT_ne b ord hOFW a c hac
    · -- OrdFreshWRT for the output branch
      simp only [List.mem_singleton] at hnf
      subst hnf
      exact ordFreshWRT_addFuture_of_witness b ord sf.label sf hmem rfl hOFW _
        ⟨⟨.pos, inner, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 8. somePastPos: addPast, linear result
  · rename_i inner heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addPast ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · intro a c hac; exact ordFreshWRT_ne b ord hOFW a c hac
    · simp only [List.mem_singleton] at hnf; subst hnf
      exact ordFreshWRT_addPast_of_witness b ord sf.label sf hmem rfl hOFW _
        ⟨⟨.pos, inner, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 9. untlPos: addFuture, branching result
  · rename_i event guard heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addFuture ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · intro a c hac; exact ordFreshWRT_ne b ord hOFW a c hac
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnf
      rcases hnf with rfl | rfl
      · -- branch1 = [⟨.pos, event, t'⟩] ++ props
        exact ordFreshWRT_addFuture_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.pos, event, branchNextTime b⟩, List.mem_cons_self, rfl⟩
      · -- branch2 = [⟨.pos, guard, t'⟩, ...] ++ props
        exact ordFreshWRT_addFuture_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.pos, guard, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 10. sncePos: addPast, branching result
  · rename_i event guard heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addPast ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · intro a c hac; exact ordFreshWRT_ne b ord hOFW a c hac
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnf
      rcases hnf with rfl | rfl
      · exact ordFreshWRT_addPast_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.pos, event, branchNextTime b⟩, List.mem_cons_self, rfl⟩
      · exact ordFreshWRT_addPast_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.pos, guard, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 11. notApplicable: ord unchanged, no output branches
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by simp at hnf⟩

omit [Hashable Atom] in
/-- `temporalApplyNeg` preserves `InstantStrict` and `OrdFreshWRT`.

For every case of `temporalApplyNeg sf b ord blocked`:
- The new ordering is `InstantStrict`
- Every output branch satisfies `OrdFreshWRT` -/
lemma temporalApplyNeg_preserves (sf : TSF Atom) (b : TBranch Atom) (ord : TimeOrdering)
    (blocked : Bool)
    (hIS : TimeOrdering.InstantStrict ord) (hOFW : OrdFreshWRT b ord) (hmem : sf ∈ b)
    (result : RuleResult (Formula Atom) TimeIndex) (newOrd : TimeOrdering)
    (h : temporalApplyNeg sf b ord blocked = (result, newOrd)) :
    TimeOrdering.InstantStrict newOrd ∧
    ∀ nf ∈ (match result with
      | .linear newForms => [newForms]
      | .branching brs => brs
      | .persistent newForms => [newForms]
      | .notApplicable => []),
      OrdFreshWRT (nf ++ b) newOrd := by
  simp only [temporalApplyNeg] at h
  -- See `temporalApplyPos_preserves` for why `split at h` replaces the broken
  -- `rcases X with _ | y` idiom (which does not propagate its case split into `h`).
  split at h <;> try split at h <;> try split at h <;> try split at h <;> try split at h <;>
    try split at h
  -- 1. allFutureNeg duality: F(Gψ)@t → T(F¬ψ)@t, linear, ord unchanged
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨hIS, fun nf hnf => ?_⟩
    simp only [List.mem_singleton] at hnf; subst hnf
    exact ordFreshWRT_append_left _ b ord hOFW
  -- 2. allPastNeg duality: F(Hψ)@t → T(P¬ψ)@t, linear, ord unchanged
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨hIS, fun nf hnf => ?_⟩
    simp only [List.mem_singleton] at hnf; subst hnf
    exact ordFreshWRT_append_left _ b ord hOFW
  -- 3. untlNeg, co-decomposition at an already-unprocessed future time: branching, ord unchanged
  · rename_i event guard _heqUntl _unprocessed _t' _tail _heqFilter
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨hIS, fun nf hnf => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnf
    rcases hnf with rfl | rfl
    all_goals exact ordFreshWRT_append_left _ b ord hOFW
  -- 4. untlNeg, no unprocessed future time, fresh time created: branching, addFuture
  · rename_i event guard _heqUntl _unprocessed _heqFilter _hcond
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addFuture ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · intro a c hac; exact ordFreshWRT_ne b ord hOFW a c hac
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnf
      rcases hnf with rfl | rfl
      · -- branch1: [⟨.neg, event, t'⟩, sf] ++ props
        exact ordFreshWRT_addFuture_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.neg, event, branchNextTime b⟩, List.mem_cons_self, rfl⟩
      · -- branch2: [⟨.neg, guard, t'⟩, ...] ++ props
        exact ordFreshWRT_addFuture_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.neg, guard, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 5. untlNeg, no unprocessed future time, depth limit reached: notApplicable
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by simp at hnf⟩
  -- 6. snceNeg, co-decomposition at an already-unprocessed past time: branching, ord unchanged
  · rename_i event guard _heqSnce _unprocessed _t' _tail _heqFilter
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨hIS, fun nf hnf => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnf
    rcases hnf with rfl | rfl
    all_goals exact ordFreshWRT_append_left _ b ord hOFW
  -- 7. snceNeg, no unprocessed past time, fresh time created: branching, addPast
  · rename_i event guard _heqSnce _unprocessed _heqFilter _hcond
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨TimeOrdering.instantStrict_addPast ord sf.label (branchNextTime b) hIS ?_ ?_,
            fun nf hnf => ?_⟩
    · exact Nat.ne_of_lt (branchNextTime_gt b sf hmem)
    · intro a c hac; exact ordFreshWRT_ne b ord hOFW a c hac
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnf
      rcases hnf with rfl | rfl
      · -- branch1: [⟨.neg, event, t'⟩, sf] ++ props
        exact ordFreshWRT_addPast_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.neg, event, branchNextTime b⟩, List.mem_cons_self, rfl⟩
      · -- branch2: [⟨.neg, guard, t'⟩, ...] ++ props
        exact ordFreshWRT_addPast_of_witness b ord sf.label sf hmem rfl hOFW _
          ⟨⟨.neg, guard, branchNextTime b⟩, List.mem_cons_self, rfl⟩
  -- 8. snceNeg, no unprocessed past time, depth limit reached: notApplicable
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by simp at hnf⟩
  -- 9. neither allFutureNeg/allPastNeg/untl/snce: notApplicable
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hIS, fun nf hnf => by simp at hnf⟩

omit [Hashable Atom] in
/-- `temporalApplyOne` preserves `InstantStrict` and `OrdFreshWRT`.

Combines `temporalApplyPos_preserves` and `temporalApplyNeg_preserves` for propositional and
temporal rules. -/
lemma temporalApplyOne_preserves (sf : TSF Atom) (b : TBranch Atom) (ord : TimeOrdering)
    (blocked : Bool)
    (hIS : TimeOrdering.InstantStrict ord) (hOFW : OrdFreshWRT b ord) (hmem : sf ∈ b)
    (result : RuleResult (Formula Atom) TimeIndex) (newOrd : TimeOrdering)
    (h : temporalApplyOne sf b ord blocked = (result, newOrd)) :
    TimeOrdering.InstantStrict newOrd ∧
    ∀ nf ∈ (match result with
      | .linear newForms => [newForms]
      | .branching brs => brs
      | .persistent newForms => [newForms]
      | .notApplicable => []),
      OrdFreshWRT (nf ++ b) newOrd := by
  simp only [temporalApplyOne] at h
  -- Try propositional rules first
  set propResult := tryAllPropRules tempAndOf? tempOrOf? tempImpOf? tempNegOf? sf
  by_cases hprop : propResult.isApplicable = true
  · -- Propositional rule fires: ord unchanged
    simp only [if_pos hprop] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨hIS, fun nf hnf => ?_⟩
    -- For the propositional case, all output branches are subsets of b's branch (ord unchanged).
    -- OrdFreshWRT (nf ++ b) ord holds for any nf by the append monotonicity lemma.
    exact ordFreshWRT_append_left nf b ord hOFW
  · -- No propositional rule fires: dispatch to pos/neg
    rw [if_neg hprop] at h
    -- `rcases sf.sign with _ | _` does not propagate its case split into `h` (see
    -- `temporalApplyPos_preserves`); `split at h` correctly reduces `h`'s `match sf.sign with ...`.
    split at h
    · -- Positive: temporalApplyPos
      exact temporalApplyPos_preserves sf b ord blocked hIS hOFW hmem result newOrd h
    · -- Negative: temporalApplyNeg
      exact temporalApplyNeg_preserves sf b ord blocked hIS hOFW hmem result newOrd h

end Cslib.Logic.Temporal.Tableau

end
