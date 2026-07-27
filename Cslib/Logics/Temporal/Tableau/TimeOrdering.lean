/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Attr.Core
public import Mathlib.Data.Int.Notation
import Mathlib.Tactic.ToDual

/-! # Time Ordering Constraint Store

This module defines the `TimeOrdering` structure: a strict-before constraint
store for the temporal tableau. Each constraint `(a, b)` asserts `a < b`.

The `TimeOrdering` is threaded through the tableau algorithm, growing
monotonically as new time points are introduced by existential rules
(someFuture/somePast and positive until/since branching).

## Design: Direct-Successor Semantics

This implementation uses **direct-successor semantics**: `futureOf t` returns
only the immediately recorded successors of `t` (times `t'` with a direct
constraint `t < t'`), not the transitive closure.

This matches the bimodal `TimeOrdering` design and is semantically sound
because the branch truth lemma ensures that the model built from the branch
satisfies the ordering constraints directly.

If Completeness requires transitive closure, the hook function
`ancestorTimes` provides a fuelled version. This decision is documented
here and revisited in the completeness module.

## References

* Bimodal `Decidability/SignedFormula.lean` lines 684–720 (algorithm template)
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

/-! ## TimeOrdering Structure -/

/-- A time ordering constraint store for the temporal tableau.

Each entry `(a, b)` represents the constraint `a < b` (time `a` is strictly
before time `b`). Constraints are added monotonically as the tableau creates
new time points via existential rules.

The `instant` field assigns an integer position to each time label, consistent
with the semantic direction of every constraint edge. This enables the corrected
ordering invariant `InstantStrict` (see below) without requiring a topological
sort or acyclicity proof. -/
structure TimeOrdering where
  /-- List of strict-order constraints as ordered pairs `(a, b)` meaning `a < b`. -/
  constraints : List (Nat × Nat)
  /-- Integer position of each time label, assigned at creation.
  The initial label has instant 0. Each `addFuture t tNew` sets
  `instant tNew = instant t + 1`; each `addPast t tNew` sets
  `instant tNew = instant t - 1`. -/
  instant : Nat → ℤ := fun _ => 0

namespace TimeOrdering

/-! ## Basic Operations -/

/-- The empty time ordering with no constraints.

All instants default to `0`; no constraints exist yet. -/
def empty : TimeOrdering := { constraints := [], instant := fun _ => 0 }

/-- Add a future constraint: `t < tNew` (time `tNew` is strictly after `t`).

Used by positive existential rules (someFuture+, untlPos) to record the
fresh future time point. Sets `instant tNew = instant t + 1`, ensuring
`instant t < instant tNew` for the new constraint edge. -/
def addFuture (ord : TimeOrdering) (t tNew : Nat) : TimeOrdering :=
  { constraints := (t, tNew) :: ord.constraints
    instant := fun a => if a = tNew then ord.instant t + 1 else ord.instant a }

/-- Add a past constraint: `tNew < t` (time `tNew` is strictly before `t`).

Used by negative existential rules (somePast+, sncePos) to record the
fresh past time point. Sets `instant tNew = instant t - 1`, ensuring
`instant tNew < instant t` for the new constraint edge. -/
def addPast (ord : TimeOrdering) (t tNew : Nat) : TimeOrdering :=
  { constraints := (tNew, t) :: ord.constraints
    instant := fun a => if a = tNew then ord.instant t - 1 else ord.instant a }

/-- All future time points of `t`: times `t'` with a direct constraint `t < t'`. -/
def futureOf (ord : TimeOrdering) (t : Nat) : List Nat :=
  ord.constraints.filterMap fun (a, b) => if a == t then some b else none

/-- All past time points of `t`: times `t'` with a direct constraint `t' < t`. -/
def pastOf (ord : TimeOrdering) (t : Nat) : List Nat :=
  ord.constraints.filterMap fun (a, b) => if b == t then some a else none

/-- All distinct time indices mentioned in any constraint. -/
def allTimes (ord : TimeOrdering) : List Nat :=
  ord.constraints.foldl (fun acc (a, b) =>
    let acc' := if acc.any (· == a) then acc else a :: acc
    if acc'.any (· == b) then acc' else b :: acc') []

/-- The total number of distinct time points recorded in the ordering.

**Historical note**: this was previously read directly by
`Rules.lean`'s `untlNeg`/`snceNeg` Reynolds co-decomposition arms as a raw numeric cap
(`0 < timeCount < 4`) bounding fresh future/past point creation. That cap has been replaced by
the `isTemporallyBlocked` dedup-based termination gate (`Branch.lean`), the same device already
used by the seriality arm (`temporalApplyPos`); `timeCount` itself is no longer consulted by any
rule-application site. Retained as a general-purpose branch-size query. -/
def timeCount (ord : TimeOrdering) : Nat :=
  ord.allTimes.length

/-- Fuelled transitive closure of future: times reachable from `t` in at most `fuel` steps.

This is the hook for Completeness if transitive closure is needed.
The default rules use `futureOf` (direct successors). -/
def ancestorTimes (ord : TimeOrdering) (t : Nat) : Nat → List Nat
  | 0 => []
  | fuel' + 1 =>
    let directs := futureOf ord t
    directs ++ (directs.flatMap (fun t' => ancestorTimes ord t' fuel'))

/-- Test whether the ordering contains the direct constraint `a < b`. -/
def hasConstraint (ord : TimeOrdering) (a b : Nat) : Bool :=
  ord.constraints.any fun (x, y) => x == a && y == b

/-! ## Membership Lemmas -/

/-- After `addFuture t tNew`, the constraint `t < tNew` is present. -/
lemma addFuture_hasConstraint (ord : TimeOrdering) (t tNew : Nat) :
    (ord.addFuture t tNew).hasConstraint t tNew = true := by
  simp [addFuture, hasConstraint]

/-- After `addPast t tNew`, the constraint `tNew < t` is present. -/
lemma addPast_hasConstraint (ord : TimeOrdering) (t tNew : Nat) :
    (ord.addPast t tNew).hasConstraint tNew t = true := by
  simp [addPast, hasConstraint]

/-- `tNew` is in `futureOf t` after `addFuture t tNew`. -/
lemma addFuture_mem_futureOf (ord : TimeOrdering) (t tNew : Nat) :
    tNew ∈ (ord.addFuture t tNew).futureOf t := by
  simp [addFuture, futureOf]

/-- `tNew` is in `pastOf t` after `addPast t tNew`. -/
lemma addPast_mem_pastOf (ord : TimeOrdering) (t tNew : Nat) :
    tNew ∈ (ord.addPast t tNew).pastOf t := by
  simp [addPast, pastOf]

/-- `futureOf` characterization: membership is equivalent to having the constraint. -/
lemma mem_futureOf_iff (ord : TimeOrdering) (t t' : Nat) :
    t' ∈ ord.futureOf t ↔ (t, t') ∈ ord.constraints := by
  simp only [futureOf, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨a, b, hmem, h⟩
    cases hae : (a == t)
    · simp [hae] at h
    · simp only [hae, ↓reduceIte, Option.some.injEq] at h
      have ha : a = t := by
        rw [show (a == t) = decide (a = t) from rfl] at hae
        exact of_decide_eq_true hae
      subst ha; subst h; exact hmem
  · intro hmem
    exact ⟨t, t', hmem, by simp⟩

/-- `pastOf` characterization: membership is equivalent to having the constraint. -/
lemma mem_pastOf_iff (ord : TimeOrdering) (t t' : Nat) :
    t' ∈ ord.pastOf t ↔ (t', t) ∈ ord.constraints := by
  simp only [pastOf, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨a, b, hmem, h⟩
    cases hbe : (b == t)
    · simp [hbe] at h
    · simp only [hbe, ↓reduceIte, Option.some.injEq] at h
      have hb : b = t := by
        rw [show (b == t) = decide (b = t) from rfl] at hbe
        exact of_decide_eq_true hbe
      subst hb; subst h; exact hmem
  · intro hmem
    exact ⟨t', t, hmem, by simp⟩

/-- Adding a future constraint is monotone for `futureOf`: existing future times are preserved. -/
lemma futureOf_addFuture_mono (ord : TimeOrdering) (t s tNew tNew' : Nat)
    (h : s ∈ ord.futureOf t) :
    s ∈ (ord.addFuture tNew tNew').futureOf t := by
  rw [mem_futureOf_iff] at *
  simp [addFuture, h]

/-- Adding a past constraint is monotone for `pastOf`: existing past times are preserved. -/
lemma pastOf_addPast_mono (ord : TimeOrdering) (t s tOld tNew : Nat)
    (h : s ∈ ord.pastOf t) :
    s ∈ (ord.addPast tOld tNew).pastOf t := by
  rw [mem_pastOf_iff] at *
  simp [addPast, h]

/-- Adding a future constraint does not remove existing past times. -/
lemma pastOf_addFuture_mono (ord : TimeOrdering) (t s tNew tNew' : Nat)
    (h : s ∈ ord.pastOf t) :
    s ∈ (ord.addFuture tNew tNew').pastOf t := by
  rw [mem_pastOf_iff] at *
  simp [addFuture, h]

/-- Adding a past constraint does not remove existing future times. -/
lemma futureOf_addPast_mono (ord : TimeOrdering) (t s tOld tNew : Nat)
    (h : s ∈ ord.futureOf t) :
    s ∈ (ord.addPast tOld tNew).futureOf t := by
  rw [mem_futureOf_iff] at *
  simp [addPast, h]

/-! ## Instant-Strict Invariant -/

/-- The edge-by-edge strict ordering invariant on integer instant assignments.

Each constraint `(a, b)` in `ord.constraints` satisfies `ord.instant a < ord.instant b`.
This is the corrected replacement for the false `ordConstraints_strict` lemma (which
required `a < b` as Nat labels but fails because `addPast t tNew` records `(tNew, t)`
with `tNew > t` numerically). Instead, the `instant` field carries a semantic integer
position that is always consistent with every constraint edge. -/
def InstantStrict (ord : TimeOrdering) : Prop :=
  ∀ a b, (a, b) ∈ ord.constraints → ord.instant a < ord.instant b

/-- `InstantStrict` holds vacuously for the empty ordering (no constraints). -/
lemma instantStrict_empty : InstantStrict TimeOrdering.empty := by
  intro a b h
  simp [TimeOrdering.empty] at h

/-- `addFuture` preserves `InstantStrict` provided `tNew` is fresh.

Freshness: `tNew` must not appear as an endpoint in any existing constraint,
and must differ from the source time `t`. In the temporal tableau these conditions
are guaranteed by `branchNextTime_gt` (every `sf.label < branchNextTime b` for
`sf ∈ b`, so the fresh time is distinct from all existing endpoints).

The new constraint `(t, tNew)` satisfies the invariant because
`instant tNew = instant t + 1 > instant t`. Old constraint endpoints are unchanged
(their instants are unaffected by the update at the fresh point `tNew`). -/
lemma instantStrict_addFuture (ord : TimeOrdering) (t tNew : Nat)
    (h : InstantStrict ord)
    (htne : t ≠ tNew)
    (hfresh : ∀ a b, (a, b) ∈ ord.constraints → a ≠ tNew ∧ b ≠ tNew) :
    InstantStrict (ord.addFuture t tNew) := by
  intro a b hab
  simp only [addFuture, List.mem_cons] at hab
  rcases hab with h0 | hmem
  · -- New edge: (a, b) = (t, tNew). Instant increases by 1.
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    simp only [addFuture, if_neg htne, ite_true]
    omega
  · -- Old edge: endpoints ≠ tNew, instants unchanged.
    obtain ⟨hane, hbne⟩ := hfresh a b hmem
    simp only [addFuture, if_neg hane, if_neg hbne]
    exact h a b hmem

/-- `addPast` preserves `InstantStrict` provided `tNew` is fresh.

Symmetric to `instantStrict_addFuture` in the past direction.
The new constraint is `(tNew, t)` with `instant tNew = instant t - 1 < instant t`. -/
lemma instantStrict_addPast (ord : TimeOrdering) (t tNew : Nat)
    (h : InstantStrict ord)
    (htne : t ≠ tNew)
    (hfresh : ∀ a b, (a, b) ∈ ord.constraints → a ≠ tNew ∧ b ≠ tNew) :
    InstantStrict (ord.addPast t tNew) := by
  intro a b hab
  simp only [addPast, List.mem_cons] at hab
  rcases hab with h0 | hmem
  · -- New edge: (a, b) = (tNew, t). Instant decreases by 1.
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    simp only [addPast, ite_true, if_neg htne]
    omega
  · -- Old edge: endpoints ≠ tNew, instants unchanged.
    obtain ⟨hane, hbne⟩ := hfresh a b hmem
    simp only [addPast, if_neg hane, if_neg hbne]
    exact h a b hmem

end TimeOrdering

/-! ## Fresh Time Generator -/

/-- Generate a fresh time index greater than all existing time labels in a list.

Given a list of `Nat` time labels, returns `max + 1`, which is guaranteed
to be strictly greater than any time in the list. -/
def freshTime (times : List Nat) : Nat :=
  times.foldl max 0 + 1

/-- `freshTime ts` is strictly greater than every element of `ts`. -/
lemma freshTime_gt (times : List Nat) (t : Nat) (h : t ∈ times) :
    t < freshTime times := by
  unfold freshTime
  suffices hle : t ≤ times.foldl max 0 by omega
  induction times with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldl]
    have hmon : ∀ (xs : List Nat) (init : Nat), init ≤ xs.foldl max init := by
      intro xs
      induction xs with
      | nil => intro _; simp
      | cons x rest ihrest =>
        intro init
        simp only [List.foldl]
        exact Nat.le_trans (Nat.le_max_left _ _) (ihrest _)
    have hmono : ∀ (xs : List Nat) (init init' : Nat),
        init ≤ init' → xs.foldl max init ≤ xs.foldl max init' := by
      intro xs
      induction xs with
      | nil => intro _ _ hle; simpa
      | cons x rest ihrest =>
        intro init init' hle
        simp only [List.foldl]
        exact ihrest _ _ (by omega)
    cases h with
    | inl heq =>
      subst heq
      -- Need: t ≤ List.foldl max (max 0 t) tl
      -- We have: t ≤ max 0 t (since max 0 t ≥ t)
      have hge : t ≤ max 0 t := by omega
      exact Nat.le_trans hge (hmon tl _)
    | inr hmem =>
      have hind := ih hmem
      -- Need: t ≤ List.foldl max (max 0 hd) tl
      -- We know: t ≤ List.foldl max 0 tl
      -- And: 0 ≤ max 0 hd
      exact Nat.le_trans hind (hmono tl 0 (max 0 hd) (Nat.zero_le _))

end Cslib.Logic.Temporal.Tableau

end
