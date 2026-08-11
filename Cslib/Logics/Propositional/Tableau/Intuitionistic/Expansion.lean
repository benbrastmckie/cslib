/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Rules
public import Cslib.Foundations.Logic.Tableau.ClosureCondition

/-! # Intuitionistic Propositional Tableau Expansion

This module implements the expansion loop for the intuitionistic propositional tableau.
The intuitionistic tableau uses `L = Nat` (Kripke world indices) and the
`IntuitionisticClosure` instance (closes on T(⊥) at any label, or on complementary
T(φ)/F(φ) pairs at the same label).

## Main Definitions

- `IntTableauResult`: Result of the intuitionistic expansion (closed or open).
- `isIntuitionisticallyClosed`/`isMinimallyClosed`: The two closure predicates.
- `applyPersistenceFixpoint`, `intStepBranch`, `intFImpReuseWitnessAnc?`: The
  single-step expansion machinery (persistence, rule application, ancestor-directed
  loop-check) consumed by the expansion loop.

The expansion loop itself (`intExpandBranches`, **parameterized by `closurePred`**,
with the per-branch fuel lists) and the entry points `intuitionisticTableau`/
`minimalTableau` live in `Intuitionistic/Scheme.lean`: their per-branch fuel budget
`intFuelExt` is sized by the blocking-derived world bound `WBound`, which is developed
there.

## Tableau Unification

The two divergence points between intuitionistic and minimal tableau are:
1. **Closure predicate**: `isIntuitionisticallyClosed` vs `isMinimallyClosed`.
2. **Bottom forcing in countermodel**: `fun _ _ => False` vs `minBranchBotForces b`.

Point 1 is handled here by the `closurePred` parameter.
Point 2 is handled in `Intuitionistic/Scheme.lean` via `IntMinScheme`.

There is no duplicate expansion function: both tableau variants are instances of
the single `intExpandBranches`/`propExpandBranches` loop (`Intuitionistic/Scheme.lean`).

## Design

The expansion loop processes one branch at a time. Within each branch:
1. First apply the persistent T(φ → ψ) rule for all T-implication formulas on the branch.
2. Then pick the first unexpanded formula and apply the appropriate rule.
3. For world-creating rules, add the new world's formulas, update the world counter,
   and extend the edge list with the new parent-child edge.
4. For branching rules, split the current branch into sub-branches (each inheriting
   the current edge list).

The fuel bound uses `2^(2 * complexity φ)` to account for the exponential blowup
possible in intuitionistic tableaux (due to world creation and persistence propagation).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 2.2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Intuitionistic Tableau Result -/

/-- The result of an intuitionistic (or minimal) propositional tableau computation.

- `closed`: Every branch is closed (the formula is valid).
- `openBranch b`: An open saturated branch `b` exists, providing a Kripke countermodel. -/
inductive IntTableauResult (Atom : Type*) : Type _ where
  /-- All branches close: the formula is valid in the logic. -/
  | closed : IntTableauResult Atom
  /-- An open saturated branch exists: the formula is not valid. -/
  | openBranch : IBranch Atom → IntTableauResult Atom

/-! ## Closure Check -/

/-- Check whether an intuitionistic branch is closed.

A branch is intuitionistically closed when either:
1. T(⊥) appears at any label (via the `IntuitionisticClosure` instance), or
2. T(φ) and F(φ) appear at the same label for some formula φ (complementary pair).

Note: complementary pairs DO close an intuitionistic branch. Although the intuitionistic
semantics does not close on complementary pairs for non-atomic formulas at the semantic
level, the tableau calculus uses both closure conditions for completeness. -/
def isIntuitionisticallyClosed (b : IBranch Atom) : Bool :=
  @ClosureCondition.isClosed _ _ IntuitionisticClosure.instClosureConditionOfBEqOfHasBot b ||
  Branch.hasContradiction b

/-- Check whether a minimal branch is closed.

A branch is minimally closed when it contains T(φ) and F(φ) at the same world for
ANY formula φ. This uses `Branch.hasContradiction`, which checks all complementary pairs
(not just atomic formulas). This is equivalent to classical closure minus the T(⊥) rule:
minimal logic does not close on T(⊥) alone, but it does close on any T(φ)/F(φ) pair.

NOTE: An atom-only closure criterion was previously used, but this is insufficient for
correctness -- for example, `⊥ → ⊥` is minimally valid but the atom-only criterion fails
to close the branch containing T(⊥)/F(⊥) at the created world. -/
def isMinimallyClosed (b : IBranch Atom) : Bool :=
  Branch.hasContradiction b

/-! ## Persistence Application -/

/-- Apply all pending T(φ → ψ) rules to the current branch state.

For each T(φ → ψ) formula at world w on the branch, and for each accessible world
w' (reachable via the edge list from w) with T(φ) at w', if T(ψ) is not yet at w',
add T(ψ) at w'.

**Also copies every POSITIVE-signed formula `T(χ)@w` to every world `w'` accessible from `w`
that does not already carry its own copy** (a generalized reinstatement of the "Deliverable 6"
channel described in the channel-history note below). This subsumes the original self-copy
channel (which copied only `T(φ → ψ)` itself) as the special case `χ = φ → ψ`: every
accessible `w'` eventually carries its own copy of *any* positive formula present at its
source, which `intStepBranch`/`intApplyRuleFull` can then resolve independently (and which
`expanded` then tracks per-`(formula, world)` pair, since each copy is a distinct `ISF`). This
mirrors `intTImpRule`'s own accessibility scan, generalized from `imp`-shaped formulas to all
positive formulas.

**Channel history.** A prior revision of this def copied only `T(φ → ψ)` itself to accessible
worlds lacking their own copy ("Deliverable 6"). A divergence probe
(`specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md`,
Table 3, variant V3) measured that this narrower self-copy is not the mechanism that bounds
world creation under ancestor-directed blocking (`intFImpReuseWitnessAnc?`), and it was removed
(commit `a70187dd`) as orthogonal hygiene. A later re-probe
(`specs/430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/`
`01_gate-a-variant-selection.md`) measured BOTH the narrow self-copy (**V1**, the literal
`a70187dd^` reinstatement) and this
generalized every-positive-formula channel (**V4**) against the same complexity-9 divergence
witness and the full 20-row propositional conformance corpus: both terminate, both saturate at
the identical fixed point as the copy-free tree (`len=219, maxLabel=21`, stable
`fuel ∈ {120,160,200}`), and both pass every conformance row. V4 was selected because it makes
positive-formula persistence hold at *every* formula shape via one channel, closing the atom
and T-implication persistence gaps uniformly rather than only at `imp`-shaped formulas.
`sat_timp` as an `IBranchSaturation` *field* does not depend on this channel: it is stated
reflexively at a copy's own label and is discharged by `intApplyRuleFull`'s `.pos, .imp`
branching arm via `expanded`-set guarding, independently of whether any copy exists on the
branch (`Soundness.lean`'s `applyAllTImpRules_sat`, the `le_rfl` reflexive case).

The overall expansion loop (`intExpandBranches`, `Intuitionistic/Scheme.lean`) terminates
unconditionally by its per-branch fuel discipline, but SATURATION is not established: the
`intUniverse φ0` bound this docstring previously appealed to is itself refuted, not merely
unproven. See the *Divergence witness* note at the end of this file for the counterexample
and its consequences.

Returns the updated branch with all pending persistence applications. -/
def applyAllTImpRules (b : IBranch Atom) (edges : IEdges) : IBranch Atom :=
  let newForms :=
    b.filterMap fun sf =>
      match sf.sign, sf.formula with
      | .pos, .imp φ ψ =>
        -- Get all accessible worlds w' with T(φ) at w' but not yet T(ψ)
        let toAdd := intTImpRule φ ψ sf.label edges b
        if toAdd.isEmpty then none else some toAdd
      | _, _ => none
  -- Generalized copy channel: every POSITIVE formula on the branch, copied to every
  -- accessible world lacking its own copy (not just `T(φ → ψ)`-shaped formulas).
  let genCopies :=
    b.filterMap fun sf =>
      match sf.sign with
      | .pos =>
        let accessibleWorlds :=
          (b.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
        let copies := accessibleWorlds.filterMap fun w' =>
          if b.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w') then
            none
          else
            some (⟨.pos, sf.formula, w'⟩ : ISF Atom)
        if copies.isEmpty then none else some copies
      | .neg => none
  b ++ newForms.flatten ++ genCopies.flatten

/-- Repeatedly apply persistence until fixpoint.

Since each application can create new T-formulas that may trigger more applications,
we iterate until no new formulas are added. Uses fuel to guarantee termination. -/
def applyPersistenceFixpoint (b : IBranch Atom) (edges : IEdges) (fuel : Nat) : IBranch Atom :=
  match fuel with
  | 0 => b
  | fuel' + 1 =>
    let b' := applyAllTImpRules b edges
    if b'.length == b.length then b  -- No new formulas added; fixpoint reached
    else applyPersistenceFixpoint b' edges fuel'

/-! ## One-Step Expansion -/

/-- One step of the intuitionistic tableau expansion on a single branch.

Finds the first formula on `b` that:
1. Is not in the `expanded` set, and
2. Has an applicable intuitionistic rule.

Returns `none` when the branch is saturated. -/
def intStepBranch (b : IBranch Atom) (expanded : List (ISF Atom)) (nextWorld : Nat) :
    Option (IntRuleResult Atom × List (ISF Atom)) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      match intApplyRuleFull sf nextWorld b with
      | .notApplicable => none
      | result => some (result, expanded ++ [sf])

omit [Hashable Atom] in
/-- If `intStepBranch` returns `some (r, e')`, then `r ≠ .notApplicable`.
The definition maps every `.notApplicable` result of `intApplyRuleFull` to `none`,
so `.notApplicable` never appears as the first component of a `some` return value. -/
lemma intStepBranch_result_ne_notApplicable
    {b : IBranch Atom} {expanded : List (ISF Atom)} {nextWorld : Nat}
    {r : IntRuleResult Atom} {exp' : List (ISF Atom)}
    (h : intStepBranch b expanded nextWorld = some (r, exp')) : r ≠ .notApplicable := by
  simp only [intStepBranch] at h
  obtain ⟨sf, _, hsf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hexp : (expanded.any (· == sf)) = true
  · simp [hexp] at hsf
  · simp only [Bool.not_eq_true] at hexp
    simp only [hexp, Bool.false_eq_true, ↓reduceIte] at hsf
    cases hint : intApplyRuleFull sf nextWorld b with
    | notApplicable => simp [hint] at hsf
    | linearResult fs nw' e =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)
    | branchingResult bs nw' =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)

/-! ## Beta-Priority Stepper -/

/-- Whether a signed formula's rule application would create a fresh Kripke world.

True exactly for `F(φ → ψ)` (`.neg, .imp`), which includes `F(¬φ) = F(φ → ⊥)` since negation is
represented as implication to `⊥`. This is the sole world-creating case: `intApplyRuleFull`'s
`.neg, .imp` clause is the only one that returns a fresh `nextWorld` via `intFImpRule`. -/
def isWorldCreating (sf : ISF Atom) : Bool :=
  match sf.sign, sf.formula with
  | .neg, .imp _ _ => true
  | _, _ => false

/-- The non-world-creating first pass of `intStepBranchPrio`: identical in shape to
`intStepBranch`, but additionally skips any `sf` for which `isWorldCreating sf` holds.
Not `private`: `Scheme.lean`'s `intStepBranchPrio_none_iff`/`intStepBranchPrio_some_exists`
bridges need to unfold it from outside this file. -/
def intStepBranchPrioFirstPass (b : IBranch Atom) (expanded : List (ISF Atom))
    (nextWorld : Nat) : Option (IntRuleResult Atom × List (ISF Atom)) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) || isWorldCreating sf then none
    else
      match intApplyRuleFull sf nextWorld b with
      | .notApplicable => none
      | result => some (result, expanded ++ [sf])

/-- Beta-priority one-step expansion: defer world creation (`F(φ → ψ)`) until no other rule
applies anywhere on the branch.

The first pass (`intStepBranchPrioFirstPass`) mirrors `intStepBranch` but additionally skips
world-creating formulas. If it finds nothing -- either every remaining formula is already
`expanded`, or the only applicable formulas left are world-creating -- this falls through to
`intStepBranch` itself, which will select a world-creating formula if (and only if) one
remains. This strictly *defers*, never forbids, world creation: `intStepBranchPrio` returns
`none` in exactly the same circumstances as `intStepBranch` (see `intStepBranchPrio_none_iff`
below), so termination is inherited unconditionally from `intStepBranch`'s own `findSome?`
search over a finite list -- no new fuel or measure argument is needed. -/
def intStepBranchPrio (b : IBranch Atom) (expanded : List (ISF Atom)) (nextWorld : Nat) :
    Option (IntRuleResult Atom × List (ISF Atom)) :=
  match intStepBranchPrioFirstPass b expanded nextWorld with
  | some r => some r
  | none => intStepBranch b expanded nextWorld

omit [Hashable Atom] in
/-- If the first pass returns `some (r, e')`, then `r ≠ .notApplicable`. Same argument as
`intStepBranch_result_ne_notApplicable`, with the extra `isWorldCreating` disjunct in the
guard handled by the same `by_cases`/`simp` shape. -/
private lemma intStepBranchPrioFirstPass_result_ne_notApplicable
    {b : IBranch Atom} {expanded : List (ISF Atom)} {nextWorld : Nat}
    {r : IntRuleResult Atom} {exp' : List (ISF Atom)}
    (h : intStepBranchPrioFirstPass b expanded nextWorld = some (r, exp')) :
    r ≠ .notApplicable := by
  simp only [intStepBranchPrioFirstPass] at h
  obtain ⟨sf, _, hsf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hguard : (expanded.any (· == sf) || isWorldCreating sf) = true
  · simp [hguard] at hsf
  · simp only [Bool.not_eq_true] at hguard
    simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hsf
    cases hint : intApplyRuleFull sf nextWorld b with
    | notApplicable => simp [hint] at hsf
    | linearResult fs nw' e =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)
    | branchingResult bs nw' =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)

omit [Hashable Atom] in
/-- If `intStepBranchPrio` returns `some (r, e')`, then `r ≠ .notApplicable`.

Either the first (non-world-creating) pass produced it
(`intStepBranchPrioFirstPass_result_ne_notApplicable`), or the first pass returned `none` and
the fallback to `intStepBranch` supplies the fact directly via
`intStepBranch_result_ne_notApplicable`. -/
lemma intStepBranchPrio_result_ne_notApplicable
    {b : IBranch Atom} {expanded : List (ISF Atom)} {nextWorld : Nat}
    {r : IntRuleResult Atom} {exp' : List (ISF Atom)}
    (h : intStepBranchPrio b expanded nextWorld = some (r, exp')) : r ≠ .notApplicable := by
  simp only [intStepBranchPrio] at h
  cases hfp : intStepBranchPrioFirstPass b expanded nextWorld with
  | none =>
    simp only [hfp] at h
    exact intStepBranch_result_ne_notApplicable h
  | some rp =>
    obtain ⟨r', exp''⟩ := rp
    simp only [hfp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hr, hexp⟩ := h
    subst hr; subst hexp
    exact intStepBranchPrioFirstPass_result_ne_notApplicable hfp

/-! ## Freeze Precondition (plan Phase 5) -/

/-- **Freeze precondition** (plan Phase 5, beta-priority repair): every formula on `b` with
label below `w0` is either world-creating (deliberately deferred by
`intStepBranchPrioFirstPass`'s first-pass guard), already recorded in `e`, or carries no rule
at all (`isRuleShape sf = false` -- atoms, `⊥`, which `intApplyRuleFull` never processes).
This is exactly the negation of `intStepBranchPrioFirstPass`'s selection guard, restricted to
labels below `w0` (`intStepBranchPrioFirstPass_none_frozen` below) -- the "nothing pending
below `w0`" checkpoint the freeze argument turns on: once every candidate below `w0` is
disposed of one way or another, no alpha/beta step can ever again write NEW content below
`w0` (only world-creation can still act on the surviving `isWorldCreating` candidates, and it
only ever writes at its own `nextWorld`, never below it). -/
def IFrozenBelow (w0 : Nat) (e : List (ISF Atom)) (b : IBranch Atom) : Prop :=
  ∀ sf ∈ b, sf.label < w0 → isWorldCreating sf = true ∨ sf ∈ e ∨ isRuleShape sf = false

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Downward closure in the threshold** (plan Phase 6, Investigation note point 1): a lower
threshold is an easier freeze checkpoint to satisfy -- `sf.label < w0'` for `w0' ≤ w0` already
forces `sf.label < w0`, so the wider `IFrozenBelow w0 e b` hypothesis directly supplies the
disjunction the narrower `IFrozenBelow w0' e b` needs. This is what lets a checkpoint recorded at
one point (e.g. `IFrozenBelow nwH eH bPers`, from `intStepBranchPrioFirstPass_none_frozen`) be
weakened to any smaller threshold `w0' ≤ nwH` needed later (e.g. `l + 1` for a specific recorded
loop-back label `l < nwH`), without re-deriving the checkpoint. -/
lemma IFrozenBelow_downward {w0 w0' : Nat} {e : List (ISF Atom)} {b : IBranch Atom}
    (hle : w0' ≤ w0) (h : IFrozenBelow w0 e b) : IFrozenBelow w0' e b :=
  fun sf hsfb hlt => h sf hsfb (lt_of_lt_of_le hlt hle)

omit [Hashable Atom] in
/-- The world-creating checkpoint: when `intStepBranchPrioFirstPass` returns `none` at
`(b, e, nextWorld)`, `b` is `IFrozenBelow nextWorld e` -- every formula on the branch (not just
those below `nextWorld`, though `ILabelBoundStrict` typically pins all of `b` there already) is
either world-creating, already expanded, or ruleless. This is the entry point of the freeze
argument: `intStepBranchPrio` only reaches its second (world-creating) pass exactly when this
holds (`intStepBranchPrio`'s `none` branch, unfolded). -/
lemma intStepBranchPrioFirstPass_none_frozen
    {b : IBranch Atom} {e : List (ISF Atom)} {nextWorld : Nat}
    (h : intStepBranchPrioFirstPass b e nextWorld = none) :
    IFrozenBelow nextWorld e b := by
  intro sf hsfb _hlt
  simp only [intStepBranchPrioFirstPass] at h
  rw [List.findSome?_eq_none_iff] at h
  have hsf := h sf hsfb
  by_cases hguard : (e.any (· == sf) || isWorldCreating sf) = true
  · rw [Bool.or_eq_true] at hguard
    rcases hguard with hexp | hwc
    · right; left
      rw [List.any_eq_true] at hexp
      obtain ⟨sf', hsf'mem, hsf'eq⟩ := hexp
      simp only [beq_iff_eq] at hsf'eq
      rwa [hsf'eq] at hsf'mem
    · left; exact hwc
  · simp only [Bool.not_eq_true] at hguard
    simp only [hguard, Bool.false_eq_true, if_false] at hsf
    right; right
    rw [← intApplyRuleFull_notApplicable_iff sf nextWorld b]
    cases hint : intApplyRuleFull sf nextWorld b with
    | notApplicable => rfl
    | linearResult _ _ _ => rw [hint] at hsf; simp at hsf
    | branchingResult _ _ => rw [hint] at hsf; simp at hsf

omit [DecidableEq Atom] [Hashable Atom] in
/-- `intApplyRuleFull`'s `.linearResult` new-edge component is `some _` exactly for the
world-creating `.neg, .imp` case (`intFImpRule`'s output) -- every other rule shape emits
`none`. Contrapositive-shaped companion to `intApplyRuleFull_labels_eq_of_not_worldCreating`;
same case-bash proof style. -/
private lemma intApplyRuleFull_not_worldCreating_newEdge_none
    {sf : ISF Atom} {nw : Nat} {b : IBranch Atom} (hwc : isWorldCreating sf ≠ true)
    {newForms : List (ISF Atom)} {nw' : Nat} {newEdge : Option (Nat × Nat)}
    (h : intApplyRuleFull sf nw b = .linearResult newForms nw' newEdge) :
    newEdge = none := by
  rcases sf with ⟨s, f, l⟩
  simp only [isWorldCreating] at hwc
  cases s <;> cases f <;> simp_all [intApplyRuleFull]

omit [Hashable Atom] in
/-- If `intStepBranchPrioFirstPass` returns a `.linearResult` with a new edge planted, that
new edge is `none` -- the first pass only ever selects non-world-creating formulas (its own
guard excludes `isWorldCreating sf`), and `intApplyRuleFull_not_worldCreating_newEdge_none`
above shows only world-creating formulas ever plant an edge. -/
private lemma intStepBranchPrioFirstPass_linearResult_newEdge_none
    {b : IBranch Atom} {expanded : List (ISF Atom)} {nextWorld : Nat}
    {newForms : List (ISF Atom)} {nw' : Nat} {newEdge : Option (Nat × Nat)}
    {exp' : List (ISF Atom)}
    (h : intStepBranchPrioFirstPass b expanded nextWorld
      = some (.linearResult newForms nw' newEdge, exp')) :
    newEdge = none := by
  simp only [intStepBranchPrioFirstPass] at h
  obtain ⟨sf, _, hsf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hguard : (expanded.any (· == sf) || isWorldCreating sf) = true
  · simp [hguard] at hsf
  · simp only [Bool.not_eq_true] at hguard
    simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hsf
    have hwc : isWorldCreating sf ≠ true := by
      simp only [Bool.or_eq_false_iff] at hguard
      simp [hguard.2]
    cases hint : intApplyRuleFull sf nextWorld b with
    | notApplicable => simp [hint] at hsf
    | linearResult fs n ed =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsf
      obtain ⟨⟨-, -, hed⟩, -⟩ := hsf
      exact hed ▸ intApplyRuleFull_not_worldCreating_newEdge_none hwc hint
    | branchingResult bs n => simp [hint] at hsf

omit [Hashable Atom] in
/-- **The world-creating checkpoint** (the fact plan Phase 6's origin-tracking machinery
needed but had not yet landed): whenever `intStepBranchPrio` actually plants a new edge (i.e.
fires the world-creating `F(φ → ψ)` rule), it can only have reached that outcome via its
SECOND pass (`intStepBranch`, the fallback) -- the FIRST pass (`intStepBranchPrioFirstPass`)
never plants an edge (previous lemma), so if the first pass HAD returned `some` here, the
overall result's edge component would have to be `none`, contradicting the hypothesis.
Composed with `intStepBranchPrioFirstPass_none_frozen`, this is the "record-time checkpoint"
`IReuseFrozenOrigin_snoc`'s docstring names: `IFrozenBelow nextWorld expanded b` is available
for free exactly when a new loop-back edge is about to be recorded. -/
lemma intStepBranchPrio_newEdge_firstPass_none
    {b : IBranch Atom} {expanded : List (ISF Atom)} {nextWorld : Nat}
    {newForms : List (ISF Atom)} {nw' : Nat} {newE : Nat × Nat} {newExp : List (ISF Atom)}
    (hstep : intStepBranchPrio b expanded nextWorld
      = some (.linearResult newForms nw' (some newE), newExp)) :
    intStepBranchPrioFirstPass b expanded nextWorld = none := by
  cases hfp : intStepBranchPrioFirstPass b expanded nextWorld with
  | none => rfl
  | some r =>
    exfalso
    simp only [intStepBranchPrio, hfp] at hstep
    obtain ⟨r1, e1⟩ := r
    simp only [Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨hr, -⟩ := hstep
    subst hr
    have := intStepBranchPrioFirstPass_linearResult_newEdge_none hfp
    simp at this

omit [Hashable Atom] in
/-- **Direct corollary**: at the exact moment `intStepBranchPrio` plants a new edge, the
branch is already `IFrozenBelow nextWorld expanded` -- composes the previous lemma with
`intStepBranchPrioFirstPass_none_frozen`. This is the checkpoint fact used to justify a
freshly-recorded loop-back edge's `IReuseFrozenOrigin` witness (`Scheme.lean`,
`IReuseFrozenOrigin_snoc`'s call site). -/
lemma intStepBranchPrio_newEdge_frozen
    {b : IBranch Atom} {expanded : List (ISF Atom)} {nextWorld : Nat}
    {newForms : List (ISF Atom)} {nw' : Nat} {newE : Nat × Nat} {newExp : List (ISF Atom)}
    (hstep : intStepBranchPrio b expanded nextWorld
      = some (.linearResult newForms nw' (some newE), newExp)) :
    IFrozenBelow nextWorld expanded b :=
  intStepBranchPrioFirstPass_none_frozen (intStepBranchPrio_newEdge_firstPass_none hstep)

/-! ## Sfor-Containment Loop-Check -/

/-- The **ancestor-directed** `Sfor`-containment loop-check (the ancestor-blocking calculus
repair's Phase 3; wired into `intExpandBranches`'s call site at Phase 4 — this is now the sole
loop-check implementation).

Following the `Sfor`-containment termination technique of Garg, Genovese & Negri,
*Countermodels from Sequent Calculi in Multi-Modal Logics* (LICS 2012)
[`GargGenoveseNegri2012`], this helper decides whether the `F(φ → ψ)`-triggered world-creation
in `go`'s `some (.linearResult newForms nw' (some newEdge), newExp)` branch — the *only*
world-creating case, produced solely by `intApplyRuleFull`'s `F(φ → ψ)` clause via
`intFImpRule` — can be **reused** instead of performed, so that no two worlds on a branch ever
end up with containment-equal forced-sets.

A prior descendant-directed formulation of this check (`isAccessible edges w x`, searching
worlds reachable *from* the source `w`) was the root defect this task repairs: a Fitting-style
loop check must search **ancestors** — worlds `x` reachable *to* `w` — so that a formula
obligation can be discharged by something already forced earlier on the same accessibility
path, not by something not-yet-created. That descendant-directed def and its spec lemma have
been retired (Phase 4); this ancestor-directed def is now the sole implementation.

**Search direction and why.** `isAccessible edges x w` (x reachable to w) and `x.ble w`
(x carries the strictly smaller, ancestor-side label); every other conjunct (including the
`F(ψ)@x` explicit-entry conjunct) is as in the retired descendant-directed design. The
rationale — `Sfor` (the forced-set at a world) takes values in the finite subset lattice of
`Sub(φ)` and grows monotonically along accessibility, so an ancestor's forced-set is a subset
of any descendant's — is attributed to
Garg, Genovese & Negri, *Countermodels from Sequent Calculi in Multi-Modal Logics* (LICS 2012)
[`GargGenoveseNegri2012`] and to Fitting, *Proof Methods for Modal and Intuitionistic Logics*
(1983) [`Fitting1983`] Ch. 4, as **provenance only**: neither source is readable from this
repository (BibTeX key only, no entry in the navigable literature corpus — see the plan's H3
honesty rule). The actual evidence for this design is
`specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md` Table 3:
real `#eval` measurement on the complexity-9 divergence witness shows the ancestor-directed
check (variant V1, conjunct retained) saturates at `fuel ≥ 120` (`maxLabel = 21`, stable across
four independent evaluations), where the descendant-directed `intFImpReuseWitness?` diverges
without bound on the same input.

**Search order.** Identical to `intFImpReuseWitness?`: candidates are the distinct world labels
appearing on `bPers` (`(bPers.map (·.label)).eraseDups`), in branch order; `List.findSome?`
returns the first label satisfying all four conditions, or `none` if no label does.

**Reuse contract.** `some x` means the ancestor `x` discharges the obligation: do NOT create
`w'`, recurse `intExpandBranches` on `bPers` **unmodified** (never Option B — appending a fresh
`F(ψ)@x` entry on reuse was tried and found UNSOUND, `Expansion.lean:256-264`), with `edges`
**unchanged** and the world counter **unconsumed**. `none` means proceed exactly as today
(create `w'` as normal). This mirrors `intFImpReuseWitness?`'s own contract exactly; only the
search direction differs.

`intExpandBranches`'s single loop-check call site calls this declaration directly (the swap
was Phase 4's explicit acceptance gate); the superseded descendant-directed
`intFImpReuseWitness?` and its `_spec` lemma were deleted in that same phase.

**Recorded limitation, PRE-REPAIR (historical): a FRAME-CONSTRUCTION defect, not a proof-route
gap.** This check verifies `Sfor`-containment (the `sfor.all (forcedAtX.contains ·)` conjunct
above) **at reuse time only**. At the time this note was written, the loop-back edge `(x, w)` it
records was **never re-validated** afterwards: if either `x` or `w` later received an independent
positive-disjunction (beta) split, the containment the edge asserted could break while the edge
itself remained on the branch, unconditionally — `x` and `w` stay preorder-equivalent under
`intAccessPreorder`'s reflexive-transitive closure even though their forced atoms have since
diverged. This was machine-verified, not hypothetical: `CslibTests/BetaSplitRefutation.lean`
exhibits `phiRef1 := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr`, where reuse fires with
`(x, l) = (1, 2)` (containment genuinely holds at that moment), the `genCopies` channel then
copies the unexpanded `T(pr ∨ ps)` to world `2` as a distinct `ISF` entry, and that copy's later,
independent beta-split used to leave worlds `1` and `2` augmented-preorder-equivalent yet
disagreeing on `pr`. This was calculus-level, in the frame construction, not a gap in any proof:
termination (the ancestor-directed search this repairs) was entirely unaffected throughout, and
`intExpandBranches_closed_unsat`/`Soundness.lean` remained sorry-free and axiom-clean even before
this repair — what was affected was the *soundness of the countermodel* an open branch yields
under the augmented accessibility relation (see `Scheme.lean`'s `openBranch_countermodel` and its
upward-closure conjunct).

**POST-REPAIR: this gap is now closed.** `intStepBranchPrio` (beta-priority scheduling, this
file) defers every world-creating step — including the world creation that triggers a loop-back
reuse decision here — until no other rule applies anywhere on the branch, so no independent
beta-split of the kind `phiRef1` exhibits can occur *after* a loop-back edge is recorded and
still be pending when persistence is needed. Combined with the freeze/provenance machinery
`IReuseFrozenOrigin` (`Scheme.lean`, plan Phase 6) — which the bare, current-branch form of
`IReuseContain` derives from directly — this gives `hpersAug` (`Scheme.lean:9645-9665`),
positive persistence over the augmented frame, still `#guard_msgs`-refuted only for the
pre-repair calculus by `CslibTests/BetaSplitRefutation.lean` and holding for the repaired one.
`CslibTests/WitnessProbe.lean`'s `phiRef1`/`phiRef2`/`phiRef3` witnesses are retained as the
durable counter-instance record explaining why `intStepBranchPrio` and `IReuseFrozenOrigin`
exist, not deleted now that the gap they exposed is closed.

**Secondary finding: a reuse event can record a self-loop.** For `phiRef1` the loop-back list is
`[(1,2), (2,2)]` — the `(2,2)` entry has `x = l = 2`. The guard `x.ble w` above is non-strict and
`isAccessible edges w w` is reflexively true, so a world can discharge its own obligation against
itself. This is harmless for persistence (a self-loop asserts no new `≤` pair beyond
reflexivity) but was previously undocumented. -/
def intFImpReuseWitnessAnc? (bPers : IBranch Atom) (edges : IEdges)
    (newForms : List (ISF Atom)) (newEdge : Nat × Nat) : Option Nat :=
  -- `w` is the source world of the would-be world-creating edge (`intFImpRule` returns
  -- edge `(w', w)`, so `newEdge.2 = w`).
  let w := newEdge.2
  match newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none) with
  | none => none  -- malformed input: no obligation entry (should not happen for this rule)
  | some ψ =>
    -- Sfor(w') = {φ} ∪ posFormulasAt bPers w, read off newForms's sign = .pos sublist.
    let sfor : List (Proposition Atom) :=
      newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none
    let candidates := (bPers.map (·.label)).eraseDups
    candidates.findSome? fun x =>
      let forcedAtX := posFormulasAt bPers x
      -- Ancestor direction: `x` is reachable *to* `w` (`isAccessible edges x w`), and carries
      -- a strictly smaller label (`x.ble w`) — the reverse of `intFImpReuseWitness?`'s
      -- descendant-direction checks.
      if isAccessible edges x w
          && x.ble w
          && sfor.all (forcedAtX.contains ·)
          && !(forcedAtX.contains ψ)
          && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) then
        some x
      else
        none

omit [Hashable Atom] in
/-- Specification lemma for `intFImpReuseWitnessAnc?`:
when it returns `some x` for the `.neg`-signed obligation `ψ` read off `newForms`, `x`
satisfies all five search conditions in **ancestor** direction, including the load-bearing
Option-A conjunct `F(ψ)@x ∈ bPers` (an explicit branch entry, not merely "not forced"). The
proof structure is `intFImpReuseWitness?_spec`'s, transferred verbatim with the two directional
conjuncts (`isAccessible`, `≤`) reversed. -/
lemma intFImpReuseWitnessAnc?_spec {bPers : IBranch Atom} {edges : IEdges}
    {newForms : List (ISF Atom)} {newEdge : Nat × Nat} {x : Nat} {ψ : Proposition Atom}
    (hψ : newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none)
        = some ψ)
    (h : intFImpReuseWitnessAnc? bPers edges newForms newEdge = some x) :
    isAccessible edges x newEdge.2 = true ∧
    x ≤ newEdge.2 ∧
    (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
      ((posFormulasAt bPers x).contains ·) = true ∧
    ¬ (posFormulasAt bPers x).contains ψ ∧
    bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) = true := by
  simp only [intFImpReuseWitnessAnc?, hψ] at h
  obtain ⟨x', _hx'mem, hif⟩ := List.exists_of_findSome?_eq_some h
  by_cases hcond : (isAccessible edges x' newEdge.2
      && x'.ble newEdge.2
      && (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
        ((posFormulasAt bPers x').contains ·)
      && !(posFormulasAt bPers x').contains ψ
      && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x')) = true
  · simp only [hcond, if_true] at hif
    injection hif with hif
    subst hif
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
    exact ⟨h1, Nat.le_of_ble_eq_true h2, h3, by simpa using h4, h5⟩
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond] at hif
    simp at hif

omit [Hashable Atom] in
/-- The `none` direction of `intFImpReuseWitnessAnc?_spec` (DP-2 support, report section 5.2):
when the reuse check returns `none`, EVERY candidate label `x` in
`(bPers.map (·.label)).eraseDups` fails the conjunction of the five search conditions. This lets
a `none` result be instantiated at a SPECIFIC candidate (e.g. a `par`-ancestor known to be a
branch member) to conclude that candidate's conjunct-3 (the containment conjunct) must fail,
given the other four conjuncts are separately established — the mint-time residue argument
(Phase 5). Proved mechanically from `List.findSome?_eq_none` plus the same `if`-unfold
`intFImpReuseWitnessAnc?_spec` uses; `intFImpReuseWitnessAnc?` itself is NOT modified. -/
lemma intFImpReuseWitnessAnc?_none_spec {bPers : IBranch Atom} {edges : IEdges}
    {newForms : List (ISF Atom)} {newEdge : Nat × Nat} {x : Nat} {ψ : Proposition Atom}
    (hψ : newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none)
        = some ψ)
    (h : intFImpReuseWitnessAnc? bPers edges newForms newEdge = none)
    (hx : x ∈ (bPers.map (·.label)).eraseDups) :
    ¬ (isAccessible edges x newEdge.2 = true ∧
       x ≤ newEdge.2 ∧
       (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
         ((posFormulasAt bPers x).contains ·) = true ∧
       ¬ (posFormulasAt bPers x).contains ψ ∧
       bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) = true) := by
  simp only [intFImpReuseWitnessAnc?, hψ] at h
  rw [List.findSome?_eq_none_iff] at h
  have hnone := h x hx
  rintro ⟨h1, h2, h3, h4, h5⟩
  have hb2 : x.ble newEdge.2 = true := Nat.ble_eq_true_of_le h2
  have hb4 : (posFormulasAt bPers x).contains ψ = false := by simpa using h4
  have hcond : (isAccessible edges x newEdge.2
      && x.ble newEdge.2
      && (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
        ((posFormulasAt bPers x).contains ·)
      && !(posFormulasAt bPers x).contains ψ
      && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x)) = true := by
    simp only [h1, hb2, h3, hb4, h5, Bool.and_self, Bool.not_false]
  simp only [hcond, if_true] at hnone
  exact absurd hnone (by simp)

/-! ### Divergence witness: no world bound exists for this calculus -/

/-!
Historical record, measured on the RETIRED global-fuel expansion loop (the predecessor of
the per-branch-fuel `intExpandBranches` in `Intuitionistic/Scheme.lean`; `intExpandBranches`
below refers to that retired engine, whose step behavior on this input is identical): the
loop never saturates on a complexity-9 witness formula, and no numeric world bound (of any
size) can be substituted for the one `intUniverse`/`intApplyRuleFull_outputs_subset` assume.
This note is the durable, greppable record of that fact, obtained by evaluating the loop on
the witness formula below at increasing fuel and observing the branch/world counts.

**Witness formula** (complexity 9):
`φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u₁→v₁) ∨ (u₂→v₂))`

**Measured growth.** Evaluating `intExpandBranches [[⟨.neg, φ0, 0⟩]] [[]] [1] [[]] fuel
isIntuitionisticallyClosed` at increasing `fuel`, the maximum world label reached is:

| fuel         | 10 | 20 | 30 | 40 | 60 | 80 | 120 | 160 | 200 | 260 |
|--------------|----|----|----|----|----|----|-----|-----|-----|-----|
| max label    | 4  | 7  | 10 | 14 | 21 | 27 | 40  | 54  | 67  | 87  |

Growth is linear in fuel with no saturation: `intStepBranch` never returns `none` on this
input, so the loop consumes its entire fuel budget every time.

**Structural duplication.** From world 3 onward, every world is an exact structural duplicate
of its grandparent — identical T-set and F-set, period 2. The two T-implication rules
(`applyAllTImpRules`'s copy channel above and `intFImpRule` in `Rules.lean`) ping-pong forever
on identical content; only the label increments.

**Three consequences:**
(a) `intApplyRuleFull_outputs_subset`'s hypothesis `hnw : nextWorld ≤ φ0.complexity + 1`
(`Scheme.lean`) is FALSE, refuted by this direct counterexample.
(b) `intUniverse`'s label range `List.range (φ.complexity + 2)` (`Scheme.lean`) is false as an
invariant of branches actually produced by `intExpandBranches`.
(c) NO numeric world bound of any size exists for the current calculus: the world count is
unbounded in fuel on this input, so no `f(φ0)` satisfies `nextWorld ≤ f(φ0)`.

**Directive.** Do not attempt to prove `intExpandBranches_world_bound` or the `hnw` hypothesis
as currently stated — they are refuted, not merely hard. Any future progress on
world-boundedness requires a calculus-level change (an ancestor-directed loop-check/blocking
rule that actually cuts the ping-pong above), not a proof effort against the present statements.

**This directive does NOT extend to `hUniv`.** What this note originally called the
`intUniverse` containment invariant now names `IAllUniv` (`Scheme.lean`), stated over the
EXTENDED universe `intUniverseExt` rather than the plain `intUniverse` consequence (b) above
refutes. Unlike `intExpandBranches_world_bound`/`hnw`, `IAllUniv` IS threaded and discharged:
it is `intExpandBranches_openBranch_sat`'s `hUniv` hypothesis, and `openBranch_countermodel`
(`Scheme.lean`) supplies it via `mem_intUniverseExt_of` at a live, sorry-free use site.

**Method.** Obtained by evaluating `intExpandBranches` on `φ0` at increasing fuel and comparing
branch contents across worlds; re-verified directly in Lean on the unmodified library, not only
by an external harness.
-/


end Cslib.Logic.PL

end
