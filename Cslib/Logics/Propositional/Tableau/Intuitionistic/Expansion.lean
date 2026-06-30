/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Rules

/-! # Intuitionistic Propositional Tableau Expansion

This module implements the expansion loop for the intuitionistic propositional tableau.
The intuitionistic tableau uses `L = Nat` (Kripke world indices) and the
`IntuitionisticClosure` instance (closes on T(⊥) at any label, or on complementary
T(φ)/F(φ) pairs at the same label).

## Main Definitions

- `IntTableauResult`: Result of the intuitionistic expansion (closed or open).
- `intExpandBranches`/`propExpandBranches`: Fuel-based expansion loop, **parameterized by
  `closurePred`** — the generic workhorse. `intuitionisticTableau` instantiates it with
  `isIntuitionisticallyClosed`; `minimalTableau` instantiates it with `isMinimallyClosed`.
  `propExpandBranches` is an alias that emphasizes this generic, closure-predicate-parameterized
  design (Phase 8, task 407 S3 follow-up).
- `intuitionisticTableau`: Starting from `F(φ)` at world 0, closes iff `IValid φ`.
- `minimalTableau`: Same as above but uses `isMinimallyClosed`; closes iff `MValid φ`.

## Tableau Unification (Phase 8)

The two divergence points between intuitionistic and minimal tableau are:
1. **Closure predicate**: `isIntuitionisticallyClosed` vs `isMinimallyClosed`.
2. **Bottom forcing in countermodel**: `fun _ _ => False` vs `minBranchBotForces b`.

Point 1 is handled here by the `closurePred` parameter.
Point 2 is handled in `Intuitionistic/Scheme.lean` via `IntMinScheme`.

There is no duplicate expansion function: both tableau variants are instances of
the single `intExpandBranches`/`propExpandBranches` loop.

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
  b ++ newForms.flatten

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
    simp [hexp] at hsf
    cases hint : intApplyRuleFull sf nextWorld b with
    | notApplicable => simp [hint] at hsf
    | linearResult fs nw' e =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)
    | branchingResult bs nw' =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)

/-! ## Expansion Loop -/

/-- Expand a list of intuitionistic tableau branches with a fuel counter.

For each open branch, applies persistence and then one expansion step.
Branches are processed sequentially; branching rules create new sub-branches.

The `edgeSets` parameter is a parallel list (one per branch) of parent-child edge lists
tracking the Kripke accessibility relation for each branch. When a world-creating rule
fires, the new edge is added to the current branch's edge set. When a branching rule
fires, both sub-branches inherit the current edge set. -/
def intExpandBranches
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuel : Nat)
    (closurePred : IBranch Atom → Bool) :
    IntTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Out of fuel: return first open branch as countermodel
    match branches.findSome? (fun b => if closurePred b then none else some b) with
    | some b => .openBranch b
    | none => .closed
  | fuel' + 1 =>
    -- Inner loop: apply persistence and expand the first open branch.
    -- Iterates through pending branches, skipping closed ones and expanding the first open one.
    let rec @[nolint docBlame] go (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges)
        : IntTableauResult Atom :=
      match pending, pendingExp, pendingNW, pendingEdges with
      | [], _, _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges =>
        -- First apply persistence to get all T(φ → ψ) consequences
        let bPers := applyPersistenceFixpoint b edges (fuel' + 1)
        if closurePred bPers then
          -- Branch is closed
          go restBs restEs restNW restEdges
            (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        else
          match intStepBranch bPers e nw with
          | none =>
            -- Branch is saturated and open: countermodel
            .openBranch bPers
          | some (.linearResult newForms nw' newEdge, newExp) =>
            -- Alpha-rule or world-creation: extend branch
            let edges' := match newEdge with
              | none => edges
              | some e => edges ++ [e]
            intExpandBranches
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              (doneEdges ++ [edges'] ++ restEdges)
              fuel'
              closurePred
          | some (.branchingResult branches' nw', newExp) =>
            -- Beta-rule: split into sub-branches (each inherits current edge set)
            intExpandBranches
              (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
              (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
              (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
              (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
              fuel'
              closurePred
          | some (.notApplicable, _) =>
            -- This case shouldn't happen (intStepBranch filters notApplicable)
            .openBranch bPers
      | _ :: restBs, _, _, _ =>
        go restBs [] [] [] done doneExp doneNW doneEdges
    go branches expandedSets nextWorlds edgeSets [] [] [] []

/-! ## Generic Alias -/

/-- `propExpandBranches` is the generic propositional tableau expansion loop,
parameterized by `closurePred : IBranch Atom → Bool`.

This is a documentation alias for `intExpandBranches`, emphasizing that the expansion loop
is closure-predicate-agnostic. The two concrete instantiations are:
- `intuitionisticTableau`: `closurePred = isIntuitionisticallyClosed`
- `minimalTableau`: `closurePred = isMinimallyClosed`

The `IntMinScheme` structure in `Scheme.lean` bundles both divergence points (closure
predicate and countermodel `botForces`) into a single parameterized interface. -/
@[inline] def propExpandBranches
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuel : Nat)
    (closurePred : IBranch Atom → Bool) :
    IntTableauResult Atom :=
  intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred

/-! ## Decision Procedures -/

/-- The intuitionistic propositional tableau decision procedure.

Given `φ`, starts with `F(φ)` at world 0 and expands using `IntuitionisticClosure`.
- Returns `closed` iff `φ` is intuitionistically valid (IValid).
- Returns `openBranch b` iff `φ` is not intuitionistically valid, with `b` an open
  saturated branch giving a Kripke countermodel.

The fuel bound `2 ^ (2 * φ.complexity + 2)` accounts for the exponential blowup
possible in intuitionistic proofs (finite model property gives this bound). -/
def intuitionisticTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  let initialBranch : IBranch Atom := [⟨.neg, φ, 0⟩]
  let fuel := 2 ^ (2 * φ.complexity + 2)
  intExpandBranches [initialBranch] [[]] [1] [[]] fuel isIntuitionisticallyClosed

/-- The minimal propositional tableau decision procedure.

Identical to the intuitionistic tableau but uses `isMinimallyClosed` instead of
`isIntuitionisticallyClosed`: a branch closes when T(φ) and F(φ) coexist at the same
world for any formula φ (not only T(⊥)).

- Returns `closed` iff `φ` is minimally valid (MValid).
- Returns `openBranch b` iff `φ` is not minimally valid. -/
def minimalTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  let initialBranch : IBranch Atom := [⟨.neg, φ, 0⟩]
  let fuel := 2 ^ (2 * φ.complexity + 2)
  intExpandBranches [initialBranch] [[]] [1] [[]] fuel isMinimallyClosed

end Cslib.Logic.PL

end
