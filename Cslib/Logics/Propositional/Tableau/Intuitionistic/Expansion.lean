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
- `intExpandBranches`: Fuel-based expansion loop for the intuitionistic tableau.
- `intuitionisticTableau`: The complete decision procedure starting from `F(φ)` at world 0.

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

NOTE: The weaker `MinimalClosure` instance (atom-only) was previously used, but this
is insufficient for correctness -- for example, `⊥ → ⊥` is minimally valid but the
atom-only closure fails to close the branch containing T(⊥)/F(⊥) at the created world. -/
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
    let rec go (pending : List (IBranch Atom))
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

Identical to the intuitionistic tableau but uses `MinimalClosure` instead:
a branch closes only when T(p) and F(p) coexist at the same world for atomic p.

- Returns `closed` iff `φ` is minimally valid (MValid).
- Returns `openBranch b` iff `φ` is not minimally valid. -/
def minimalTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  let initialBranch : IBranch Atom := [⟨.neg, φ, 0⟩]
  let fuel := 2 ^ (2 * φ.complexity + 2)
  intExpandBranches [initialBranch] [[]] [1] [[]] fuel isMinimallyClosed

end Cslib.Logic.PL

end
