/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Defs
public import Cslib.Foundations.Logic.Tableau.ClosureCondition
public import Cslib.Foundations.Logic.Tableau.PropositionalRules
public import Cslib.Logics.Propositional.Subformula

/-! # Classical Propositional Tableau Expansion

This module implements the classical propositional tableau decision procedure.
The classical tableau uses `L = Unit` (all formulas share a single implicit world)
and the `ClassicalClosure` instance (closes on T(⊥) or T(φ)/F(φ) contradiction).

## Main Definitions

- `ClassicalTableauResult Atom`: The result of running the classical tableau.
- `classicalApplyOne`: Apply all classical rules to a single signed formula.
- `classicalTableau`: Fuel-based expansion loop for classical propositional tableau.

## Design

The expansion loop tracks which signed formulas have already been expanded to avoid
redundant expansion. Each step picks the first unexpanded formula, applies all 8 classical
rules, and adds resulting formulas to the branch. Branching rules split the current branch
into two sub-branches.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

section ClassicalExpansion

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Classical Tableau Result -/

/-- The result of a classical propositional tableau computation.

- `closed`: Every branch is closed (the formula is a classical tautology).
- `openBranch b`: An open (non-closed), saturated branch `b` exists, providing a countermodel. -/
inductive ClassicalTableauResult (Atom : Type*) : Type _ where
  /-- All branches close: the formula is a classical tautology. -/
  | closed : ClassicalTableauResult Atom
  /-- An open saturated branch exists: the formula is not a tautology. -/
  | openBranch : Branch (Proposition Atom) Unit → ClassicalTableauResult Atom

/-! ## Expansion Helpers -/

/-- Apply classical propositional rules to a single signed formula.

Uses `propImpOf?` for proper implication (excluding `φ → ⊥`) and `propNegOf?` for negation
(`φ → ⊥`), together with `propAndOf?` and `propOrOf?`. Returns `notApplicable` when
no rule matches (e.g., for atoms and bot). -/
def classicalApplyOne (sf : SignedFormula (Proposition Atom) Unit) :
    RuleResult (Proposition Atom) Unit :=
  tryAllPropRules propAndOf? propOrOf? propImpOf? propNegOf? sf

/-- Check whether a classical branch is closed.

Uses the `ClassicalClosure` instance (anonymous), which closes when T(⊥) is present
or when both T(φ) and F(φ) appear at the same label. -/
def isClassicallyClosed (b : Branch (Proposition Atom) Unit) : Bool :=
  @ClosureCondition.isClosed _ _ ClassicalClosure.instClosureConditionOfBEqOfHasBot b

/-! ## Branch Expansion -/

/-- One step of the classical tableau expansion on a single branch.

Finds the first signed formula on `b` that (1) is not yet expanded and (2) has a
rule applicable to it. Returns `none` when the branch is saturated.

Returns `some (newBranches, newExpanded)`:
- `newBranches`: sub-branches created by the rule (1 for alpha-rules, 2 for beta-rules)
- `newExpanded`: the updated expanded set -/
def classicalStepBranch (b : Branch (Proposition Atom) Unit)
    (expanded : List (SignedFormula (Proposition Atom) Unit)) :
    Option (List (Branch (Proposition Atom) Unit) ×
            List (SignedFormula (Proposition Atom) Unit)) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      match classicalApplyOne sf with
      | .linear newForms =>
        some ([Branch.extendMany b newForms], expanded ++ [sf])
      | .branching branches =>
        some (branches.map (Branch.extendMany b ·), expanded ++ [sf])
      | .persistent newForms =>
        some ([Branch.extendMany b newForms], expanded ++ [sf])
      | .notApplicable => none

/-- Expand a list of classical tableau branches with a fuel counter.

Processes each branch in turn:
- If the branch is closed, skip it.
- If the branch has no more applicable rules (saturated and open), return it as a countermodel.
- Otherwise apply one expansion step and recurse with remaining fuel.

Termination is guaranteed by the fuel parameter, which is bounded by the total number of
expandable signed formulas in the initial branch. -/
def classicalExpandBranches
    (branches : List (Branch (Proposition Atom) Unit))
    (expandedSets : List (List (SignedFormula (Proposition Atom) Unit)))
    (fuel : Nat) : ClassicalTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: treat any non-closed branch as the countermodel
    match branches.findSome? (fun b => if isClassicallyClosed b then none else some b) with
    | some b => .openBranch b
    | none => .closed
  | fuel' + 1 =>
    -- Process branches: find first open branch to expand
    -- Inner loop: iterate through branches, skipping closed ones and expanding the first open one.
    -- Inner helper: iterate through pending branches, skipping closed ones and expanding
    -- the first open branch. Accumulates processed branches in `done`/`doneExp`.
    let rec @[nolint docBlame] processNext (pending : List (Branch (Proposition Atom) Unit))
        (pendingExp : List (List (SignedFormula (Proposition Atom) Unit)))
        (done : List (Branch (Proposition Atom) Unit))
        (doneExp : List (List (SignedFormula (Proposition Atom) Unit)))
        : ClassicalTableauResult Atom :=
      match pending, pendingExp with
      | [], _ => .closed  -- All branches processed and closed
      | b :: restBs, e :: restEs =>
        if isClassicallyClosed b then
          processNext restBs restEs (done ++ [b]) (doneExp ++ [e])
        else
          match classicalStepBranch b e with
          | none => .openBranch b  -- Saturated and open: countermodel
          | some (newBs, newExp) =>
            classicalExpandBranches
              (done ++ newBs ++ restBs)
              (doneExp ++ newBs.map (fun _ => newExp) ++ restEs)
              fuel'
      | _ :: restBs, [] =>
        processNext restBs [] done doneExp
    processNext branches expandedSets [] []

/-- The classical propositional tableau decision procedure.

Given a formula `φ`, runs the signed tableau starting from `F(φ)` at label `()`.
- Returns `closed` iff `φ` is a classical tautology.
- Returns `openBranch b` iff `φ` is not a tautology; `b` is an open saturated branch
  from which a Boolean countermodel can be extracted (see `Classical/Soundness.lean`).

The fuel bound `3 ^ φ.complexity` is a base-3 exponential bound derived from the
measure-decrease termination proof: `classicalExpMeasure` uses a `3^C` Lyapunov function
where `C = classicalBranchComplexity`, and the initial single-branch state has measure
exactly `3 ^ φ.complexity`. The prior linear bound `4 * (φ.complexity + 1) + 1` was
insufficient for formulas of complexity ≥ 3. -/
def classicalTableau (φ : Proposition Atom) : ClassicalTableauResult Atom :=
  let initialBranch : Branch (Proposition Atom) Unit := [⟨.neg, φ, ()⟩]
  let fuel := 3 ^ φ.complexity
  classicalExpandBranches [initialBranch] [[]] fuel

end ClassicalExpansion

end Cslib.Logic.PL

end
