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
`IntuitionisticClosure` instance (closes only on T(⊥) at any label).

## Main Definitions

- `IntTableauResult`: Result of the intuitionistic expansion (closed or open).
- `intExpandBranches`: Fuel-based expansion loop for the intuitionistic tableau.
- `intuitionisticTableau`: The complete decision procedure starting from `F(φ)` at world 0.

## Design

The expansion loop processes one branch at a time. Within each branch:
1. First apply the persistent T(φ → ψ) rule for all T-implication formulas on the branch.
2. Then pick the first unexpanded formula and apply the appropriate rule.
3. For world-creating rules, add the new world's formulas and update the world counter.
4. For branching rules, split the current branch into sub-branches.

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

Uses the `IntuitionisticClosure` instance, which closes only when T(⊥) appears
at any label. Unlike classical closure, complementary pairs do NOT close a branch. -/
def isIntuitionisticallyClosed (b : IBranch Atom) : Bool :=
  open IntuitionisticClosure in
  ClosureCondition.isClosed b

/-- Check whether a minimal branch is closed.

Uses the `MinimalClosure` instance, which closes when T(p) and F(p) appear at the same
world for an atomic formula p. This is weaker than classical but stronger than intuitionistic
in the sense that it allows atom contradictions but NOT T(⊥). -/
def isMinimallyClosed (b : IBranch Atom) : Bool :=
  open MinimalClosure in
  ClosureCondition.isClosed b

/-! ## Persistence Application -/

/-- Apply all pending T(φ → ψ) rules to the current branch state.

For each T(φ → ψ) formula at world w on the branch, and for each accessible world
w' ≥ w with T(φ) at w', if T(ψ) is not yet at w', add T(ψ) at w'.

Returns the updated branch with all pending persistence applications. -/
def applyAllTImpRules (b : IBranch Atom) : IBranch Atom :=
  let newForms :=
    b.filterMap fun sf =>
      match sf.sign, sf.formula with
      | .pos, .imp φ ψ =>
        -- Get all worlds w' ≥ sf.label with T(φ) at w' but not yet T(ψ)
        let toAdd := intTImpRule φ ψ sf.label b
        if toAdd.isEmpty then none else some toAdd
      | _, _ => none
  b ++ newForms.flatten

/-- Repeatedly apply persistence until fixpoint.

Since each application can create new T-formulas that may trigger more applications,
we iterate until no new formulas are added. Uses fuel to guarantee termination. -/
def applyPersistenceFixpoint (b : IBranch Atom) (fuel : Nat) : IBranch Atom :=
  match fuel with
  | 0 => b
  | fuel' + 1 =>
    let b' := applyAllTImpRules b
    if b'.length == b.length then b  -- No new formulas added; fixpoint reached
    else applyPersistenceFixpoint b' fuel'

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
Branches are processed sequentially; branching rules create new sub-branches. -/
def intExpandBranches
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
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
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        : IntTableauResult Atom :=
      match pending, pendingExp, pendingNW with
      | [], _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, nw :: restNW =>
        -- First apply persistence to get all T(φ → ψ) consequences
        let bPers := applyPersistenceFixpoint b (fuel' + 1)
        if closurePred bPers then
          -- Branch is closed
          go restBs restEs restNW (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw])
        else
          match intStepBranch bPers e nw with
          | none =>
            -- Branch is saturated and open: countermodel
            .openBranch bPers
          | some (.linearResult newForms nw', newExp) =>
            -- Alpha-rule or world-creation: extend branch
            intExpandBranches
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              fuel'
              closurePred
          | some (.branchingResult branches' nw', newExp) =>
            -- Beta-rule: split into sub-branches
            intExpandBranches
              (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
              (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
              (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
              fuel'
              closurePred
          | some (.notApplicable, _) =>
            -- This case shouldn't happen (intStepBranch filters notApplicable)
            .openBranch bPers
      | _ :: restBs, _, _ =>
        go restBs [] [] done doneExp doneNW
    go branches expandedSets nextWorlds [] [] []

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
  intExpandBranches [initialBranch] [[]] [1] fuel isIntuitionisticallyClosed

/-- The minimal propositional tableau decision procedure.

Identical to the intuitionistic tableau but uses `MinimalClosure` instead:
a branch closes only when T(p) and F(p) coexist at the same world for atomic p.

- Returns `closed` iff `φ` is minimally valid (MValid).
- Returns `openBranch b` iff `φ` is not minimally valid. -/
def minimalTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  let initialBranch : IBranch Atom := [⟨.neg, φ, 0⟩]
  let fuel := 2 ^ (2 * φ.complexity + 2)
  intExpandBranches [initialBranch] [[]] [1] fuel isMinimallyClosed

end Cslib.Logic.PL

end
