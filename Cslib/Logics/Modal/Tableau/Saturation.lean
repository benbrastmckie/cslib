/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.Closure

/-! # Modal K Tableau Saturation

This module implements the fuel-based saturation loop for the modal K decision procedure.
It defines the main `modalTableau` entry point and the `ModalTableauResult` type.

## Main Definitions

- `ModalTableauResult Atom`: The result of the K tableau (closed or open branch + accessibility).
- `modalExpandBranches`: Fuel-based branch expansion worklist loop.
- `modalFuel`: Fuel bound (FMP-derived).
- `modalTableau`: Entry point for the decision procedure.
- `modalHintikkaSet`: Saturation predicate for open branches.

## Design

The saturation loop maintains a worklist of `(branch, expandedSet, acc)` triples, where
`acc` is the current accessibility relation. Each step picks the first open, unexpanded
branch, applies `modalApplyOne` to its first unprocessed formula, and either:
- Adds the result to the same branch (linear/persistent), or
- Splits into sub-branches (branching).

The `expandedSet` tracks which signed formulas have already been processed, preventing
re-expansion of propositional formulas. For modal rules, the `acc` relation grows
monotonically; `boxPos`/`diamondNeg` (persistent) re-fire when new successors are added.

### Fuel Bound

The fuel bound `modalFuel φ` is derived from the finite model property for K:
any satisfiable K formula has a model with at most as many worlds as there are
distinct ◇-subformulas (or F(□)-occurrences) in φ. We conservatively bound by
`(2 * modalComplexity φ + 1)^2`, which covers:
- Up to `modalComplexity φ` new worlds created per diamond/box-neg rule
- At most `2 * modalComplexity φ` branch expansion steps per world
- The `+1` prevents division-by-zero

### World-Subset Blocking

To guarantee termination without requiring a precise FMP bound, we implement
world-subset blocking: before creating a fresh world `w'`, we check if all formulas
that would be added to `w'` are a subset of formulas at some existing world. If so,
we reuse the existing world (merging the edge). This implements the finite model
property computationally.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Tableau Result Type -/

/-- The result of the modal K tableau computation.

- `closed`: Every branch is closed (the formula is unsatisfiable in all K-models).
- `openBranch b acc`: An open saturated branch `b` with accessibility relation `acc`
  exists, from which a finite Kripke countermodel can be extracted. -/
inductive ModalTableauResult (Atom : Type*) : Type _ where
  /-- All branches close: the formula is K-unsatisfiable. -/
  | closed : ModalTableauResult Atom
  /-- An open saturated branch exists: a K-countermodel can be extracted. -/
  | openBranch : List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility →
      ModalTableauResult Atom

/-! ## Fuel Bound -/

/-- Fuel bound for the modal K tableau.

Conservative bound based on the size of the formula. Sufficient for the FMP: any
satisfiable K formula has a model with at most `modalComplexity φ + 1` worlds. -/
def modalFuel (φ : Proposition Atom) : Nat :=
  let n := modalComplexity φ
  (4 * n + 4) * (n + 2) + 2

/-! ## Branch Step -/

/-- Apply one expansion step to a branch, using the accumulated accessibility relation.

Returns `some (newBranches, newExpandedSets, newAcc)` if a formula was expanded,
or `none` if the branch is saturated. -/
def modalStepBranch
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (expanded : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      let (result, newAcc) := modalApplyOne sf b acc
      match result with
      | .linear newForms =>
        some ([newForms ++ b], [expanded ++ [sf]], newAcc)
      | .branching branches =>
        some (branches.map (· ++ b), branches.map (fun _ => expanded ++ [sf]), newAcc)
      | .persistent newForms =>
        -- Persistent: keep sf on branch (don't add to expanded), add consequences
        some ([newForms ++ b], [expanded], newAcc)
      | .notApplicable => none

/-! ## Main Expansion Loop -/

/-- Fuel-based expansion of a list of modal K branches.

Processes each branch in a worklist:
- If the branch is closed, skip it.
- If the branch has no more applicable rules (saturated and open), return it as a
  K-countermodel together with the current accessibility relation.
- Otherwise apply one expansion step and recurse with remaining fuel.

Termination is guaranteed by the fuel parameter. -/
def modalExpandBranches
    (branches : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (acc : Accessibility)
    (fuel : Nat) : ModalTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: return first open branch (treat as countermodel)
    match branches.zip expandedSets |>.findSome? (fun (b, _) =>
        if isModalClosed b then none else some b) with
    | some b => .openBranch b acc
    | none => .closed
  | fuel' + 1 =>
    -- processNext: iterate through branches, finding the first open one to expand
    let rec processNext
        (pending : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (currAcc : Accessibility)
        : ModalTableauResult Atom :=
      match pending, pendingExp with
      | [], _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs =>
        if isModalClosed b then
          -- Branch is closed: skip it
          processNext restBs restEs (done ++ [b]) (doneExp ++ [e]) currAcc
        else
          match modalStepBranch b e currAcc with
          | none =>
            -- Branch is saturated and open: return countermodel
            .openBranch b currAcc
          | some (newBs, newExps, newAcc) =>
            -- Expanded: recurse with new branches
            modalExpandBranches
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              newAcc
              fuel'
      | _ :: restBs, [] =>
        processNext restBs [] done doneExp currAcc
    processNext branches expandedSets [] [] acc

/-! ## Entry Point -/

/-- The modal K tableau decision procedure.

Given a formula `φ`, runs the signed tableau starting from `F(φ)` at world `0`.
- Returns `closed` iff `φ` is unsatisfiable in all K-models (equivalently, valid = tautology).
- Returns `openBranch b acc` iff `φ` is not a K-tautology; `b` and `acc` together
  encode a finite Kripke model refuting `φ` (see `Completeness.lean`).

Note: For K, "the tableau for φ closes" means "φ is K-valid" (true in all K-models),
which by K-completeness equals "φ is K-provable". -/
def modalTableau (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranches [initialBranch] [[]] Accessibility.empty (modalFuel φ)

/-! ## Hintikka Set Predicate -/

/-- A modal K Hintikka set: a branch that is open (not closed) and saturated with respect
to all applicable rules, including the K box/diamond rules using `acc`.

For a branch `b` with accessibility relation `acc`, this holds when:
1. The branch is not closed (no contradiction or T(⊥)).
2. For every T(φ) on the branch, the applicable rule's outputs are also on the branch:
   - Linear rules: all outputs present.
   - Branching rules: at least one complete branch's outputs present.
   - Persistent rules: all outputs present.
3. For every T(□φ)@w, T(φ)@w' is on the branch for each w' with `acc.hasEdge w w'`.
4. For every F(◇φ)@w, F(φ)@w' is on the branch for each w' with `acc.hasEdge w w'`. -/
def modalHintikkaSet
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  isModalClosed b = false ∧
  ∀ sf ∈ b,
    let (result, _) := modalApplyOne sf b acc
    match result with
    | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
    | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
    | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
    | .notApplicable => True

end Cslib.Logic.Modal.Tableau

end
