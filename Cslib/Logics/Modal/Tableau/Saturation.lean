/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Closure
public import Cslib.Logics.Modal.Tableau.Rules

/-! # Modal K Tableau Saturation

This module implements the fuel-based saturation loop for the modal K decision procedure.
It defines the main `modalTableau` entry point and the `ModalTableauResult` type.

## Main Definitions

- `ModalTableauResult Atom`: The result of the K tableau (closed or open branch + accessibility).
- `modalExpandBranches`: Fuel-based branch expansion worklist loop.
- `modalFuel`: Fuel bound (FMP-derived).
- `modalTableau`: Entry point for the decision procedure.
- `modalHintikkaSet`: Saturation predicate for open branches.
- `modalHintikkaSetGen`: `modalHintikkaSet`, generalized over an abstract `apply : RuleApply Atom`
  (task 510). Spec-free (no `RuleApplicationSpec` obligation) -- lives here, upstream of
  `GenericDriver.lean`, precisely so any system (including S4, which discharges no spec) can
  consume the generic Hintikka-set *statement shape*.

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

The fuel bound `modalFuel φ` is a triple-exponential closed form over `modalComplexity φ`
only: `3 ^ (4 * (2n+1) * ((2n+1)^(n+1) + 1))` where `n = modalComplexity φ`. It dominates
the base-3 counting termination measure `modalExpMeasure` over the finite world-bounded
signed-formula universe `modalUniverse φ` defined in `FmpMeasure.lean` (which imports this
module, so `modalFuel` cannot itself reference `modalUniverse` without an import cycle).
See `FmpMeasure.modalExpMeasure_entry_le_fuel` for the bridge lemma establishing
sufficiency: the initial worklist measure is `≤ modalFuel φ`, and each saturation step
strictly decreases the measure by at least 1, so `fuel = 0` is reached only once every
branch is closed or saturated.

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

Triple-exponential closed form over `modalComplexity φ` only (a `modalUniverse`-based
`3 ^ (2 * |modalUniverse φ|)` bound would create an import cycle, since `modalUniverse`
lives in `FmpMeasure.lean`, which imports this module). Sufficiency (not tightness) is
the requirement: `FmpMeasure.modalExpMeasure_entry_le_fuel` proves this closed form
dominates the counting-measure entry bound `3 ^ (2 * |modalUniverse φ|)`. -/
def modalFuel (φ : Proposition Atom) : Nat :=
  let n := modalComplexity φ
  3 ^ (4 * (2 * n + 1) * ((2 * n + 1) ^ (n + 1) + 1))

/-! ## Rule-Application Function Shape -/

/-- The shape of a rule-application function, matching `modalApplyOne`'s signature. Any
function of this type can be threaded through the generic driver `modalStepBranchGen` /
`modalExpandBranchesGen` / `modalTableauGen` below. -/
@[nolint unusedArguments]
abbrev RuleApply (Atom : Type*) [DecidableEq Atom] [Hashable Atom] : Type _ :=
  SignedFormula (Proposition Atom) WorldIndex →
  List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility →
  RuleResult (Proposition Atom) WorldIndex × Accessibility

/-! ## Branch Step -/

/-- Generic one-step branch expansion, parametrized over an abstract rule-application
function `apply` with `modalApplyOne`'s signature. `modalStepBranch` (K) is the trivial
instantiation `modalStepBranchGen modalApplyOne` (see `modalStepBranch_eq`); T's driver
instantiates it with `modalApplyOneT` (see `TDriver.lean`).

Returns `some (newBranches, newExpandedSets, newAcc)` if a formula was expanded,
or `none` if the branch is saturated. -/
def modalStepBranchGen
    (apply : RuleApply Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (expanded : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      let (result, newAcc) := apply sf b acc
      match result with
      | .linear newForms =>
        some ([newForms ++ b], [expanded ++ [sf]], newAcc)
      | .branching branches =>
        some (branches.map (· ++ b), branches.map (fun _ => expanded ++ [sf]), newAcc)
      | .persistent newForms =>
        -- Persistent: keep sf on branch (don't add to expanded), add consequences
        some ([newForms ++ b], [expanded], newAcc)
      | .notApplicable => none

/-- Apply one expansion step to a branch, using the accumulated accessibility relation.
Kept as the exact original definition (not a wrapper around `modalStepBranchGen`) so that
every existing K proof's `simp only [modalStepBranch]`/`unfold modalStepBranch` continues to
unfold to the identical normal form (14+ call sites across `Completeness.lean`,
`CompletenessLoop.lean`, `FmpMeasure.lean`, `Soundness.lean`, `SoundnessStep.lean` rely on this
exact unfold shape). `modalStepBranch` and `modalStepBranchGen modalApplyOne` compute the same
result on every input; see `modalStepBranch_eq`.

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

/-- `modalStepBranch` is the trivial instantiation of `modalStepBranchGen` at
`apply := modalApplyOne`. Zero-regression bridge lemma: all downstream K proofs may rewrite
via this equation to reach the generic driver. -/
theorem modalStepBranch_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (expanded : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    modalStepBranch b expanded acc = modalStepBranchGen modalApplyOne b expanded acc := rfl

/-! ## Main Expansion Loop -/

/-- Generic fuel-based expansion of a list of modal branches, parametrized over an abstract
rule-application function `apply`. `modalExpandBranches` (K) is the trivial instantiation
`modalExpandBranchesGen modalApplyOne` (see `modalExpandBranches_eq`).

Processes each branch in a worklist:
- If the branch is closed, skip it.
- If the branch has no more applicable rules (saturated and open), return it as a
  countermodel together with the branch-local accessibility relation.
- Otherwise apply one expansion step and recurse with remaining fuel.

Each branch carries its own `Accessibility` relation in the parallel list `accs`
(with `accs.length = branches.length`), so an existential-rule edge fired on one
branch cannot pollute sibling branches.

Termination is guaranteed by the fuel parameter. -/
def modalExpandBranchesGen
    (apply : RuleApply Atom)
    (branches : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (fuel : Nat) : ModalTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: return first open branch with its local accessibility relation
    match (branches.zip accs) |>.findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | some (b, a) => .openBranch b a
    | none => .closed
  | fuel' + 1 =>
    -- processNext: iterate through branches, finding the first open one to expand
    let rec @[nolint docBlame] processNext
        (pending : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        : ModalTableauResult Atom :=
      match pending, pendingExp, pendingAccs with
      | [], _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, a :: restAs =>
        if isModalClosed b then
          -- Branch is closed: skip it, carry its acc to done
          processNext restBs restEs restAs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
        else
          match modalStepBranchGen apply b e a with
          | none =>
            -- Branch is saturated and open: return with this branch's local acc
            .openBranch b a
          | some (newBs, newExps, newAcc) =>
            -- Expanded: recurse with new branches using newAcc for each child
            modalExpandBranchesGen apply
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              fuel'
      | _, _, _ => .closed  -- malformed (length invariant rules this out)
    processNext branches expandedSets accs [] [] []

/-- Fuel-based expansion of a list of modal K branches. Kept as the exact original recursive
definition (with its own `modalExpandBranches.processNext` well-founded-recursion helper, which
`Soundness.lean`/`CompletenessLoop.lean` reference by name) rather than a wrapper around
`modalExpandBranchesGen`, so every existing K proof continues to see the identical elaborated
term with zero regression. `modalExpandBranches` and `modalExpandBranchesGen modalApplyOne`
compute the same result on every input; see `modalExpandBranches_eq`.

Processes each branch in a worklist:
- If the branch is closed, skip it.
- If the branch has no more applicable rules (saturated and open), return it as a
  K-countermodel together with the branch-local accessibility relation.
- Otherwise apply one expansion step and recurse with remaining fuel.

Each branch carries its own `Accessibility` relation in the parallel list `accs`
(with `accs.length = branches.length`), so an existential-rule edge fired on one
branch cannot pollute sibling branches.

Termination is guaranteed by the fuel parameter. -/
def modalExpandBranches
    (branches : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (fuel : Nat) : ModalTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: return first open branch with its local accessibility relation
    match (branches.zip accs) |>.findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | some (b, a) => .openBranch b a
    | none => .closed
  | fuel' + 1 =>
    -- processNext: iterate through branches, finding the first open one to expand
    let rec @[nolint docBlame] processNext
        (pending : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        : ModalTableauResult Atom :=
      match pending, pendingExp, pendingAccs with
      | [], _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, a :: restAs =>
        if isModalClosed b then
          -- Branch is closed: skip it, carry its acc to done
          processNext restBs restEs restAs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
        else
          match modalStepBranch b e a with
          | none =>
            -- Branch is saturated and open: return with this branch's local acc
            .openBranch b a
          | some (newBs, newExps, newAcc) =>
            -- Expanded: recurse with new branches using newAcc for each child
            modalExpandBranches
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              fuel'
      | _, _, _ => .closed  -- malformed (length invariant rules this out)
    processNext branches expandedSets accs [] [] []

/-- `modalExpandBranches` computes the same result as the trivial instantiation of
`modalExpandBranchesGen` at `apply := modalApplyOne`. Zero-regression bridge lemma: any proof
about the generic driver at `modalApplyOne` transports to a K fact via this equation (and
conversely). Proved by induction on `fuel`, with an inner induction on the worklist (mirroring
each `processNext`'s own recursion) since `modalStepBranch b e a` and
`modalStepBranchGen modalApplyOne b e a` are definitionally equal (`modalStepBranch_eq`). -/
theorem modalExpandBranches_eq
    (branches : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (fuel : Nat) :
    modalExpandBranches branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOne branches expandedSets accs fuel := by
  induction fuel generalizing branches expandedSets accs with
  | zero => simp [modalExpandBranches, modalExpandBranchesGen]
  | succ fuel' ih =>
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        modalExpandBranches.processNext fuel' pending pendingExp pendingAccs done doneExp
            doneAccs =
          modalExpandBranchesGen.processNext modalApplyOne fuel' pending pendingExp pendingAccs
            done doneExp doneAccs by
      have hkey := key branches expandedSets accs [] [] []
      simpa [modalExpandBranches, modalExpandBranchesGen] using hkey
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs done doneExp doneAccs
      simp [modalExpandBranches.processNext, modalExpandBranchesGen.processNext]
    | cons b restBs ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
      cases pendingExp with
      | nil => simp [modalExpandBranches.processNext, modalExpandBranchesGen.processNext]
      | cons e restEs =>
        cases pendingAccs with
        | nil => simp [modalExpandBranches.processNext, modalExpandBranchesGen.processNext]
        | cons a restAs =>
          simp only [modalExpandBranches.processNext, modalExpandBranchesGen.processNext]
          by_cases hc : isModalClosed b
          · simp only [hc, if_true]
            exact ih_inner restEs restAs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
          · simp only [hc]
            rw [show modalStepBranch b e a = modalStepBranchGen modalApplyOne b e a from rfl]
            cases modalStepBranchGen modalApplyOne b e a with
            | none => rfl
            | some x =>
              obtain ⟨newBs, newExps, newAcc⟩ := x
              exact ih _ _ _

/-! ## Entry Point -/

/-- The modal decision procedure driven by an abstract rule-application function `apply`,
starting the signed tableau from `F(φ)` at world `0`. `modalTableau` (K) is the trivial
instantiation `modalTableauGen modalApplyOne` (see `modalTableau_eq`). -/
def modalTableauGen (apply : RuleApply Atom) (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranchesGen apply [initialBranch] [[]] [Accessibility.empty] (modalFuel φ)

/-- The modal K tableau decision procedure.

Given a formula `φ`, runs the signed tableau starting from `F(φ)` at world `0`.
- Returns `closed` iff `φ` is unsatisfiable in all K-models (equivalently, valid = tautology).
- Returns `openBranch b acc` iff `φ` is not a K-tautology; `b` and `acc` together
  encode a finite Kripke model refuting `φ` (see `Completeness.lean`).

Note: For K, "the tableau for φ closes" means "φ is K-valid" (true in all K-models),
which by K-completeness equals "φ is K-provable". Kept as the exact original definition (not a
wrapper around `modalTableauGen`) so that `simp only [modalTableau]` (used in
`Soundness.lean`) continues to unfold to the identical `modalExpandBranches [...] ...` normal
form; see `modalTableau_eq` for the (non-defeq) bridge to the generic driver. -/
def modalTableau (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranches [initialBranch] [[]] [Accessibility.empty] (modalFuel φ)

/-- `modalTableau` computes the same result as the trivial instantiation of `modalTableauGen`
at `apply := modalApplyOne`. Zero-regression bridge lemma. -/
theorem modalTableau_eq (φ : Proposition Atom) :
    modalTableau φ = modalTableauGen modalApplyOne φ := by
  simp only [modalTableau, modalTableauGen]
  exact modalExpandBranches_eq _ _ _ _

/-! ## Hintikka Set Predicate -/

/-- A modal K Hintikka set: a branch that is open (not closed) and saturated with respect
to all applicable rules, including the K box/diamond rules using `acc`.

For a branch `b` with accessibility relation `acc`, this holds when:
1. The branch is not closed (no contradiction or T(⊥)).
2. For every signed formula on the branch whose rule result is not boxNeg (`F(□φ)@w`) and
   not diamondPos (`T(◇φ)@w`), the rule outputs are present:
   - Linear rules: all outputs present on branch.
   - Branching rules: at least one complete sub-branch's outputs present.
   - Persistent rules: all outputs present (captures T(□φ)@w box-positive closure:
     `modalApplyOne` returns `.persistent (boxPropagation b acc φ w)`, which is empty
     iff all T(φ)@w' are already in `b`, so the persistent clause forces them in; and
     F(◇φ)@w diamondNeg closure similarly, via successor propagation).
3. For every `F(□φ)@w` on the branch, there exists a successor `w'` (with
   `acc.hasEdge w w' = true`) such that `F(φ)@w' ∈ b`.
4. For every `T(◇φ)@w` on the branch, there exists a successor `w'` (with
   `acc.hasEdge w w' = true`) such that `T(φ)@w' ∈ b`.

Conjuncts 3 and 4 are separate because `boxNeg`/`diamondPos` create a FRESH world
`modalNextWorld b` whose index exceeds all labels in `b` (task 441: `diamondPos` is now a
genuinely-firing native rule, no longer dead code under the old Lukasiewicz encoding where
`negOf?` always intercepted diamond-shaped formulas first -- see the historical note in
`Completeness.lean`'s `## Saturation Characterisation` section). Re-evaluating
`modalApplyOne` against the (larger) final branch would mint an even-fresher witness world
than the one actually recorded, so the standard linear/persistent membership condition
would be vacuously false for these two rules' outputs; conjuncts 3/4 instead assert the
*existence* of some valid witness successor already on the branch (not tied to the specific
world index `modalApplyOne` would recompute).

Note: T(□φ)@w box-positive and F(◇φ)@w diamond-negative closure are captured by the
persistent clause in conjunct 2: if the respective propagation list is non-empty, the
persistent condition forces the missing propagated formulas into `b`; if empty,
`notApplicable` and all successors already carry the propagated formula. -/
def modalHintikkaSet
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  isModalClosed b = false ∧
  (∀ sf ∈ b,
    let (result, _) := modalApplyOne sf b acc
    match sf.sign, sf.formula with
    | .neg, .box _ => True    -- F(□φ): fresh-world rule; handled by conjunct 3
    | .pos, .diamond _ => True  -- T(◇φ): fresh-world rule; handled by conjunct 4
    | _, _ =>
      match result with
      | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
      | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .notApplicable => True) ∧
  -- Box-negative witness: F(□φ)@w on the branch implies a successor world with F(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.neg, .box φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.neg, φ, w'⟩ ∈ b) ∧
  -- Diamond-positive witness: T(◇φ)@w on the branch implies a successor world with T(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.pos, .diamond φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.pos, φ, w'⟩ ∈ b)

/-- **Generic Hintikka set** (task 510): `modalHintikkaSet`, generalized over an abstract
`apply : RuleApply Atom`. A one-token substitution (`modalApplyOne ↦ apply` in conjunct 2's
`let (result, _) := apply sf b acc`); conjuncts 1, 3, 4 mention no rule function at all. This
definition is **spec-free** -- it depends on nothing from `RuleApplicationSpec`
(`GenericDriver.lean`) -- and lives here, upstream of `GenericDriver.lean`, so that any system
(including S4, which is explicitly excluded from discharging `RuleApplicationSpec`,
`GenericDriver.lean`'s module docstring) can consume the *statement shape* of a generic Hintikka
set without discharging the spec. `modalHintikkaSet` is retained unchanged (its `unfold`/
`simp only` call sites rely on its exact normal form, mirroring the deliberate
`modalStepBranch`/`modalStepBranchGen` + `modalStepBranch_eq` precedent above); see
`modalHintikkaSet_eq` for the bridge. -/
def modalHintikkaSetGen (apply : RuleApply Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  isModalClosed b = false ∧
  (∀ sf ∈ b,
    let (result, _) := apply sf b acc
    match sf.sign, sf.formula with
    | .neg, .box _ => True    -- F(□φ): fresh-world rule; handled by conjunct 3
    | .pos, .diamond _ => True  -- T(◇φ): fresh-world rule; handled by conjunct 4
    | _, _ =>
      match result with
      | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
      | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .notApplicable => True) ∧
  -- Box-negative witness: F(□φ)@w on the branch implies a successor world with F(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.neg, .box φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.neg, φ, w'⟩ ∈ b) ∧
  -- Diamond-positive witness: T(◇φ)@w on the branch implies a successor world with T(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.pos, .diamond φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.pos, φ, w'⟩ ∈ b)

/-- Bridge (task 510): `modalHintikkaSet` is exactly `modalHintikkaSetGen modalApplyOne`. Closes
by `rfl`, confirming the substitution in `modalHintikkaSetGen` is faithful. Lets K's
`modalTableau_complete` recover the concrete `modalHintikkaSet` form from a generic conclusion. -/
theorem modalHintikkaSet_eq (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : modalHintikkaSet b acc = modalHintikkaSetGen modalApplyOne b acc := rfl

end Cslib.Logic.Modal.Tableau

end
