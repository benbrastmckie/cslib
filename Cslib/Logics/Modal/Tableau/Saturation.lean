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
- `modalHintikkaSetGen`: `modalHintikkaSet`, generalized over an abstract `apply : RuleApply Atom`.
  Spec-free (no `RuleApplicationSpec` obligation) -- lives here, upstream of
  `GenericDriver.lean`, precisely so any system (including S4, which discharges no spec) can
  consume the generic Hintikka-set *statement shape*.
- `RuleApplySt`, `modalStepBranchGenSt`, `modalExpandBranchesGenSt`, `modalTableauGenSt`: the
  State-Threading Ladder -- `RuleApply`/`modalStepBranchGen`/`modalExpandBranchesGen`/
  `modalTableauGen`, each generalized with an extra threaded state parameter `σ`, bridged back to
  the stateless driver at `σ := Unit` by `modalStepBranchGen_eq_St`,
  `modalExpandBranchesGen_eq_St`, and `modalTableauGen_eq_St`.

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
`modalNextWorld b` whose index exceeds all labels in `b` (`diamondPos` is a
genuinely-firing native rule, not dead code under the old Lukasiewicz encoding where
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

/-- **Generic Hintikka set**: `modalHintikkaSet`, generalized over an abstract
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

/-- Bridge: `modalHintikkaSet` is exactly `modalHintikkaSetGen modalApplyOne`. Closes
by `rfl`, confirming the substitution in `modalHintikkaSetGen` is faithful. Lets K's
`modalTableau_complete` recover the concrete `modalHintikkaSet` form from a generic conclusion. -/
theorem modalHintikkaSet_eq (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : modalHintikkaSet b acc = modalHintikkaSetGen modalApplyOne b acc := rfl

/-! ## State-Threading Ladder

A purely additive generalization of the `RuleApply`/`modalStepBranchGen`/`modalExpandBranchesGen`/
`modalTableauGen` driver above, threading an extra abstract state value `σ` through every step
(`RuleApplySt`/`modalStepBranchGenSt`/`modalExpandBranchesGenSt`/`modalTableauGenSt`), together
with the three bridge theorems establishing that the state-threaded driver at `σ := Unit`,
lifted via `liftRuleApply`, computes the same result as the stateless driver
(`modalStepBranchGen_eq_St`/`modalExpandBranchesGen_eq_St`/`modalTableauGen_eq_St`).

The ladder now has a landed consumer: `modalExpandBranchesS4Keyed` (`LoopChecking.lean`) is
bridged onto `modalExpandBranchesGenSt` via `modalExpandBranchesGenSt_eq_S4Keyed`, instantiated
at the keyed `RuleApplySt` rule `modalApplyOneS4KeyedSt` (threading `keyss : List σ`, with
`σ := List (WorldIndex × Finset (Sign × Proposition Atom))` as the abstract state), and the
migration is additive -- `modalApplyOneS4Keyed`, `modalStepBranchS4Keyed`, and
`modalExpandBranchesS4Keyed` themselves are untouched. The KeyedOrdered driver
(`modalStepBranchS4KeyedOrdered`/`modalExpandBranchesS4KeyedOrdered`) remains unmigrated: it is
structurally impossible against this ladder as it stands, since `modalStepBranchGenSt` abstracts
over the *rule* passed to it, not over the *traversal* it performs, while the ordered driver's
minting gate depends on a global, traversal-level property of the branch that no choice of rule
can express. -/

/-- The shape of a state-threading rule-application function: `RuleApply Atom`, generalized
with an extra state parameter `σ` that is read and written on every step alongside the
`Accessibility` relation. The argument order `RuleApplySt (Atom) [insts] (σ)` is deliberate:
fixing `Atom` and its instances first and abstracting only over `σ` makes `RuleApplySt Atom Unit`
read as "`RuleApply Atom`, state-threaded" rather than as an unrelated two-parameter family.
`σ` is left fully abstract here; the intended first instantiation is a `keyss`-style list carried
alongside `accs` by `modalExpandBranchesS4Keyed` (see `modalStepBranchGenSt`'s docstring), but
nothing in this ladder commits to that shape.

Carries `@[nolint unusedArguments]` for the same reason as `RuleApply`: `abbrev` unfolds to a
function type mentioning none of `Atom`, `DecidableEq Atom`, or `Hashable Atom` in its body
(they appear only inside `SignedFormula (Proposition Atom) WorldIndex`, which the linter does
not trace through), so the environment linter would otherwise flag them as unused. -/
@[nolint unusedArguments]
abbrev RuleApplySt (Atom : Type*) [DecidableEq Atom] [Hashable Atom] (σ : Type*) : Type _ :=
  SignedFormula (Proposition Atom) WorldIndex →
  List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → σ →
  RuleResult (Proposition Atom) WorldIndex × Accessibility × σ

/-- Lift a stateless rule into the trivial state-threading rule at `σ := Unit`, discarding the
threaded `Unit` value on every call and returning `()` unconditionally.

`RuleApply Atom` is **bridged into** `RuleApplySt Atom Unit` by this function, not equal to it:
`RuleApplySt Atom Unit` has an extra `Unit →` argument and an extra `× Unit` component in its
result, and neither `Unit → X = X` nor `X × Unit = X` holds definitionally, so
`RuleApply Atom = RuleApplySt Atom Unit` is not available as a `rfl`. Forcing that equality
would require editing `RuleApply` itself, which the purely-additive constraint on this ladder
forbids and which would risk breaking the driver `rfl` bridges downstream of it. `liftRuleApply`
plus the three theorems below (`modalStepBranchGen_eq_St`, `modalExpandBranchesGen_eq_St`,
`modalTableauGen_eq_St`) is the actual relationship: an explicit embedding, proved compatible at
each level of the driver. -/
def liftRuleApply (apply : RuleApply Atom) : RuleApplySt Atom Unit :=
  fun sf b acc _ => ((apply sf b acc).1, (apply sf b acc).2, ())

/-- State-threading one-step branch expansion: `modalStepBranchGen`, generalized to thread a
state value `st : σ` through the single call to `apply`, returning the (possibly updated) state
alongside the new branches/expanded sets/accessibility relation.

The state is threaded **per-step**, matching how `modalExpandBranchesGenSt` below threads it
**per-branch** (as `sts : List σ` parallel to `accs`): this shape is forced by the intended first
consumer `modalExpandBranchesS4Keyed`, which carries a `keyss : List σ` list parallel to `accs`
and propagates one updated `keys'` to every child branch produced by a split, exactly as `newAcc`
is propagated to every child today. When the probed formula is `.notApplicable`, the state `st`
is discarded exactly as `.notApplicable`'s `newAcc` is discarded today (the whole call returns
`none` and neither is ever consulted) — no behavioural divergence from the stateless driver. -/
def modalStepBranchGenSt {σ : Type*} (apply : RuleApplySt Atom σ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (expanded : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (st : σ) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility × σ) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      let (result, newAcc, newSt) := apply sf b acc st
      match result with
      | .linear newForms =>
        some ([newForms ++ b], [expanded ++ [sf]], newAcc, newSt)
      | .branching branches =>
        some (branches.map (· ++ b), branches.map (fun _ => expanded ++ [sf]), newAcc, newSt)
      | .persistent newForms =>
        some ([newForms ++ b], [expanded], newAcc, newSt)
      | .notApplicable => none

/-- `Option.map` commutes out of `List.findSome?`: mapping `g` over the result of a search with
`f` is the same as searching with `f` post-composed with `some ∘ g`. A local helper for the
step-level bridge `modalStepBranchGen_eq_St` below — absent from Mathlib (`lean_loogle`, 0 hits)
and from the rest of the project (local search, 0 hits). It exists because
`modalStepBranchGen_eq_St` cannot be proved by induction on the branch `b`: the searched function
`fun sf => apply sf b acc st` closes over the *whole* branch `b` in its own definition, not just
the tail being recursed on, so an inductive hypothesis obtained that way would be about a
different (and useless) function. Factoring the `Option.map` that turns
`modalStepBranchGen`'s result into `modalStepBranchGenSt`'s result out of the `findSome?` via this
lemma, and closing the resulting per-element equality with a single `funext` instead, is the
working route. -/
theorem findSome?_map_comm {α β γ : Type*} (f : α → Option β) (g : β → γ) (l : List α) :
    l.findSome? (fun x => (f x).map g) = (l.findSome? f).map g := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h, ih]

/-- Step-level bridge: `modalStepBranchGenSt` at the lifted rule `liftRuleApply apply` and the
trivial state `()` computes the same result as `modalStepBranchGen apply`, up to appending a
final `()` component to the returned tuple (the projection-at-`σ := Unit` reading — the
state-threaded driver, instantiated at the trivial state type, is the stateless driver plus an
inert `Unit` tag). Proved via `findSome?_map_comm`, since `modalStepBranchGenSt`'s search closure
is exactly `modalStepBranchGen`'s search closure post-composed with the tuple-tagging map. -/
theorem modalStepBranchGen_eq_St (apply : RuleApply Atom)
    (b expanded : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchGenSt (liftRuleApply apply) b expanded acc () =
      (modalStepBranchGen apply b expanded acc).map
        (fun x => (x.1, x.2.1, x.2.2, ())) := by
  rw [modalStepBranchGenSt, modalStepBranchGen, ← findSome?_map_comm]
  congr 1
  funext sf
  by_cases h : expanded.any (· == sf)
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, liftRuleApply]
    cases hr : apply sf b acc with
    | mk result newAcc => cases result <;> simp

/-- State-threading fuel-based expansion of a list of modal branches: `modalExpandBranchesGen`,
generalized to carry a state list `sts : List σ` parallel to `branches`/`expandedSets`/`accs`
(with `sts.length = accs.length`, mirroring the existing `accs.length = branches.length`
invariant), threading each branch's own state value through `modalStepBranchGenSt` and
propagating the updated state to every child produced by a split via `List.replicate`, exactly as
`newAcc` is propagated today.

The inner `processNext` loop replicates `modalExpandBranchesGen.processNext`'s worklist shape
declaration-for-declaration — same `pending`/`done` split, same `isModalClosed` skip branch, same
`done ++ newBs ++ restBs` reassembly on expansion — with only `pendingSts`/`doneSts` added
alongside the existing accessibility lists. This shape match is what makes
`modalExpandBranchesGen_eq_St` provable by a direct induction mirroring `processNext`'s own
recursion, the same technique `modalExpandBranches_eq` already uses one level up. -/
def modalExpandBranchesGenSt {σ : Type*} (apply : RuleApplySt Atom σ)
    (branches : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (sts : List σ)
    (fuel : Nat) : ModalTableauResult Atom :=
  match fuel with
  | 0 =>
    match (branches.zip accs) |>.findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | some (b, a) => .openBranch b a
    | none => .closed
  | fuel' + 1 =>
    let rec @[nolint docBlame] processNext
        (pending : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingSts : List σ)
        (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneSts : List σ)
        : ModalTableauResult Atom :=
      match pending, pendingExp, pendingAccs, pendingSts with
      | [], _, _, _ => .closed
      | b :: restBs, e :: restEs, a :: restAs, s :: restSs =>
        if isModalClosed b then
          processNext restBs restEs restAs restSs (done ++ [b]) (doneExp ++ [e])
            (doneAccs ++ [a]) (doneSts ++ [s])
        else
          match modalStepBranchGenSt apply b e a s with
          | none => .openBranch b a
          | some (newBs, newExps, newAcc, newSt) =>
            modalExpandBranchesGenSt apply
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              (doneSts ++ List.replicate newBs.length newSt ++ restSs)
              fuel'
      | _, _, _, _ => .closed
    processNext branches expandedSets accs sts [] [] [] []

/-- Loop-level bridge: `modalExpandBranchesGen apply` computes the same result as
`modalExpandBranchesGenSt` at the lifted rule `liftRuleApply apply`, with the state list
instantiated as `accs.map fun _ => ()` rather than `List.replicate accs.length ()`.

The `.map` form is chosen over `List.replicate` because it is what makes the induction close
with **no side hypothesis**: `accs.map fun _ => ()` commutes definitionally through the loop's
three `++` appends and its `List.replicate newBs.length newAcc` (via `List.map_append` and
`List.map_replicate`), so at every recursive call the state list carried by the induction
hypothesis is *literally* `(the current accs list).map fun _ => ()` again, closed by `simpa`. A
`List.replicate accs.length ()`-based statement would instead need the auxiliary invariant
`sts.length = accs.length` threaded and re-established through both the pending and done lists
at every step, since `List.replicate` does not commute through `++` for free the way `.map` does
over already-paired lists — extra bookkeeping this proof does not need. -/
theorem modalExpandBranchesGen_eq_St (apply : RuleApply Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesGen apply branches expandedSets accs fuel =
      modalExpandBranchesGenSt (liftRuleApply apply) branches expandedSets accs
        (accs.map fun _ => ()) fuel := by
  induction fuel generalizing branches expandedSets accs with
  | zero =>
    simp only [modalExpandBranchesGen, modalExpandBranchesGenSt]
  | succ fuel' ih =>
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        modalExpandBranchesGen.processNext apply fuel' pending pendingExp pendingAccs done doneExp
            doneAccs =
          modalExpandBranchesGenSt.processNext (liftRuleApply apply) fuel' pending pendingExp
            pendingAccs (pendingAccs.map fun _ => ()) done doneExp doneAccs
            (doneAccs.map fun _ => ()) by
      have hkey := key branches expandedSets accs [] [] []
      simpa [modalExpandBranchesGen, modalExpandBranchesGenSt] using hkey
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs done doneExp doneAccs
      simp [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext]
    | cons b restBs ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
      cases pendingExp with
      | nil => simp [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext]
      | cons e restEs =>
        cases pendingAccs with
        | nil => simp [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext]
        | cons a restAs =>
          simp only [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext,
            List.map_cons]
          by_cases hc : isModalClosed b
          · simp only [hc, if_true]
            have := ih_inner restEs restAs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
            simpa using this
          · simp only [hc]
            rw [modalStepBranchGen_eq_St]
            cases hs : modalStepBranchGen apply b e a with
            | none => rfl
            | some x =>
              obtain ⟨newBs, newExps, newAcc⟩ := x
              simp only [Option.map_some]
              have := ih (done ++ newBs ++ restBs) (doneExp ++ newExps ++ restEs)
                (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              simpa using this

/-- State-threading entry point: `modalTableauGen`, generalized to take an explicit initial state
`st0 : σ` alongside the rule-application function, seeding the single initial branch's state
before handing off to `modalExpandBranchesGenSt`.

The initial state is a required explicit argument, not defaulted, because the intended first
consumer needs a non-trivial seed: `modalExpandBranchesS4Keyed`'s entry point seeds
`keys := [(0, ∅)]`, not `[]` (world `0` starts with an empty key set, not no key-set entry at
all). At `σ := Unit` the only possible value is `st0 = ()`, which is exactly what
`modalTableauGen_eq_St` below supplies. -/
def modalTableauGenSt {σ : Type*} (apply : RuleApplySt Atom σ) (st0 : σ)
    (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) := [⟨.neg, φ, 0⟩]
  modalExpandBranchesGenSt apply [initialBranch] [[]] [Accessibility.empty] [st0] (modalFuel φ)

/-- Entry-point bridge: `modalTableauGen apply φ` computes the same result as
`modalTableauGenSt (liftRuleApply apply) () φ`. The two-line corollary of the loop bridge
`modalExpandBranchesGen_eq_St`: both sides unfold to `modalExpandBranchesGen`/
`modalExpandBranchesGenSt` applied to the identical initial worklist, and
`(([Accessibility.empty]).map fun _ => ()) = [()]` closes the state-list mismatch. -/
theorem modalTableauGen_eq_St (apply : RuleApply Atom) (φ : Proposition Atom) :
    modalTableauGen apply φ = modalTableauGenSt (liftRuleApply apply) () φ := by
  simp only [modalTableauGen, modalTableauGenSt]
  exact modalExpandBranchesGen_eq_St _ _ _ _ _

end Cslib.Logic.Modal.Tableau

end
