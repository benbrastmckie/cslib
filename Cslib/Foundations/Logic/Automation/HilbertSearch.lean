/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.ProofSystem
public import Cslib.Foundations.Logic.Theorems.Combinators
public import Cslib.Foundations.Logic.Theorems.Modal.Basic

/-! # Hilbert Proof-Search Tactic

This module implements `hilbert_search`, a bounded depth-first proof-search tactic
for Hilbert-style proof systems in CSLib.

## Architecture

The tactic uses MetaM's `MVarId.apply` + `observing?` for backtracking search,
eliminating the need for formula-decomposition typeclasses. Lean's unifier handles
goal matching transparently, and typeclass availability is checked implicitly by
whether `apply` succeeds.

### Search Strategy (Four-Priority Stratification)

1. **Assumption lookup**: Scan local context for hypotheses of type `DerivableIn S phi`
2. **Zero-subgoal axioms**: Axiom typeclasses (ImplyK, ImplyS, K, T, 4, B, 5, D, etc.)
3. **One-subgoal derived rules**: Necessitation, box_mono, identity, b_combinator
4. **Two-subgoal rules**: MP (modus ponens), imp_trans (tried last to avoid explosion)

### Fuel Parameter

Default fuel is 30, which covers observed proof depths in CSLib (max ~20 for `app2`).
Each rule application decrements fuel. Depth exhaustion produces an informative error
message with a remediation hint.

### Trace Class

Enable debugging output with:
```
set_option trace.Cslib.Logic.hilbertSearch true
```

## Usage

```lean
example [ModalHilbert S (F := F)] (phi : F) :
    InferenceSystem.DerivableIn S (HasImp.imp phi phi) := by
  hilbert_search

example [ModalHilbert S (F := F)] (phi psi : F)
    (h : InferenceSystem.DerivableIn S (HasImp.imp phi psi)) :
    InferenceSystem.DerivableIn S (HasImp.imp (HasBox.box phi) (HasBox.box psi)) := by
  hilbert_search
```
-/

public meta section

open Lean Meta Elab Tactic

namespace Cslib.Logic.Automation

/-- Register the trace class for debugging the `hilbert_search` tactic.
Enable with `set_option trace.Cslib.Logic.hilbertSearch true`. -/
initialize registerTraceClass `Cslib.Logic.hilbertSearch

/-- The zero-subgoal axiom and theorem names (propositional, modal, temporal, bimodal).
These are tried by direct `apply` on the goal — success with no remaining subgoals
(after filtering type-level universe goals) means the goal is closed. -/
private def zeroSubgoalAxioms : Array Name := #[
  -- Propositional axioms
  ``HasAxiomImplyK.implyK,
  ``HasAxiomImplyS.implyS,
  ``HasAxiomEFQ.efq,
  ``HasAxiomPeirce.peirce,
  -- And/Or axioms
  ``HasAxiomAndI.andI,
  ``HasAxiomAndE1.andE1,
  ``HasAxiomAndE2.andE2,
  ``HasAxiomOrI1.orI1,
  ``HasAxiomOrI2.orI2,
  ``HasAxiomOrE.orE,
  -- Modal axioms
  ``HasAxiomK.K,
  ``HasAxiomT.T,
  ``HasAxiom4.four,
  ``HasAxiomB.B,
  ``HasAxiom5.five,
  ``HasAxiomD.D,
  -- Temporal axioms (serial)
  ``HasAxiomSerialFuture.serialFuture,
  ``HasAxiomSerialPast.serialPast,
  -- Temporal axioms (monotonicity)
  ``HasAxiomLeftMonoUntilG.leftMonoUntilG,
  ``HasAxiomLeftMonoSinceH.leftMonoSinceH,
  ``HasAxiomRightMonoUntil.rightMonoUntil,
  ``HasAxiomRightMonoSince.rightMonoSince,
  -- Temporal axioms (connectedness)
  ``HasAxiomConnectFuture.connectFuture,
  ``HasAxiomConnectPast.connectPast,
  -- Temporal axioms (enrichment, accumulation, absorption)
  ``HasAxiomEnrichmentUntil.enrichmentUntil,
  ``HasAxiomEnrichmentSince.enrichmentSince,
  ``HasAxiomSelfAccumUntil.selfAccumUntil,
  ``HasAxiomSelfAccumSince.selfAccumSince,
  ``HasAxiomAbsorbUntil.absorbUntil,
  ``HasAxiomAbsorbSince.absorbSince,
  -- Temporal axioms (linearity, eventuality, equivalence)
  ``HasAxiomLinearUntil.linearUntil,
  ``HasAxiomLinearSince.linearSince,
  ``HasAxiomUntilF.untilF,
  ``HasAxiomSinceP.sinceP,
  ``HasAxiomTempLinearity.tempLinearity,
  ``HasAxiomTempLinearityPast.tempLinearityPast,
  ``HasAxiomFUntilEquiv.fUntilEquiv,
  ``HasAxiomPSinceEquiv.pSinceEquiv,
  -- Bimodal interaction axiom
  ``HasAxiomMF.MF,
  -- Derived propositional theorems (zero-hypothesis, all formula args unified by `apply`)
  ``Cslib.Logic.Theorems.Combinators.identity,
  ``Cslib.Logic.Theorems.Combinators.b_combinator
]

/-- The one-subgoal derived rule names.
These rules take a single derivability hypothesis and produce a derivability conclusion. -/
private def oneSubgoalRules : Array Name := #[
  ``Necessitation.nec,
  ``TemporalNecessitation.tempNec,
  ``TemporalNecessitation.tempNecPast,
  ``Cslib.Logic.Theorems.Modal.Basic.box_mono
]

/-- The two-subgoal rule names (tried last to avoid combinatorial explosion).
These rules take two derivability hypotheses to produce a derivability conclusion. -/
private def twoSubgoalRules : Array Name := #[
  ``Cslib.Logic.Theorems.Combinators.imp_trans,
  ``ModusPonens.mp
]

/-- Try to apply `name` to `goal`. Returns `some subgoals` on success, `none` on failure.
Uses `mkConstWithFreshMVarLevels` for universe polymorphism and
`ApplyConfig { newGoals := .nonDependentOnly }` to filter type-level goals. -/
private def tryApplyName (goal : MVarId) (name : Name) : MetaM (Option (List MVarId)) :=
  observing? do
    let c ← mkConstWithFreshMVarLevels name
    goal.apply c { newGoals := .nonDependentOnly }

/-- Core bounded DFS search function.

Tries to close `goal : MVarId` within `fuel` steps by:
1. Local assumption lookup
2. Zero-subgoal axiom application
3. One-subgoal rule application with recursive search
4. Two-subgoal rule application with recursive search

Uses `observing?` for checkpoint/rollback backtracking.
Uses `visited : HashSet Expr` for cycle detection (same goal type on the current path).

Returns `true` if the goal was closed, `false` if all rules failed. -/
partial def hilbertSearchCore (goal : MVarId) (fuel : Nat)
    (visited : ExprSet) : MetaM Bool := do
  if fuel == 0 then
    trace[Cslib.Logic.hilbertSearch] "fuel exhausted"
    return false
  let goalTy ← goal.getType
  let goalTyNorm ← whnf goalTy
  if visited.contains goalTyNorm then
    trace[Cslib.Logic.hilbertSearch] "cycle detected: {goalTy}"
    return false
  let visited' := visited.insert goalTyNorm
  -- Priority 1: Assumption lookup
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    if ← isDefEq decl.type goalTy then
      goal.assign decl.toExpr
      trace[Cslib.Logic.hilbertSearch] "closed by assumption: {decl.userName}"
      return true
  -- Priority 2: Zero-subgoal axioms
  let mut closed2 := false
  for name in zeroSubgoalAxioms do
    if closed2 then break
    if let some subgoals ← tryApplyName goal name then
      if subgoals.isEmpty then
        trace[Cslib.Logic.hilbertSearch] "closed by axiom: {name}"
        closed2 := true
  if closed2 then return true
  -- Priority 3: One-subgoal derived rules
  -- We use savepoint to backtrack if the recursive search fails
  let mctxBefore ← getMCtx
  let mut closed3 := false
  for name in oneSubgoalRules do
    if closed3 then break
    if let some subgoals ← tryApplyName goal name then
      let pending ← subgoals.filterM (fun g => do
        let assigned ← g.isAssigned
        let delayAssigned ← g.isDelayedAssigned
        return !assigned && !delayAssigned)
      match pending with
      | [] =>
        trace[Cslib.Logic.hilbertSearch] "closed by one-subgoal rule (auto): {name}"
        closed3 := true
      | [sg] =>
        let ok ← hilbertSearchCore sg (fuel - 1) visited'
        if ok then
          trace[Cslib.Logic.hilbertSearch] "closed by one-subgoal rule: {name}"
          closed3 := true
        else
          -- Backtrack: restore MetaContext
          setMCtx mctxBefore
      | _ => pure ()  -- Multiple subgoals: skip (restore is automatic via observing? scoping)
  if closed3 then return true
  -- Priority 4: Two-subgoal rules (tried last)
  let mctxBefore4 ← getMCtx
  let mut closed4 := false
  for name in twoSubgoalRules do
    if closed4 then break
    if let some subgoals ← tryApplyName goal name then
      let pending ← subgoals.filterM (fun g => do
        let assigned ← g.isAssigned
        let delayAssigned ← g.isDelayedAssigned
        return !assigned && !delayAssigned)
      -- Try to close all pending subgoals recursively
      let mut allOk := true
      for sg in pending do
        if allOk then
          let ok ← hilbertSearchCore sg (fuel - 1) visited'
          if !ok then allOk := false
      if allOk then
        trace[Cslib.Logic.hilbertSearch] "closed by two-subgoal rule: {name}"
        closed4 := true
      else
        setMCtx mctxBefore4
  return closed4

/-- `hilbert_search` tactic: bounded depth-first search for Hilbert-style derivations.

Searches for a proof of the current goal (which should be of the form
`InferenceSystem.DerivableIn S phi`) using the Hilbert-style proof system
registered for `S`. The search uses a stratified rule ordering (assumptions
first, then axioms, then derived rules, then modus ponens) to avoid
combinatorial blowup.

**Syntax**: `hilbert_search` uses default fuel 30; `hilbert_search N` uses fuel N.

**Trace**: Enable `set_option trace.Cslib.Logic.hilbertSearch true` for debugging.

**Error**: On exhaustion, produces an informative error with a remediation hint. -/
elab "hilbert_search" n:(num)? : tactic => do
  let fuel : Nat := match n with
    | some numStx => numStx.getNat
    | none        => 30
  let goal ← getMainGoal
  let goalTy ← goal.getType
  trace[Cslib.Logic.hilbertSearch] "hilbert_search (fuel={fuel}): {goalTy}"
  let ok ← hilbertSearchCore goal fuel (∅ : Lean.ExprSet)
  if ok then
    replaceMainGoal []
  else
    throwTacticEx `hilbert_search goal
      m!"hilbert_search failed: could not prove\n  {goalTy}\nat fuel={fuel}.\
      \nTry increasing the fuel: `hilbert_search {fuel * 2}`"

end Cslib.Logic.Automation

end -- meta section
