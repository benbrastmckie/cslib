/-
Scratch probe for task 574, Phase 1 (divergence-attribution probe and variant selection).
NOT part of the Cslib library build -- compiled standalone via `lake env lean`. Zero lines of
this file land in Cslib/; it exists to convert design forks D3/D4 (see the plan's Decision
section) from argument into measured `#eval` output before any Cslib/ file is touched.

Compile with:
  lake env lean specs/574_tableau_calculus_repair_ancestor_blocking/scratch/DivergenceProbe.lean
-/

module

import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace DivergenceProbe

/-! ## Witness formula

`φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u1→v1) ∨ (u2→v2))`, complexity 9, the recorded divergence
witness (`Expansion.lean:482-526`). -/

def a : Proposition Nat := .atom 0
def b : Proposition Nat := .atom 1
def c : Proposition Nat := .atom 2
def d : Proposition Nat := .atom 3
def e : Proposition Nat := .atom 4
def f : Proposition Nat := .atom 5
def u1 : Proposition Nat := .atom 6
def v1 : Proposition Nat := .atom 7
def u2 : Proposition Nat := .atom 8
def v2 : Proposition Nat := .atom 9

def phi0 : Proposition Nat :=
  (((a → b) → c) ∧ ((d → e) → f)) → ((u1 → v1) ∨ (u2 → v2))

/-- Adapter reporting branch length / max label / distinct-label count, the three quantities
`Expansion.lean:494-501`'s table tabulates (max label only). -/
def worldStats : IntTableauResult Nat → String
  | .closed => "CLOSED"
  | .openBranch br =>
    let labels := br.map (·.label)
    let maxLabel := labels.foldl max 0
    let distinctLabels := labels.eraseDups.length
    s!"OPEN len={br.length} maxLabel={maxLabel} distinctLabels={distinctLabels}"

/-! ## Baseline row (fidelity check)

Calls the UNMODIFIED library `intExpandBranches` directly (bypassing `intFuel`'s astronomical
default, matching the divergence-witness note's own methodology at `Expansion.lean:494`). -/

def baselineRow (fuel : Nat) : String :=
  worldStats (intExpandBranches [[(⟨.neg, phi0, 0⟩ : ISF Nat)]] [[]] [1] [[]] fuel
    isIntuitionisticallyClosed)

#eval baselineRow 10
#eval baselineRow 20
#eval baselineRow 30
#eval baselineRow 40
#eval baselineRow 60
#eval baselineRow 80
#eval baselineRow 120

/-! ## Variant harness

Each variant is a local copy of `applyAllTImpRules` (persistence step, self-copy channel
optionally dropped) and `intFImpReuseWitness?` (loop-check, direction/conjunct varied), wired
into a local copy of `intExpandBranches`'s `go` loop. `reuseWitness = none` means no loop-check
at all (V0, the control -- must reproduce the baseline row exactly). -/

/-- Local copy of `applyAllTImpRules`, with the self-copy channel gated by `dropSelfCopy`. -/
def applyAllTImpRulesVariant (dropSelfCopy : Bool) (br : IBranch Nat) (edges : IEdges) :
    IBranch Nat :=
  let newForms :=
    br.filterMap fun sf =>
      match sf.sign, sf.formula with
      | .pos, .imp φ ψ =>
        let toAdd := intTImpRule φ ψ sf.label edges br
        let copies :=
          if dropSelfCopy then []
          else
            let accessibleWorlds :=
              (br.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
            accessibleWorlds.filterMap fun w' =>
              if br.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w')
              then none
              else some (⟨.pos, sf.formula, w'⟩ : ISF Nat)
        let combined := toAdd ++ copies
        if combined.isEmpty then none else some combined
      | _, _ => none
  br ++ newForms.flatten

def applyPersistenceFixpointVariant (dropSelfCopy : Bool) (br : IBranch Nat) (edges : IEdges)
    (fuel : Nat) : IBranch Nat :=
  match fuel with
  | 0 => br
  | fuel' + 1 =>
    let br' := applyAllTImpRulesVariant dropSelfCopy br edges
    if br'.length == br.length then br
    else applyPersistenceFixpointVariant dropSelfCopy br' edges fuel'

/-- V1: ancestor-directed loop-check, `F(ψ)@x` conjunct RETAINED. Swaps
`isAccessible edges w x` -> `isAccessible edges x w` and `w.ble x` -> `x.ble w` relative to the
library's `intFImpReuseWitness?`; keeps the other three conjuncts (containment, obligation-open,
explicit-F-entry). -/
def reuseWitnessAncRetained (bPers : IBranch Nat) (edges : IEdges)
    (newForms : List (ISF Nat)) (newEdge : Nat × Nat) : Option Nat :=
  let w := newEdge.2
  match newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none) with
  | none => none
  | some ψ =>
    let sfor : List (Proposition Nat) :=
      newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none
    let candidates := (bPers.map (·.label)).eraseDups
    candidates.findSome? fun x =>
      let forcedAtX := posFormulasAt bPers x
      if isAccessible edges x w
          && x.ble w
          && sfor.all (forcedAtX.contains ·)
          && !(forcedAtX.contains ψ)
          && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) then
        some x
      else none

/-- True control: an EXACT copy of the library's CURRENT `intFImpReuseWitness?`, direction and
conjuncts unchanged. NOTE (correction after first run): `reuseWitness = none` (skip the
loop-check entirely) is NOT the same as the unmodified library, because `intExpandBranches`
ALREADY calls `intFImpReuseWitness?` today (`Expansion.lean:423`) -- the existing, buggy
DESCENDANT-direction check, which fires occasionally. The first run of this file used `none` as
"V0" and it did NOT reproduce the baseline row (5/10/15/20/30/40/60 vs. baseline's 4/7/10/14/
20/27/40), which is exactly the discrepancy this def and the `runVariant none false` calls below
are kept to document: `none` measures a *different, more aggressive* control ("never reuse"),
useful context but not the fidelity check. `reuseWitnessDescendant` below IS the correct control
and reproduces the baseline exactly (verified separately in `ProbeControl.lean`, same 7-point
match: 4/7/10/14/20/27/40). -/
def reuseWitnessDescendant (bPers : IBranch Nat) (edges : IEdges)
    (newForms : List (ISF Nat)) (newEdge : Nat × Nat) : Option Nat :=
  let w := newEdge.2
  match newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none) with
  | none => none
  | some ψ =>
    let sfor : List (Proposition Nat) :=
      newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none
    let candidates := (bPers.map (·.label)).eraseDups
    candidates.findSome? fun x =>
      let forcedAtX := posFormulasAt bPers x
      if isAccessible edges w x
          && w.ble x
          && sfor.all (forcedAtX.contains ·)
          && !(forcedAtX.contains ψ)
          && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) then
        some x
      else none

/-- V2: ancestor-directed loop-check, `F(ψ)@x` conjunct DROPPED (the task's literal
instruction). -/
def reuseWitnessAncDropped (bPers : IBranch Nat) (edges : IEdges)
    (newForms : List (ISF Nat)) (newEdge : Nat × Nat) : Option Nat :=
  let w := newEdge.2
  match newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none) with
  | none => none
  | some ψ =>
    let sfor : List (Proposition Nat) :=
      newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none
    let candidates := (bPers.map (·.label)).eraseDups
    candidates.findSome? fun x =>
      let forcedAtX := posFormulasAt bPers x
      if isAccessible edges x w
          && x.ble w
          && sfor.all (forcedAtX.contains ·)
          && !(forcedAtX.contains ψ) then
        some x
      else none

/-- Local copy of `intExpandBranches`'s loop, parameterized by an optional reuse-witness
function (`none` = V0 control, no loop-check at all) and whether the self-copy channel is
dropped from persistence. -/
def expandBranchesVariant
    (reuseWitness : Option (IBranch Nat → IEdges → List (ISF Nat) → Nat × Nat → Option Nat))
    (dropSelfCopy : Bool)
    (branches : List (IBranch Nat))
    (expandedSets : List (List (ISF Nat)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuel : Nat) :
    IntTableauResult Nat :=
  match fuel with
  | 0 =>
    match branches.findSome? (fun br => if isIntuitionisticallyClosed br then none else some br)
    with
    | some br => .openBranch br
    | none => .closed
  | fuel' + 1 =>
    let rec @[nolint docBlame] go (pending : List (IBranch Nat))
        (pendingExp : List (List (ISF Nat)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Nat))
        (doneExp : List (List (ISF Nat)))
        (doneNW : List Nat)
        (doneEdges : List IEdges)
        : IntTableauResult Nat :=
      match pending, pendingExp, pendingNW, pendingEdges with
      | [], _, _, _ => .closed
      | br :: restBs, ex :: restEs, nw :: restNW, edges :: restEdges =>
        let bPers := applyPersistenceFixpointVariant dropSelfCopy br edges (fuel' + 1)
        if isIntuitionisticallyClosed bPers then
          go restBs restEs restNW restEdges
            (done ++ [bPers]) (doneExp ++ [ex]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        else
          match intStepBranch bPers ex nw with
          | none => .openBranch bPers
          | some (.linearResult newForms nw' newEdge, newExp) =>
            match newEdge with
            | none =>
              expandBranchesVariant reuseWitness dropSelfCopy
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                fuel'
            | some newEdgeVal =>
              match reuseWitness with
              | none =>
                expandBranchesVariant reuseWitness dropSelfCopy
                  (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                  (doneExp ++ [newExp] ++ restEs)
                  (doneNW ++ [nw'] ++ restNW)
                  (doneEdges ++ [edges ++ [newEdgeVal]] ++ restEdges)
                  fuel'
              | some checkFn =>
                match checkFn bPers edges newForms newEdgeVal with
                | some _x =>
                  expandBranchesVariant reuseWitness dropSelfCopy
                    (done ++ [bPers] ++ restBs)
                    (doneExp ++ [newExp] ++ restEs)
                    (doneNW ++ [nw] ++ restNW)
                    (doneEdges ++ [edges] ++ restEdges)
                    fuel'
                | none =>
                  expandBranchesVariant reuseWitness dropSelfCopy
                    (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                    (doneExp ++ [newExp] ++ restEs)
                    (doneNW ++ [nw'] ++ restNW)
                    (doneEdges ++ [edges ++ [newEdgeVal]] ++ restEdges)
                    fuel'
          | some (.branchingResult branches' nw', newExp) =>
            expandBranchesVariant reuseWitness dropSelfCopy
              (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
              (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
              (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
              (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
              fuel'
          | some (.notApplicable, _) => .openBranch bPers
      | _ :: restBs, _, _, _ =>
        go restBs [] [] [] done doneExp doneNW doneEdges
    go branches expandedSets nextWorlds edgeSets [] [] [] []

def runVariant
    (reuseWitness : Option (IBranch Nat → IEdges → List (ISF Nat) → Nat × Nat → Option Nat))
    (dropSelfCopy : Bool) (fuel : Nat) : String :=
  worldStats (expandBranchesVariant reuseWitness dropSelfCopy
    [[(⟨.neg, phi0, 0⟩ : ISF Nat)]] [[]] [1] [[]] fuel)

/-! ### V0-naive (`none` = never reuse): NOT the fidelity check, kept only to document the
first-run finding that `none` diverges from baseline (see the `reuseWitnessDescendant`
docstring above). -/

#eval runVariant none false 10
#eval runVariant none false 20
#eval runVariant none false 30
#eval runVariant none false 40
#eval runVariant none false 60
#eval runVariant none false 80
#eval runVariant none false 120

/-! ### V0 (true control): must match the baseline row exactly -- confirms this file's `go`-loop
copy is faithful to the real `intExpandBranches` before V1/V2/V3's numbers are trusted. -/

#eval runVariant (some reuseWitnessDescendant) false 10
#eval runVariant (some reuseWitnessDescendant) false 20
#eval runVariant (some reuseWitnessDescendant) false 30
#eval runVariant (some reuseWitnessDescendant) false 40
#eval runVariant (some reuseWitnessDescendant) false 60
#eval runVariant (some reuseWitnessDescendant) false 80
#eval runVariant (some reuseWitnessDescendant) false 120

/-! ### V1: ancestor-directed, conjunct retained -/

#eval runVariant (some reuseWitnessAncRetained) false 10
#eval runVariant (some reuseWitnessAncRetained) false 20
#eval runVariant (some reuseWitnessAncRetained) false 30
#eval runVariant (some reuseWitnessAncRetained) false 40
#eval runVariant (some reuseWitnessAncRetained) false 60
#eval runVariant (some reuseWitnessAncRetained) false 80
#eval runVariant (some reuseWitnessAncRetained) false 120

/-! ### V2: ancestor-directed, conjunct dropped -/

#eval runVariant (some reuseWitnessAncDropped) false 10
#eval runVariant (some reuseWitnessAncDropped) false 20
#eval runVariant (some reuseWitnessAncDropped) false 30
#eval runVariant (some reuseWitnessAncDropped) false 40
#eval runVariant (some reuseWitnessAncDropped) false 60
#eval runVariant (some reuseWitnessAncDropped) false 80
#eval runVariant (some reuseWitnessAncDropped) false 120

/-! ## Companion files (higher-fuel confirmation, V3, conformance corpus)

Splitting this probe across several standalone files was a compute-time scope adaptation (a
single `fuel = 260` baseline call alone costs 6-11 minutes under `#eval`'s bytecode evaluator;
running the full 10-point ladder for 4+ variants in one file was infeasible). Each companion file
is independently compiled and re-runnable via the same `lake env lean` invocation:

- `ProbeControl.lean`: re-derives the true control (`reuseWitnessDescendant`) in isolation;
  confirms the 7-point exact match against baseline (4/7/10/14/20/27/40).
- `ProbeHighFuel.lean`: V1 and V2 at `fuel ∈ {160, 200, 260}`. Result: V1 saturates at
  `maxLabel = 21` for all three (identical to its `fuel = 120` value); V2 saturates at
  `maxLabel = 15` for all three (identical to its `fuel = 80`/`120` values). Both CONFIRMED
  terminating.
- `ProbeV3.lean`: V3 = V1 (conjunct retained) + self-copy channel removed, at
  `fuel ∈ {10, 20, 40, 80, 120, 160, 260}`. Result: saturates at `maxLabel = 21`
  (`len = 219, distinctLabels = 22`) for `fuel ≥ 120` -- IDENTICAL to V1's saturated branch.
  Confirms D3: once ancestor blocking (STEP 2) is active, removing the self-copy channel
  (STEP 1) changes nothing about the termination outcome.
- `ProbeConformance.lean`: all 19 propositional formulas (`TableauConformance.lean:235-328`)
  under V1, V2, and V3 at `fuel = 400`. Result: **ALL 19 ROWS MATCH** for all three variants (14
  CLOSED + 5 OPEN, exactly the file's stated expectations). Zero completeness regression under
  any terminating variant.
-/

end DivergenceProbe
