module

import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace DivergenceProbeHigh

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

def worldStats : IntTableauResult Nat → String
  | .closed => "CLOSED"
  | .openBranch br =>
    let labels := br.map (·.label)
    let maxLabel := labels.foldl max 0
    let distinctLabels := labels.eraseDups.length
    s!"OPEN len={br.length} maxLabel={maxLabel} distinctLabels={distinctLabels}"

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

-- V1 at higher fuel: does it eventually saturate, or keep climbing?
#eval runVariant (some reuseWitnessAncRetained) false 160
#eval runVariant (some reuseWitnessAncRetained) false 200
#eval runVariant (some reuseWitnessAncRetained) false 260

-- V2 at higher fuel: confirm the fuel=80/120 saturation persists (same value = true fixpoint).
#eval runVariant (some reuseWitnessAncDropped) false 160
#eval runVariant (some reuseWitnessAncDropped) false 200
#eval runVariant (some reuseWitnessAncDropped) false 260

end DivergenceProbeHigh
