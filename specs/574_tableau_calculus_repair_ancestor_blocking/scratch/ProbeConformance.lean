module

import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace DivergenceProbeConformance

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

def verdict
    (reuseWitness : Option (IBranch Nat → IEdges → List (ISF Nat) → Nat × Nat → Option Nat))
    (dropSelfCopy : Bool) (fuel : Nat) (φ : Proposition Nat) : String :=
  match expandBranchesVariant reuseWitness dropSelfCopy
      [[(⟨.neg, φ, 0⟩ : ISF Nat)]] [[]] [1] [[]] fuel with
  | .closed => "CLOSED"
  | .openBranch _ => "OPEN"

-- 19-formula corpus, verbatim from CslibTests/TableauConformance.lean:230-328.
def ia : Proposition Nat := .atom 0
def ib : Proposition Nat := .atom 1
def ic : Proposition Nat := .atom 2

def corpus : List (Proposition Nat × String) := [
  (ia → ia, "CLOSED"),
  (ia → (ib → ia), "CLOSED"),
  (ib → (ia → ib), "CLOSED"),
  (((ia → ib) ∧ ia) → ib, "CLOSED"),
  (¬ (ia ∧ ¬ ia), "CLOSED"),
  ((ia → (ib → ic)) → ((ia → ib) → (ia → ic)), "CLOSED"),
  ((¬ ia ∨ ib) → (ia → ib), "CLOSED"),
  ((ia → ib) → (¬ ib → ¬ ia), "CLOSED"),
  ((ia → ic) → ((ib → ic) → ((ia ∨ ib) → ic)), "CLOSED"),
  ((ia ∧ (ib ∨ ic)) → ((ia ∧ ib) ∨ (ia ∧ ic)), "CLOSED"),
  ((ia → ib) → ((ib → ic) → (ia → ic)), "CLOSED"),
  (((ia → ib) → (ia → ic)) → (ia → (ib → ic)), "CLOSED"),
  (¬ (¬ (¬ ia)) → ¬ ia, "CLOSED"),
  (((ia → ib) → ic) → (ib → ic), "CLOSED"),
  (((ia → ib) → ia) → ia, "OPEN"),
  ((ia → ib) ∨ (ib → ia), "OPEN"),
  (¬ (ia ∧ ib) → (¬ ia ∨ ¬ ib), "OPEN"),
  (¬ ia ∨ ¬ (¬ ia), "OPEN"),
  ((¬ ia → (ib ∨ ic)) → ((¬ ia → ib) ∨ (¬ ia → ic)), "OPEN")
]

def runCorpus
    (label : String)
    (reuseWitness : Option (IBranch Nat → IEdges → List (ISF Nat) → Nat × Nat → Option Nat))
    (dropSelfCopy : Bool) (fuel : Nat) : IO Unit := do
  let mut mismatches : List String := []
  let mut idx := 0
  for (φ, expected) in corpus do
    idx := idx + 1
    let actual := verdict reuseWitness dropSelfCopy fuel φ
    if actual != expected then
      mismatches := mismatches ++ [s!"row {idx}: expected {expected}, got {actual}"]
  if mismatches.isEmpty then
    IO.println s!"{label}: ALL 19 ROWS MATCH"
  else
    IO.println s!"{label}: {mismatches.length} MISMATCHES: {mismatches}"

#eval runCorpus "V1 (ancestor, conjunct retained)" (some reuseWitnessAncRetained) false 400
#eval runCorpus "V2 (ancestor, conjunct dropped)" (some reuseWitnessAncDropped) false 400
#eval runCorpus "V3 (V1 + self-copy removed)" (some reuseWitnessAncRetained) true 400

end DivergenceProbeConformance
