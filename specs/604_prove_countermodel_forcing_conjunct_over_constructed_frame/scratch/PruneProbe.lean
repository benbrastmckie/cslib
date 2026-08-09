module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
public meta import Cslib.Foundations.Logic.Tableau.Branch

set_option autoImplicit false
set_option maxRecDepth 100000

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace PruneProbe

/-- Recreated expansion result carrying BOTH edge lists (mirrors
`CslibTests.BetaSplitRefutation.AugRes`). -/
inductive AugRes where
  | closed
  | openBranch (b : IBranch Nat) (augEdges : IEdges) (rawEdges : IEdges)

instance : Inhabited AugRes := ⟨.closed⟩

/-- `partial` copy of `CslibTests.BetaSplitRefutation.goRaw` (termination already proved there;
this is a scratch probe, so the measure is not re-proved). Returns the RAW edge list alongside
the augmented one. -/
partial def goRaw
    (closurePred : IBranch Nat → Bool)
    (pending : List (IBranch Nat))
    (pendingExp : List (List (ISF Nat)))
    (pendingNW : List Nat)
    (pendingEdges : List IEdges)
    (pendingAug : List IEdges)
    (pendingFuels : List Nat)
    (done : List (IBranch Nat))
    (doneExp : List (List (ISF Nat)))
    (doneNW : List Nat)
    (doneEdges : List IEdges)
    (doneAug : List IEdges)
    (doneFuels : List Nat) :
    AugRes :=
  match pending, pendingExp, pendingNW, pendingEdges, pendingAug, pendingFuels with
  | [], _, _, _, _, _ => .closed
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, augH :: augT, f :: restFs =>
    let bPers := applyPersistenceFixpoint b edges f
    if closurePred bPers then
      goRaw closurePred restBs restEs restNW restEdges augT restFs
        (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        (doneAug ++ [augH]) (doneFuels ++ [f])
    else
      match f with
      | 0 => .openBranch bPers augH edges
      | f' + 1 =>
        match intStepBranch bPers e nw with
        | none => .openBranch bPers augH edges
        | some (.linearResult newForms nw' newEdge, newExp) =>
          match newEdge with
          | none =>
            goRaw closurePred
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              (doneEdges ++ [edges] ++ restEdges)
              (doneAug ++ [augH] ++ augT)
              (doneFuels ++ [f'] ++ restFs)
              [] [] [] [] [] []
          | some newE =>
            match intFImpReuseWitnessAnc? bPers edges newForms newE with
            | some x =>
              goRaw closurePred
                (done ++ [bPers] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                (doneAug ++ [augH ++ [(x, newE.2)]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] []
            | none =>
              goRaw closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges ++ [newE]] ++ restEdges)
                (doneAug ++ [augH ++ [newE]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] []
        | some (.branchingResult branches' nw', newExp) =>
          goRaw closurePred
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
            (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
            (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
            (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
            (doneAug ++ branches'.map (fun _ => augH) ++ augT)
            (doneFuels ++ branches'.map (fun _ => f') ++ restFs)
            [] [] [] [] [] []
        | some (.notApplicable, _) => .openBranch bPers augH edges
  | _ :: restBs, _pExp, _pNW, _pEdges, _pAug, _pFuels =>
    goRaw closurePred restBs [] [] [] [] [] done doneExp doneNW doneEdges doneAug doneFuels

/-- Run the recreation on `φ` at `fuel` under the intuitionistic closure predicate. -/
def expandRaw (φ : Proposition Nat) (fuel : Nat) : AugRes :=
  goRaw isIntuitionisticallyClosed [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [[]] [fuel] [] [] [] [] [] []

def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

def stepFrom (edges : IEdges) (w : Nat) : List Nat :=
  edges.filterMap fun e => if e.2 == w then some e.1 else none

def succsAux (edges : IEdges) (acc : List Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let next := (acc ++ acc.flatMap (stepFrom edges)).eraseDups
    if next.length == acc.length then acc else succsAux edges next f

def succs (edges : IEdges) (w : Nat) : List Nat := succsAux edges [w] (edges.length + 2)

/-- Decidable mirror of `IForces` over `intAccessPreorder edges`, `intExtractValuation b`,
`intBotForces`. -/
def evalF (edges : IEdges) (b : IBranch Nat) : Nat → Proposition Nat → Bool
  | w, .atom p => forcesAtom b p w
  | _, .bot => false
  | w, .imp f g => (succs edges w).all fun w' => !(evalF edges b w' f) || evalF edges b w' g
  | w, .and f g => evalF edges b w f && evalF edges b w g
  | w, .or f g => evalF edges b w f || evalF edges b w g

def worldUniverse (b : IBranch Nat) (edges : IEdges) : List Nat :=
  (branchLabels b ++ edges.map (·.1) ++ edges.map (·.2)).eraseDups

def upwardClosed (b : IBranch Nat) (edges : IEdges) : Bool :=
  (worldUniverse b edges).all fun w => (succs edges w).all fun w' =>
    (branchAtoms b).all fun p => !(forcesAtom b p w) || forcesAtom b p w'

/-- Loop-back edges: augmented edges that are not raw edges. -/
def loopBackEdges (raw aug : IEdges) : IEdges := aug.filter (fun e => !(raw.contains e))

/-- Worlds at which the algorithm discharged an `F(φ→ψ)` obligation by ANCESTOR REUSE rather
than by creating a fresh child: the PARENT component of a loop-back edge `(x, w)`. -/
def blockedWorlds (raw aug : IEdges) : List Nat :=
  ((loopBackEdges raw aug).map (·.2)).eraseDups

/-- Same, excluding self-reuse `(w, w)` (a self-loop witness is already reflexively accessible
in the raw frame, so it needs no pruning). -/
def blockedWorldsStrict (raw aug : IEdges) : List Nat :=
  (((loopBackEdges raw aug).filter (fun e => e.1 != e.2)).map (·.2)).eraseDups

/-- Candidate uniform construction: raw tree edges with every edge INTO a blocked world cut.
Since the raw edges form a forest (each world has a unique parent), this disconnects each
blocked world together with its entire subtree. -/
def prunedEdges (raw aug : IEdges) : IEdges :=
  raw.filter (fun e => !((blockedWorlds raw aug).contains e.1))

def prunedEdgesStrict (raw aug : IEdges) : IEdges :=
  raw.filter (fun e => !((blockedWorldsStrict raw aug).contains e.1))

/-- `(upwardClosed, forces φ at 0)`. Witness for `openBranch_countermodel` iff `(true, false)`. -/
def check (b : IBranch Nat) (φ : Proposition Nat) (edges : IEdges) : Bool × Bool :=
  (upwardClosed b edges, evalF edges b 0 φ)

/-! ### The `IFimpAccess`-support greatest fixpoint

The construction a `truthLemma` proof over a sub-raw frame actually needs: the largest set `K`
of worlds on which `IFimpAccess` holds *internally* -- every `F(φ→ψ)@w` for `w ∈ K` has a
witness `w'` reachable from `w` inside `K` carrying `T(φ)@w'` and `F(ψ)@w'`. On such a `K` the
F-imp case of `truthLemma` closes by construction, and `IPosPersistRaw`/`IWorldsPlanted` (both
already sorry-free over raw edges) chain along `K`'s edges since `K`'s edges are a sub-list of
`rawEdges`. -/

/-- All `F(φ→ψ)` obligations recorded at world `w` on `b`. -/
def fimpObligations (b : IBranch Nat) (w : Nat) : List (Proposition Nat × Proposition Nat) :=
  b.filterMap fun sf =>
    if sf.sign == .neg && sf.label == w then
      match sf.formula with
      | .imp f g => some (f, g)
      | _ => none
    else none

/-- Raw edges with both endpoints inside `K`. -/
def restrict (edges : IEdges) (K : List Nat) : IEdges :=
  edges.filter fun e => K.contains e.1 && K.contains e.2

/-- `w` has all its `F(→)` obligations witnessed inside `K`. -/
def supportedIn (b : IBranch Nat) (edges : IEdges) (K : List Nat) (w : Nat) : Bool :=
  (fimpObligations b w).all fun fg =>
    (succs (restrict edges K) w).any fun w' =>
      K.contains w' &&
      b.any (fun sf => sf.sign == .pos && sf.formula == fg.1 && sf.label == w') &&
      b.any (fun sf => sf.sign == .neg && sf.formula == fg.2 && sf.label == w')

/-- One downward pass of the greatest-fixpoint computation. -/
def supportStep (b : IBranch Nat) (edges : IEdges) (K : List Nat) : List Nat :=
  K.filter (supportedIn b edges K)

/-- Iterate `supportStep` to a fixpoint (bounded by `|K|` passes). -/
def supportFix (b : IBranch Nat) (edges : IEdges) (K : List Nat) : Nat → List Nat
  | 0 => K
  | n + 1 =>
    let K' := supportStep b edges K
    if K'.length == K.length then K else supportFix b edges K' n

/-- The greatest `IFimpAccess`-supported subframe of the raw tree. -/
def supportedFrame (b : IBranch Nat) (raw : IEdges) : List Nat × IEdges :=
  let labels := branchLabels b
  let K := supportFix b raw labels (labels.length + 1)
  (K, restrict raw K)

/-- Full per-formula report at the REAL entry-point fuel `intFuelExt φ`:
`(rawEdges, loopBacks, blockedWorlds, prunedEdges,
  check raw, check pruned, check prunedStrict, recreationAgreesWithRealTableau)`. -/
def report (φ : Proposition Nat) :
    String × IEdges × IEdges × List Nat × IEdges ×
      (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × Bool :=
  match expandRaw φ (intFuelExt φ) with
  | .closed => ("CLOSED", [], [], [], [], (true, true), (true, true), (true, true), true)
  | .openBranch b aug raw =>
    let agrees :=
      match intuitionisticTableau φ with
      | .openBranch b' => b == b'
      | .closed => false
    ("OPEN", raw, loopBackEdges raw aug, blockedWorlds raw aug, prunedEdges raw aug,
      check b φ raw, check b φ (prunedEdges raw aug), check b φ (prunedEdgesStrict raw aug),
      agrees)

/-- Fixpoint report: `(K, K's edges, 0 ∈ K, check over K's frame)`. -/
def reportFix (φ : Proposition Nat) :
    String × List Nat × IEdges × Bool × (Bool × Bool) :=
  match expandRaw φ (intFuelExt φ) with
  | .closed => ("CLOSED", [], [], true, (true, true))
  | .openBranch b _aug raw =>
    let (K, e) := supportedFrame b raw
    ("OPEN", K, e, K.contains 0, check b φ e)

/-- Worlds at which `IFimpAccess raw b` FAILS: some `F(φ→ψ)@w` has no raw-reachable witness.
Empty list = `IFimpAccess rawEdges b` holds for this branch. -/
def fimpFailures (b : IBranch Nat) (raw : IEdges) : List Nat :=
  (branchLabels b).filter (fun w => !(supportedIn b raw (branchLabels b) w))

/-- `(worlds where IFimpAccess raw fails, worlds where it fails over the AUGMENTED frame)`. -/
def reportFimp (φ : Proposition Nat) : String × List Nat × List Nat :=
  match expandRaw φ (intFuelExt φ) with
  | .closed => ("CLOSED", [], [])
  | .openBranch b aug raw => ("OPEN", fimpFailures b raw, fimpFailures b aug)

def pa : Proposition Nat := .atom 0
def pb : Proposition Nat := .atom 1
def pr : Proposition Nat := .atom 2
def ps : Proposition Nat := .atom 3

def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr
def phiRef2 : Proposition Nat := ((pr ∨ ps) ∧ (((pr ∨ ps) → ((pr ∨ ps) → pr)) → pb)) → pr
def phiRef3 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → (ps → pr))) → pb)) → pr
def exMiddle : Proposition Nat := pa ∨ (pa → .bot)
def dblNeg : Proposition Nat := ((pa → .bot) → .bot) → pa
def peirce : Proposition Nat := ((pa → pb) → pa) → pa
def deMorgan : Proposition Nat := ((pa ∧ pb) → .bot) → ((pa → .bot) ∨ (pb → .bot))
def dummett : Proposition Nat := (pa → pb) ∨ (pb → pa)

#eval! report phiRef1
#eval! report phiRef2
#eval! report phiRef3
#eval! report exMiddle
#eval! report dblNeg
#eval! report peirce
#eval! report deMorgan
#eval! report dummett

#eval! reportFix phiRef1
#eval! reportFix phiRef2
#eval! reportFix phiRef3
#eval! reportFix exMiddle
#eval! reportFix dblNeg
#eval! reportFix peirce
#eval! reportFix deMorgan
#eval! reportFix dummett


#eval! reportFimp phiRef1
#eval! reportFimp phiRef2
#eval! reportFimp phiRef3
#eval! reportFimp exMiddle
#eval! reportFimp dblNeg
#eval! reportFimp peirce
#eval! reportFimp deMorgan
#eval! reportFimp dummett

end PruneProbe
