module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
public meta import Cslib.Foundations.Logic.Tableau.Branch

set_option autoImplicit false

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace WitnessProbe

def pb : Proposition Nat := .atom 1
def pr : Proposition Nat := .atom 2
def ps : Proposition Nat := .atom 3

def phiRef1 : Proposition Nat :=
  ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr

def realBranch : Option (IBranch Nat) :=
  match intuitionisticTableau phiRef1 with
  | .closed => none
  | .openBranch b => some b

def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- Worlds mentioned anywhere (branch labels plus both components of every edge). -/
def worldUniverse (b : IBranch Nat) (edges : IEdges) : List Nat :=
  (branchLabels b ++ edges.map (·.1) ++ edges.map (·.2)).eraseDups

/-- One BFS step: worlds directly reachable via a parent->child edge. -/
def stepFrom (edges : IEdges) (w : Nat) : List Nat :=
  edges.filterMap fun e => if e.2 == w then some e.1 else none

/-- Reflexive-transitive closure of the parent->child step relation, computed by saturation.
This is exactly `(intAccessPreorder edges).le w ·` restricted to the finite worldUniverse:
`ReflTransGen` of `isAccessible` collapses to `ReflTransGen` of the one-step relation. -/
def succsAux (edges : IEdges) (acc : List Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let next := (acc ++ acc.flatMap (stepFrom edges)).eraseDups
    if next.length == acc.length then acc else succsAux edges next f

def succs (edges : IEdges) (w : Nat) : List Nat :=
  succsAux edges [w] (edges.length + 1)

/-- Decidable evaluator mirroring `IForces` over `intAccessPreorder edges`,
`intExtractValuation b`, and `intBotForces` (bot never forced). -/
def evalF (edges : IEdges) (b : IBranch Nat) : Nat → Proposition Nat → Bool
  | w, .atom p => forcesAtom b p w
  | _, .bot => false
  | w, .imp f g => (succs edges w).all fun w' => !(evalF edges b w' f) || evalF edges b w' g
  | w, .and f g => evalF edges b w f && evalF edges b w g
  | w, .or f g => evalF edges b w f || evalF edges b w g

/-- Upward closure of `intExtractValuation b` along `intAccessPreorder edges`, checked over
every world/atom pair in the worldUniverse. -/
def upwardClosed (b : IBranch Nat) (edges : IEdges) : Bool :=
  let us := worldUniverse b edges
  us.all fun w => (succs edges w).all fun w' =>
    (branchAtoms b).all fun p => !(forcesAtom b p w) || forcesAtom b p w'

/-- `(edges, upwardClosed, forces phiRef1 at 0)`. The existential in
`openBranch_countermodel` is witnessed exactly when the pair is `(true, false)`. -/
def check (edges : IEdges) : Option (Bool × Bool) :=
  realBranch.map fun b => (upwardClosed b edges, evalF edges b 0 phiRef1)

def atomTable : List (Nat × List Nat) :=
  match realBranch with
  | none => []
  | some b => (branchLabels b).map fun w => (w, (branchAtoms b).filter (forcesAtom b · w))

#eval! atomTable
-- empty frame (discrete order)
#eval! check []
-- raw tree edges
#eval! check [(1, 0), (2, 1)]
-- raw minus the 1->2 edge
#eval! check [(1, 0)]
-- augmented frame (raw + loop-backs) -- the one the source refutes
#eval! check [(1, 0), (2, 1), (1, 2), (2, 2)]
-- sanity: successor sets
#eval! (succs [(1,0),(2,1)] 0, succs [(1,0),(2,1)] 1, succs [(1,0)] 1)
#eval! (succs [(1,0),(2,1),(1,2),(2,2)] 1, succs [(1,0),(2,1),(1,2),(2,2)] 2)

end WitnessProbe
