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

namespace MinProbe

def pb : Proposition Nat := .atom 1
def pr : Proposition Nat := .atom 2
def ps : Proposition Nat := .atom 3
def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr

def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups
def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)
def botAtMin (b : IBranch Nat) (w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == (Proposition.bot : Proposition Nat)
    && sf.label == w)
def atomsAt (b : IBranch Nat) (w : Nat) : List Nat :=
  (branchAtoms b).filter (forcesAtom b · w)
def stepFrom (edges : IEdges) (w : Nat) : List Nat :=
  edges.filterMap fun e => if e.2 == w then some e.1 else none
def succsAux (edges : IEdges) (acc : List Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let next := (acc ++ acc.flatMap (stepFrom edges)).eraseDups
    if next.length == acc.length then acc else succsAux edges next f
def succs (edges : IEdges) (w : Nat) : List Nat := succsAux edges [w] (edges.length + 2)
def evalF (botAt : Nat → Bool) (edges : IEdges) (b : IBranch Nat) :
    Nat → Proposition Nat → Bool
  | w, .atom p => forcesAtom b p w
  | w, .bot => botAt w
  | w, .imp f g =>
    (succs edges w).all fun w' => !(evalF botAt edges b w' f) || evalF botAt edges b w' g
  | w, .and f g => evalF botAt edges b w f && evalF botAt edges b w g
  | w, .or f g => evalF botAt edges b w f || evalF botAt edges b w g
def upwardClosed (b : IBranch Nat) (ws : List Nat) (edges : IEdges) : Bool :=
  ws.all fun w => (succs edges w).all fun w' =>
    (branchAtoms b).all fun p => !(forcesAtom b p w) || forcesAtom b p w'
def botUC (botAt : Nat → Bool) (ws : List Nat) (edges : IEdges) : Bool :=
  ws.all fun w => (succs edges w).all fun w' => !(botAt w) || botAt w'

def minBranch : Option (IBranch Nat) :=
  match minimalTableau phiRef1 with | .closed => none | .openBranch b => some b

/-- world table for the minimal run: `(world, positive atoms, forces ⊥)` -/
#eval! minBranch.map fun b =>
  ((branchLabels b).map fun w => (w, atomsAt b w, botAtMin b w))

/-- `(edges, val upward-closed, ⊥ upward-closed, ¬Forces φ at 0)`;
`(true, true, true)` means the edge set witnesses the minimal-scheme existential. -/
def try1 (edges : IEdges) : Option (IEdges × Bool × Bool × Bool) :=
  minBranch.map fun b =>
    let ws := branchLabels b
    (edges, upwardClosed b ws edges, botUC (botAtMin b) ws edges,
      !(evalF (botAtMin b) edges b 0 phiRef1))

#eval! try1 []
#eval! try1 [(1,0)]
#eval! try1 [(1,0),(2,1)]
#eval! try1 [(2,0)]
#eval! try1 [(1,0),(2,0)]

end MinProbe
