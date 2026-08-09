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

namespace WitnessSearch2

def pa : Proposition Nat := .atom 0
def pb : Proposition Nat := .atom 1
def pr : Proposition Nat := .atom 2
def ps : Proposition Nat := .atom 3

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

def evalF (edges : IEdges) (b : IBranch Nat) : Nat → Proposition Nat → Bool
  | w, .atom p => forcesAtom b p w
  | _, .bot => false
  | w, .imp f g => (succs edges w).all fun w' => !(evalF edges b w' f) || evalF edges b w' g
  | w, .and f g => evalF edges b w f && evalF edges b w g
  | w, .or f g => evalF edges b w f || evalF edges b w g

def upwardClosed (b : IBranch Nat) (ws : List Nat) (edges : IEdges) : Bool :=
  ws.all fun w => (succs edges w).all fun w' =>
    (branchAtoms b).all fun p => !(forcesAtom b p w) || forcesAtom b p w'

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let rest := subsets xs; rest ++ rest.map (x :: ·)

/-- Atom set of world `w` on `b`, as a sublist of the branch's atoms. -/
def atomsAt (b : IBranch Nat) (w : Nat) : List Nat :=
  (branchAtoms b).filter (forcesAtom b · w)

/-- `A(p) ⊆ A(c)`: the only pairs an upward-closed valuation can tolerate. -/
def inclOk (b : IBranch Nat) (p c : Nat) : Bool :=
  (atomsAt b p).all fun x => (atomsAt b c).contains x

/-- Exhaustive search over the COMPLETE space of admissible edge sets.

Any `edges` whose `intAccessPreorder` keeps `intExtractValuation b` upward-closed must satisfy
`w ≤ w' → A(w) ⊆ A(w')`, i.e. its reflexive-transitive closure is contained in the atom-set
inclusion preorder `⊑`. Since `⊑` is already transitive, the admissible edge sets are EXACTLY
the subsets of `⊑`'s pair set, and every such subset is automatically upward-closed. So this
enumeration is complete, not a sample: if it finds no witness, none exists. -/
def searchWitness (φ : Proposition Nat) :
    String × Nat × Nat × Option IEdges × Nat :=
  match intuitionisticTableau φ with
  | .closed => ("CLOSED (no obligation)", 0, 0, none, 0)
  | .openBranch b =>
    let labels := branchLabels b
    let fresh := labels.foldl max 0 + 1
    let ws := labels ++ [fresh]
    -- edge (child, parent) means parent ≤ child, so require A(parent) ⊆ A(child)
    let inclPairs := (ws.flatMap fun p => ws.map fun c => (c, p)).filter
      fun e => e.1 != e.2 && inclOk b e.2 e.1
    let cands := subsets inclPairs
    let good := cands.filter fun e => !(evalF e b 0 φ)
    -- sanity: confirm every reported witness really is upward-closed
    let allUC := good.all (upwardClosed b ws ·)
    (if allUC then "OPEN" else "OPEN/UC-SANITY-FAILED",
      ws.length, inclPairs.length, good.head?, good.length)

def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr
def phiRef2 : Proposition Nat := ((pr ∨ ps) ∧ (((pr ∨ ps) → ((pr ∨ ps) → pr)) → pb)) → pr
def phiRef3 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → (ps → pr))) → pb)) → pr

def exMiddle : Proposition Nat := pa ∨ (pa → .bot)
def dblNeg : Proposition Nat := ((pa → .bot) → .bot) → pa
def peirce : Proposition Nat := ((pa → pb) → pa) → pa
def deMorgan : Proposition Nat := ((pa ∧ pb) → .bot) → ((pa → .bot) ∨ (pb → .bot))
def dummett : Proposition Nat := (pa → pb) ∨ (pb → pa)

-- (verdict, #worlds, #admissible edge-pairs, first witness, #witnesses)
#eval! searchWitness phiRef1
#eval! searchWitness phiRef2
#eval! searchWitness phiRef3
#eval! searchWitness exMiddle
#eval! searchWitness dblNeg
#eval! searchWitness peirce
#eval! searchWitness deMorgan
#eval! searchWitness dummett

end WitnessSearch2
