module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Tableau.Minimal.Soundness
public meta import Cslib.Logics.Propositional.Tableau.Minimal.Soundness
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
public meta import Cslib.Foundations.Logic.Tableau.Branch

set_option autoImplicit false
set_option maxRecDepth 100000

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace WitnessSearch3

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

/-- Evaluator parameterised by whether `⊥` is forced at a world (`intScheme`: never). -/
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

def atomsAt (b : IBranch Nat) (w : Nat) : List Nat :=
  (branchAtoms b).filter (forcesAtom b · w)
def inclOk (b : IBranch Nat) (p c : Nat) : Bool :=
  (atomsAt b p).all fun x => (atomsAt b c).contains x

/-- The MAXIMAL admissible frame: every pair the atom-set inclusion preorder allows. -/
def inclEdges (b : IBranch Nat) (ws : List Nat) : IEdges :=
  (ws.flatMap fun p => ws.map fun c => (c, p)).filter fun e => e.1 != e.2 && inclOk b e.2 e.1

/-- Does the MAXIMAL inclusion frame `⊑` itself witness the existential?
Reported both with and without a fresh atom-free world in the universe. -/
def maximalFrameCheck (botAt : IBranch Nat → Nat → Bool)
    (res : IntTableauResult Nat) (φ : Proposition Nat) :
    String × (Bool × Bool) × (Bool × Bool) :=
  match res with
  | .closed => ("CLOSED", (false, false), (false, false))
  | .openBranch b =>
    let labels := branchLabels b
    let fresh := labels.foldl max 0 + 1
    let wsNo := labels
    let wsFr := labels ++ [fresh]
    let eNo := inclEdges b wsNo
    let eFr := inclEdges b wsFr
    ("OPEN",
      (upwardClosed b wsNo eNo, !(evalF (botAt b) eNo b 0 φ)),
      (upwardClosed b wsFr eFr, !(evalF (botAt b) eFr b 0 φ)))

/-- intScheme: `⊥` is never forced. -/
def intBot : IBranch Nat → Nat → Bool := fun _ _ => false

def checkInt (φ : Proposition Nat) := maximalFrameCheck intBot (intuitionisticTableau φ) φ
def checkMin (φ : Proposition Nat) :=
  maximalFrameCheck (fun b w =>
    b.any (fun sf => sf.sign == .pos && sf.formula == (Proposition.bot : Proposition Nat)
      && sf.label == w)) (minimalTableau φ) φ

def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr
def phiRef2 : Proposition Nat := ((pr ∨ ps) ∧ (((pr ∨ ps) → ((pr ∨ ps) → pr)) → pb)) → pr
def phiRef3 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → (ps → pr))) → pb)) → pr
def exMiddle : Proposition Nat := pa ∨ (pa → .bot)
def dblNeg : Proposition Nat := ((pa → .bot) → .bot) → pa
def peirce : Proposition Nat := ((pa → pb) → pa) → pa
def deMorgan : Proposition Nat := ((pa ∧ pb) → .bot) → ((pa → .bot) ∨ (pb → .bot))
def dummett : Proposition Nat := (pa → pb) ∨ (pb → pa)

-- (verdict, (UC, ¬Forces) without fresh world, (UC, ¬Forces) with fresh world)
-- (true, true) in either slot means the maximal inclusion frame witnesses the existential.
#eval! checkInt phiRef1
#eval! checkInt phiRef2
#eval! checkInt phiRef3
#eval! checkInt exMiddle
#eval! checkInt dblNeg
#eval! checkInt peirce
#eval! checkInt deMorgan
#eval! checkInt dummett

-- minimal scheme (DP-4 site)
#eval! checkMin phiRef1
#eval! checkMin exMiddle
#eval! checkMin peirce
#eval! checkMin dummett

end WitnessSearch3
