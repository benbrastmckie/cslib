/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
public meta import Cslib.Foundations.Logic.Tableau.Branch

/-!
# The maximal inclusion frame is NOT a uniform countermodel witness

For each of 8 formulas under `intuitionisticTableau` and 4 under `minimalTableau`, this file
checks whether the single MAXIMAL admissible frame `⊑` (every pair the atom-set-inclusion
preorder on the returned branch's worlds allows, with no subset search) itself witnesses
`openBranch_countermodel`'s existential — reported both with and without an extra atom-free
world in the universe.

The result: the maximal frame witnesses the existential for every formula EXCEPT `phiRef1` and
`phiRef3` (and their `minimalTableau` counterpart `phiRef1`), where it FAILS — `checkInt phiRef1`
and `checkInt phiRef3` report the `(true, false)` pattern (upward-closed but does not falsify the
formula) rather than `(true, true)`. This is what backs the claim that the maximal inclusion
frame is not a uniform witness for `openBranch_countermodel`: for the `phiRef1`/`phiRef3` family
a smaller, specifically-chosen edge set (checked directly in `CslibTests/WitnessProbe.lean` and
`CslibTests/MinProbe.lean`) is required instead.

Promoted from `specs/591_decide_openbranch_countermodel_disposition/scratch/WitnessSearch3.lean`;
every assertion below is now `#guard_msgs`-protected.

## `Minimal.Soundness` import

The scratch file imports `Cslib.Logics.Propositional.Tableau.Minimal.Soundness` alongside the
three shared imports. This file omits it: the build below resolves `minimalTableau` (used by
`checkMin`) from `Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` and the other shared
imports alone, with no build failure, so the extra import was unnecessary in the scratch file. -/

set_option autoImplicit false
set_option maxRecDepth 100000

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace CslibTests.WitnessSearch3

/-- The atom `pa`. -/
def pa : Proposition Nat := .atom 0

/-- The atom `pb`. -/
def pb : Proposition Nat := .atom 1

/-- The atom `pr`. -/
def pr : Proposition Nat := .atom 2

/-- The atom `ps`. -/
def ps : Proposition Nat := .atom 3

/-- The distinct world labels appearing on `b`. -/
def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

/-- The distinct atom indices appearing on `b`. -/
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

/-- `true` iff `b` positively forces atom `p` at world `w`. -/
def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- One BFS step: worlds directly reachable via a parent→child edge. -/
def stepFrom (edges : IEdges) (w : Nat) : List Nat :=
  edges.filterMap fun e => if e.2 == w then some e.1 else none

/-- Reflexive-transitive closure of the parent→child step relation, computed by saturation. -/
def succsAux (edges : IEdges) (acc : List Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let next := (acc ++ acc.flatMap (stepFrom edges)).eraseDups
    if next.length == acc.length then acc else succsAux edges next f

/-- Reflexive-transitive successors of `w` under `edges`. -/
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

/-- Upward closure of `intExtractValuation b` along `edges`, checked over every world/atom pair
in `ws`. -/
def upwardClosed (b : IBranch Nat) (ws : List Nat) (edges : IEdges) : Bool :=
  ws.all fun w => (succs edges w).all fun w' =>
    (branchAtoms b).all fun p => !(forcesAtom b p w) || forcesAtom b p w'

/-- Atom set of world `w` on `b`. -/
def atomsAt (b : IBranch Nat) (w : Nat) : List Nat :=
  (branchAtoms b).filter (forcesAtom b · w)

/-- `A(p) ⊆ A(c)`: the only pairs an upward-closed valuation can tolerate. -/
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

/-- `intScheme`: `⊥` is never forced. -/
def intBot : IBranch Nat → Nat → Bool := fun _ _ => false

/-- The maximal-inclusion-frame check for `φ` under `intuitionisticTableau`. -/
def checkInt (φ : Proposition Nat) := maximalFrameCheck intBot (intuitionisticTableau φ) φ

/-- The maximal-inclusion-frame check for `φ` under `minimalTableau`, with `⊥` forced exactly
where `T(⊥)` appears on the branch. -/
def checkMin (φ : Proposition Nat) :=
  maximalFrameCheck (fun b w =>
    b.any (fun sf => sf.sign == .pos && sf.formula == (Proposition.bot : Proposition Nat)
      && sf.label == w)) (minimalTableau φ) φ

/-- **The construction that defeats the maximal frame** (shared with `WitnessProbe.lean`). -/
def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr

/-- Variant: the reuse-driving nested implication uses `pr ∨ ps` itself as the antecedent. -/
def phiRef2 : Proposition Nat := ((pr ∨ ps) ∧ (((pr ∨ ps) → ((pr ∨ ps) → pr)) → pb)) → pr

/-- Variant: one more nesting level between the reuse target and the reused-into world; also
defeats the maximal frame (checked below alongside `phiRef1`). -/
def phiRef3 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → (ps → pr))) → pb)) → pr

/-- Excluded middle, `pa ∨ ¬pa`. -/
def exMiddle : Proposition Nat := pa ∨ (pa → .bot)

/-- Double negation elimination, `¬¬pa → pa`. -/
def dblNeg : Proposition Nat := ((pa → .bot) → .bot) → pa

/-- Peirce's law, `((pa → pb) → pa) → pa`. -/
def peirce : Proposition Nat := ((pa → pb) → pa) → pa

/-- De Morgan's law, `¬(pa ∧ pb) → (¬pa ∨ ¬pb)`. -/
def deMorgan : Proposition Nat := ((pa ∧ pb) → .bot) → ((pa → .bot) ∨ (pb → .bot))

/-- Dummett's law, `(pa → pb) ∨ (pb → pa)`. -/
def dummett : Proposition Nat := (pa → pb) ∨ (pb → pa)

/-! `(verdict, (UC, ¬Forces) without fresh world, (UC, ¬Forces) with fresh world)`. `(true, true)`
in either slot means the maximal inclusion frame witnesses the existential. The `phiRef1` and
`phiRef3` rows below FAIL — `(true, false)` — which is the cited fact. -/

/-- info: ("OPEN", (true, false), true, false) -/
#guard_msgs in
#eval checkInt phiRef1

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkInt phiRef2

/-- info: ("OPEN", (true, false), true, false) -/
#guard_msgs in
#eval checkInt phiRef3

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkInt exMiddle

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkInt dblNeg

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkInt peirce

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkInt deMorgan

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkInt dummett

/-! Minimal scheme (`isMinimallyClosed`) rows. `checkMin phiRef1` FAILS the maximal frame too. -/

/-- info: ("OPEN", (true, false), true, false) -/
#guard_msgs in
#eval checkMin phiRef1

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkMin exMiddle

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkMin peirce

/-- info: ("OPEN", (true, true), true, true) -/
#guard_msgs in
#eval checkMin dummett

end CslibTests.WitnessSearch3
