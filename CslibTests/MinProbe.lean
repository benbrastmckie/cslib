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
# Minimal-scheme (`isMinimallyClosed`) witness for `phiRef1`

Under `minimalTableau`/`isMinimallyClosed`, `openBranch_countermodel`'s existential demands an
edge set that discharges TWO upward-closure obligations simultaneously — the ordinary
valuation-upward-closure check (as in the intuitionistic scheme) AND a `⊥`-upward-closure check
(minimal closure additionally closes a branch whenever `T(χ)` and `F(χ)` coexist for any `χ`, not
only `⊥`, so the countermodel must also keep "forces `⊥`" upward-closed) — while still falsifying
`phiRef1` at world `0`.

This file checks five candidate edge sets against `minimalTableau phiRef1`'s actual returned
branch and confirms that exactly two, `[(1,0)]` and `[(1,0),(2,0)]`, discharge both upward-closure
obligations simultaneously (reported as the all-three-true pattern `(true, true, true)`); the
other three (`[]`, `[(1,0),(2,1)]`, `[(2,0)]`) fail at least one conjunct.

This is the fact `Minimal/Completeness.lean` cites (inline, with no filename before this
promotion) to retract the "independent refutation" claim for the minimal scheme.

Promoted from `specs/591_decide_openbranch_countermodel_disposition/scratch/MinProbe.lean`. That
scratch file has a genuine Lean parse error: two `/-- ... -/` declaration docstrings sit directly
above bare `#eval!` commands, which this repo's `module`-file dialect rejects (a declaration
docstring must attach to a following declaration, not a command — `unexpected token '#eval!';
expected 'lemma'`). This promotion fixes that by construction: both docstrings' explanatory prose
is either folded into this module docstring or converted to a `/-! ... -/` section comment, and
the printed values themselves become `/-- info: ... -/` arguments of `#guard_msgs`, which the
`#guard_msgs` elaborator (not the docstring-attachment mechanism) consumes. -/

set_option autoImplicit false
set_option maxRecDepth 100000

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace CslibTests.MinProbe

/-- The atom `pb`. -/
def pb : Proposition Nat := .atom 1

/-- The atom `pr`, whose upward-closure failure the witness below exhibits. -/
def pr : Proposition Nat := .atom 2

/-- The atom `ps`. -/
def ps : Proposition Nat := .atom 3

/-- The formula whose minimal-scheme countermodel witness this file checks. -/
def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr

/-- The distinct world labels appearing on `b`. -/
def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

/-- The distinct atom indices appearing on `b`. -/
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

/-- `true` iff `b` positively forces atom `p` at world `w`. -/
def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- `true` iff `b` forces `⊥` (positively) at world `w` — the extra obligation the minimal
scheme's closure predicate adds beyond the intuitionistic one. -/
def botAtMin (b : IBranch Nat) (w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == (Proposition.bot : Proposition Nat)
    && sf.label == w)

/-- Atom set of world `w` on `b`. -/
def atomsAt (b : IBranch Nat) (w : Nat) : List Nat :=
  (branchAtoms b).filter (forcesAtom b · w)

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

/-- Decidable evaluator mirroring `IForces` over `edges`, parameterised by whether `⊥` is forced
at each world (via `botAt`, since the minimal scheme's `⊥` is not uniformly absent). -/
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

/-- Upward closure of the "forces `⊥`" predicate along `edges` — the extra obligation the
minimal scheme's closure predicate demands. -/
def botUC (botAt : Nat → Bool) (ws : List Nat) (edges : IEdges) : Bool :=
  ws.all fun w => (succs edges w).all fun w' => !(botAt w) || botAt w'

/-- The open branch `minimalTableau` actually returns for `phiRef1`, if any. -/
def minBranch : Option (IBranch Nat) :=
  match minimalTableau phiRef1 with | .closed => none | .openBranch b => some b

/-! World table for the minimal run: `(world, positive atoms, forces ⊥)`. -/

/-- info: some [(2, [2, 3], false), (1, [3], false), (0, [], false)] -/
#guard_msgs in
#eval minBranch.map fun b =>
  ((branchLabels b).map fun w => (w, atomsAt b w, botAtMin b w))

/-- `(edges, val upward-closed, ⊥ upward-closed, ¬Forces phiRef1 at 0)`;
`(true, true, true)` means the edge set witnesses the minimal-scheme existential. -/
def try1 (edges : IEdges) : Option (IEdges × Bool × Bool × Bool) :=
  minBranch.map fun b =>
    let ws := branchLabels b
    (edges, upwardClosed b ws edges, botUC (botAtMin b) ws edges,
      !(evalF (botAtMin b) edges b 0 phiRef1))

/-- info: some ([], true, true, false) -/
#guard_msgs in
#eval try1 []

/-! **A witness**: `[(1,0)]` discharges both upward-closure obligations while falsifying
`phiRef1` at world `0`. -/

/-- info: some ([(1, 0)], true, true, true) -/
#guard_msgs in
#eval try1 [(1,0)]

/-- info: some ([(1, 0), (2, 1)], true, true, false) -/
#guard_msgs in
#eval try1 [(1,0),(2,1)]

/-- info: some ([(2, 0)], true, true, false) -/
#guard_msgs in
#eval try1 [(2,0)]

/-! **A second witness**: `[(1,0),(2,0)]` also discharges both obligations while falsifying
`phiRef1`. -/

/-- info: some ([(1, 0), (2, 0)], true, true, true) -/
#guard_msgs in
#eval try1 [(1,0),(2,0)]

end CslibTests.MinProbe
