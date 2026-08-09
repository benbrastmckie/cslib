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
# Intuitionistic witness for `phiRef1`: the `[(1,0)]` edge set

`openBranch_countermodel` requires, for an open branch `b` returned by `intuitionisticTableau`,
an edge set on `b`'s worlds that is simultaneously (a) upward-closed for `intExtractValuation b`
and (b) a countermodel to the refuted formula at world `0`. This file checks four concrete edge
sets against `intuitionisticTableau phiRef1`'s actual returned branch and confirms that exactly
one of them, `[(1,0)]`, satisfies both conjuncts: `upwardClosed = true` and
`¬forces phiRef1 at 0 = true` (reported as the pair `(true, false)`). The empty frame, the raw
tree, and the augmented frame (raw plus loop-back edges) each fail one of the two conjuncts.

This evidence is what retracted the former PERMANENTLY DEFERRED annotations on
`openBranch_countermodel` for the intuitionistic scheme: the existential the theorem statement
posits is not merely non-empty in principle, it has an explicit, machine-checked witness.

Promoted from `specs/591_decide_openbranch_countermodel_disposition/scratch/WitnessProbe.lean`
(where the same checks ran as unprotected `#eval!` calls); every assertion below is now
`#guard_msgs`-protected, so a future change to `intuitionisticTableau` that disturbs this witness
is a `lake test` build failure rather than a silent drift.

## The exhaustive search, and why it is not re-executed here

The admissible edge sets for `openBranch_countermodel`'s existential are exactly the subsets of
the atom-set-inclusion pair set `⊑` on `b`'s worlds (`⊑` is already transitive, and any
upward-closed valuation's reflexive-transitive closure must be contained in it, so every subset
of `⊑`'s pairs is automatically upward-closed and no admissible edge set lies outside this
family). Consequently the original scratch enumeration in `WitnessSearch2.lean` — which computed
this pair set and then filtered its full powerset for countermodel witnesses — was a *complete*
search, not a sample: if it reported witnesses, that count is exhaustive over the whole
admissible space.

That original interactive run reported **40 witnesses for `phiRef1`**. This figure is
**attributed to the original interactive scratch run and is NOT re-verified here**: a fresh
attempt to re-run the same `subsets`/`searchWitness` enumeration as a live computation measured
no output after 9m10s, even for the first formula, so it is not safe to run as part of `lake
test`. Anyone wanting to re-derive the 40-witness figure by hand can re-run
`specs/591_decide_openbranch_countermodel_disposition/scratch/WitnessSearch2.lean` interactively.

There is deliberately no `CslibTests/WitnessSearch2.lean`: a file of that name containing no
search would misrepresent what it certifies. The `Scheme.lean` docstring citation of
`WitnessSearch2.lean` should therefore retarget to this file
(`CslibTests/WitnessProbe.lean`) in a follow-up docstring edit (out of this task's
`CslibTests/`-only scope).

For the search-space size itself: `WitnessSearch3.lean` (promoted separately) already witnesses
six of `WitnessSearch2.lean`'s other seven formulas (`phiRef2`, `exMiddle`, `dblNeg`, `peirce`,
`deMorgan`, `dummett`) cheaply via the maximal inclusion frame, at negligible cost, with no
powerset needed. No exhaustive per-formula sweep is promoted for any formula; the `phiRef1`
witness asserted below and the `phiRef1`/`[(1,0),(2,0)]` witnesses in `MinProbe.lean` are the
only specific edge-set witnesses this task promotes into CI.

Measuring the cheap half of `WitnessSearch2.lean`'s enumeration (`inclPairs`, an O(n²) filter,
with no powerset step) was considered as a bounded optional addition here, exposing
`(worldCount, admissiblePairCount)` for `phiRef1`. It was not added: computing `inclPairs`
requires the same `atomsAt`/`inclOk` machinery `WitnessSearch3.lean` already defines for the
maximal-frame check, and duplicating it here for a single extra assertion was judged not to add
CI-protected content beyond what `WitnessSearch3.lean` and the direct `check` assertions below
already give. If a future task wants that specific search-space-size guarantee, `inclPairs` can
be added as a small extension of this file at that time.
-/

set_option autoImplicit false

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace CslibTests.WitnessProbe

/-- The atom `pb`. -/
def pb : Proposition Nat := .atom 1

/-- The atom `pr`, whose upward-closure failure the witness below exhibits. -/
def pr : Proposition Nat := .atom 2

/-- The atom `ps`. -/
def ps : Proposition Nat := .atom 3

/-- The formula whose intuitionistic refutation's countermodel witness this file checks. -/
def phiRef1 : Proposition Nat :=
  ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr

/-- The open branch `intuitionisticTableau` actually returns for `phiRef1`, if any. -/
def realBranch : Option (IBranch Nat) :=
  match intuitionisticTableau phiRef1 with
  | .closed => none
  | .openBranch b => some b

/-- The distinct world labels appearing on `b`. -/
def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

/-- The distinct atom indices appearing on `b`. -/
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

/-- `true` iff `b` positively forces atom `p` at world `w`. -/
def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- Worlds mentioned anywhere (branch labels plus both components of every edge). -/
def worldUniverse (b : IBranch Nat) (edges : IEdges) : List Nat :=
  (branchLabels b ++ edges.map (·.1) ++ edges.map (·.2)).eraseDups

/-- One BFS step: worlds directly reachable via a parent→child edge. -/
def stepFrom (edges : IEdges) (w : Nat) : List Nat :=
  edges.filterMap fun e => if e.2 == w then some e.1 else none

/-- Reflexive-transitive closure of the parent→child step relation, computed by saturation.
This is exactly `(intAccessPreorder edges).le w ·` restricted to the finite `worldUniverse`:
`ReflTransGen` of `isAccessible` collapses to `ReflTransGen` of the one-step relation. -/
def succsAux (edges : IEdges) (acc : List Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let next := (acc ++ acc.flatMap (stepFrom edges)).eraseDups
    if next.length == acc.length then acc else succsAux edges next f

/-- Reflexive-transitive successors of `w` under `edges`. -/
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
every world/atom pair in the `worldUniverse`. -/
def upwardClosed (b : IBranch Nat) (edges : IEdges) : Bool :=
  let us := worldUniverse b edges
  us.all fun w => (succs edges w).all fun w' =>
    (branchAtoms b).all fun p => !(forcesAtom b p w) || forcesAtom b p w'

/-- `(upwardClosed, ¬forces phiRef1 at 0)` for `edges` against the real returned branch. The
existential in `openBranch_countermodel` is witnessed exactly when the pair is `(true, false)`. -/
def check (edges : IEdges) : Option (Bool × Bool) :=
  realBranch.map fun b => (upwardClosed b edges, evalF edges b 0 phiRef1)

/-- Positive atoms per world, for reading off the countermodel by hand. -/
def atomTable : List (Nat × List Nat) :=
  match realBranch with
  | none => []
  | some b => (branchLabels b).map fun w => (w, (branchAtoms b).filter (forcesAtom b · w))

/-- info: [(2, [2, 3]), (1, [3]), (0, [])] -/
#guard_msgs in
#eval atomTable

/-! The empty (discrete-order) frame: upward-closure holds trivially, but it does not falsify
`phiRef1` at world `0` (`evalF ... = true`), so it is not a witness. -/

/-- info: some (true, true) -/
#guard_msgs in
#eval check []

/-! The raw tree edges: upward-closed, but also does not falsify `phiRef1` at world `0`. -/

/-- info: some (true, true) -/
#guard_msgs in
#eval check [(1, 0), (2, 1)]

/-! **The witness**: `[(1,0)]` is upward-closed AND falsifies `phiRef1` at world `0` — the pair
`(true, false)`. -/

/-- info: some (true, false) -/
#guard_msgs in
#eval check [(1, 0)]

/-! The augmented frame (raw plus loop-back edges) — the one the source construction actually
refutes upward closure over. It is NOT upward-closed (`upwardClosed = false`) and also does not
falsify `phiRef1` (`evalF ... = false`, i.e. `¬forces = false`), giving `(false, false)`. -/

/-- info: some (false, false) -/
#guard_msgs in
#eval check [(1, 0), (2, 1), (1, 2), (2, 2)]

/-! Sanity check on `succs` over the raw tree and over `[(1,0)]`. -/

/-- info: ([0, 1, 2], [1, 2], [1]) -/
#guard_msgs in
#eval (succs [(1,0),(2,1)] 0, succs [(1,0),(2,1)] 1, succs [(1,0)] 1)

/-! Sanity check on `succs` over the augmented frame. -/

/-- info: ([1, 2], [2, 1]) -/
#guard_msgs in
#eval (succs [(1,0),(2,1),(1,2),(2,2)] 1, succs [(1,0),(2,1),(1,2),(2,2)] 2)

end CslibTests.WitnessProbe
