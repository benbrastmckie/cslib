/-
PHASE 15 GATE (scratch probe -- NOT production Lean, NOT in the CI-built tree).

Confirms or falsifies the three load-bearing claims of the Euclidean route
(Phases 16-23) before any file is written to Cslib/. Run via:

    lake env lean specs/515_s5_universal_rule_termination_unblock_504/probes/phase15-euclidean-route-gate.lean

A clean exit 0 with no `sorry`/`admit` in the four load-bearing theorems below
means the GATE PASSES. The `#print axioms` lines at the end must report only
[propext, Classical.choice, Quot.sound] (or a subset) -- no sorryAx.

Claims vetted:
  (a) EuclGen exists and is the least right-Euclidean closure of r.
  (b) Rooted normal form: for right-Euclidean r and root w, R(w) x R(w) ⊆ R.
  (c) KB5 shape: symmetric + right-Euclidean is a PER (transitive), so a rooted
      KB5 frame is edge-isolated-root OR a full cluster containing the root.
  (rule shape) The mint-arm structural claim is argued in prose in the gate
      write-up (it is not a single Lean proposition); the Lean content that
      backs it is that EuclGen's `eucl` constructor gives right-Euclideanness
      directly, i.e. the closure's successor structure is the S5w cluster shape.
-/

import Cslib.Foundations.Relation.Euclidean

open Relator

namespace Phase15Gate

variable {α : Type*} {r s : α → α → Prop}

/-! ## Claim (a): the least right-Euclidean closure exists and is inductive. -/

/-- The inductive least right-Euclidean closure of `r`. -/
inductive EuclGen (r : α → α → Prop) : α → α → Prop
  | base {a b} : r a b → EuclGen r a b
  | eucl {a b c} : EuclGen r a b → EuclGen r a c → EuclGen r b c

/-- (a.1) `EuclGen r` is right-Euclidean -- directly by the `eucl` constructor. -/
instance instRightEuclideanEuclGen : Relation.RightEuclidean (EuclGen r) where
  rightEuclidean := EuclGen.eucl

/-- (a.2) `r` embeds into its closure. -/
theorem euclGen_mono (h : r a b) : EuclGen r a b := EuclGen.base h

/-- (a.3) THE least property. `EuclGen r` is below every right-Euclidean relation
containing `r`. This is the intersection characterization in usable form:
Euclideanness is closed under arbitrary intersection and the full relation is
Euclidean, so the least Euclidean relation containing `r` exists, and this is it. -/
theorem euclGen_least [Relation.RightEuclidean s]
    (hle : ∀ a b, r a b → s a b) : EuclGen r a b → s a b := by
  intro h
  induction h with
  | base hr => exact hle _ _ hr
  | eucl _ _ ihab ihac => exact Relation.RightEuclidean.rightEuclidean ihab ihac

/-! ## Claim (b): rooted normal form -- successors of the root form a universal
cluster. For right-Euclidean `r` and any root `w`, `R(w) x R(w) ⊆ R`. -/

/-- (b.1) The cluster-is-universal fact: it IS `rightEuclidean` applied at the root. -/
theorem rooted_cluster_universal [Relation.RightEuclidean r]
    (w a b : α) (hwa : r w a) (hwb : r w b) : r a b :=
  Relation.RightEuclidean.rightEuclidean hwa hwb

/-- (b.2) The landed `equiv_cod` gives the cluster's `IsEquiv` for free -- confirm it
applies (consume, do not re-derive). This is the single biggest cost reducer. -/
theorem rooted_cluster_isEquiv [Relation.RightEuclidean r] : IsEquiv (Relation.cod r) r :=
  Relation.RightEuclidean.equiv_cod

/-! ## Claim (c): KB5 shape -- symmetric + right-Euclidean is a PER. -/

/-- (c.1) For a symmetric relation, right-Euclidean IFF transitive; hence a symmetric
right-Euclidean relation is transitive (a PER on its domain). Routes via the landed
`symm_rightEuclidean_iff_trans`. -/
theorem kb5_per [Std.Symm r] [Relation.RightEuclidean r] : IsTrans α r :=
  (Relation.symm_rightEuclidean_iff_trans).mp inferInstance

/-- (c.2) The dichotomy witness at the Lean level: from symmetric + right-Euclidean,
if the root `w` has ANY successor then it is reflexive at `w` (full cluster contains
the root); the alternative is the edge-isolated root with no successor. `refl_cod`
plus symmetry deliver the "full cluster contains root" branch. -/
theorem kb5_root_reflexive_if_has_succ [Std.Symm r] [Relation.RightEuclidean r]
    (w a : α) (hwa : r w a) : r w w :=
  -- r w a and (by symm) r a w, then rightEuclidean: r w a, r w a ⊢ r a a; and
  -- transitivity of the PER closes r w w. Simplest: refl_cod on the symmetric edge.
  Relation.RightEuclidean.rightEuclidean (Std.Symm.symm w a hwa) (Std.Symm.symm w a hwa)

end Phase15Gate

-- GATE AXIOM CHECK: these must report only propext / Classical.choice / Quot.sound.
#print axioms Phase15Gate.instRightEuclideanEuclGen
#print axioms Phase15Gate.euclGen_least
#print axioms Phase15Gate.rooted_cluster_universal
#print axioms Phase15Gate.rooted_cluster_isEquiv
#print axioms Phase15Gate.kb5_per
#print axioms Phase15Gate.kb5_root_reflexive_if_has_succ
