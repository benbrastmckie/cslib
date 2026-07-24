/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # `CS5` Native Hilbert Completeness via the Atom-Sum Pair Lindenbaum Construction

This module completes the native Hilbert completeness route for constructive `CS5` over the
fallible-world `CKValidFC` semantics, closing the one open sub-problem `CS5.lean` identifies:
the truth lemma's box-backward case in the **symmetric-tail** canonical model
(`cs5Tail`/`cs5Mreach`/`CS5Segment`, `CS5.lean:610-993`), which needs a simultaneous maximal
theory *pair* `⟨H', T⟩` (`cs5_symmetric_tail_box_gap`, `CS5.lean:686`).

**Not the birelational route.** This module is independent of `CS5Canonical.lean`'s birelational
one-sided construction (`cs5CanonMreach`/`cs5FCIncest`), which pursues a *different* completeness
strategy and hit its own wall (`cs5Incest` is mechanically false on every world type tried there).
This module instead completes the *original* symmetric-tail construction of `CS5.lean` via the
technique `CS5.lean`'s module docstring identifies as the way forward: encode the box-backward
pair as a single quasi-prime theory over the doubled atom space `Atom ⊕ Atom`, under a combined
axiom system (`CS5PairAxiom`) that internalises the two cross-condition implications as axioms
rather than as an externally-imposed, non-`cl`-stable side predicate on a pair poset (the gap the
archived probe `specs/archive/509_.../probes/cs5-pair-primeness.lean` diagnoses).

**Distinct from the discarded `CS5Combined` scaffold.** `CS5Canonical.lean`'s module docstring
records that an earlier `Atom ⊕ Atom` attempt (`CS5Combined`) re-entered Pacheco's unsound
negation-completeness move (`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, unsound for a poset-maximal quasi-prime `Θ`) and
was discarded. This module's construction never invokes negation-completeness: the
cross-conditions are *axioms*, available to any deductively-closed set via a single `modus_ponens`
step, not something derived from maximality. The de-risking probe
(`specs/551_.../probes/cs5-pair-combined-atomsum.lean`) confirms this mechanically: both
soundness and `cl`-stability of `CS5PairAxiom` close sorry-free, with no negation-completeness
step anywhere.

## Main Definitions (this phase)

- `cs5PairTauL`/`cs5PairTauR`: the doubled-atom tagging maps (`Proposition.map Sum.inl`/`Sum.inr`).
- `CS5PairAxiom`: the combined axiom system over `Atom ⊕ Atom` -- `CS5ModalAxiom` on each tagged
  copy, plus the two cross-condition axioms realising `boxInv X ⊆ Y`/`boxInv Y ⊆ X`.
- `cs5PairAxiom_left_derivable`/`cs5PairAxiom_right_derivable`: the easy transport direction,
  `Derivable CS5ModalAxiom φ → Derivable CS5PairAxiom (τ_L φ)` (and the `τ_R` analogue), via
  `Derivable.map` (`DerivationTree.lean`). The converse (needed to show the eventual projected
  pair's components are themselves `CS5ModalAxiom`-quasi-prime) is Phase 5's R2 conservativity
  lemma, not this phase's concern.
- `crossCond_left_stable`/`crossCond_right_stable`: `cl`-stability of the cross-conditions for
  any `CS5PairAxiom`-deductively-closed set -- library port of the probe's prototype (ii).

## References

* `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` -- `CS5ModalAxiom`, `cs5Tail`,
  `cs5_symmetric_tail_box_gap`, `cs5_axiom_sound''`.
* `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` -- `Derivable.map` (atom-relabeling
  functoriality).
* `specs/551_.../probes/cs5-pair-combined-atomsum.lean` -- the de-risking probe this module's
  definitions and `cl`-stability lemma promote to the library.
* [L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024] -- source of
  the pair-construction *technique* (Lemma 18's skeleton only; its primeness step, Lemma 16, is
  unsound as written -- see `CS5.lean`'s module docstring).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Tagging Maps and the Combined Axiom System -/

/-- Tag a proposition as belonging to the "left" copy of the doubled atom space `Atom ⊕ Atom`,
used for the box-backward pair's head component `H'`. -/
def cs5PairTauL : Proposition Atom → Proposition (Atom ⊕ Atom) := Proposition.map Sum.inl

/-- Tag a proposition as belonging to the "right" copy of the doubled atom space `Atom ⊕ Atom`,
used for the box-backward pair's tail component `T`. -/
def cs5PairTauR : Proposition Atom → Proposition (Atom ⊕ Atom) := Proposition.map Sum.inr

/-- **The combined `CS5` pair axiom system.** `CS5ModalAxiom` on each tagged copy (`left`/
`right`) plus the two cross-condition implications, internalised as *axioms* rather than as an
externally-imposed invariant on a pair poset (the design that makes the cross-conditions
`cl`-stable "for free" -- see `crossCond_left_stable`/`crossCond_right_stable` below). Verified
simultaneously sound and `cl`-stable by the Phase 1 probe
(`specs/551_.../probes/cs5-pair-combined-atomsum.lean`). -/
inductive CS5PairAxiom : Proposition (Atom ⊕ Atom) → Prop where
  /-- Every `CS5ModalAxiom` instance holds on the left-tagged copy. -/
  | left (ψ : Proposition Atom) (h : CS5ModalAxiom ψ) : CS5PairAxiom (cs5PairTauL ψ)
  /-- Every `CS5ModalAxiom` instance holds on the right-tagged copy. -/
  | right (ψ : Proposition Atom) (h : CS5ModalAxiom ψ) : CS5PairAxiom (cs5PairTauR ψ)
  /-- Cross-condition realising `boxInv X ⊆ Y`. -/
  | cross1 (B : Proposition Atom) :
      CS5PairAxiom ((Proposition.box (cs5PairTauL B)).imp (cs5PairTauR B))
  /-- Cross-condition realising `boxInv Y ⊆ X`. -/
  | cross2 (B : Proposition Atom) :
      CS5PairAxiom ((Proposition.box (cs5PairTauR B)).imp (cs5PairTauL B))

/-! ## The Easy Transport Direction

`Derivable CS5ModalAxiom φ → Derivable CS5PairAxiom (τ_L φ)` (and the `τ_R` analogue), via
`Derivable.map` (`DerivationTree.lean`) instantiated at `f := Sum.inl`/`Sum.inr` and the
schema-compatibility witness `CS5PairAxiom.left`/`.right`. The converse direction (needed for
Phase 5's projection to be faithful) is deferred to Phase 5's R2 conservativity lemma. -/

/-- `CS5`-derivability transports to the left-tagged copy of `CS5PairAxiom`. -/
theorem cs5PairAxiom_left_derivable {φ : Proposition Atom} (h : Derivable (@CS5ModalAxiom Atom) φ) :
    Derivable (@CS5PairAxiom Atom) (cs5PairTauL φ) :=
  Derivable.map Sum.inl (fun ψ hψ => CS5PairAxiom.left ψ hψ) h

/-- `CS5`-derivability transports to the right-tagged copy of `CS5PairAxiom`. -/
theorem cs5PairAxiom_right_derivable {φ : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) φ) :
    Derivable (@CS5PairAxiom Atom) (cs5PairTauR φ) :=
  Derivable.map Sum.inr (fun ψ hψ => CS5PairAxiom.right ψ hψ) h

/-! ## `cl`-Stability of the Cross-Conditions

Any set deductively closed under `CS5PairAxiom` satisfies both cross-conditions -- no appeal to
preservation of an *external* side predicate under `cl` is needed (contrast the archived probe's
`Cons_Y Z := boxInv Z ⊆ Y`, not closure-stable for `Y` externally fixed). Here the "other side" is
never fixed externally: it is read off the very same set `Z`, via `cs5PairTauR`/`cs5PairTauL`, so
the fact holds uniformly for *every* deductively-closed `Z`, including every set reached during a
Zorn/Lindenbaum extension (`QuasiPrime CS5PairAxiom` reuses the fully generic `QuasiPrime`
machinery from `Segment.lean`, so Phase 4's `prime_set_exclusion` application inherits this for
free). -/

/-- **Cross-condition 1 is `cl`-stable.** For any `CS5PairAxiom`-deductively-closed `Z`,
`□(τ_L B) ∈ Z → τ_R B ∈ Z`, by a single `modus_ponens` against the internalised axiom
`cross1`. -/
theorem crossCond_left_stable {Z : Set (Proposition (Atom ⊕ Atom))}
    (hZ : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5PairAxiom Atom)) Z)
    {B : Proposition Atom} (hB : Proposition.box (cs5PairTauL B) ∈ Z) : cs5PairTauR B ∈ Z := by
  refine hZ [Proposition.box (cs5PairTauL B)] (cs5PairTauR B) ?_ ?_
  · intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hB
  · exact ⟨.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (CS5PairAxiom.cross1 B)) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_singleton.mpr rfl))⟩

/-- **Cross-condition 2 is `cl`-stable.** Symmetric to `crossCond_left_stable`, using `cross2`. -/
theorem crossCond_right_stable {Z : Set (Proposition (Atom ⊕ Atom))}
    (hZ : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5PairAxiom Atom)) Z)
    {B : Proposition Atom} (hB : Proposition.box (cs5PairTauR B) ∈ Z) : cs5PairTauL B ∈ Z := by
  refine hZ [Proposition.box (cs5PairTauR B)] (cs5PairTauL B) ?_ ?_
  · intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hB
  · exact ⟨.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (CS5PairAxiom.cross2 B)) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_singleton.mpr rfl))⟩

end Cslib.Logic.Modal
