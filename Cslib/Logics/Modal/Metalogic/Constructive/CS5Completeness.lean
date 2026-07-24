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

/-- **The combined `CS5` pair axiom system.** A **two-tier** design:

1. **Modal tier, pure-tagged**: `CS5ModalAxiom` on each tagged copy (`left`/`right`), plus the two
   cross-condition implications `cross1`/`cross2`, internalised as *axioms* rather than as an
   externally-imposed invariant on a pair poset (the design that makes the cross-conditions
   `cl`-stable "for free" -- see `crossCond_left_stable`/`crossCond_right_stable` below). This
   tier is the only place left/right content mixes modally; every modal schema instance is either
   entirely left-tagged, entirely right-tagged, or one of the two designated bridges.
2. **Propositional tier, whole-type**: the nine propositional-core schemata (`implyK`, `implyS`,
   `efq`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`), quantified over the **entire**
   `Proposition (Atom ⊕ Atom)` type rather than routed through `cs5PairTauL`/`cs5PairTauR`. This
   whole-type quantification is *forced*, not a stylistic choice: the generic primeness engine
   (`Metalogic.prime_exclusion`/`Metalogic.prime_set_exclusion`,
   `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`) needs its `hOrE`/`hEFQ`/`hCut`
   hypotheses (`PrimeExclusion.lean:229,237,346-351,435-448`) discharged at *arbitrary* formulas
   of the ambient type `F` -- including genuinely mixed formulas such as
   `(atom (inl p)).or (atom (inr q))` that never arise as the image of `cs5PairTauL`/`cs5PairTauR`
   -- because the engine's Zorn/Lindenbaum construction inserts and case-splits on formulas built
   from the *T ∪ {X}*/*disjunction* combinators, not just tagged formulas. A propositional core
   confined to the two tagged copies would leave those mixed instances undischargeable.

Verified simultaneously sound and `cl`-stable by the Phase 1 probe
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
  /-- Weakening, at the whole combined type: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (φ.imp (ψ.imp φ))
  /-- Distribution, at the whole combined type:
  `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet, at the whole combined type: `⊥ → φ`. -/
  | efq (φ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction, at the whole combined type: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination, at the whole combined type: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination, at the whole combined type: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction, at the whole combined type: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction, at the whole combined type: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination, at the whole combined type:
  `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition (Atom ⊕ Atom)) :
      CS5PairAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)

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

/-! ## Discharging the Primeness-Engine's Precondition Bundle at `CS5PairAxiom`

The propositional core landed above makes the generic primeness engine's schema hypotheses
(`hImplyK`/`hImplyS`/`hEFQ`/`hOrI1`/`hOrI2`/`hOrE`/`hCut`,
`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`) dischargeable at `CS5PairAxiom`, at
*arbitrary* formulas of the combined type -- not just at tagged formulas. Landing these as
named, reusable library lemmas makes `Metalogic.prime_exclusion`/`Metalogic.prime_set_exclusion`
applicable to `CS5PairAxiom` at all; this is useful under either eventual route (Route A or
Route Native, see the module docstring). The one precondition these lemmas do **not** supply is
`DerivExcludes` at the two-sided seed (`cs5PairSeed`, defined below) -- that is the named open
obligation forward-referenced from a later phase, not attempted here. -/

/-- The engine's `hImplyK` schema precondition at `CS5PairAxiom`: `φ → (ψ → φ)` is an axiom
instance for every `φ ψ` in the combined type. Feeds `cs5Pair_hCut` via
`modal_deriv_imp_of_union`. -/
theorem cs5Pair_hImplyK (φ ψ : Proposition (Atom ⊕ Atom)) :
    CS5PairAxiom (φ.imp (ψ.imp φ)) :=
  .implyK φ ψ

/-- The engine's `hImplyS` schema precondition at `CS5PairAxiom`. Feeds `cs5Pair_hCut` via
`modal_deriv_imp_of_union`. -/
theorem cs5Pair_hImplyS (φ ψ χ : Proposition (Atom ⊕ Atom)) :
    CS5PairAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  .implyS φ ψ χ

/-- The engine's `hEFQ` precondition at `CS5PairAxiom`: `⊥ → φ` is derivable for every `φ` in
the combined type. -/
theorem cs5Pair_hEFQ (φ : Proposition (Atom ⊕ Atom)) :
    Deriv (@CS5PairAxiom Atom) [] (Proposition.bot.imp φ) :=
  ⟨.ax [] _ (.efq φ)⟩

/-- The engine's `hOrI1` precondition at `CS5PairAxiom`: `φ → φ ∨ ψ` is derivable. -/
theorem cs5Pair_hOrI1 (φ ψ : Proposition (Atom ⊕ Atom)) :
    Deriv (@CS5PairAxiom Atom) [] (φ.imp (φ.or ψ)) :=
  ⟨.ax [] _ (.orI1 φ ψ)⟩

/-- The engine's `hOrI2` precondition at `CS5PairAxiom`: `ψ → φ ∨ ψ` is derivable. -/
theorem cs5Pair_hOrI2 (φ ψ : Proposition (Atom ⊕ Atom)) :
    Deriv (@CS5PairAxiom Atom) [] (ψ.imp (φ.or ψ)) :=
  ⟨.ax [] _ (.orI2 φ ψ)⟩

/-- The engine's `hOrE` precondition at `CS5PairAxiom`: disjunction elimination is derivable. -/
theorem cs5Pair_hOrE (φ ψ χ : Proposition (Atom ⊕ Atom)) :
    Deriv (@CS5PairAxiom Atom) [] ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))) :=
  ⟨.ax [] _ (.orE φ ψ χ)⟩

/-- The engine's `hCut` precondition at `CS5PairAxiom`: the deduction-theorem-style cut witness,
supplied by **instantiating** the existing generic supplier `modal_deriv_imp_of_union`
(`Intuitionistic/PrimeTheory.lean`) at `Axioms := CS5PairAxiom` with `cs5Pair_hImplyK`/
`cs5Pair_hImplyS` -- no new cut machinery is needed. `modal_deriv_imp_of_union` already has the
singleton `S ∪ {a}` shape `prime_set_exclusion` expects (`SegmentLindenbaum.lean:286-288`
confirms this precedent); the conversion from the engine's `insert a U` shape to that `S ∪ {a}`
shape via `Set.mem_insert_iff`/`Set.mem_union_left`/`Set.mem_union_right` mirrors
`quasi_prime_set_exclusion` (`CS5.lean:864-870`) and `modal_prime_exclusion`
(`Intuitionistic/PrimeTheory.lean:348-353`). -/
theorem cs5Pair_hCut {U : Set (Proposition (Atom ⊕ Atom))}
    {L : List (Proposition (Atom ⊕ Atom))} {a b : Proposition (Atom ⊕ Atom)}
    (hL : ∀ x ∈ L, x ∈ insert a U) (hd : Deriv (@CS5PairAxiom Atom) L b) :
    ∃ L', (∀ x ∈ L', x ∈ U) ∧ Deriv (@CS5PairAxiom Atom) L' (a.imp b) :=
  modal_deriv_imp_of_union cs5Pair_hImplyK cs5Pair_hImplyS
    (fun x hx => by
      rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
      · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
      · exact Set.mem_union_left _ hu)
    hd

/-! ## The Two-Sided Seed `cs5PairSeed`

The base set every downstream seed-exclusion statement (the cross-inertness lemma, the two
individual exclusions, and the named open obligation) refers to -- defined once here so all
later phases share the identical definition. Two components, each with its own provenance:

- **`cs5PairTauL '' H`**: the left-tagged image of the head `H` itself, i.e. the box-backward
  pair's head component under construction.
- **`cs5PairTauR '' (modalDeductiveClosure CS5ModalAxiom (boxInv H))`**: the right-tagged image
  of the `CS5`-deductive closure of `H`'s box-inverse `boxInv H` (`Segment.lean:103`,
  `{B | □B ∈ H}`) -- the "tail-side" content the symmetric canonical model's box-backward case
  needs (`cs5_symmetric_tail_box_gap`, `CS5.lean:686`), pre-saturated by `modalDeductiveClosure`
  (`Intuitionistic/PrimeTheory.lean:78`) so that later exclusion arguments see a deductively
  closed tail rather than the bare box-inverse set. -/
def cs5PairSeed (H : Set (Proposition Atom)) : Set (Proposition (Atom ⊕ Atom)) :=
  cs5PairTauL '' H ∪ cs5PairTauR '' (modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H))

/-- `cs5PairTauL` is injective: the left tagging map never collapses two distinct left-copy
formulas together. A corollary of `Proposition.map_injective` (`Sum.inl` is injective); used by
`cs5PairSeed_mem_iff` to rule out tag collision within the left branch -- the witnessing `φ`
recovered from a left-tagged element of the seed is uniquely determined. -/
theorem cs5PairTauL_injective : Function.Injective (@cs5PairTauL Atom) :=
  Proposition.map_injective Sum.inl_injective

/-- `cs5PairTauR` is injective: the right tagging map never collapses two distinct right-copy
formulas together. Symmetric to `cs5PairTauL_injective`, ruling out tag collision within the
right branch. -/
theorem cs5PairTauR_injective : Function.Injective (@cs5PairTauR Atom) :=
  Proposition.map_injective Sum.inr_injective

/-- **Left injection into the seed.** Every `φ ∈ H` tags into `cs5PairSeed H` via `cs5PairTauL`. -/
theorem cs5PairSeed_mem_left {H : Set (Proposition Atom)} {φ : Proposition Atom} (hφ : φ ∈ H) :
    cs5PairTauL φ ∈ cs5PairSeed H :=
  Set.mem_union_left _ (Set.mem_image_of_mem cs5PairTauL hφ)

/-- **Right injection into the seed.** Every `φ` in the `CS5`-deductive closure of `boxInv H`
tags into `cs5PairSeed H` via `cs5PairTauR`. -/
theorem cs5PairSeed_mem_right {H : Set (Proposition Atom)} {φ : Proposition Atom}
    (hφ : φ ∈ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H)) :
    cs5PairTauR φ ∈ cs5PairSeed H :=
  Set.mem_union_right _ (Set.mem_image_of_mem cs5PairTauR hφ)

/-- **Membership-inversion for the seed.** Every element of `cs5PairSeed H` arises from exactly
one of the two tagging maps: either it is `cs5PairTauL φ` for some `φ ∈ H`, or it is
`cs5PairTauR ψ` for some `ψ` in the `CS5`-deductive closure of `boxInv H`
(`cs5PairTauL_injective`/`cs5PairTauR_injective` rule out tag collision within each branch, so
the witnessing `φ`/`ψ` is uniquely determined whichever branch an element falls in). This is the
case-split the cross-inertness lemma and the two individual exclusions (later phases) induct
against. -/
theorem cs5PairSeed_mem_iff {H : Set (Proposition Atom)} {x : Proposition (Atom ⊕ Atom)} :
    x ∈ cs5PairSeed H ↔
      (∃ φ ∈ H, cs5PairTauL φ = x) ∨
        (∃ ψ ∈ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H), cs5PairTauR ψ = x) := by
  simp only [cs5PairSeed, Set.mem_union, Set.mem_image]

end Cslib.Logic.Modal
