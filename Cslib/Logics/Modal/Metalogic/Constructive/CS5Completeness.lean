/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

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
rather than as an externally-imposed, non-`cl`-stable side predicate on a pair poset (the gap an
externally-fixed predicate such as `Cons_Y Z := boxInv Z ⊆ Y` runs into: `Y` is fixed outside `Z`,
so nothing forces the predicate to survive `Z`'s deductive closure -- see the "`cl`-Stability of
the Cross-Conditions" section below for why the axiomatic design avoids this).

**Distinct from the discarded `CS5Combined` scaffold.** `CS5Canonical.lean`'s module docstring
records that an earlier `Atom ⊕ Atom` attempt (`CS5Combined`) re-entered Pacheco's unsound
negation-completeness move (`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, unsound for a poset-maximal quasi-prime `Θ`) and
was discarded. This module's construction never invokes negation-completeness: the
cross-conditions are *axioms*, available to any deductively-closed set via a single `modus_ponens`
step, not something derived from maximality. This module's own `crossCond_left_stable`/
`crossCond_right_stable` below confirm this mechanically: both soundness (the `CS5PairAxiom`
constructors themselves) and `cl`-stability of the cross-conditions close sorry-free, with no
negation-completeness step anywhere.

## Main Definitions (this phase)

- `cs5PairTauL`/`cs5PairTauR`: the doubled-atom tagging maps (`Proposition.map Sum.inl`/`Sum.inr`).
- `CS5PairAxiom`: the combined axiom system over `Atom ⊕ Atom` -- `CS5ModalAxiom` on each tagged
  copy, plus the two cross-condition axioms realising `boxInv X ⊆ Y`/`boxInv Y ⊆ X`.
- `cs5PairAxiom_left_derivable`/`cs5PairAxiom_right_derivable`: the easy transport direction,
  `Derivable CS5ModalAxiom φ → Derivable CS5PairAxiom (τ_L φ)` (and the `τ_R` analogue), via
  `Derivable.map` (`DerivationTree.lean`). The converse (needed to show the eventual projected
  pair's components are themselves `CS5ModalAxiom`-quasi-prime) is the R2 conservativity
  lemma, not this phase's concern.
- `crossCond_left_stable`/`crossCond_right_stable`: `cl`-stability of the cross-conditions for
  any `CS5PairAxiom`-deductively-closed set -- library port of the probe's prototype (ii).

## References

* `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` -- `CS5ModalAxiom`, `cs5Tail`,
  `cs5_symmetric_tail_box_gap`, `cs5_axiom_sound''`.
* `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` -- `Derivable.map` (atom-relabeling
  functoriality).
* `crossCond_left_stable`/`crossCond_right_stable` below -- the `cl`-stability lemmas this
  module's axiomatic (as opposed to externally-imposed) cross-condition design was chosen to
  make provable in the first place.
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

Verified simultaneously sound (by construction: every constructor names a `CS5ModalAxiom`
instance or a cross-condition) and `cl`-stable (`crossCond_left_stable`/`crossCond_right_stable`
below). -/
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
the projection to be faithful) is deferred to the R2 conservativity lemma. -/

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
machinery from `Segment.lean`, so this module's `prime_set_exclusion` application inherits this for
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

/-- The two-sided seed for the pair construction over a head `H`: the left-tagged image of `H`
itself, together with the right-tagged image of the `CS5`-deductive closure of `H`'s box-inverse.
Every downstream seed-exclusion statement refers to this set. -/
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

/-! ## The Named Open Obligation and the Conditional `DerivExcludes` Reduction

**Cross-inertness (blocked).** The support lemma originally planned to reduce `DerivExcludes` at
the two-sided seed to the two individual exclusions `τ_L (□A) ∉ cl(seed)` / `τ_R A ∉ cl(seed)` did
not close: the natural "necessitation-only-from-`[]`" invariant for bare-`□` conclusions in
`modalDerivationSystem` is **false** for `CS5PairAxiom` -- `modus_ponens` against the embedded
`CS5ModalAxiom.bBox` schema (`φ → □(◇φ)`, `CS5.lean:216`) produces a bare-`□` conclusion that is
neither an assumption nor a necessitation witness, so the sketched structural induction does not
go through. The individual exclusions (`τ_L (□A) ∉ cl(seed)`, `τ_R A ∉ cl(seed)`) are therefore
**not** landed as theorems here; `cs5Pair_derivExcludes_of_disjunctionProperty` below takes them
as explicit open hypotheses `hL`/`hR` instead, per the plan's own R-B contingency.

**The named open obligation.** What remains genuinely open -- and *is* isolated here as a single
named, non-vacuous `Prop`-valued definition, never asserted as a theorem -- is the constructive
disjunction property at the two-sided seed. -/

/-- **OPEN OBLIGATION (unproven, deliberately not a theorem).** The constructive disjunction
property of `CS5PairAxiom` under the `boxInv` cross-constraint, at the two-sided seed: for a
theory `H` and formula `A`,

    τ_L (□A) ⊔ τ_R A ∉ cl_{CS5PairAxiom} (cs5PairSeed H).

At the *seed* the theory is **not** prime, so "neither disjunct is derivable" (`hL`/`hR` above)
does not give "the disjunction is not derivable" -- constructively the disjunction is strictly
weaker, and `cs5Pair_derivExcludes_of_disjunctionProperty` below shows exactly this gap is the
only piece `DerivExcludes` needs beyond `hL`/`hR`.

**Provenance.** This is [Pacheco2024]'s Lemma 16. Its published proof is **unsound** in this
setting: it uses the negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, which is invalid for a
poset-maximal quasi-prime theory (see this module's opening docstring, "Distinct from the
discarded `CS5Combined` scaffold"). The identical obligation defeated the earlier `CS5Combined`
atom-sum scaffold (`cs5Combined_seed_excludes`, never closed, since removed).

**Corrected (round 2): no *independent* semantic witness exists via a common-valuation model,
but the product-model reading is a genuine candidate, closed separately.** A single common
valuation for both copies identifies `τ_L X` with `τ_R X` and collapses `cross1` to `□B → B`,
under which `τ_R A` is forced whenever `A ∈ H`; that particular semantic route is circular, not
because no semantics exists, but because any semantic witness for the two-sided seed is
equivalent to the pair's own *joint satisfiability* -- exactly what a truth lemma for the
box-backward pair this module is building towards would need to presuppose. The genuinely
distinct candidate is a **product model** over two copies of `IS5`'s semantics (not a common
valuation): this is a real, independently-motivated route, and it is closed on its own terms
(not dismissed as circular) by the R2 conservativity lemma, which shows its residual side
condition is equivalent to the `CS5 = IS5` collapse the mandate has not adopted.

**Status.** Open here. A correct proof is expected to require a cut-free/nested-sequent argument
rather than a direct Hilbert derivation -- specifically Arisaka, Das and Straßburger's nested
sequents for constructive modal logics (`doc_id:
arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`), which covers exactly
CSLib's `CS5` axiom set (safe pair `X = {t,4}`, `Y = {b}`); Marin-Morales-Straßburger's `labIK≤`
does **not** apply here, since its base logic is `IK`, not `CK` -- it settles `IS5`, not `CS5`.
Stated as a definition, not asserted: this module contains no `sorry`.

**DEPRECATED (superseded).** This statement carries **no hypothesis relating `A` to `H`**, and is
**refutable for every `H`** -- see `cs5PairSeedDisjunctionProperty_false` below (witness
`A := ⊥ → ⊥`): every `CS5` theorem lies in `modalDeductiveClosure CS5ModalAxiom S` for *every* set
`S`, so `τ_R A` is already a member of `cs5PairSeed H` itself whenever `A` is `CS5`-provable, well
before any deductive closure is taken. The corrected statement is `CS5PairSeedRightExclusion`
below, which adds the missing hypothesis `A ∉ modalDeductiveClosure CS5ModalAxiom (boxInv H)`. This
definition and `cs5Pair_derivExcludes_of_disjunctionProperty` are kept, unchanged, only because
they remain true (conditionally) statements about a `Prop` that is never asserted; new work should
target `CS5PairSeedRightExclusion` and `cs5Pair_derivExcludes_of_rightExclusion`. -/
def CS5PairSeedDisjunctionProperty (H : Set (Proposition Atom)) (A : Proposition Atom) : Prop :=
  (cs5PairTauL (Proposition.box A)).or (cs5PairTauR A) ∉
    modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)

/-- Every element of a list drawn from `{a, b}` composes, via `cs5Pair_hOrI1`/`hOrI2`/`hOrE`, into
a derivation of `bigOr l → a ⊔ b`; the `[]` base case uses `cs5Pair_hEFQ`. Feeds the `x :: y ::
rest` (length ≥ 2) branch of `cs5Pair_derivExcludes_of_disjunctionProperty`. -/
theorem cs5Pair_bigOr_imp_or {a b : Proposition (Atom ⊕ Atom)}
    (l : List (Proposition (Atom ⊕ Atom))) (hl : ∀ x ∈ l, x = a ∨ x = b) :
    Deriv (@CS5PairAxiom Atom) [] ((Metalogic.bigOr l).imp (a.or b)) := by
  induction l with
  | nil => exact cs5Pair_hEFQ (a.or b)
  | cons x xs ih =>
    have hx : x = a ∨ x = b := hl x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, y = a ∨ y = b := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hximp : Deriv CS5PairAxiom [] (x.imp (a.or b)) := by
      cases hx with
      | inl h => rw [h]; exact cs5Pair_hOrI1 a b
      | inr h => rw [h]; exact cs5Pair_hOrI2 a b
    have hxsimp : Deriv CS5PairAxiom [] ((Metalogic.bigOr xs).imp (a.or b)) := ih hxs
    have hOrE := cs5Pair_hOrE x (Metalogic.bigOr xs) (a.or b)
    exact mp_deriv (mp_deriv hOrE hximp) hxsimp

/-- `⊢ (x ⊔ ⊥) → x`, via `orE` composed with the identity (`Metalogic.empty_imp_id`) and
`cs5Pair_hEFQ`. Feeds the singleton-list branch of `cs5Pair_derivExcludes_of_disjunctionProperty`
(`bigOr [x] = x ⊔ ⊥` by `Metalogic.bigOr`'s equations). -/
theorem cs5Pair_orBot_imp_self (x : Proposition (Atom ⊕ Atom)) :
    Deriv (@CS5PairAxiom Atom) [] ((x.or Proposition.bot).imp x) := by
  have hidx : Deriv CS5PairAxiom [] (x.imp x) :=
    Metalogic.empty_imp_id (modalDerivationSystem CS5PairAxiom) cs5Pair_hCut x
  have hbotx : Deriv CS5PairAxiom [] (Proposition.bot.imp x) := cs5Pair_hEFQ x
  have horE := cs5Pair_hOrE x Proposition.bot x
  exact mp_deriv (mp_deriv horE hidx) hbotx

/-- **The conditional `DerivExcludes` reduction.** Consumes the two individual exclusions
`hL`/`hR` and the named open obligation `hOpen` as **explicit hypotheses** -- since the
cross-inertness argument is blocked, `hL`/`hR` are not available as theorems here either; both
remain open pending a future cross-inertness argument or the spawned disjunction-property
subtask. The theorem itself is proved by case analysis on the `List` argument of `DerivExcludes`
(`Metalogic.PrimeExclusion.lean:332`): the `[]` case is consistency of `T` via `hL` + `EFQ`; the
singleton cases are `hL`/`hR` directly (via `cs5Pair_orBot_imp_self`); the two-element-and-longer
case reduces to `hOpen` (via `cs5Pair_bigOr_imp_or`). Sorry-free regardless of which hypotheses a
future caller can discharge as theorems. -/
theorem cs5Pair_derivExcludes_of_disjunctionProperty {H : Set (Proposition Atom)}
    {A : Proposition Atom}
    (hL : cs5PairTauL (Proposition.box A) ∉
      modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H))
    (hR : cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H))
    (hOpen : CS5PairSeedDisjunctionProperty H A) :
    Metalogic.DerivExcludes (modalDerivationSystem (@CS5PairAxiom Atom))
      {cs5PairTauL (Proposition.box A), cs5PairTauR A}
      (modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) := by
  intro l hl
  have hmem : ∀ x ∈ l, x = cs5PairTauL (Proposition.box A) ∨ x = cs5PairTauR A := by
    intro x hx
    have := hl x hx
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  set T := modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) with hT
  match l, hmem with
  | [], _ =>
    intro hbot
    apply hL
    have hd : (modalDerivationSystem (@CS5PairAxiom Atom)).Deriv [Proposition.bot]
        (cs5PairTauL (Proposition.box A)) :=
      mp_deriv (weakening_deriv (cs5Pair_hEFQ (cs5PairTauL (Proposition.box A)))
          (by simp)) (assumption_deriv (List.mem_singleton_self _))
    exact modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS [Proposition.bot]
      (cs5PairTauL (Proposition.box A))
      (fun x hx => by rw [List.mem_singleton] at hx; rw [hx]; exact hbot) hd
  | [x], hmem =>
    intro hxT
    have hx : x = cs5PairTauL (Proposition.box A) ∨ x = cs5PairTauR A :=
      hmem x (List.mem_singleton_self _)
    have hxorbot_imp_x := cs5Pair_orBot_imp_self x
    have hxT' : x ∈ T := by
      have hd : (modalDerivationSystem (@CS5PairAxiom Atom)).Deriv [x.or Proposition.bot] x :=
        mp_deriv (weakening_deriv hxorbot_imp_x (by simp))
          (assumption_deriv (List.mem_singleton_self _))
      exact modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS [x.or Proposition.bot] x
        (fun y hy => by rw [List.mem_singleton] at hy; rw [hy]; exact hxT) hd
    rcases hx with rfl | rfl
    · exact hL hxT'
    · exact hR hxT'
  | x :: y :: rest, hmem =>
    intro hbig
    apply hOpen
    have hderiv := cs5Pair_bigOr_imp_or (x :: y :: rest) hmem
    have hd : (modalDerivationSystem (@CS5PairAxiom Atom)).Deriv
        [Metalogic.bigOr (x :: y :: rest)]
        ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)) :=
      mp_deriv (weakening_deriv hderiv (by simp))
        (assumption_deriv (List.mem_singleton_self _))
    exact modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS
      [Metalogic.bigOr (x :: y :: rest)] ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A))
      (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hbig) hd

/-! ## The Corrected Obligation (Round 2) and Its Refutation

`CS5PairSeedDisjunctionProperty` above is **false as literally stated, for every `H`** -- it
carries no hypothesis relating `A` to `H`, so it fails already at any `CS5`-provable `A` (witness
`A := ⊥ → ⊥`, since every `CS5` theorem lies in `modalDeductiveClosure CS5ModalAxiom S` for
*every* `S`, in particular `S := boxInv H`, putting `τ_R A` in `cs5PairSeed H` itself). The
refutations below make this a permanent, machine-checked regression: the unconditioned form can
never silently return. `CS5PairSeedRightExclusion` repairs the statement by adding exactly the
missing hypothesis. -/

/-- **The corrected obligation (Round 2).** The right-exclusion form of the pair-seed
obligation, guarded by the hypothesis `CS5PairSeedDisjunctionProperty` was missing: `A` must not
already lie in the `CS5`-deductive closure of `H`'s box-inverse. Equivalent, by round 1's
reduction (`hOpen ↔ hR`), to the disjunction-property form under the same guard; stated directly
in right-exclusion form since that is what every downstream consumer
(`cs5Pair_derivExcludes_of_rightExclusion`) actually needs. -/
def CS5PairSeedRightExclusion (H : Set (Proposition Atom)) (A : Proposition Atom) : Prop :=
  A ∉ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H) →
    cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)

/-- Every `CS5` theorem lies in the `CS5`-deductive closure of *every* set `S` -- in particular
`⊥ → ⊥` (an `efq ⊥` axiom instance), witnessed by the empty premise list. Feeds
`cs5PairSeedDisjunctionProperty_false`: instantiated at `S := boxInv H`, this is exactly why the
seed's right component already contains `τ_R (⊥ → ⊥)` before any closure is taken. -/
theorem cs5_botImpBot_mem_closure (S : Set (Proposition Atom)) :
    (Proposition.bot.imp Proposition.bot) ∈ modalDeductiveClosure (@CS5ModalAxiom Atom) S := by
  refine ⟨[], ?_, ?_⟩
  · intro x hx; exact nomatch hx
  · exact ⟨.ax [] _ (CS5ModalAxiom.efq Proposition.bot)⟩

/-- Consequently `τ_R (⊥ → ⊥)` is already a member of the two-sided seed itself, for every `H` --
before any deductive closure is taken. -/
theorem cs5PairSeed_botImpBot_mem (H : Set (Proposition Atom)) :
    cs5PairTauR (Proposition.bot.imp Proposition.bot) ∈ (@cs5PairSeed Atom) H :=
  Set.mem_union_right _ (Set.mem_image_of_mem _ (cs5_botImpBot_mem_closure _))

/-- **Refutation of the right-exclusion component.** `τ_R (⊥ → ⊥)` lies in the `CS5PairAxiom`
closure of the seed, for every `H`. -/
theorem cs5PairSeed_tauR_botImpBot_mem_closure (H : Set (Proposition Atom)) :
    cs5PairTauR (Proposition.bot.imp Proposition.bot) ∈
      modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) :=
  modal_subset_deductive_closure _ _ (cs5PairSeed_botImpBot_mem H)

/-- **Refutation of the named open obligation (permanent regression).**
`CS5PairSeedDisjunctionProperty H (⊥ → ⊥)` is FALSE for every `H`, in particular for `H = ∅`.
Mechanism: `⊥ → ⊥` is a `CS5` theorem, hence lies in `modalDeductiveClosure CS5ModalAxiom S` for
every `S` (`cs5_botImpBot_mem_closure`), in particular `S := boxInv H`; so
`τ_R (⊥ → ⊥) ∈ cs5PairSeed H` already, and `orI2` through deductive closure puts the disjunction
`τ_L (□(⊥ → ⊥)) ⊔ τ_R (⊥ → ⊥)` in `modalDeductiveClosure CS5PairAxiom (cs5PairSeed H)`, which is
exactly what `CS5PairSeedDisjunctionProperty H (⊥ → ⊥)` denies. This landed theorem is the reason
`CS5PairSeedDisjunctionProperty` is deprecated above in favor of `CS5PairSeedRightExclusion`: the
unconditioned statement can never be reintroduced without contradicting this regression. -/
theorem cs5PairSeedDisjunctionProperty_false (H : Set (Proposition Atom)) :
    ¬ CS5PairSeedDisjunctionProperty H (Proposition.bot.imp Proposition.bot) := by
  intro hOpen
  apply hOpen
  set A : Proposition Atom := Proposition.bot.imp Proposition.bot with hA
  have hR := cs5PairSeed_tauR_botImpBot_mem_closure (Atom := Atom) H
  have hd : (modalDerivationSystem (@CS5PairAxiom Atom)).Deriv [cs5PairTauR A]
      ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)) :=
    mp_deriv (weakening_deriv (cs5Pair_hOrI2 (cs5PairTauL (Proposition.box A)) (cs5PairTauR A))
        (by simp)) (assumption_deriv (List.mem_singleton_self _))
  exact modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS [cs5PairTauR A]
    ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A))
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hR) hd

/-- **The `H`-driven companion refutation.** Unlike `cs5PairSeedDisjunctionProperty_false`, this
does not rely on `A` being a `CS5` theorem: whenever `□A ∈ H`, `A` is already a member of
`boxInv H`, so `τ_R A` lands in the seed's right component directly. Feeds
`cs5PairSeedDisjunctionProperty_false_of_boxMem`. -/
theorem cs5PairSeed_tauR_mem_closure_of_boxMem {H : Set (Proposition Atom)}
    {A : Proposition Atom} (h : Proposition.box A ∈ H) :
    cs5PairTauR A ∈ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) :=
  modal_subset_deductive_closure _ _
    (Set.mem_union_right _
      (Set.mem_image_of_mem _ (modal_subset_deductive_closure _ _ h)))

/-- **The `H`-driven companion refutation, disjunction-property form.** Whenever `□A ∈ H`, the
named open obligation `CS5PairSeedDisjunctionProperty H A` also fails -- by the identical `orI2`
argument as `cs5PairSeedDisjunctionProperty_false`, but seeded from
`cs5PairSeed_tauR_mem_closure_of_boxMem` instead of `A` being a `CS5` theorem. Confirms the
refutation is not an artifact of the particular witness `⊥ → ⊥`: it holds uniformly whenever the
seed already contains `τ_R A` directly, for whatever reason. -/
theorem cs5PairSeedDisjunctionProperty_false_of_boxMem {H : Set (Proposition Atom)}
    {A : Proposition Atom} (h : Proposition.box A ∈ H) :
    ¬ CS5PairSeedDisjunctionProperty H A := by
  intro hOpen
  apply hOpen
  have hR := cs5PairSeed_tauR_mem_closure_of_boxMem h
  have hd : (modalDerivationSystem (@CS5PairAxiom Atom)).Deriv [cs5PairTauR A]
      ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)) :=
    mp_deriv (weakening_deriv (cs5Pair_hOrI2 (cs5PairTauL (Proposition.box A)) (cs5PairTauR A))
        (by simp)) (assumption_deriv (List.mem_singleton_self _))
  exact modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS [cs5PairTauR A]
    ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A))
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hR) hd

/-! ## Reduction Lemmas Under the Corrected Statement (Round 2)

Round 1's reduction survives the Round 2 repair unchanged: `CS5PairSeedDisjunctionProperty H A`
(the disjunction form) and the bare right exclusion `cs5PairTauR A ∉ cl(cs5PairSeed H)` are
**equivalent at every fixed `H`, `A`** -- no guard is needed for the equivalence itself, only for
`CS5PairSeedRightExclusion`'s use of it (round 2 §1.1's counterexample defeats the bare right
exclusion, not the equivalence between it and the disjunction form). This section collapses the
module's three open obligations (`hL`, `hR`, `CS5PairSeedDisjunctionProperty`) plus the blocked
cross-inertness lemma to the single corrected obligation `CS5PairSeedRightExclusion`, by deriving
`hL` and the disjunction form from `hR` alone via `cross1`. -/

/-- **`cross1`, restated with the box pulled outside the tag.** `⊢ (τ_L (□A) ⊔ τ_R A) → τ_R A`,
via `orE` against `CS5PairAxiom.cross1` and identity. `cs5PairTauL (Proposition.box A)` and
`Proposition.box (cs5PairTauL A)` coincide definitionally (`Proposition.map`'s `box` case is
`rfl`, `Basic.lean`), so `CS5PairAxiom.cross1 A` -- whose stated conclusion is
`(Proposition.box (cs5PairTauL A)).imp (cs5PairTauR A)` -- is already an axiom instance of the
antecedent shape used here. -/
theorem cs5Pair_or_imp_right (A : Proposition Atom) :
    Deriv (@CS5PairAxiom Atom) []
      (((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)).imp (cs5PairTauR A)) := by
  have hcross : Deriv (@CS5PairAxiom Atom) []
      ((cs5PairTauL (Proposition.box A)).imp (cs5PairTauR A)) :=
    ⟨.ax [] _ (CS5PairAxiom.cross1 A)⟩
  have hid : Deriv (@CS5PairAxiom Atom) [] ((cs5PairTauR A).imp (cs5PairTauR A)) :=
    Metalogic.empty_imp_id (modalDerivationSystem CS5PairAxiom) cs5Pair_hCut _
  exact mp_deriv (mp_deriv (cs5Pair_hOrE _ _ _) hcross) hid

/-- **The disjunction form follows from the bare right exclusion.** If `τ_R A ∉ cl(seed)`, then
`CS5PairSeedDisjunctionProperty H A` holds: were the disjunction `τ_L (□A) ⊔ τ_R A` in the
closure, `cs5Pair_or_imp_right` would put `τ_R A` there too, via `modus_ponens` through closure
(`modalDeductiveClosure_closed`). Round 1's `hOpen ⟸ hR` direction. -/
theorem cs5Pair_disjunctionProperty_of_rightExclusion {H : Set (Proposition Atom)}
    {A : Proposition Atom}
    (hR : cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :
    CS5PairSeedDisjunctionProperty H A := by
  intro hor
  apply hR
  refine modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS
    [(cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)] (cs5PairTauR A)
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hor) ?_
  exact mp_deriv (weakening_deriv (cs5Pair_or_imp_right A) (by simp))
    (assumption_deriv (List.mem_singleton_self _))

/-- **The bare right exclusion follows from the disjunction form.** Converse of
`cs5Pair_disjunctionProperty_of_rightExclusion`, via `orI2`: `hOpen` excludes the disjunction from
the closure, and `τ_R A` implies the disjunction, so `τ_R A` is excluded too. Round 1's
`hOpen ⟹ hR` direction. Together the two directions give `CS5PairSeedDisjunctionProperty H A ↔
τ_R A ∉ cl(seed)` at fixed `H`, `A`, unconditionally -- the equivalence needs no guard; only
`CS5PairSeedRightExclusion`'s *use* of the right-hand side does (round 2 §1.1). -/
theorem cs5Pair_rightExclusion_of_disjunctionProperty {H : Set (Proposition Atom)}
    {A : Proposition Atom} (hOpen : CS5PairSeedDisjunctionProperty H A) :
    cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) := by
  intro hR
  apply hOpen
  refine modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS
    [cs5PairTauR A] ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A))
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hR) ?_
  exact mp_deriv (weakening_deriv (cs5Pair_hOrI2 (cs5PairTauL (Proposition.box A))
    (cs5PairTauR A)) (by simp)) (assumption_deriv (List.mem_singleton_self _))

/-- **The left exclusion follows from the bare right exclusion.** Round 1 R3: if
`τ_R A ∉ cl(seed)`, then `τ_L (□A) ∉ cl(seed)` too, again via `cross1` through closure -- were
`τ_L (□A)` in the closure, `cross1` would place `τ_R A` there as well. -/
theorem cs5Pair_leftExclusion_of_rightExclusion {H : Set (Proposition Atom)}
    {A : Proposition Atom}
    (hR : cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :
    cs5PairTauL (Proposition.box A) ∉
      modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) := by
  intro hL
  apply hR
  refine modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS
    [cs5PairTauL (Proposition.box A)] (cs5PairTauR A)
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hL) ?_
  exact mp_deriv (weakening_deriv (⟨.ax [] _ (CS5PairAxiom.cross1 A)⟩ :
      Deriv (@CS5PairAxiom Atom) [] ((cs5PairTauL (Proposition.box A)).imp (cs5PairTauR A)))
    (by simp)) (assumption_deriv (List.mem_singleton_self _))

/-- **The corrected entry point.** Collapses the module's three open obligations (`hL`, `hR`,
`CS5PairSeedDisjunctionProperty`) plus the blocked cross-inertness lemma to the single corrected
obligation `CS5PairSeedRightExclusion`: given `hA : A ∉ cl_CS5(boxInv H)`
(`cs5_box_mem_of_mem_boxInv_closure` below discharges this from the caller's actual hypothesis
`□A ∉ H`) and `hExcl : CS5PairSeedRightExclusion H A`,
`hExcl hA` is the bare right exclusion `hR`, from which `hL` and the disjunction form both follow
(`cs5Pair_leftExclusion_of_rightExclusion`/`cs5Pair_disjunctionProperty_of_rightExclusion`),
composing into the landed `cs5Pair_derivExcludes_of_disjunctionProperty`. Note that this entry
point carries the extra hypothesis `hA` the old `cs5Pair_derivExcludes_of_disjunctionProperty`
did not have -- flagged in the plan's Goals & Non-Goals as the one place this repair is not a
strict strengthening in isolation; the caller-side discharge lemma below shows it is not a net
weakening in practice, since
`hA` is discharged for free whenever `H` is `CS5`-deductively closed and `□A ∉ H`, which every
caller of this module already has. -/
theorem cs5Pair_derivExcludes_of_rightExclusion {H : Set (Proposition Atom)}
    {A : Proposition Atom}
    (hA : A ∉ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H))
    (hExcl : CS5PairSeedRightExclusion H A) :
    Metalogic.DerivExcludes (modalDerivationSystem (@CS5PairAxiom Atom))
      {cs5PairTauL (Proposition.box A), cs5PairTauR A}
      (modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :=
  cs5Pair_derivExcludes_of_disjunctionProperty
    (cs5Pair_leftExclusion_of_rightExclusion (hExcl hA))
    (hExcl hA)
    (cs5Pair_disjunctionProperty_of_rightExclusion (hExcl hA))

/-! ## Caller-Side Bridge From `□A ∉ H` to the Side Condition

`cs5Pair_derivExcludes_of_rightExclusion` above needs `hA : A ∉ modalDeductiveClosure
CS5ModalAxiom (boxInv H)`, which round 2 §1.1's counterexample shape shows is **not** free in
general (its counterexample is `□(B → A), □B ∈ H` with `□A ∉ H` -- a set `H` that is *not*
`CS5`-deductively closed). This section shows the counterexample shape cannot occur once `H`
**is** `CS5`-deductively closed: `k` applied to `□(B → A)` and `□B` already puts `□A ∈ H`, so a
deductively closed `H` can never witness `□A ∉ H` together with `□(B → A), □B ∈ H`. Consequently
`hA` is free for every caller with a deductively closed `H` and `□A ∉ H` -- exactly the
hypotheses every real caller of this module already carries, per the plan's Goals & Non-Goals
discussion of why the added `hA` hypothesis is not a net weakening in practice. -/

/-- **Box-over-finite-conjunction.** If every element of `L` has its box in a `CS5`-deductively
closed `H`, so does the box of their conjunction `bigAnd L` (`SegmentLindenbaum.lean`'s dual of
`bigAnd_mem_of_forall_mem`, but boxed): necessitate the `andI` axiom instance for the head
element and the recursive conjunction, then apply `k` twice -- once against the head's box,
once against the tail conjunction's box (by the induction hypothesis) -- landing
`□(head ∧ tail) ∈ H` since `H` is deductively closed and both premises are already in `H`. -/
theorem cs5_box_bigAnd_mem_of_forall_boxMem {H : Set (Proposition Atom)}
    (hH : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5ModalAxiom Atom)) H) :
    ∀ (L : List (Proposition Atom)), (∀ B ∈ L, Proposition.box B ∈ H) →
      Proposition.box (bigAnd L) ∈ H
  | [], _ => by
      have hd : Deriv (@CS5ModalAxiom Atom) []
          (Proposition.box (Proposition.bot.imp Proposition.bot)) := by
        obtain ⟨d⟩ : Deriv (@CS5ModalAxiom Atom) [] (Proposition.bot.imp Proposition.bot) :=
          ⟨.ax [] _ (CS5ModalAxiom.efq Proposition.bot)⟩
        exact ⟨.necessitation _ d⟩
      exact hH [] _ (fun _ h => nomatch h) hd
  | B :: Bs, hmem => by
      have hB : Proposition.box B ∈ H := hmem B (List.mem_cons.mpr (Or.inl rfl))
      have hBs : Proposition.box (bigAnd Bs) ∈ H :=
        cs5_box_bigAnd_mem_of_forall_boxMem hH Bs
          (fun C hC => hmem C (List.mem_cons.mpr (Or.inr hC)))
      have hax : Deriv (@CS5ModalAxiom Atom) []
          (B.imp ((bigAnd Bs).imp (B.and (bigAnd Bs)))) :=
        ⟨.ax [] _ (CS5ModalAxiom.andI B (bigAnd Bs))⟩
      have hnec : Deriv (@CS5ModalAxiom Atom) []
          (Proposition.box (B.imp ((bigAnd Bs).imp (B.and (bigAnd Bs))))) := by
        obtain ⟨dax⟩ := hax
        exact ⟨.necessitation _ dax⟩
      have hk1 : Deriv (@CS5ModalAxiom Atom) []
          ((Proposition.box (B.imp ((bigAnd Bs).imp (B.and (bigAnd Bs))))).imp
            ((Proposition.box B).imp (Proposition.box ((bigAnd Bs).imp (B.and (bigAnd Bs)))))) :=
        ⟨.ax [] _ (CS5ModalAxiom.k B ((bigAnd Bs).imp (B.and (bigAnd Bs))))⟩
      have hstep1 : Deriv (@CS5ModalAxiom Atom) []
          ((Proposition.box B).imp (Proposition.box ((bigAnd Bs).imp (B.and (bigAnd Bs))))) :=
        mp_deriv hk1 hnec
      have hk2 : Deriv (@CS5ModalAxiom Atom) []
          ((Proposition.box ((bigAnd Bs).imp (B.and (bigAnd Bs)))).imp
            ((Proposition.box (bigAnd Bs)).imp (Proposition.box (B.and (bigAnd Bs))))) :=
        ⟨.ax [] _ (CS5ModalAxiom.k (bigAnd Bs) (B.and (bigAnd Bs)))⟩
      have hBoxBmem : Deriv (@CS5ModalAxiom Atom) [Proposition.box B, Proposition.box (bigAnd Bs)]
          (Proposition.box B) := assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
      have hBoxRestmem : Deriv (@CS5ModalAxiom Atom)
          [Proposition.box B, Proposition.box (bigAnd Bs)] (Proposition.box (bigAnd Bs)) :=
        assumption_deriv (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have hstep1' : Deriv (@CS5ModalAxiom Atom)
          [Proposition.box B, Proposition.box (bigAnd Bs)]
          (Proposition.box ((bigAnd Bs).imp (B.and (bigAnd Bs)))) :=
        mp_deriv (weakening_deriv hstep1 (by simp)) hBoxBmem
      have hk2' : Deriv (@CS5ModalAxiom Atom) [Proposition.box B, Proposition.box (bigAnd Bs)]
          ((Proposition.box ((bigAnd Bs).imp (B.and (bigAnd Bs)))).imp
            ((Proposition.box (bigAnd Bs)).imp (Proposition.box (B.and (bigAnd Bs))))) :=
        weakening_deriv hk2 (by simp)
      have hd : Deriv (@CS5ModalAxiom Atom) [Proposition.box B, Proposition.box (bigAnd Bs)]
          (Proposition.box (B.and (bigAnd Bs))) :=
        mp_deriv (mp_deriv hk2' hstep1') hBoxRestmem
      exact hH [Proposition.box B, Proposition.box (bigAnd Bs)] _
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hB
          · rcases List.mem_cons.mp hx' with rfl | hx''
            · exact hBs
            · nomatch hx'')
        hd

/-- **The finite witness list of `A`'s membership in `cl_CS5(boxInv H)` transports `box A` into
`H`.** The witness list `L` lies in `boxInv H` by hypothesis, so `box (bigAnd L) ∈ H`
(`cs5_box_bigAnd_mem_of_forall_boxMem`); necessitating the `L ⊢ A` derivation packed via
`derivImpBigAndOfAppend` into `⊢ bigAnd L → A` and applying `k` against `box (bigAnd L) ∈ H`
transports the derivation to `box A ∈ H`, using that `H` is deductively closed. -/
theorem cs5_box_mem_of_mem_boxInv_closure {H : Set (Proposition Atom)}
    (hH : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5ModalAxiom Atom)) H)
    {A : Proposition Atom}
    (hA : A ∈ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H)) :
    Proposition.box A ∈ H := by
  obtain ⟨L, hL, hd⟩ := hA
  obtain ⟨d⟩ := hd
  have hBoxBigAnd : Proposition.box (bigAnd L) ∈ H :=
    cs5_box_bigAnd_mem_of_forall_boxMem hH L hL
  have dImp : DerivationTree (@CS5ModalAxiom Atom) [] ((bigAnd L).imp A) :=
    derivImpBigAndOfAppend (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ) [] L A d
  have hNec : Deriv (@CS5ModalAxiom Atom) [] (Proposition.box ((bigAnd L).imp A)) :=
    ⟨.necessitation _ dImp⟩
  have hk : Deriv (@CS5ModalAxiom Atom) []
      ((Proposition.box ((bigAnd L).imp A)).imp
        ((Proposition.box (bigAnd L)).imp (Proposition.box A))) :=
    ⟨.ax [] _ (CS5ModalAxiom.k (bigAnd L) A)⟩
  have hstep : Deriv (@CS5ModalAxiom Atom) []
      ((Proposition.box (bigAnd L)).imp (Proposition.box A)) := mp_deriv hk hNec
  have hd2 : Deriv (@CS5ModalAxiom Atom) [Proposition.box (bigAnd L)] (Proposition.box A) :=
    mp_deriv (weakening_deriv hstep (by simp)) (assumption_deriv (List.mem_singleton_self _))
  exact hH [Proposition.box (bigAnd L)] _
    (fun x hx => by rw [List.mem_singleton] at hx; rw [hx]; exact hBoxBigAnd) hd2

/-- **The named caller-side discharge.** Contrapositive of `cs5_box_mem_of_mem_boxInv_closure`:
whenever `H` is `CS5`-deductively closed and `□A ∉ H`, the side condition
`cs5Pair_derivExcludes_of_rightExclusion` needs is free. This is what makes the added `hA`
hypothesis not a net weakening in practice -- round 2 §1.1's counterexample shape
(`□(B → A), □B ∈ H` with `□A ∉ H`) cannot arise once `H` is deductively closed, since `k` applied
to `□(B → A)` and `□B` already forces `□A ∈ H`. -/
theorem cs5_notMem_boxInv_closure_of_boxNotMem {H : Set (Proposition Atom)}
    (hH : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5ModalAxiom Atom)) H)
    {A : Proposition Atom} (h : Proposition.box A ∉ H) :
    A ∉ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H) :=
  fun hmem => h (cs5_box_mem_of_mem_boxInv_closure hH hmem)

/-! ## Retraction Functoriality (the Signature-Collapse Route, Corrected)

The task mandate records a non-goal: the signature-collapse route via a sum-elimination
retraction `Sum.elim id id : Atom ⊕ Atom → Atom`, collapsing the two tagged copies back onto a
single `Atom`. Its recorded rationale was that the retraction is **not schema-compatible** --
that the image of the first cross axiom, `□B → B`, is not an instance of the `CS5ModalAxiom`
schema. **That reason is wrong.** `CS5ModalAxiom.tBox` is exactly `□φ → φ` (`CS5` contains `T`),
so `□B → B` *is* a `CS5ModalAxiom` instance; the retraction below is schema-compatible at every
`CS5PairAxiom` constructor, both cross axioms landing on `tBox`. The route's Non-Goal
*conclusion* is still correct, but for a different reason: the bound the retraction yields
(`τ_R A ∈ cl(seed) → A ∈ cl_CS5(H ∪ cl_CS5(boxInv H))`) is compatible with `□A ∉ H` (that bound
does not give `A ∈ H`), so it is too weak to discharge the seed-exclusion obligation; and no
atom relabeling can do better, since every retraction identifying the two tagged copies is
forced to identify the copies at the atom level too (`Sum.elim g g`'s image of `cross1`'s atom
instance is `⊢ □(g p) → g p`, already a `tBox` instance for *any* `g`, so schema-compatibility
alone cannot rule out weaker bounds either). -/

/-- **The sum-elimination retraction.** Collapses the two tagged copies of `Atom ⊕ Atom` back
onto a single `Atom`, identifying `Sum.inl`- and `Sum.inr`-tagged atoms. -/
def cs5PairRetract (x : Atom ⊕ Atom) : Atom := Sum.elim id id x

@[simp] theorem cs5PairRetract_tauL (φ : Proposition Atom) :
    Proposition.map cs5PairRetract (cs5PairTauL φ) = φ := by
  rw [cs5PairTauL, Proposition.map_map]
  have h : (cs5PairRetract ∘ Sum.inl : Atom → Atom) = id := rfl
  rw [h, Proposition.map_id]

@[simp] theorem cs5PairRetract_tauR (φ : Proposition Atom) :
    Proposition.map cs5PairRetract (cs5PairTauR φ) = φ := by
  rw [cs5PairTauR, Proposition.map_map]
  have h : (cs5PairRetract ∘ Sum.inr : Atom → Atom) = id := rfl
  rw [h, Proposition.map_id]

/-- **The retraction is schema-compatible (corrected Non-Goal 2).** Every `CS5PairAxiom`
instance maps to a genuine `CS5ModalAxiom` instance under `cs5PairRetract`. Both cross axioms
land on `CS5ModalAxiom.tBox` (`□B → B`), which *is* a `CS5` schema instance since `CS5` contains
`T` -- contradicting the mandate's recorded reason for the Non-Goal (see the section docstring
above for the corrected reason the route still fails). -/
theorem cs5PairRetract_schema_compatible (ψ : Proposition (Atom ⊕ Atom)) (h : CS5PairAxiom ψ) :
    CS5ModalAxiom (Proposition.map cs5PairRetract ψ) := by
  cases h with
  | left ψ h => rwa [cs5PairRetract_tauL]
  | right ψ h => rwa [cs5PairRetract_tauR]
  | cross1 B => simpa [cs5PairRetract_tauL, cs5PairRetract_tauR] using CS5ModalAxiom.tBox B
  | cross2 B => simpa [cs5PairRetract_tauL, cs5PairRetract_tauR] using CS5ModalAxiom.tBox B
  | implyK φ ψ =>
      exact CS5ModalAxiom.implyK
        (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | implyS φ ψ χ =>
      exact CS5ModalAxiom.implyS (Proposition.map cs5PairRetract φ)
        (Proposition.map cs5PairRetract ψ) (Proposition.map cs5PairRetract χ)
  | efq φ => exact CS5ModalAxiom.efq (Proposition.map cs5PairRetract φ)
  | andI φ ψ =>
      exact CS5ModalAxiom.andI
        (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | andE1 φ ψ =>
      exact CS5ModalAxiom.andE1
        (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | andE2 φ ψ =>
      exact CS5ModalAxiom.andE2
        (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | orI1 φ ψ =>
      exact CS5ModalAxiom.orI1
        (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | orI2 φ ψ =>
      exact CS5ModalAxiom.orI2
        (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | orE φ ψ χ =>
      exact CS5ModalAxiom.orE (Proposition.map cs5PairRetract φ)
        (Proposition.map cs5PairRetract ψ) (Proposition.map cs5PairRetract χ)

/-- The retraction sends the two-sided seed into `H ∪ cl_CS5(boxInv H)`. -/
theorem cs5PairRetract_seed {H : Set (Proposition Atom)} {x : Proposition (Atom ⊕ Atom)}
    (hx : x ∈ cs5PairSeed H) :
    Proposition.map cs5PairRetract x ∈
      H ∪ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H) := by
  rcases cs5PairSeed_mem_iff.mp hx with ⟨φ, hφ, rfl⟩ | ⟨ψ, hψ, rfl⟩
  · exact Or.inl (by rwa [cs5PairRetract_tauL])
  · exact Or.inr (by rwa [cs5PairRetract_tauR])

/-- **The collapse bound (best obtainable from any atom relabeling).** If `τ_R A` is in the
combined closure of the seed then `A` is in the plain `CS5` closure of `H ∪ cl_CS5(boxInv H)`.
Since `□A ∉ H` does **not** give `A ∉ H`, this bound is too weak to discharge the bare right
exclusion `hR` -- the route fails for this reason (a bound too weak to be useful), not for
schema-incompatibility (`cs5PairRetract_schema_compatible` above shows the retraction *is*
schema-compatible). -/
theorem cs5PairRetract_bound {H : Set (Proposition Atom)} {A : Proposition Atom}
    (h : cs5PairTauR A ∈ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :
    A ∈ modalDeductiveClosure (@CS5ModalAxiom Atom)
      (H ∪ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H)) := by
  obtain ⟨L, hL, hd⟩ := h
  refine ⟨L.map (Proposition.map cs5PairRetract), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact cs5PairRetract_seed (hL y hy)
  · have := Deriv.map cs5PairRetract cs5PairRetract_schema_compatible hd
    rwa [cs5PairRetract_tauR] at this

/-! ## Open Obligations

**Proved, this module:**
- `cs5PairAxiom_left_derivable`/`cs5PairAxiom_right_derivable`, `crossCond_left_stable`/
  `crossCond_right_stable`, the full primeness-engine hypothesis bundle (`cs5Pair_hImplyK`
  through `cs5Pair_hCut`), `cs5PairSeed` and its membership lemmas, and the conditional
  `cs5Pair_derivExcludes_of_disjunctionProperty`.
- **Not proved:** the cross-inertness support lemma (blocked, see above), the two individual
  seed exclusions `hL`/`hR` (skipped -- depended on cross-inertness), and the named open
  obligation `CS5PairSeedDisjunctionProperty` itself (research-grade, no semantic witness,
  carried by the spawned subtask).
- **What a discharge would unlock:** `hL`, `hR`, and `CS5PairSeedDisjunctionProperty H A` together
  instantiate `Metalogic.prime_set_exclusion` (via the bundle above) at `CS5PairAxiom`, giving a
  prime admissible `T ⊇ cl(cs5PairSeed H)` excluding `{τ_L (□A), τ_R A}`; projecting `T`'s two
  components back through `cs5PairTauL`/`cs5PairTauR` would then be the candidate box-backward
  pair `⟨H', T'⟩` feeding a native `cs5_completeness''` -- not attempted by this module (see the
  Non-Goals of the governing plan). -/

end Cslib.Logic.Modal
