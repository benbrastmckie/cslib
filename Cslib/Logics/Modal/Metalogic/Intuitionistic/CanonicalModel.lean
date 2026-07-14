/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory
public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Semantics.Birelational

/-! # Canonical Model for Intuitionistic Modal Logic

This module lays down the birelational canonical-frame data for intuitionistic modal logic:
worlds are prime modal theories (`PrimeTheory.lean`), `≤` is set inclusion, `canonicalVal` is
the atom-membership valuation, and `canonicalR` is the two-clause canonical accessibility
relation required because `◇` is primitive (not `□`-definable) in this framework's
`Modal.Proposition` datatype.

This file is Phase 2a of a multi-phase construction (task 480 plan v2): it contains
**definitions only**, no witness proofs. `canonical_box_witness` (Phase 2b),
`canonical_diamond_witness` (Phase 2c), and the frame conditions `canonical_f1`/`canonical_f2`
(Phase 2d) are added by subsequent phases in this same file.

## Confirmed `Birelational.lean` API (read during Phase 2a, task 480)

- `BFrame World` (requires `[Preorder World]`) bundles `r : World → World → Prop`,
  `f1 : ∀ {w w' v}, w ≤ w' → r w v → ∃ v', r w' v' ∧ v ≤ v'` (up-confluence), and
  `f2 : ∀ {w v v'}, r w v → v ≤ v' → ∃ w', w ≤ w' ∧ r w' v'` (down-confluence).
- `BModel World Atom extends BFrame World` adds `v : World → Atom → Prop`,
  `botForces : World → Prop`, `v_upward_closed`, `bf_upward_closed`.
- `BForces r v botForces w φ` is the forcing relation; `@[simp]` unfolds exist for every
  constructor, in particular `BForces_box` (`∀ w' ≥ w, ∀ u, r w' u → BForces … u φ`) and
  `BForces_diamond` (`∃ u, r w u ∧ BForces … u φ`).
- `IValid`/`MValid` universally quantify over `World`/`r`/`f1`/`f2`/valuation (and, for
  `MValid`, `botForces`), matching the report's §7 parametricity requirement.

These names and shapes are used verbatim by `canonicalR` below and by the later phases
(`canonical_f1`/`canonical_f2` in 2d must match `BFrame.f1`/`BFrame.f2` exactly).

## Main Definitions

- `CanonicalPrimeWorld`: canonical worlds, i.e. prime modal theories (`ModalPrimeTheory`).
- The canonical `Preorder` instance: `≤` is set inclusion on the underlying theory.
- `canonicalVal`: the canonical valuation, `atom p` forced at `w` iff `atom p ∈ w`.
- `canonicalR`: the two-clause canonical accessibility relation (Simpson 1994, clauses 3.2/3.5;
  Wijesekera 1990 on the primitive-`◇` box condition):
  - box clause: `□φ ∈ w → φ ∈ v`;
  - diamond clause: `φ ∈ v → ◇φ ∈ w`.

  Both clauses are required (unlike the classical single-clause canonical relation) because `◇`
  is a primitive connective here, not defined as `¬□¬`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3, clauses 3.2/3.5.
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (the diamond clause has no classical analogue).
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## Canonical Worlds -/

/-- A canonical world for intuitionistic modal logic is a prime modal theory
(`ModalPrimeTheory Axioms`), parametric over the axiom predicate `Axioms`. Worlds are prime
(rather than maximal-consistent, as in the classical `MCS.lean` canonical model) so that the
disjunction property is available for the `or` case of the truth lemma (`TruthLemma.lean`,
Phase 3). -/
def CanonicalPrimeWorld (Axioms : Proposition Atom → Prop) :=
  { S : Set (Proposition Atom) // ModalPrimeTheory Axioms S }

/-- The canonical preorder on `CanonicalPrimeWorld Axioms`: set inclusion of the underlying
prime theories. Mirrors the propositional canonical preorder
(`Cslib.Logic.PL.instPreorderIntCanonicalWorld` in `IntStrongCompleteness.lean`). -/
instance {Axioms : Proposition Atom → Prop} : Preorder (CanonicalPrimeWorld Axioms) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-! ## Canonical Valuation -/

/-- The canonical valuation: atom `p` is forced at world `w` iff `atom p` is a member of the
prime theory underlying `w`. Mirrors `intCanonicalVal` (`IntStrongCompleteness.lean`). -/
def canonicalVal {Axioms : Proposition Atom → Prop} (w : CanonicalPrimeWorld Axioms) (p : Atom) :
    Prop :=
  Proposition.atom p ∈ w.val

/-- The canonical valuation is upward-closed with respect to the canonical preorder, as required
by `BModel.v_upward_closed`. -/
theorem canonicalVal_upward_closed {Axioms : Proposition Atom → Prop}
    {w w' : CanonicalPrimeWorld Axioms} (p : Atom) (hw : w ≤ w') (hv : canonicalVal w p) :
    canonicalVal w' p :=
  hw hv

/-! ## Canonical Accessibility Relation -/

/-- The canonical accessibility relation `canonicalR w v`, carrying **both** a box clause and a
diamond clause since `◇` is primitive and not `□`-definable (Wijesekera 1990; report §6.4):

- box clause (`□φ ∈ w → φ ∈ v`): every boxed formula true at `w` is true at `v`
  ([Simpson1994], clause 3.2's accessibility side);
- diamond clause (`φ ∈ v → ◇φ ∈ w`): every formula true at `v` is possible at `w`
  ([Simpson1994], clause 3.5's accessibility side).

The witness lemmas establishing that this relation actually exists between suitable worlds
(`canonical_box_witness`, `canonical_diamond_witness`) are proved in Phases 2b/2c. -/
def canonicalR {Axioms : Proposition Atom → Prop} (w v : CanonicalPrimeWorld Axioms) : Prop :=
  (∀ φ, (□φ) ∈ w.val → φ ∈ v.val) ∧ (∀ φ, φ ∈ v.val → (◇φ) ∈ w.val)

end Cslib.Logic.Modal
