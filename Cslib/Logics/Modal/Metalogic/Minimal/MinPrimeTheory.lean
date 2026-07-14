/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Minimal.MK
public import Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum

/-! # Quasi-Prime Canonical Worlds for `MK`

This module assembles the canonical-world scaffolding for `MK`'s completeness proof by
**reusing** the delivered, `Axioms`-parametric, efq-free quasi-prime machinery
(`QuasiPrime` + `quasi_prime_exclusion` + `imp_refuting_theory` + `box_refuting_theory` +
`dia_refuting_theory` + `quasi_head_realization`, `Constructive/{Segment,SegmentLindenbaum}.lean`)
instantiated at `Axioms := MKModalAxiom`. No new abstractions are introduced: every declaration
here is a thin wrapper (world type + `Preorder` + valuation + `botForces`) copying the shape of
the propositional `MinStrongCompleteness.lean:74-114`.

## Main Definitions

- `MinCanonicalPrimeWorld`: canonical worlds for `MK`, i.e. quasi-prime `MKModalAxiom` theories
  (`QuasiPrime MKModalAxiom`) -- deductively closed with the disjunction property, **no**
  consistency requirement (fallible worlds admitted).
- The canonical `Preorder` instance: `≤` is set inclusion on the underlying theory.
- `canonicalVal`: the canonical valuation, `atom p` forced at `w` iff `atom p ∈ w.val`.
- `minBotForces`: `⊥` is forced at `w` iff `⊥ ∈ w.val` -- a genuine (non-trivial) predicate,
  upward-closed for free via `≤ = ⊆`.
- `min_head_realization`: any `MKModalAxiom`-underivable formula is omitted by the head of some
  quasi-prime theory (thin wrapper over `quasi_head_realization`).

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3.
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Canonical Worlds -/

/-- A canonical world for `MK` is a quasi-prime `MKModalAxiom` theory (`QuasiPrime`):
deductively closed with the disjunction property, but **not** required consistent -- fallible
worlds (containing `⊥`) are admitted. Reuses `QuasiPrime` from `Constructive/Segment.lean`
directly; no redefinition. -/
def MinCanonicalPrimeWorld (Atom : Type u) :=
  { S : Set (Proposition Atom) // QuasiPrime (MKModalAxiom (Atom := Atom)) S }

/-- The canonical preorder on `MinCanonicalPrimeWorld`: set inclusion of the underlying
quasi-prime theories. Mirrors `MinCanonicalWorld`'s `Preorder` instance
(`MinStrongCompleteness.lean:78-81`) and `CanonicalPrimeWorld`'s
(`Intuitionistic/CanonicalModel.lean:85-88`). -/
instance : Preorder (MinCanonicalPrimeWorld Atom) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-- `≤` on `MinCanonicalPrimeWorld` is set inclusion (definitional unfolding lemma). -/
theorem MinCanonicalPrimeWorld.le_iff {w w' : MinCanonicalPrimeWorld Atom} :
    w ≤ w' ↔ w.val ⊆ w'.val := Iff.rfl

/-! ## Canonical Valuation -/

/-- The canonical valuation: atom `p` is forced at world `w` iff `atom p` is a member of the
quasi-prime theory underlying `w`. Mirrors `canonicalVal` (`Intuitionistic/CanonicalModel.lean:94`)
and `minCanonicalVal` (`MinStrongCompleteness.lean:84`). -/
def canonicalVal (w : MinCanonicalPrimeWorld Atom) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val

/-- The canonical valuation is upward-closed with respect to the canonical preorder, as required
by `BModel.v_upward_closed`. -/
theorem canonicalVal_upward_closed
    {w w' : MinCanonicalPrimeWorld Atom} (p : Atom) (hw : w ≤ w') (hv : canonicalVal w p) :
    canonicalVal w' p :=
  hw hv

/-! ## Canonical `botForces` -/

/-- The canonical `botForces` predicate for `MK`: `⊥` is forced at world `w` iff `⊥ ∈ w.val`.
Unlike `IK`'s hard-coded `fun _ => False`, this is a genuine, non-trivial predicate (some
quasi-prime worlds contain `⊥` -- the fallible/exploding worlds), matching `minBotForces`
(`MinStrongCompleteness.lean:101-102`) and `cbotForces` (`Constructive/Segment.lean:182-183`). -/
def minBotForces (w : MinCanonicalPrimeWorld Atom) : Prop :=
  (Proposition.bot : Proposition Atom) ∈ w.val

/-- `minBotForces` is upward-closed: if `⊥ ∈ w.val` and `w ≤ w'`, then `⊥ ∈ w'.val`. Free via
`≤ = ⊆`, matching `minBotForces_upward_closed` (`MinStrongCompleteness.lean:105-108`). -/
theorem minBotForces_upward_closed
    {w w' : MinCanonicalPrimeWorld Atom} (hw : w ≤ w') (hbf : minBotForces w) :
    minBotForces w' :=
  hw hbf

/-- `minBotForces w ↔ ⊥ ∈ w.val` is trivially `Iff.rfl` (the definition). Documents the
membership-based `botForces` convention shared with `MinStrongCompleteness.lean` and
`Constructive/Segment.lean`. -/
theorem minBotForces_iff_botMem (w : MinCanonicalPrimeWorld Atom) :
    minBotForces w ↔ (Proposition.bot : Proposition Atom) ∈ w.val := Iff.rfl

/-! ## Head Realization -/

/-- **Head realization for `MK`**: any `MKModalAxiom`-underivable formula is omitted by some
quasi-prime theory. Thin wrapper over `quasi_head_realization`
(`Constructive/SegmentLindenbaum.lean:242`), instantiated at `Axioms := MKModalAxiom` with the
`implyK`/`implyS`/`orE` constructors as the axiom-membership witnesses. -/
theorem min_head_realization {φ : Proposition Atom}
    (h_nd : ¬ Derivable MKModalAxiom φ) :
    ∃ T, QuasiPrime (MKModalAxiom (Atom := Atom)) T ∧ φ ∉ T :=
  quasi_head_realization (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun A B χ => .orE A B χ) h_nd

end Cslib.Logic.Modal
