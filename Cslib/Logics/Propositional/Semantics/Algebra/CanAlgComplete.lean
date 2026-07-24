/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentGeneric
public import Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness

/-! # Fragment-Generic Algebraic Completeness

**`CanAlgComplete` is the single documented terminal interface for fragment algebraic
completeness** in the propositional-algebra completeness stack. Every piecewise completeness
theorem in this directory (`MPL.hilbert_alg_completeness` in `HilbertCompleteness.lean`,
`conjImp_brouwerian_completeness` in `BrouwerianCompleteness.lean`, and the corresponding
`MplConservativeChain.lean` results) is a **load-bearing internal input** to one of the three
instances below (`canAlgCompleteIsBotFree`, `canAlgCompleteIsOrBotFree`,
`canAlgCompleteIsImpTopOnly`) — those inputs stay public because they have dozens of external
use-sites (see each theorem's own docstring for the exact count), but callers wanting the
*fragment-completeness* property itself should go through `CanAlgComplete`/`canAlgComplete_iff`
rather than the piecewise theorems directly.

This module bundles the per-fragment algebraic completeness results (already proved piecewise in
`HilbertCompleteness.lean`, `MplConservativeChain.lean`, and `BrouwerianCompleteness.lean`) behind
a single generic interface, `CanAlgComplete P`. It completes the residual documented in
`FragmentGeneric.lean`: the syntactic side `GHAValid φ → Derivable X-logic φ` is *not* new
mathematics, only the unifying abstraction was missing.

See also `FragmentConservativity` (`FragmentConservativity.lean`) for the sibling generic
interface on the *conservativity* (subsumption/biconditional/ND) side of the same fragments;
`CanAlgComplete` and `FragmentConservativity` together are the two terminal interfaces of the
propositional-algebra completeness/conservativity stack.

## The `CanAlgComplete` Property

A formula predicate `P` *can be algebraically completed* if there is a target axiom system `Ax`
whose derivability coincides with GHA-validity on the `P`-fragment. This is captured by the
`structure CanAlgComplete P` bundling:
- `Ax`: the target sub-logic;
- `complete`: GHA-validity of a `P`-formula yields derivability in `Ax`;
- `sound`: derivability in `Ax` yields GHA-validity.

A `structure` (rather than a `class`) is used because `Ax` is *output* data that varies per
fragment and cannot be inferred by instance resolution.

## Main Results

- `CanAlgComplete`: the bundled completeness property for a formula predicate.
- `canAlgComplete_iff`: on the `P`-fragment, `Derivable Ax φ ↔ GHAValid φ`.
- `canAlgComplete_haValid_iff`: for ⊥-free fragments, this upgrades to `Derivable Ax φ ↔ HAValid φ`
  by composing with `ghaValid_iff_haValid_of_botFree`.
- `canAlgCompleteIsBotFree`, `canAlgCompleteIsOrBotFree`, `canAlgCompleteIsImpTopOnly`: the three
  fragment instances, each built entirely by reuse of existing sorry-free theorems.

## Design Notes

This file is **additive**: no existing proof is modified. The three instances are term-level
compositions of `MPL.hilbert_alg_completeness`, `mplAxiom_iff_impAxiom`,
`conjImp_brouwerian_completeness`, `GHAValid_implies_BrouwerianValid_direct`, and the
axiom-subsumption lemmas. The canonical algebras used are `LowerSet B` (for the Brouwerian route)
and `WithBot G` (for the ⊥-free collapse), not a bespoke implicative free algebra: the
implicational fragment `IsImpTopOnly` is recovered by
fragment subsumption (`IsImpTopOnly → IsOrBotFree → LowerSet B`), so no Rasiowa free implicative
algebra is required.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

universe u

/-! ## The CanAlgComplete Property -/

/-- A formula predicate `P` is **algebraically completable** if it has a target axiom system `Ax`
whose derivability coincides with GHA-validity on the `P`-fragment. The two fields are the
completeness and soundness halves; both are discharged by reuse for every existing fragment.

A `structure` (not a `class`) is used because `Ax` is *output* data that varies per fragment and is
not inferable by instance search. -/
structure CanAlgComplete {Atom : Type u} (P : PL.Proposition Atom → Bool) where
  /-- The target sub-logic whose derivability characterizes the fragment. -/
  Ax : PL.Proposition Atom → Prop
  /-- Completeness core: GHA-validity of a `P`-formula yields derivability in `Ax`. -/
  complete : ∀ {φ : PL.Proposition Atom}, P φ = true → GHAValid.{u, u} φ → Derivable Ax φ
  /-- Soundness: derivability in `Ax` yields GHA-validity. -/
  sound : ∀ {φ : PL.Proposition Atom}, Derivable Ax φ → GHAValid.{u, u} φ

/-! ## Packaged Completeness Theorems -/

/-- The packaged completeness theorem: on the `P`-fragment, derivability in the target logic is
equivalent to GHA-validity. -/
theorem canAlgComplete_iff {Atom : Type u} {P : PL.Proposition Atom → Bool}
    (C : CanAlgComplete P) {φ : PL.Proposition Atom} (hφ : P φ = true) :
    Derivable C.Ax φ ↔ GHAValid.{u, u} φ :=
  ⟨C.sound, C.complete hφ⟩

/-- With evaluation-independence on a ⊥-free fragment, the GHA characterization upgrades to an HA
characterization: on the `P`-fragment, derivability in the target logic is equivalent to
HA-validity. The `AlgEvalIndependent` hypothesis records the fragment context; the upgrade itself
is the `WithBot`-backed `ghaValid_iff_haValid_of_botFree`. -/
theorem canAlgComplete_haValid_iff {Atom : Type u} {P : PL.Proposition Atom → Bool}
    (C : CanAlgComplete P) (_hInd : AlgEvalIndependent P)
    (hsub : ∀ {φ : PL.Proposition Atom}, P φ = true → φ.IsBotFree = true)
    {φ : PL.Proposition Atom} (hφ : P φ = true) :
    Derivable C.Ax φ ↔ HAValid.{u, u} φ := by
  rw [canAlgComplete_iff C hφ]
  exact ghaValid_iff_haValid_of_botFree (hsub hφ)

/-! ## Fragment Instances (by Reuse) -/

/-- `IsBotFree` is algebraically completable with target logic `MinPropAxiom` (MPL). Both fields
are projections of the *total* iff `MPL.hilbert_alg_completeness` (which holds for all `φ`), so
⊥-freeness is not used in the fields themselves — it only matters for the `HAValid` upgrade. -/
def canAlgCompleteIsBotFree {Atom : Type u} :
    CanAlgComplete (Atom := Atom) Proposition.IsBotFree where
  Ax := MinPropAxiom
  complete := fun _ h => MPL.hilbert_alg_completeness.mpr h
  sound := fun h => MPL.hilbert_alg_completeness.mp h

/-- `IsOrBotFree` is algebraically completable with target logic `ConjImpAxiom` (IPL⟨∧,→,⊤⟩).
Completeness routes GHA-validity through the canonical Heyting model `LowerSet B`
(`GHAValid_implies_BrouwerianValid_direct`) and the Brouwerian completeness theorem
(`conjImp_brouwerian_completeness`); soundness uses axiom subsumption into MPL. -/
def canAlgCompleteIsOrBotFree {Atom : Type u} :
    CanAlgComplete (Atom := Atom) Proposition.IsOrBotFree where
  Ax := ConjImpAxiom
  complete := fun hφ h =>
    conjImp_brouwerian_completeness hφ (GHAValid_implies_BrouwerianValid_direct hφ h)
  sound := fun h => MPL.hilbert_alg_completeness.mp (derivableMinOfDerivableConjImp h)

/-- `IsImpTopOnly` is algebraically completable with target logic `ImpAxiom` (IPL⟨→,⊤⟩).
Completeness routes through MPL completeness and the conservativity link `mplAxiom_iff_impAxiom`
(which itself reduces imp-top-only to or-bot-free, hence to `LowerSet B`); soundness uses axiom
subsumption into MPL. No Rasiowa free implicative algebra is required. -/
def canAlgCompleteIsImpTopOnly {Atom : Type u} :
    CanAlgComplete (Atom := Atom) Proposition.IsImpTopOnly where
  Ax := ImpAxiom
  complete := fun hφ h => (mplAxiom_iff_impAxiom hφ).mp (MPL.hilbert_alg_completeness.mpr h)
  sound := fun h => MPL.hilbert_alg_completeness.mp (derivableMinOfDerivableImp h)

end Cslib.Logic.PL

end
