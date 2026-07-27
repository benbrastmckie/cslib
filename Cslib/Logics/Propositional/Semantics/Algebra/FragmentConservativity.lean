/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko

/-! # Generic Fragment-Conservativity Core

This module factors the shared four-theorem skeleton realized independently by
`ImpConservative.lean`, `ConjImpConservative.lean`, `ConjImpBotConservative.lean`, and
`OrImpConservative.lean` into a single generic `structure FragmentConservativity P`, using the
same structure-by-reuse idiom as the analogous fragment-completeness developments elsewhere in
this directory.

Each of the four fragment files proves the same four-theorem shape for its own fragment
predicate `P`, target axiom system `Ax`, and hard-direction proof route:

1. **Hard direction** (`hilbertIplConservativeOverX`): `P`-fragment + `IntPropAxiom`-derivable
   implies `Ax`-derivable. This is fragment-specific (different algebraic or proof-theoretic
   route per fragment) and is **retained verbatim** in its home file.
2. **Subsumption** (`derivableXOfDerivableInt`): `Ax`-derivable implies `IntPropAxiom`-derivable,
   via `derivable_mono` and an axiom-inclusion chain.
3. **Biconditional** (`hilbertIplConservativeOverX_iff`): bundles 1 and 2.
4. **ND corollary** (`ipl_conservative_over_X`): the biconditional's hard direction restated for
   the ND system `IPL`, via the syntactic bridge `derivableInIplIffDerivableInt`.

Steps 2-4 are *identical in shape* across all four fragments; only `Ax`, `P`, and the field 1
proof route vary. This module derives 2-4 **once** from the `FragmentConservativity` structure,
replacing the `4 × 3 = 12` boilerplate theorems with three generic ones plus four `def`
instances (see `FragmentConservativityInstances.lean`).

## The `FragmentConservativity` Structure

- `Ax`: the target sub-logic axiom predicate (output data, varies per fragment).
- `hard`: the retained fragment-specific hard-direction proof.
- `sub`: the axiom-level subsumption `Ax ψ → IntPropAxiom ψ`, feeding `derivable_mono`.

A `structure` (not a `class`) is used because `Ax` is *output* data that varies per fragment and
is not inferable by instance search.

## Main Results

- `FragmentConservativity`: the bundled fragment-conservativity property for a formula predicate.
- `fragmentConservativity_derivableOfDerivableInt`: the generic subsumption direction.
- `fragmentConservativity_iff`: the generic biconditional.
- `fragmentConservativity_nd`: the generic ND corollary.
- `liftDerivationTree`, `derivable_mono`: the generic axiom-monotonicity combinators, relocated
  here from `ConjImpConservative.lean` (transitional re-export preserved there).

## Design Notes

This file is a pure re-organization: every theorem here is either a direct relocation of an
existing sorry-free proof (`liftDerivationTree`, `derivable_mono`) or a one-line consequence of
the structure's fields. No new mathematics.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

universe u

/-! ## Generic Axiom-Monotonicity Combinators -/

/-- Axiom-monotonicity: given an axiom subsumption `h_sub : ∀ φ, Axioms1 φ → Axioms2 φ`,
lift a `DerivationTree Axioms1 Γ φ` to a `DerivationTree Axioms2 Γ φ`.

Relocated from `ConjImpConservative.lean` (Part B consolidation): this combinator is shared by
every fragment's subsumption direction, not specific to the conjunctive-implicational fragment. -/
def liftDerivationTree
    {Atom : Type u}
    {Axioms1 Axioms2 : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, Axioms1 ψ → Axioms2 ψ)
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    DerivationTree Axioms1 Γ φ → DerivationTree Axioms2 Γ φ
  | .ax Γ φ h => .ax Γ φ (h_sub φ h)
  | .assumption Γ φ h => .assumption Γ φ h
  | .modusPonens Γ φ ψ d₁ d₂ =>
      .modusPonens Γ φ ψ (liftDerivationTree h_sub d₁) (liftDerivationTree h_sub d₂)
  | .weakening Γ Δ φ d h => .weakening Γ Δ φ (liftDerivationTree h_sub d) h

/-- **Axiom-monotonicity**: if every axiom of `A₁` is also an axiom of `A₂`, then every
formula derivable from `A₁` is also derivable from `A₂`.

This is the "subsumption" or "monotonicity" lemma for Hilbert derivability. It lifts the
pointwise axiom inclusion `h_sub : ∀ ψ, A₁ ψ → A₂ ψ` to a derivability inclusion
`Derivable A₁ φ → Derivable A₂ φ` using `liftDerivationTree`.

Relocated from `ConjImpConservative.lean` (Part B consolidation): this is the combinator that
`fragmentConservativity_derivableOfDerivableInt` below specializes to the generic structure's
`sub` field. -/
theorem derivable_mono {Atom : Type u}
    {A₁ A₂ : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, A₁ ψ → A₂ ψ)
    {φ : PL.Proposition Atom}
    (h : Derivable A₁ φ) : Derivable A₂ φ :=
  let ⟨d⟩ := h; ⟨liftDerivationTree h_sub d⟩

/-! ## The FragmentConservativity Property -/

/-- A formula predicate `P` **has fragment conservativity** if there is a target axiom system
`Ax` such that: (1) `P`-fragment `IntPropAxiom`-derivability implies `Ax`-derivability (`hard`,
the fragment-specific hard direction, kept verbatim per instance), and (2) every axiom of `Ax`
is an `IntPropAxiom` (`sub`, feeding the generic subsumption direction via `derivable_mono`).

A `structure` (not a `class`) is used because `Ax` is *output* data that varies per fragment and
is not inferable by instance search. -/
structure FragmentConservativity {Atom : Type u} (P : PL.Proposition Atom → Bool) where
  /-- The target sub-logic axiom predicate whose derivability characterizes the fragment. -/
  Ax : PL.Proposition Atom → Prop
  /-- Hard direction: `P`-fragment `IntPropAxiom`-derivability implies `Ax`-derivability. This
  is the fragment-specific proof route (algebraic or proof-theoretic), retained verbatim. -/
  hard : ∀ {φ : PL.Proposition Atom}, P φ = true →
    Derivable (@IntPropAxiom Atom) φ → Derivable Ax φ
  /-- Axiom-level subsumption: every axiom of `Ax` is an `IntPropAxiom`. Feeds the generic
  subsumption direction via `derivable_mono`. -/
  sub : ∀ ψ : PL.Proposition Atom, Ax ψ → (@IntPropAxiom Atom) ψ

/-! ## Generic Derived Theorems -/

/-- **Generic subsumption**: every formula derivable in the fragment's target axiom system `Ax`
is derivable in the full intuitionistic Hilbert system.

Uses `derivable_mono` with the structure's `sub` field. This is the generic form of
`derivableConjImpOfDerivableInt`, `derivableImpOfDerivableInt`, `derivableConjImpBotOfDerivableInt`,
and `derivableOrImpOfDerivableInt`. -/
theorem fragmentConservativity_derivableOfDerivableInt {Atom : Type u}
    {P : PL.Proposition Atom → Bool} (F : FragmentConservativity P)
    {φ : PL.Proposition Atom} (h : Derivable F.Ax φ) :
    Derivable (@IntPropAxiom Atom) φ :=
  derivable_mono F.sub h

/-- **Generic biconditional**: for `P`-fragment formulas, derivability in the intuitionistic
Hilbert system and derivability in the fragment's target axiom system `Ax` coincide.

This is the generic form of `hilbertIplConservativeOverConjImp_iff`,
`hilbertIplConservativeOverImp_iff`, `hilbertIplConservativeOverConjImpBot_iff`, and
`hilbertIplConservativeOverOrImp_iff`. -/
theorem fragmentConservativity_iff {Atom : Type u} {P : PL.Proposition Atom → Bool}
    (F : FragmentConservativity P) {φ : PL.Proposition Atom} (hP : P φ = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable F.Ax φ :=
  ⟨F.hard hP, fragmentConservativity_derivableOfDerivableInt F⟩

/-- **Generic ND corollary**: for `P`-fragment formulas, if a formula is derivable in the ND
system for IPL, then it is derivable in the fragment's target axiom system `Ax`.

Derived via the syntactic bridge `derivableInIplIffDerivableInt`. This is the generic form of
`ipl_conservative_over_conjImp`, `ipl_conservative_over_imp`, `ipl_conservative_over_conjImpBot`,
and `ipl_conservative_over_orImp`. -/
theorem fragmentConservativity_nd {Atom : Type u} [DecidableEq Atom]
    {P : PL.Proposition Atom → Bool} (F : FragmentConservativity P)
    {A : PL.Proposition Atom} (hP : P A = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable F.Ax A :=
  F.hard hP (derivableInIplIffDerivableInt.mp h)

end Cslib.Logic.PL

end
