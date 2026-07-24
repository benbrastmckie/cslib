/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentConservativity
public import Cslib.Logics.Propositional.Semantics.Algebra.ImpConservative
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpBotConservative
public import Cslib.Logics.Propositional.Semantics.Algebra.OrImpConservative

/-! # Fragment-Conservativity Instances

This module supplies the four `FragmentConservativity` instances — one per conservativity
fragment realized in `ImpConservative.lean`, `ConjImpConservative.lean`,
`ConjImpBotConservative.lean`, and `OrImpConservative.lean`.

Each instance's `hard` field reuses its fragment's retained hard-direction proof **verbatim**:
no proof is re-derived. The `OrImp` instance is the sequent-calculus route
(`hilbertIplConservativeOverOrImp`, via `hilbert_iff_lj` → `LJProof.cutElim` →
`cutFreeLJ_toOrImp`), kept exactly as-is; the other three route through Brouwerian/Hilbert
algebra completeness.

## Instances

- `fragmentConservativityConjImp` : `IsOrBotFree` → `ConjImpAxiom`
- `fragmentConservativityImp` : `IsImpTopOnly` → `ImpAxiom`
- `fragmentConservativityConjImpBot` : `IsOrFree` → `ConjImpBotAxiom`
- `fragmentConservativityOrImp` : `IsAndBotFree` → `OrImpAxiom`

## Re-homed Boilerplate

For each fragment `X`, the following three theorems are one-line applications of
`fragmentConservativity_derivableOfDerivableInt` / `fragmentConservativity_iff` /
`fragmentConservativity_nd` to the matching instance, preserving the exact public name and
signature that `ImpConservative.lean` / `ConjImpConservative.lean` / `ConjImpBotConservative.lean`
/ `OrImpConservative.lean` previously defined directly (their bespoke bodies have been removed
from those files to avoid a duplicate-declaration clash; see each file's docstring):

- `derivableXOfDerivableInt`
- `hilbertIplConservativeOverX_iff`
- `ipl_conservative_over_X`

## Design Notes

This file is a pure re-organization: every theorem here is either a `def` reusing an
already-proved fact (the fragment's hard-direction theorem) verbatim, or a one-line consequence
of the generic core's derived theorems. No new mathematics; no proof is re-derived.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

universe u

/-! ## Fragment Instances -/

/-- `IsOrBotFree` has fragment conservativity with target logic `ConjImpAxiom` (IPL⟨∧,→,⊤⟩).
The hard direction is `hilbertIplConservativeOverConjImp` (the `LowerSet B` Heyting /
`brouwerianEmbeddingLemma` / `conjImp_brouwerian_complete` route), reused verbatim. -/
def fragmentConservativityConjImp {Atom : Type u} :
    FragmentConservativity (Atom := Atom) Proposition.IsOrBotFree where
  Ax := ConjImpAxiom
  hard := hilbertIplConservativeOverConjImp
  sub := fun _ hψ => hψ.toMinPropAxiom.toIntPropAxiom

/-- `IsImpTopOnly` has fragment conservativity with target logic `ImpAxiom` (IPL⟨→,⊤⟩).
The hard direction is `hilbertIplConservativeOverImp` (the ConjImp + `FreeMeetExtension` free
BSL + `freeMeetEvaluateEq` + `imp_hilbert_complete` route), reused verbatim. -/
def fragmentConservativityImp {Atom : Type u} :
    FragmentConservativity (Atom := Atom) Proposition.IsImpTopOnly where
  Ax := ImpAxiom
  hard := hilbertIplConservativeOverImp
  sub := fun _ hψ => hψ.toConjImpAxiom.toMinPropAxiom.toIntPropAxiom

/-- `IsOrFree` has fragment conservativity with target logic `ConjImpBotAxiom` (IPL⟨∧,→,⊥,⊤⟩).
The hard direction is `hilbertIplConservativeOverConjImpBot` (the `NonemptyLowerSet` Heyting +
`nonemptyLowerSet_evaluate_commutes` + `conjImpBot_pointedBrouwerian_complete` route), reused
verbatim. -/
def fragmentConservativityConjImpBot {Atom : Type u} :
    FragmentConservativity (Atom := Atom) Proposition.IsOrFree where
  Ax := ConjImpBotAxiom
  hard := hilbertIplConservativeOverConjImpBot
  sub := fun _ hψ => hψ.toIntPropAxiom

/-- `IsAndBotFree` has fragment conservativity with target logic `OrImpAxiom` (IPL⟨∨,→,⊤⟩).
The hard direction is `hilbertIplConservativeOverOrImp` (the **sequent-calculus** route:
`hilbert_iff_lj` → `LJProof.cutElim` → `cutFreeLJ_toOrImp` — not algebraic), reused verbatim. -/
def fragmentConservativityOrImp {Atom : Type u} :
    FragmentConservativity (Atom := Atom) Proposition.IsAndBotFree where
  Ax := OrImpAxiom
  hard := hilbertIplConservativeOverOrImp
  sub := fun _ hψ => hψ.toMinPropAxiom.toIntPropAxiom

/-! ## Re-homed Boilerplate: ConjImp -/

/-- **Subsumption**: every formula derivable in the conjunctive-implicational Hilbert system
is derivable in the full intuitionistic Hilbert system. Generic form applied to
`fragmentConservativityConjImp`. -/
theorem derivableConjImpOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ConjImpAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ :=
  fragmentConservativity_derivableOfDerivableInt fragmentConservativityConjImp h

/-- **Biconditional**: for or-bot-free formulas, derivability in the intuitionistic Hilbert
system and derivability in the conjunctive-implicational Hilbert system coincide. Generic form
applied to `fragmentConservativityConjImp`. -/
theorem hilbertIplConservativeOverConjImp_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@ConjImpAxiom Atom) φ :=
  fragmentConservativity_iff fragmentConservativityConjImp hOBF

/-- **ND conservative extension**: IPL is a conservative extension of IPL⟨∧,→,⊤⟩ for
or-bot-free formulas. Generic form applied to `fragmentConservativityConjImp`. -/
theorem ipl_conservative_over_conjImp {Atom : Type u} [DecidableEq Atom]
    {A : PL.Proposition Atom}
    (hOBF : A.IsOrBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ConjImpAxiom Atom) A :=
  fragmentConservativity_nd fragmentConservativityConjImp hOBF h

/-! ## Re-homed Boilerplate: Imp -/

/-- **Subsumption**: every formula derivable in the purely implicational Hilbert system is
derivable in the full intuitionistic Hilbert system. Generic form applied to
`fragmentConservativityImp`. -/
theorem derivableImpOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ImpAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ :=
  fragmentConservativity_derivableOfDerivableInt fragmentConservativityImp h

/-- **Biconditional**: for imp-top-only formulas, derivability in the intuitionistic Hilbert
system and derivability in the purely implicational Hilbert system coincide. Generic form
applied to `fragmentConservativityImp`. -/
theorem hilbertIplConservativeOverImp_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@ImpAxiom Atom) φ :=
  fragmentConservativity_iff fragmentConservativityImp hITO

/-- **ND conservative extension**: IPL is a conservative extension of IPL⟨→,⊤⟩ for
imp-top-only formulas. Generic form applied to `fragmentConservativityImp`. -/
theorem ipl_conservative_over_imp {Atom : Type u} [DecidableEq Atom] {A : PL.Proposition Atom}
    (hITO : A.IsImpTopOnly = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ImpAxiom Atom) A :=
  fragmentConservativity_nd fragmentConservativityImp hITO h

/-! ## Re-homed Boilerplate: ConjImpBot -/

/-- **Subsumption**: every formula derivable in the conjunctive-implicational-bot Hilbert
system is derivable in the full intuitionistic Hilbert system. Generic form applied to
`fragmentConservativityConjImpBot`. -/
theorem derivableConjImpBotOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ConjImpBotAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ :=
  fragmentConservativity_derivableOfDerivableInt fragmentConservativityConjImpBot h

/-- **Biconditional**: for or-free formulas, derivability in the intuitionistic Hilbert system
and derivability in the conjunctive-implicational-bot Hilbert system coincide. Generic form
applied to `fragmentConservativityConjImpBot`. -/
theorem hilbertIplConservativeOverConjImpBot_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@ConjImpBotAxiom Atom) φ :=
  fragmentConservativity_iff fragmentConservativityConjImpBot hOF

/-- **ND conservative extension**: IPL is a conservative extension of IPL⟨∧,→,⊥,⊤⟩ for
or-free formulas. Generic form applied to `fragmentConservativityConjImpBot`. -/
theorem ipl_conservative_over_conjImpBot {Atom : Type u} [DecidableEq Atom]
    {A : PL.Proposition Atom}
    (hOF : A.IsOrFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ConjImpBotAxiom Atom) A :=
  fragmentConservativity_nd fragmentConservativityConjImpBot hOF h

/-! ## Re-homed Boilerplate: OrImp -/

/-- **Subsumption**: every formula derivable in the disjunctive-implicational Hilbert system
is derivable in the full intuitionistic Hilbert system. Generic form applied to
`fragmentConservativityOrImp`. -/
theorem derivableOrImpOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@OrImpAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ :=
  fragmentConservativity_derivableOfDerivableInt fragmentConservativityOrImp h

/-- **Biconditional**: for and-bot-free formulas, derivability in the intuitionistic Hilbert
system and derivability in the disjunctive-implicational Hilbert system coincide. Generic form
applied to `fragmentConservativityOrImp`. -/
theorem hilbertIplConservativeOverOrImp_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hABF : φ.IsAndBotFree = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@OrImpAxiom Atom) φ :=
  fragmentConservativity_iff fragmentConservativityOrImp hABF

/-- **ND conservative extension**: IPL is a conservative extension of IPL⟨∨,→,⊤⟩ for
and-bot-free formulas. Generic form applied to `fragmentConservativityOrImp`. -/
theorem ipl_conservative_over_orImp {Atom : Type u} [DecidableEq Atom] {A : PL.Proposition Atom}
    (hABF : A.IsAndBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@OrImpAxiom Atom) A :=
  fragmentConservativity_nd fragmentConservativityOrImp hABF h

end Cslib.Logic.PL

end
