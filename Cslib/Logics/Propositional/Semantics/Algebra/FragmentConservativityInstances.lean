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

## Design Notes

The `4 × 3 = 12` boilerplate theorems (subsumption / biconditional / ND corollary, per fragment)
that consume these instances are re-homed here in Phase 3 of the consolidation, once their
bespoke bodies are removed from the four per-fragment files — this avoids a duplicate-declaration
clash between the bespoke body and the generic-core one-liner during the interval where both
would otherwise coexist.

This file is a pure re-organization: every `def` here reuses an already-proved fact (the
fragment's hard-direction theorem) verbatim. No new mathematics; no proof is re-derived.

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

end Cslib.Logic.PL

end
