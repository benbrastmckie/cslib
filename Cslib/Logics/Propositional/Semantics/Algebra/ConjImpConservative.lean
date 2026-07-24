/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentConservativity

/-! # Conservative Extension: IPL over IPL⟨∧,→,⊤⟩

This module proves that IPL is a conservative extension of the conjunctive-implicational
fragment IPL⟨∧,→,⊤⟩ for or-bot-free formulas.

## Main Results

- `hilbertIplConservativeOverConjImp`: IPL is a conservative extension of IPL⟨∧,→,⊤⟩ for
  or-bot-free formulas, stated in terms of `Derivable IntPropAxiom` and `Derivable ConjImpAxiom`.
  This is the hard-direction proof; it is the sole content retained in this file. The generic
  subsumption/biconditional/ND-corollary boilerplate (`derivableConjImpOfDerivableInt`,
  `hilbertIplConservativeOverConjImp_iff`, `ipl_conservative_over_conjImp`) is re-homed as a
  `FragmentConservativity` instance in `FragmentConservativityInstances.lean`.

## Proof Strategy

The main theorem mirrors `hilbertIplConservativeOverMpl` in `HilbertConservativeGlivenko.lean`,
replacing the `WithBot` free completion with the `LowerSet` free join completion:
1. `IPL.hilbert_alg_complete.mp h` converts `Derivable IntPropAxiom φ` to `HAValid φ`.
2. Instantiate at `H := LowerSet B` (a `HeytingAlgebra`) with valuation `LowerSet.Iic ∘ v`.
3. `brouwerianEmbeddingLemma` converts the result to `BrouwerianEvaluate v φ = ⊤`.
4. `conjImp_brouwerian_complete` converts `BrouwerianValid φ` to `Derivable ConjImpAxiom φ`.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

universe u

/-! ## Generic Axiom-Monotonicity Combinators (relocated)

`liftDerivationTree` and `derivable_mono` now live in `FragmentConservativity.lean` (Part B
consolidation of the fragment-conservativity sprawl); they are re-exported here transitively via
the `public import` above so that every existing consumer of this file continues to resolve
them unchanged. -/

/-! ## Hilbert-Primary Conservative Extension -/

/-- **Hilbert-primary conservative extension theorem**: IPL is a conservative extension of
IPL⟨∧,→,⊤⟩ for or-bot-free formulas. If `φ` is derivable in the intuitionistic Hilbert
system and `φ` contains no `∨` or `⊥`, then `φ` is already derivable in the
conjunctive-implicational Hilbert system.

The proof routes through algebraic validity:
1. `IPL.hilbert_alg_complete.mp h` converts `Derivable IntPropAxiom φ` to `HAValid φ`.
2. For any `BrouwerianSemilattice B` and `v : Atom → B`, instantiate `HAValid φ` at
   `H := LowerSet B` with valuation `LowerSet.Iic ∘ v`. Since `LowerSet B` is a
   `HeytingAlgebra` (via `CompletelyDistribLattice`), this gives
   `AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤`.
3. `brouwerianEmbeddingLemma` rewrites this to `BrouwerianEvaluate v φ = ⊤`.
4. `conjImp_brouwerian_complete` converts `BrouwerianValid φ` to `Derivable ConjImpAxiom φ`.

This is the primary version, stated in the Hilbert setting without `[DecidableEq Atom]`.
The ND corollary `ipl_conservative_over_conjImp` is below. -/
theorem hilbertIplConservativeOverConjImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@ConjImpAxiom Atom) φ := by
  apply conjImp_brouwerian_complete hOBF
  intro B _ v
  have hHA := IPL.hilbert_alg_complete.mp h (H := LowerSet B) (LowerSet.Iic ∘ v)
  exact (brouwerianEmbeddingLemma v φ hOBF).mpr hHA

/-! ## Subsumption / Biconditional / ND Corollary (re-homed)

The generic subsumption, biconditional, and ND-corollary boilerplate for this fragment
(`derivableConjImpOfDerivableInt`, `hilbertIplConservativeOverConjImp_iff`,
`ipl_conservative_over_conjImp`) now lives in `FragmentConservativityInstances.lean`, as
one-line consequences of `fragmentConservativityConjImp` applied to the generic
`FragmentConservativity` core (Part B consolidation). -/

end Cslib.Logic.PL

end

end
