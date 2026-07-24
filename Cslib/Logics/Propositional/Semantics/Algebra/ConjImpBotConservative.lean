/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerianCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.NonemptyLowerSet
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative

/-! # Conservative Extension: IPL over IPL⟨∧,→,⊥,⊤⟩

This module proves that IPL is a conservative extension of the conjunctive-implicational-bot
fragment IPL⟨∧,→,⊥,⊤⟩ for or-free formulas.

## Main Results

- `hilbertIplConservativeOverConjImpBot`: IPL is a conservative extension of IPL⟨∧,→,⊥,⊤⟩
  for or-free formulas, stated in terms of `Derivable IntPropAxiom` and
  `Derivable ConjImpBotAxiom`. This is the hard-direction proof; it is the sole content
  retained in this file. The generic subsumption/biconditional/ND-corollary boilerplate
  (`derivableConjImpBotOfDerivableInt`, `hilbertIplConservativeOverConjImpBot_iff`,
  `ipl_conservative_over_conjImpBot`) is re-homed as a `FragmentConservativity` instance in
  `FragmentConservativityInstances.lean`.

## Proof Strategy

The main theorem routes through pointed Brouwerian validity via the `NonemptyLowerSet`
Heyting algebra construction:
1. `IPL.hilbert_alg_complete.mp h` converts `Derivable IntPropAxiom φ` to `HAValid φ`.
2. Instantiate at `H := NonemptyLowerSet B` (a `HeytingAlgebra`) with valuation
   `iicNonemptyLowerSet ∘ v`. This gives
   `AlgEvaluate (iicNonemptyLowerSet ∘ v) ⊥ φ = ⊤`.
3. `nonemptyLowerSet_evaluate_commutes` rewrites this to
   `iicNonemptyLowerSet (PointedBrouwerianEvaluate v φ) = ⊤`.
4. `iicNonemptyLowerSet_eq_top_iff` extracts `PointedBrouwerianEvaluate v φ = ⊤`.
5. So `PointedBrouwerianValid φ`, and `conjImpBot_pointedBrouwerian_complete` gives
   `Derivable ConjImpBotAxiom φ`.

The key improvement over `ConjImpConservative.lean`: the `NonemptyLowerSet` embedding
preserves `⊥` (unlike the plain `LowerSet` embedding), enabling the bot case in the
commutation lemma and extending the result from or-bot-free to or-free formulas.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn
open NonemptyLowerSet

universe u

/-! ## Hilbert-Primary Conservative Extension -/

/-- **Hilbert-primary conservative extension theorem**: IPL is a conservative extension of
IPL⟨∧,→,⊥,⊤⟩ for or-free formulas. If `φ` is derivable in the intuitionistic Hilbert
system and `φ` contains no `∨`, then `φ` is already derivable in the
conjunctive-implicational-bot Hilbert system.

The proof routes through pointed Brouwerian validity via the `NonemptyLowerSet` Heyting algebra:
1. `IPL.hilbert_alg_complete.mp h` converts `Derivable IntPropAxiom φ` to `HAValid φ`.
2. For any `BrouwerianSemilattice B` with `OrderBot` and `v : Atom → B`, instantiate `HAValid φ`
   at `H := NonemptyLowerSet B` with valuation `iicNonemptyLowerSet ∘ v`. This gives
   `AlgEvaluate (iicNonemptyLowerSet ∘ v) ⊥ φ = ⊤`.
3. `nonemptyLowerSet_evaluate_commutes` rewrites this to
   `iicNonemptyLowerSet (PointedBrouwerianEvaluate v φ) = ⊤`.
4. `iicNonemptyLowerSet_eq_top_iff` extracts `PointedBrouwerianEvaluate v φ = ⊤`.
5. Since `v` and `B` were arbitrary, `PointedBrouwerianValid φ`.
6. `conjImpBot_pointedBrouwerian_complete hOF` gives `Derivable ConjImpBotAxiom φ`.

The key distinction from `hilbertIplConservativeOverConjImp` (the or-bot-free version):
`NonemptyLowerSet` preserves `⊥` via `iicNonemptyLowerSet_bot`, while the plain `LowerSet`
embedding does not (since `LowerSet.Iic ⊥ ≠ ⊥ : LowerSet B`). This enables handling
formulas with `⊥`, extending the result to all or-free (not just or-bot-free) formulas. -/
theorem hilbertIplConservativeOverConjImpBot {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@ConjImpBotAxiom Atom) φ := by
  apply conjImpBot_pointedBrouwerian_complete hOF
  intro B _ _ v
  have hHA := IPL.hilbert_alg_complete.mp h
    (H := NonemptyLowerSet B) (iicNonemptyLowerSet ∘ v)
  rw [← nonemptyLowerSet_evaluate_commutes v φ hOF] at hHA
  exact iicNonemptyLowerSet_eq_top_iff.mp hHA

/-! ## Subsumption / Biconditional / ND Corollary (re-homed)

The generic subsumption, biconditional, and ND-corollary boilerplate for this fragment
(`derivableConjImpBotOfDerivableInt`, `hilbertIplConservativeOverConjImpBot_iff`,
`ipl_conservative_over_conjImpBot`) now lives in `FragmentConservativityInstances.lean`, as
one-line consequences of `fragmentConservativityConjImpBot` applied to the generic
`FragmentConservativity` core (Part B consolidation). -/

end Cslib.Logic.PL

end

end
