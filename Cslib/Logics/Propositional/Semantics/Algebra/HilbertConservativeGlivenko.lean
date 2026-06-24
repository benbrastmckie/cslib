/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.Conservative
public import Cslib.Logics.Propositional.Semantics.Algebra.Glivenko
public import Cslib.Logics.Propositional.NaturalDeduction.AxiomAdmissibility

/-! # Hilbert-Primary Conservative Extension and Glivenko Theorems

This module is the canonical source for the conservative extension theorem and Glivenko's
theorem. The Hilbert-primary versions are proved directly; the ND versions are derived as
corollaries via syntactic bridges.

## Hilbert-Primary Theorems

- `hilbertIplConservativeOverMpl`: IPL is a conservative extension of MPL for bot-free formulas
  stated directly in terms of `Derivable IntPropAxiom` and `Derivable MinPropAxiom`.
  Does not require `[DecidableEq Atom]`.
- `hilbertGlivenko`: Glivenko's theorem for the Hilbert system: CPL derivability of `φ` implies
  IPL derivability of `¬¬φ`, stated in terms of `Derivable PropositionalAxiom` and
  `Derivable IntPropAxiom`. Does not require `[DecidableEq Atom]`.

## Syntactic Bridges

Three equivalences connecting the ND and Hilbert systems via proof-theoretic composition:

- `derivableInMplIffDerivableMin`: `DerivableIn (∅ : Theory Atom) φ ↔ Derivable MinPropAxiom φ`
- `derivableInIplIffDerivableInt`: `DerivableIn (IPL : Theory Atom) φ ↔ Derivable IntPropAxiom φ`
- `derivableInCplIffDerivableProp`: `DerivableIn (IPL ∪ CPL : Theory Atom) φ ↔`
  `Derivable PropositionalAxiom φ`

Each bridge is proved by composing `axiomTheory_*_iff_*` (from `AxiomAdmissibility.lean`)
with `hilbert_iff_nd_*` (from `Equivalence.lean`). The `axiomTheory_*` equivalences show that
ND derivability with a concrete theory (MPL/IPL/IPL∪CPL) is equivalent to ND derivability
under the corresponding `AxiomTheory`. The `hilbert_iff_nd_*` equivalences then connect
`AxiomTheory` ND derivability to Hilbert derivability.

## ND Corollaries (Canonical Names)

- `ipl_conservative_over_mpl`: ND conservative extension, derived as a corollary of
  `hilbertIplConservativeOverMpl` via the syntactic bridges.
- `glivenko`: ND Glivenko, derived as a corollary of `hilbertGlivenko` via the syntactic bridges.

## Architecture

The Hilbert system is primary: theorems are proved directly using Hilbert algebraic completeness
(`hilbert_alg_complete`) and algebraic infrastructure (`coe_AlgEvaluate`, `glivenko_algebraic`).
The ND system results are derived as corollaries through the syntactic bridges, which compose
`hilbert_iff_nd` (the Hilbert/ND equivalence via `AxiomTheory`) with the axiom admissibility
equivalences from `AxiomAdmissibility.lean`.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [V. I. Glivenko, *Sur quelques points de la Logique de M. Brouwer*][Glivenko1929]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

universe u

/-! ## Hilbert-Primary Conservative Extension -/

/-- **Hilbert-primary conservative extension theorem**: IPL is a conservative extension of MPL
for bot-free formulas. If `φ` is derivable in the intuitionistic Hilbert system and mentions
no `⊥`, then `φ` is already derivable in the minimal Hilbert system.

The proof routes through algebraic validity:
1. `IPL.hilbert_alg_complete.mp h` converts `Derivable IntPropAxiom φ` to `HAValid φ`.
2. For any `GeneralizedHeytingAlgebra G` and valuation `v`, instantiate `HAValid φ` at
   `WithBot G` (with `instHeytingAlgebraWithBot`). The embedding lemma `coe_AlgEvaluate` rewrites
   the result back to `AlgEvaluate v bot_val φ = ⊤` in `G` (using bot-freeness and injectivity of
   the coercion `G → WithBot G`).
3. `MPL.hilbert_alg_complete.mpr` converts `GHAValid φ` back to `Derivable MinPropAxiom φ`.

This is the primary version, stated directly in the Hilbert setting without the
`[DecidableEq Atom]` constraint. The ND corollary `ipl_conservative_over_mpl` is below. -/
theorem hilbertIplConservativeOverMpl {Atom : Type u} {φ : PL.Proposition Atom}
    (hBF : φ.IsBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@MinPropAxiom Atom) φ := by
  rw [MPL.hilbert_alg_complete]
  intro G _ v bot_val
  have hIPL := IPL.hilbert_alg_complete.mp h (H := WithBot G) (fun x => (v x : WithBot G))
  rw [coe_AlgEvaluate v bot_val φ hBF] at hIPL
  exact WithBot.coe_eq_coe.mp hIPL

/-! ## Hilbert-Primary Glivenko Theorem -/

/-- **Hilbert-primary Glivenko theorem**: if `φ` is derivable in the classical Hilbert system,
then `¬¬φ` is derivable in the intuitionistic Hilbert system.

The proof routes through algebraic validity:
1. `CPL.hilbert_alg_complete.mp h` converts `Derivable PropositionalAxiom φ` to `BAValid φ`.
2. `glivenko_algebraic` lifts `BAValid φ` to `HAValid (¬¬φ)`.
3. `IPL.hilbert_alg_complete.mpr` converts `HAValid (¬¬φ)` back to `Derivable IntPropAxiom (¬¬φ)`.

This is the primary version, stated directly in the Hilbert setting without the
`[DecidableEq Atom]` constraint. The ND corollary `glivenko` is below. -/
theorem hilbertGlivenko {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@PropositionalAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) (¬¬φ) := by
  rw [IPL.hilbert_alg_complete]
  intro H _ v
  apply glivenko_algebraic
  intro H' _ v'
  exact CPL.hilbert_alg_complete.mp h H' v'

/-! ## Syntactic Bridges (DerivableIn ↔ Derivable) -/

variable {Atom : Type u} [DecidableEq Atom]

/-- **MPL bridge**: ND derivability in MPL (the empty theory) is equivalent to Hilbert derivability
with `MinPropAxiom`.

Proof: compose `axiomTheory_min_iff_mpl` with `hilbert_iff_nd_min.symm`. The former connects
`DerivableIn (∅)` with `DerivableIn (AxiomTheory MinPropAxiom)`; the latter connects
`DerivableIn (AxiomTheory MinPropAxiom)` with `Derivable MinPropAxiom`. -/
theorem derivableInMplIffDerivableMin {φ : PL.Proposition Atom} :
    DerivableIn (∅ : Theory Atom) φ ↔ Derivable (@MinPropAxiom Atom) φ :=
  axiomTheory_min_iff_mpl.trans hilbert_iff_nd_min.symm

/-- **IPL bridge**: ND derivability in IPL is equivalent to Hilbert derivability with
`IntPropAxiom`.

Proof: compose `axiomTheory_int_iff_ipl` with `hilbert_iff_nd_int.symm`. The former connects
`DerivableIn (IPL)` with `DerivableIn (AxiomTheory IntPropAxiom)`; the latter connects
`DerivableIn (AxiomTheory IntPropAxiom)` with `Derivable IntPropAxiom`. -/
theorem derivableInIplIffDerivableInt {φ : PL.Proposition Atom} :
    DerivableIn (IPL : Theory Atom) φ ↔ Derivable (@IntPropAxiom Atom) φ :=
  axiomTheory_int_iff_ipl.trans hilbert_iff_nd_int.symm

/-- **CPL bridge**: ND derivability in `IPL ∪ CPL` is equivalent to Hilbert derivability with
`PropositionalAxiom`.

Proof: compose `axiomTheory_cl_iff_cpl` with `hilbert_iff_nd_cl.symm`. The former connects
`DerivableIn (IPL ∪ CPL)` with `DerivableIn (AxiomTheory PropositionalAxiom)`; the latter
connects `DerivableIn (AxiomTheory PropositionalAxiom)` with `Derivable PropositionalAxiom`. -/
theorem derivableInCplIffDerivableProp {φ : PL.Proposition Atom} :
    DerivableIn (IPL ∪ CPL : Theory Atom) φ ↔ Derivable (@PropositionalAxiom Atom) φ :=
  axiomTheory_cl_iff_cpl.trans hilbert_iff_nd_cl.symm

/-! ## ND Corollaries via Bridges -/

/-- **ND conservative extension**: IPL is a conservative extension of MPL for bot-free formulas.
If a bot-free formula is derivable in IPL, then it is already derivable in MPL.

This is the canonical ND version, derived as a corollary of the Hilbert-primary theorem
`hilbertIplConservativeOverMpl` via the algebraic bridges `derivableInIplIffDerivableInt`
and `derivableInMplIffDerivableMin`. -/
theorem ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (∅ : Theory Atom) A :=
  derivableInMplIffDerivableMin.mpr
    (hilbertIplConservativeOverMpl hBF (derivableInIplIffDerivableInt.mp h))

/-- **Glivenko's theorem**: if `A` is derivable in CPL (`IPL ∪ CPL`), then `¬¬A` is derivable
in IPL.

This is the canonical ND version, derived as a corollary of the Hilbert-primary theorem
`hilbertGlivenko` via the algebraic bridges `derivableInCplIffDerivableProp` and
`derivableInIplIffDerivableInt`. -/
theorem glivenko {A : PL.Proposition Atom}
    (h : DerivableIn (IPL ∪ CPL : Theory Atom) A) :
    DerivableIn (IPL : Theory Atom) (¬¬A) :=
  derivableInIplIffDerivableInt.mpr
    (hilbertGlivenko (derivableInCplIffDerivableProp.mp h))

end Cslib.Logic.PL
