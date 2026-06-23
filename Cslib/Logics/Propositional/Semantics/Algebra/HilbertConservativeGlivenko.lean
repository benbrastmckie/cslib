/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.Conservative
public import Cslib.Logics.Propositional.Semantics.Algebra.Glivenko
public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness

/-! # Hilbert-Primary Conservative Extension and Glivenko Theorems

This module provides Hilbert-primary restatements of the conservative extension theorem and
Glivenko's theorem, algebraic bridges between the ND (`DerivableIn`) and Hilbert (`Derivable`)
derivability predicates for MPL, IPL, and CPL, and ND corollaries derived via those bridges.

## Hilbert-Primary Theorems

- `hilbertIplConservativeOverMpl`: IPL is a conservative extension of MPL for bot-free formulas
  stated directly in terms of `Derivable IntPropAxiom` and `Derivable MinPropAxiom`.
- `hilbertGlivenko`: Glivenko's theorem for the Hilbert system: CPL derivability of `φ` implies
  IPL derivability of `¬¬φ`, stated in terms of `Derivable PropositionalAxiom` and
  `Derivable IntPropAxiom`.

## Algebraic Bridges

Three equivalences connecting the ND and Hilbert systems via algebraic completeness:

- `derivableInMplIffDerivableMin`: `DerivableIn (∅ : Theory Atom) φ ↔ Derivable MinPropAxiom φ`
- `derivableInIplIffDerivableInt`: `DerivableIn (IPL : Theory Atom) φ ↔ Derivable IntPropAxiom φ`
- `derivableInCplIffDerivableProp`: `DerivableIn (IPL ∪ CPL : Theory Atom) φ ↔`
  `Derivable PropositionalAxiom φ`

## ND Corollaries

- `iplConservativeOverMpl'`: ND conservative extension as a corollary of
  `hilbertIplConservativeOverMpl`.
- `glivenko'`: ND Glivenko as a corollary of `hilbertGlivenko`.

## Proof Strategy

Each Hilbert-primary theorem routes through algebraic validity:
1. Apply Hilbert completeness (`.mp`) to convert `Derivable Axioms φ` to algebraic validity.
2. Apply the algebraic core (`coe_AlgEvaluate` or `glivenko_algebraic`).
3. Apply Hilbert completeness (`.mpr`) to recover `Derivable Axioms' φ`.

Each algebraic bridge routes through both ND completeness (`alg_complete`) and Hilbert
completeness (`hilbert_alg_complete`), with the algebra as the common intermediate.

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

This mirrors the algebraic core of `ipl_conservative_over_mpl` in `Conservative.lean`,
but stated directly in the Hilbert setting without the `[DecidableEq Atom]` constraint. -/
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

This mirrors the algebraic core of `glivenko` in `Glivenko.lean`, but stated directly in the
Hilbert setting without the `[DecidableEq Atom]` constraint. -/
theorem hilbertGlivenko {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@PropositionalAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) (¬¬φ) := by
  rw [IPL.hilbert_alg_complete]
  intro H _ v
  apply glivenko_algebraic
  intro H' _ v'
  exact CPL.hilbert_alg_complete.mp h H' v'

/-! ## Algebraic Bridges (DerivableIn ↔ Derivable) -/

variable {Atom : Type u} [DecidableEq Atom]

/-- **MPL bridge**: ND derivability in MPL (the empty theory) is equivalent to Hilbert derivability
with `MinPropAxiom`. Both are equivalent to `GHAValid`, giving the bridge via algebra.

Forward: `MPL.alg_complete.mp` converts ND derivability to GHA-validity for all `H : Type u`,
then `MPL.hilbert_alg_complete.mpr` converts GHA-validity to Hilbert derivability.
Backward: `MPL.hilbert_alg_complete.mp` → GHA-validity → `MPL.alg_complete.mpr`. -/
theorem derivableInMplIffDerivableMin {φ : PL.Proposition Atom} :
    DerivableIn (∅ : Theory Atom) φ ↔ Derivable (@MinPropAxiom Atom) φ := by
  constructor
  · intro h
    rw [MPL.hilbert_alg_complete]
    intro H _ v bot_val
    exact MPL.alg_complete.mp h v bot_val
  · intro h
    rw [MPL.alg_complete]
    intro H _ v bot_val
    exact MPL.hilbert_alg_complete.mp h H v bot_val

/-- **IPL bridge**: ND derivability in IPL is equivalent to Hilbert derivability with
`IntPropAxiom`. Both are equivalent to `HAValid`, giving the bridge via algebra.

Forward: `IPL.alg_complete.mp` converts ND derivability to HA-validity for all `H : Type u`,
then `IPL.hilbert_alg_complete.mpr` converts HA-validity to Hilbert derivability.
Backward: `IPL.hilbert_alg_complete.mp` → HA-validity → `IPL.alg_complete.mpr`. -/
theorem derivableInIplIffDerivableInt {φ : PL.Proposition Atom} :
    DerivableIn (IPL : Theory Atom) φ ↔ Derivable (@IntPropAxiom Atom) φ := by
  constructor
  · intro h
    rw [IPL.hilbert_alg_complete]
    intro H _ v
    exact IPL.alg_complete.mp h v
  · intro h
    rw [IPL.alg_complete]
    intro H _ v
    exact IPL.hilbert_alg_complete.mp h H v

/-- **CPL bridge**: ND derivability in `IPL ∪ CPL` is equivalent to Hilbert derivability with
`PropositionalAxiom`. Both are equivalent to `BAValid` (with appropriate theory hypotheses),
giving the bridge via algebra.

Forward: `alg_complete_classical.mp` converts ND derivability to BA-validity, then
`CPL.hilbert_alg_complete.mpr` converts BA-validity to Hilbert derivability. The theory
hypothesis for `IPL ∪ CPL` is discharged by case analysis: IPL axioms `⊥ → C` evaluate to `⊤`
by `simp`, and CPL axioms `¬¬C → C` evaluate to `⊤` via `compl_compl` in any BooleanAlgebra.
Backward: `CPL.hilbert_alg_complete.mp` → `BAValid` → `alg_complete_classical.mpr`. -/
theorem derivableInCplIffDerivableProp {φ : PL.Proposition Atom} :
    DerivableIn (IPL ∪ CPL : Theory Atom) φ ↔ Derivable (@PropositionalAxiom Atom) φ := by
  constructor
  · intro h
    rw [CPL.hilbert_alg_complete]
    rw [alg_complete_classical] at h
    intro H _ v
    apply h v
    intro B hB
    rcases (Set.mem_union B IPL CPL).mp hB with hIPL | hCPL
    · obtain ⟨C, rfl⟩ := Set.mem_range.mp hIPL
      simp [AlgEvaluate]
    · obtain ⟨C, rfl⟩ := Set.mem_range.mp hCPL
      simp only [Proposition.neg, AlgEvaluate_imp, AlgEvaluate_bot]
      rw [himp_eq_top_iff, HeytingAlgebra.himp_bot, HeytingAlgebra.himp_bot, compl_compl]
  · intro h
    rw [alg_complete_classical]
    intro H _ v hT
    exact CPL.hilbert_alg_complete.mp h H v

/-! ## ND Corollaries via Bridges -/

/-- **ND conservative extension (bridge corollary)**: IPL is a conservative extension of MPL
for bot-free formulas, in the ND setting. This is a corollary of `hilbertIplConservativeOverMpl`
via the algebraic bridges `derivableInIplIffDerivableInt` and `derivableInMplIffDerivableMin`. -/
theorem iplConservativeOverMpl' {A : PL.Proposition Atom}
    (hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (∅ : Theory Atom) A :=
  derivableInMplIffDerivableMin.mpr
    (hilbertIplConservativeOverMpl hBF (derivableInIplIffDerivableInt.mp h))

/-- **ND Glivenko (bridge corollary)**: if `A` is derivable in `IPL ∪ CPL`, then `¬¬A` is
derivable in IPL. This is a corollary of `hilbertGlivenko` via the algebraic bridges
`derivableInCplIffDerivableProp` and `derivableInIplIffDerivableInt`. -/
theorem glivenko' {A : PL.Proposition Atom}
    (h : DerivableIn (IPL ∪ CPL : Theory Atom) A) :
    DerivableIn (IPL : Theory Atom) (¬¬A) :=
  derivableInIplIffDerivableInt.mpr
    (hilbertGlivenko (derivableInCplIffDerivableProp.mp h))

end Cslib.Logic.PL
