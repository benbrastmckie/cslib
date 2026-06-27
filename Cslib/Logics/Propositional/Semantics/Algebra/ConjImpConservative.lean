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

/-! # Conservative Extension: IPL over IPL⟨∧,→,⊤⟩

This module proves that IPL is a conservative extension of the conjunctive-implicational
fragment IPL⟨∧,→,⊤⟩ for or-bot-free formulas.

## Main Results

- `hilbertIplConservativeOverConjImp`: IPL is a conservative extension of IPL⟨∧,→,⊤⟩ for
  or-bot-free formulas, stated in terms of `Derivable IntPropAxiom` and `Derivable ConjImpAxiom`.
- `derivableConjImpOfDerivableInt`: Every `ConjImpAxiom`-derivable formula is
  `IntPropAxiom`-derivable (subsumption).
- `hilbertIplConservativeOverConjImp_iff`: For or-bot-free formulas, Hilbert IPL derivability
  and IPL⟨∧,→,⊤⟩ derivability coincide.
- `ipl_conservative_over_conjImp`: ND corollary of the conservative extension theorem.

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

/-! ## Generic Axiom-Monotonicity Combinator -/

/-- Axiom-monotonicity: given an axiom subsumption `h_sub : ∀ φ, Axioms1 φ → Axioms2 φ`,
lift a `DerivationTree Axioms1 Γ φ` to a `DerivationTree Axioms2 Γ φ`. -/
def liftDerivationTree
    {Atom : Type u}
    {Axioms1 Axioms2 : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, Axioms1 ψ → Axioms2 ψ)
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    DerivationTree Axioms1 Γ φ → DerivationTree Axioms2 Γ φ
  | .ax Γ φ h => .ax Γ φ (h_sub φ h)
  | .assumption Γ φ h => .assumption Γ φ h
  | .modus_ponens Γ φ ψ d₁ d₂ =>
      .modus_ponens Γ φ ψ (liftDerivationTree h_sub d₁) (liftDerivationTree h_sub d₂)
  | .weakening Γ Δ φ d h => .weakening Γ Δ φ (liftDerivationTree h_sub d) h

/-! ## Axiom-Monotonicity Lemma -/

/-- **Axiom-monotonicity**: if every axiom of `A₁` is also an axiom of `A₂`, then every
formula derivable from `A₁` is also derivable from `A₂`.

This is the "subsumption" or "monotonicity" lemma for Hilbert derivability. It lifts the
pointwise axiom inclusion `h_sub : ∀ ψ, A₁ ψ → A₂ ψ` to a derivability inclusion
`Derivable A₁ φ → Derivable A₂ φ` using `liftDerivationTree`. -/
theorem derivable_mono {Atom : Type u}
    {A₁ A₂ : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, A₁ ψ → A₂ ψ)
    {φ : PL.Proposition Atom}
    (h : Derivable A₁ φ) : Derivable A₂ φ :=
  let ⟨d⟩ := h; ⟨liftDerivationTree h_sub d⟩

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

/-! ## Subsumption Direction -/

/-- **Subsumption**: every formula derivable in the conjunctive-implicational Hilbert system
is derivable in the full intuitionistic Hilbert system.

Uses `liftDerivationTree` with the axiom subsumption chain
`ConjImpAxiom → MinPropAxiom → IntPropAxiom`. -/
theorem derivableConjImpOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ConjImpAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ :=
  derivable_mono (fun _ hψ => hψ.toMinPropAxiom.toIntPropAxiom) h

/-! ## Biconditional -/

/-- **Biconditional**: for or-bot-free formulas, derivability in the intuitionistic Hilbert
system and derivability in the conjunctive-implicational Hilbert system coincide. -/
theorem hilbertIplConservativeOverConjImp_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@ConjImpAxiom Atom) φ :=
  ⟨hilbertIplConservativeOverConjImp hOBF, derivableConjImpOfDerivableInt⟩

/-! ## ND Corollary -/

variable {Atom : Type u} [DecidableEq Atom]

/-- **ND conservative extension**: IPL is a conservative extension of IPL⟨∧,→,⊤⟩ for
or-bot-free formulas. If a formula containing no `∨` or `⊥` is derivable in the ND system
for IPL, then it is derivable in the conjunctive-implicational Hilbert system.

This is derived as a corollary of `hilbertIplConservativeOverConjImp` via the algebraic
bridge `derivableInIplIffDerivableInt`. -/
theorem ipl_conservative_over_conjImp {A : PL.Proposition Atom}
    (hOBF : A.IsOrBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ConjImpAxiom Atom) A :=
  hilbertIplConservativeOverConjImp hOBF (derivableInIplIffDerivableInt.mp h)

end Cslib.Logic.PL

end

end
