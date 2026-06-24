/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension
public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative

/-! # Conservative Extension: IPL over IPL⟨→,⊤⟩

This module proves that IPL is a conservative extension of the purely implicational fragment
IPL⟨→,⊤⟩ for imp-top-only formulas.

## Main Results

- `freeMeetEvaluateEq`: For `IsImpTopOnly φ`, `BrouwerianEvaluate (freeMeetEmbed ∘ v) φ =
  freeMeetEmbed (HilbertEvaluate v φ)`. The singleton embedding intertwines the two evaluators.
- `hilbertConjImpConservativeOverImp`: IPL⟨∧,→,⊤⟩ is a conservative extension of IPL⟨→,⊤⟩
  for imp-top-only formulas.
- `hilbertIplConservativeOverImp`: IPL is a conservative extension of IPL⟨→,⊤⟩ for
  imp-top-only formulas.
- `derivableImpOfDerivableInt`: Every `ImpAxiom`-derivable formula is `IntPropAxiom`-derivable
  (subsumption direction).
- `hilbertIplConservativeOverImp_iff`: For imp-top-only formulas, IPL and IPL⟨→,⊤⟩ derivability
  coincide.
- `ipl_conservative_over_imp`: ND corollary of the conservative extension theorem.

## Proof Strategy

1. **Embedding lemma** (`freeMeetEvaluateEq`): By structural induction on imp-top-only formulas,
   the `BrouwerianEvaluate` at `FreeMeetExtension H` with valuation `freeMeetEmbed ∘ v` agrees
   with `freeMeetEmbed (HilbertEvaluate v φ)`. The key step for `imp` uses `freeMeetEmbed_himp`.
2. **ConjImp→Imp conservativity** (`hilbertConjImpConservativeOverImp`):
   - `conjImp_brouwerian_soundness_derivable` gives `BrouwerianValid φ`.
   - Instantiate at `FreeMeetExtension H` with `freeMeetEmbed ∘ v`.
   - `freeMeetEvaluateEq` rewrites to `freeMeetEmbed (HilbertEvaluate v φ) = ⊤`.
   - `freeMeetEmbed_eq_top_iff` gives `HilbertEvaluate v φ = ⊤`.
   - `imp_hilbert_complete` closes.
3. **IPL→Imp conservativity** (`hilbertIplConservativeOverImp`): compose Step 1 and Step 2 via
   `hilbertIplConservativeOverConjImp` and `IsImpTopOnly_implies_IsOrBotFree`.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn HilbertAlgebra

universe u

/-! ## Evaluation Coherence Lemma -/

/-- For imp-top-only formulas, the Brouwerian evaluator at `FreeMeetExtension H` with valuation
`freeMeetEmbed ∘ v` agrees with the Hilbert evaluator followed by the singleton embedding.

This is the key bridge between `BrouwerianEvaluate` (used in ConjImp completeness) and
`HilbertEvaluate` (used in Imp completeness): both compute the same thing on imp-top-only
formulas, up to the embedding `freeMeetEmbed : H → FreeMeetExtension H`. -/
theorem freeMeetEvaluateEq {Atom : Type u} {H : Type u} [HilbertAlgebra H]
    (v : Atom → H) (φ : PL.Proposition Atom) (hφ : φ.IsImpTopOnly = true) :
    BrouwerianEvaluate (freeMeetEmbed ∘ v) φ = freeMeetEmbed (HilbertEvaluate v φ) := by
  induction φ with
  | atom x => rfl
  | bot => simp [Proposition.IsImpTopOnly] at hφ
  | imp a b iha ihb =>
    simp only [Proposition.IsImpTopOnly, Bool.and_eq_true] at hφ
    simp only [BrouwerianEvaluate_imp, HilbertEvaluate_imp,
               iha hφ.1, ihb hφ.2, freeMeetEmbed_himp]
  | and _ _ _ _ => simp [Proposition.IsImpTopOnly] at hφ
  | or _ _ _ _ => simp [Proposition.IsImpTopOnly] at hφ

/-! ## ConjImp→Imp Conservative Extension -/

/-- **Hilbert ConjImp-to-Imp conservative extension theorem**: IPL⟨∧,→,⊤⟩ is a conservative
extension of IPL⟨→,⊤⟩ for imp-top-only formulas. If `φ` is derivable in the
conjunctive-implicational Hilbert system and contains no `∧`, `∨`, or `⊥`, then `φ` is already
derivable in the purely implicational Hilbert system.

The proof routes through the free BrouwerianSemilattice construction:
1. `conjImp_brouwerian_soundness_derivable h` gives `BrouwerianValid φ`.
2. Instantiate at `FreeMeetExtension H` with `freeMeetEmbed ∘ v`. This gives
   `BrouwerianEvaluate (freeMeetEmbed ∘ v) φ = ⊤`.
3. `freeMeetEvaluateEq` rewrites this to `freeMeetEmbed (HilbertEvaluate v φ) = ⊤`.
4. `freeMeetEmbed_eq_top_iff` gives `HilbertEvaluate v φ = ⊤`.
5. `imp_hilbert_complete` converts to `Derivable ImpAxiom φ`. -/
theorem hilbertConjImpConservativeOverImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Derivable (@ConjImpAxiom Atom) φ) :
    Derivable (@ImpAxiom Atom) φ := by
  apply imp_hilbert_complete hITO
  intro H _ v
  have hBV := conjImp_brouwerian_soundness_derivable h
  have hFME := hBV (FreeMeetExtension H) (freeMeetEmbed ∘ v)
  rw [freeMeetEvaluateEq v φ hITO] at hFME
  exact freeMeetEmbed_eq_top_iff.mp hFME

/-! ## Full IPL→Imp Conservative Extension -/

/-- **Hilbert IPL-to-Imp conservative extension theorem**: IPL is a conservative extension of
IPL⟨→,⊤⟩ for imp-top-only formulas. If `φ` is derivable in the intuitionistic Hilbert system
and contains no `∧`, `∨`, or `⊥`, then `φ` is already derivable in the purely implicational
Hilbert system.

The proof composes the two conservativity steps:
1. `hilbertIplConservativeOverConjImp` reduces IPL to ConjImp derivability (requires IsOrBotFree,
   which follows from `IsImpTopOnly_implies_IsOrBotFree`).
2. `hilbertConjImpConservativeOverImp` reduces ConjImp to Imp derivability (uses the free BSL). -/
theorem hilbertIplConservativeOverImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@ImpAxiom Atom) φ :=
  hilbertConjImpConservativeOverImp hITO
    (hilbertIplConservativeOverConjImp (IsImpTopOnly_implies_IsOrBotFree φ hITO) h)

/-! ## Subsumption Direction -/

/-- **Subsumption**: every formula derivable in the purely implicational Hilbert system is
derivable in the full intuitionistic Hilbert system.

Uses `liftDerivationTree` with the axiom subsumption chain
`ImpAxiom → ConjImpAxiom → MinPropAxiom → IntPropAxiom`. -/
theorem derivableImpOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ImpAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ := by
  obtain ⟨d⟩ := h
  exact ⟨liftDerivationTree
    (fun ψ hψ => hψ.toConjImpAxiom.toMinPropAxiom.toIntPropAxiom) d⟩

/-! ## Biconditional -/

/-- **Biconditional**: for imp-top-only formulas, derivability in the intuitionistic Hilbert
system and derivability in the purely implicational Hilbert system coincide. -/
theorem hilbertIplConservativeOverImp_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@ImpAxiom Atom) φ :=
  ⟨hilbertIplConservativeOverImp hITO, derivableImpOfDerivableInt⟩

/-! ## ND Corollary -/

variable {Atom : Type u} [DecidableEq Atom]

/-- **ND conservative extension**: IPL is a conservative extension of IPL⟨→,⊤⟩ for
imp-top-only formulas. If a formula containing no `∧`, `∨`, or `⊥` is derivable in the ND
system for IPL, then it is derivable in the purely implicational Hilbert system.

This is derived as a corollary of `hilbertIplConservativeOverImp` via the algebraic
bridge `derivableInIplIffDerivableInt`. -/
theorem ipl_conservative_over_imp {A : PL.Proposition Atom}
    (hITO : A.IsImpTopOnly = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ImpAxiom Atom) A :=
  hilbertIplConservativeOverImp hITO (derivableInIplIffDerivableInt.mp h)

end Cslib.Logic.PL

end

end
