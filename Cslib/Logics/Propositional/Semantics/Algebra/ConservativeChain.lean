/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentConservativityInstances
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko
public import Cslib.Logics.Propositional.Semantics.Algebra.Conservative
-- Classical conservativity column (Kalmár / truth-assignment method):
-- CL-A CPL⟨→,⊤⟩ ⊂ CPL, CL-B CPL⟨∧,→,⊤⟩ ⊂ CPL, CL-C CPL⟨∧,→,⊥,⊤⟩ ⊂ CPL

/-! # Conservative Extension Chain for Propositional Logic

This module is the capstone of the algebraic semantics programme for propositional logic.
It consolidates the full conservative extension chain connecting five proof systems at
increasing expressive power, and the corresponding algebraic hierarchy connecting five
classes of algebras.

## The Conservative Extension Chain

```
IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ MPL ⊂ IPL ⊂ CPL
```

Each `⊂` denotes conservative extension for the smaller fragment's language:

| Step | Theorem | Fragment | Condition |
|------|---------|----------|-----------|
| IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ | `hilbertConjImpConservativeOverImp` | imp-top-only | `IsImpTopOnly` |
| IPL⟨→,⊤⟩ ⊂ IPL | `hilbertIplConservativeOverImp` | imp-top-only | `IsImpTopOnly` |
| IPL⟨∧,→,⊤⟩ ⊂ IPL | `hilbertIplConservativeOverConjImp` | or-bot-free | `IsOrBotFree` |
| MPL ⊂ IPL | `hilbertIplConservativeOverMpl` | bot-free | `IsBotFree` |
| IPL ⊂ CPL (Glivenko) | `hilbertGlivenko` | all | ¬¬-translation |

## Classical Conservativity Column (Kalmár / Truth-Assignment Method)

All three classical conservativity results (CL-A, CL-B, CL-C) use the Kalmár /
Tarski–Bernays truth-assignment method, in contrast to the algebraic/Brouwerian route above.

| Step (CL) | Theorem | Fragment | Condition |
|-----------|---------|----------|-----------|
| CL-A: CPL⟨→,⊤⟩ ⊂ CPL | `cpl_conservative_over_imp` | imp-top-only | `IsImpTopOnly` |
| CL-B: CPL⟨∧,→,⊤⟩ ⊂ CPL | `cpl_conservative_over_classicalConjImp` | or-bot-free | `IsOrBotFree` |
| CL-C: CPL⟨∧,→,⊥,⊤⟩ ⊂ CPL | `cpl_conservative_over_classicalConjImpBot` | or-free | `IsOrFree` |

The three towers — MPL (minimal), IPL (intuitionistic), CPL (classical) — are now
structurally symmetric: each is conservative over its ⟨∧,→,⊥,⊤⟩ rung by the route
appropriate to it (algebraic/Brouwerian for MPL/IPL, truth-assignment for CPL).

The new **inter-fragment** conservativity corollaries in this module compose these:

- `hilbertConjImpConservativeOverImp_fromMpl`: IPL⟨∧,→,⊤⟩ is conservative over IPL⟨→,⊤⟩
  by routing through IPL (IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ IPL).
- `hilbertMplConservativeOverImp`: MPL is conservative over IPL⟨→,⊤⟩ for imp-top-only
  bot-free formulas (composition of two steps).
- `hilbertMplConservativeOverConjImp`: MPL is conservative over IPL⟨∧,→,⊤⟩ for or-bot-free
  formulas (alias, since `IsOrBotFree → IsBotFree`, but derived via composition).

## The Algebraic Validity Subsumption Chain

```
HilbertValid ⊇ BrouwerianValid ⊇ GHAValid ⊇ HAValid ⊇ BAValid
```

(Each `⊇` means: if φ is valid in the more expressive class, it is valid in the
more restrictive class, restricted to the appropriate fragment.)

For the full language, the subsumption direction is reversed: more expressive logics
require more expressive algebraic models for soundness and completeness to hold.

The algebraic completeness theorems connect both sides:

| Logic | Axioms | Algebra | Completeness |
|-------|--------|---------|-------------|
| IPL⟨→,⊤⟩ | `ImpAxiom` | Hilbert algebras | `imp_hilbert_iff` |
| IPL⟨∧,→,⊤⟩ | `ConjImpAxiom` | Brouwerian semilattices | `conjImp_brouwerian_iff` |
| MPL | `MinPropAxiom` | GHAs | `MPL.hilbert_alg_completeness` |
| IPL | `IntPropAxiom` | Heyting algebras | `IPL.hilbert_alg_completeness` |
| CPL | `PropositionalAxiom` | Boolean algebras | `CPL.hilbert_alg_completeness` |

## The Derivability Subsumption Chain

```
ImpAxiom ⊆ ConjImpAxiom ⊆ MinPropAxiom ⊆ IntPropAxiom ⊆ PropositionalAxiom
```

Each inclusion holds by the respective `.toConjImpAxiom`, `.toMinPropAxiom`,
`.toIntPropAxiom`, `.toPropositionalAxiom` coercions (from `Axioms.lean` and
`FragmentAxioms.lean`).

## See Also

`MplConservativeChain.lean` provides alternative direct-algebraic proofs of the MPL
conservativity steps (`hilbertMplConservativeOverConjImp`, `hilbertMplConservativeOverImp`,
`GHAValid_implies_BrouwerianValid_orBotFree`) that stay entirely within GHA semantics
without routing through IPL derivability. Compare the `_direct` suffixed counterparts there.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [V. I. Glivenko, *Sur quelques points de la Logique de M. Brouwer*][Glivenko1929]
* [A. Rasiowa, R. Sikorski, *The Mathematics of Metamathematics*][RasiowaSikorski1963]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

universe u

/-! ## Derivability Subsumption Chain -/

/-- **Subsumption**: every formula derivable in the minimal Hilbert system is derivable
in the full intuitionistic Hilbert system.

Uses `liftDerivationTree` with the axiom subsumption chain
`MinPropAxiom → IntPropAxiom`. -/
theorem derivableMinOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ :=
  derivable_mono (fun _ hψ => hψ.toIntPropAxiom) h

/-- **Subsumption**: every formula derivable in the full intuitionistic Hilbert system is
derivable in the classical Hilbert system.

Uses `liftDerivationTree` with the axiom subsumption chain
`IntPropAxiom → PropositionalAxiom` via `IntPropAxiom.toPropAxiom`. -/
theorem derivableIntOfDerivableProp {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@PropositionalAxiom Atom) φ :=
  derivable_mono (fun _ hψ => hψ.toPropAxiom) h

/-- **Derivability subsumption chain**: derivability in `ImpAxiom` implies derivability in
`PropositionalAxiom`, via `IntPropAxiom`. For any formula `φ`:
```
Derivable ImpAxiom φ
  → Derivable IntPropAxiom φ
  → Derivable PropositionalAxiom φ
```
This is the proof-theoretic manifestation of the Imp → Int → Prop portion of the logical
hierarchy (the separate Min → Int → Prop chain above, at `derivableMinOfDerivableInt` /
`derivableIntOfDerivableProp`, is not what this theorem establishes). -/
theorem derivability_subsumption_chain {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ImpAxiom Atom) φ) :
    Derivable (@PropositionalAxiom Atom) φ :=
  derivableIntOfDerivableProp (derivableImpOfDerivableInt h)

/-! ## Algebraic Validity Subsumption Chain -/

/-- **Validity subsumption**: Hilbert-validity implies Brouwerian-validity for imp-top-only
formulas.

The proof routes through derivability using completeness:
1. `imp_hilbert_completeness hITO h` converts `HilbertValid φ` to `Derivable ImpAxiom φ`.
2. `liftDerivationTree` lifts to `Derivable ConjImpAxiom φ` (axiom subsumption).
3. `conjImp_brouwerian_soundness_derivable` converts to `BrouwerianValid φ`. -/
theorem HilbertValid_implies_BrouwerianValid_impTopOnly {Atom : Type u}
    {φ : PL.Proposition Atom} (hITO : φ.IsImpTopOnly = true) (h : HilbertValid.{u, u} φ) :
    BrouwerianValid.{u, u} φ := by
  obtain ⟨d⟩ := imp_hilbert_completeness hITO h
  exact conjImp_brouwerian_soundness_derivable
    ⟨liftDerivationTree (fun ψ hψ => hψ.toConjImpAxiom) d⟩

/-- **Validity subsumption**: GHA-validity implies Brouwerian-validity for or-bot-free formulas.

The proof routes through derivability using completeness:
1. `MPL.hilbert_alg_completeness.mpr h` converts `GHAValid φ` to `Derivable MinPropAxiom φ`.
2. `derivableMinOfDerivableInt` lifts to `Derivable IntPropAxiom φ` (subsumption).
3. `hilbertIplConservativeOverConjImp hOBF` reduces to `Derivable ConjImpAxiom φ`.
4. `conjImp_brouwerian_soundness_derivable` gives `BrouwerianValid φ`.

See also `GHAValid_implies_BrouwerianValid_direct` in `MplConservativeChain.lean` for a
direct algebraic proof that stays within GHA semantics without routing through IPL. -/
theorem GHAValid_implies_BrouwerianValid_orBotFree {Atom : Type u}
    {φ : PL.Proposition Atom} (hOBF : φ.IsOrBotFree = true) (h : GHAValid.{u, u} φ) :
    BrouwerianValid φ :=
  conjImp_brouwerian_soundness_derivable
    (hilbertIplConservativeOverConjImp hOBF
      (derivableMinOfDerivableInt (MPL.hilbert_alg_completeness.mpr h)))

/-- **Validity subsumption**: HA-validity implies GHA-validity for bot-free formulas.

For bot-free `φ`, `AlgEvaluate v bot_val φ` is independent of `bot_val` by
`AlgEvaluate_botFree_independent`. Hence evaluating in any GHA `G` with any `bot_val`
reduces to evaluating in `G` with `bot_val' := ⊤` (or any other value). Every GHA is
also an HA (since `GeneralizedHeytingAlgebra` is a superclass of `HeytingAlgebra` — wait,
the direction is reversed). Instead: use the `WithBot` construction.

Actually: for bot-free `φ`, `AlgEvaluate v bot_val φ = AlgEvaluate v ⊤ φ` for any `bot_val`.
So `GHAValid φ` reduces to: `∀ G _ v, AlgEvaluate v ⊤ φ = ⊤`, which is a special case of
`HAValid φ` (since every HA `H` satisfies `⊥ ≤ ⊤`, and we can pick `H` to be an HA, with `⊥`
in place of `bot_val`). But we want the other direction: `HAValid → GHAValid` for bot-free φ.

For bot-free `φ`: given any GHA `G`, assignment `v`, and `bot_val : G`, by
`AlgEvaluate_botFree_independent`, `AlgEvaluate v bot_val φ = AlgEvaluate v ⊥ φ` (where `⊥`
here means... wait, GHA may have no `⊥`). We instead reindex: use `WithBot G` (a HA), lift `v`
to `WithBot G`, apply `HAValid`, then project back using `coe_AlgEvaluate`. -/
theorem HAValid_implies_GHAValid {Atom : Type u} {φ : PL.Proposition Atom}
    (hBF : φ.IsBotFree = true) (h : HAValid.{u, u} φ) :
    GHAValid.{u, u} φ := by
  intro G _ v bot_val
  have hWithBot : AlgEvaluate (fun x => (v x : WithBot G)) (⊥ : WithBot G) φ = ⊤ :=
    h (WithBot G) (fun x => (v x : WithBot G))
  rw [coe_AlgEvaluate v bot_val φ hBF] at hWithBot
  exact WithBot.coe_eq_coe.mp hWithBot

/-! ## Inter-Fragment Conservativity Corollaries -/

/-- **MPL conservative over IPL⟨→,⊤⟩**: for imp-top-only bot-free formulas, MPL derivability
implies ImpAxiom derivability.

The proof composes two conservative extension steps:
1. `hilbertIplConservativeOverMpl` reduces IPL derivability to MPL derivability.
   But here we go in reverse: if derivable in IPL, reduce to MPL.
   Actually: for imp-top-only formulas, IPL ↔ Imp. Then Mpl ⊆ IPL always.
   So if φ is derivable in MPL (and imp-top-only, bot-free), then it's derivable in IPL
   (subsumption), and then by the IplConservativeOverImp it's derivable in Imp.

Formally: `derivableMinOfDerivableInt` (Mpl → IPL) composed with
`hilbertIplConservativeOverImp` (IPL → Imp for imp-top-only).

See also `hilbertMplConservativeOverImp_direct` in `MplConservativeChain.lean` for a
direct algebraic proof that avoids routing through IPL. -/
theorem hilbertMplConservativeOverImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@ImpAxiom Atom) φ :=
  hilbertIplConservativeOverImp hITO (derivableMinOfDerivableInt h)

/-- **ConjImp conservative over IPL⟨→,⊤⟩ via IPL**: for imp-top-only formulas, IPL⟨∧,→,⊤⟩
derivability implies ImpAxiom derivability (composing through IPL).

This makes the IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ conservativity step explicit in the chain:
ConjImp derivability implies IPL derivability (subsumption), which for imp-top-only
formulas reduces to Imp derivability. -/
theorem hilbertConjImpConservativeOverImp_viaIpl {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Derivable (@ConjImpAxiom Atom) φ) :
    Derivable (@ImpAxiom Atom) φ :=
  hilbertIplConservativeOverImp hITO (derivableConjImpOfDerivableInt h)

/-- **MPL conservative over IPL⟨∧,→,⊤⟩**: for or-bot-free formulas, MPL derivability
implies ConjImpAxiom derivability.

The proof composes: `derivableMinOfDerivableInt` (Mpl → IPL subsumption) followed by
`hilbertIplConservativeOverConjImp` (IPL → ConjImp for or-bot-free formulas).

See also `hilbertMplConservativeOverConjImp_direct` in `MplConservativeChain.lean` for a
direct algebraic proof via the GHA→BSL bridge that avoids routing through IPL. -/
theorem hilbertMplConservativeOverConjImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@ConjImpAxiom Atom) φ :=
  hilbertIplConservativeOverConjImp hOBF (derivableMinOfDerivableInt h)

/-! ## Glivenko Strength Wrapper

(The biconditionals `impAxiom_iff_chain` / `conjImpAxiom_iff_chain` / `orImpAxiom_iff_chain` /
`minAxiom_iff_chain` are not restated here: each is a `.symm` of an already-public
biconditional (`hilbertIplConservativeOverX_iff` / the `minAxiom` case) with no external
use-site, so a restatement here would add no new content.) -/

/-- **Theory-parametric Glivenko (strength wrapper)**: if every axiom of `A_cl` is a
`PropositionalAxiom` (classical soundness), and every `IntPropAxiom` is an axiom of `A_int`
(intuitionistic completeness), then CPL-strength derivability of `φ` implies
IPL-strength derivability of `¬¬φ`.

This is a convenience wrapper over `hilbertGlivenko_theory` that discharges the BA-soundness
and HA-completeness hypotheses via the Hilbert-level completeness theorems:
- `h_cl ψ hψ = CPL.hilbert_alg_completeness.mp (derivable_mono hcl hψ)` (soundness via CPL)
- `h_int ψ hHA = derivable_mono hint (IPL.hilbert_alg_completeness.mpr hHA)` (completeness via IPL)

**Design note (deviation from plan)**: The plan proposed using `CPL ⊆ AxiomTheory A_cl` /
`IPL ⊆ AxiomTheory A_int` as the strength hypotheses, following the ND-theory inclusion
idiom. Those inclusion conditions alone do not imply BA-soundness of `A_cl` (the axiom set
could contain non-BA-valid elements). The correct condition for BA-soundness is
`∀ ψ, A_cl ψ → PropositionalAxiom ψ` (A_cl is a sub-predicate of `PropositionalAxiom`), and
for HA-completeness is `∀ ψ, IntPropAxiom ψ → A_int ψ` (A_int extends IPL axioms).

**Concrete recovery**: `hilbertGlivenko = hilbertGlivenko_strength PropositionalAxiom IntPropAxiom
  (fun ψ h => h) (fun ψ h => h.toIntPropAxiom)`. -/
theorem hilbertGlivenko_strength {Atom : Type u} {φ : PL.Proposition Atom}
    (A_cl A_int : PL.Proposition Atom → Prop)
    [MinimalAxioms A_cl] [MinimalAxioms A_int]
    (hcl : ∀ ψ, A_cl ψ → @PropositionalAxiom Atom ψ)
    (hint : ∀ ψ, @IntPropAxiom Atom ψ → A_int ψ)
    (h : Derivable A_cl φ) : Derivable A_int (¬¬φ) :=
  hilbertGlivenko_theory A_cl A_int
    (fun _ hψ => CPL.hilbert_alg_completeness.mp (derivable_mono hcl hψ))
    (fun _ hHA => derivable_mono hint (IPL.hilbert_alg_completeness.mpr hHA))
    h

/-! ## ND Corollaries via Bridges -/

variable {Atom : Type u} [DecidableEq Atom]

/-- **ND inter-fragment conservativity**: for imp-top-only formulas, IPL derivability
implies ImpAxiom derivability (ND version of the chain endpoint).

Composes `derivableInIplIffDerivableInt` (bridge) with `hilbertIplConservativeOverImp`. -/
theorem nd_chain_ipl_to_imp {A : PL.Proposition Atom}
    (hITO : A.IsImpTopOnly = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ImpAxiom Atom) A :=
  ipl_conservative_over_imp hITO h

/-- **ND inter-fragment conservativity**: for or-bot-free formulas, IPL derivability
implies ConjImpAxiom derivability (ND version). -/
theorem nd_chain_ipl_to_conjImp {A : PL.Proposition Atom}
    (hOBF : A.IsOrBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ConjImpAxiom Atom) A :=
  ipl_conservative_over_conjImp hOBF h

/-- **ND inter-fragment conservativity**: for and-bot-free formulas, IPL derivability
implies OrImpAxiom derivability (ND version). -/
theorem nd_chain_ipl_to_orImp {A : PL.Proposition Atom}
    (hABF : A.IsAndBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@OrImpAxiom Atom) A :=
  ipl_conservative_over_orImp hABF h

/-- **ND Glivenko corollary**: if `A` is CPL-derivable, then `¬¬A` is IPL-derivable.
The negative translation bridges IPL and CPL at the top of the chain. -/
theorem nd_chain_cpl_glivenko {A : PL.Proposition Atom}
    (h : DerivableIn (IPL ∪ CPL : Theory Atom) A) :
    DerivableIn (IPL : Theory Atom) (¬¬A) :=
  glivenko h

end Cslib.Logic.PL

end
