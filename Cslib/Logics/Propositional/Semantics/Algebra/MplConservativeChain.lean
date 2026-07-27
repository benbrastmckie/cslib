/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentConservativity
public import Cslib.Logics.Propositional.Semantics.Algebra.ImpConservative
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative
public import Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative

/-! # MPL Conservative Extension Chain (Direct Algebraic Route)

This module proves that MPL (Minimal Propositional Logic) is conservative over the
conjunctive-implicational fragment IPL⟨∧,→,⊤⟩ and the purely implicational fragment
IPL⟨→,⊤⟩ via a **direct algebraic route** that does not pass through IPL.

## The MPL Chain

```
IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ MPL
```

In terms of derivability:

```
ImpAxiom ⊆ ConjImpAxiom ⊆ MinPropAxiom
```

The conservativity direction (restricting MPL theorems to smaller fragments) is:
- For or-bot-free `φ`: `Derivable MinPropAxiom φ → Derivable ConjImpAxiom φ`
- For imp-top-only `φ`: `Derivable MinPropAxiom φ → Derivable ImpAxiom φ`

## Why a Standalone Module?

The corresponding results in `ConservativeChain.lean` route through IPL derivability:
```
MinPropAxiom ↪ IntPropAxiom  (subsumption)
              ↓ hilbertIplConservativeOverConjImp
            ConjImpAxiom
```

This module provides a **direct algebraic route** that stays entirely within GHA semantics:
```
GHAValid φ
    ↓ instantiate GHAValid at LowerSet B (a HA, hence a GHA)
AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤
    ↓ brouwerianEmbeddingLemma (reverse direction)
BrouwerianEvaluate v φ = ⊤
    ↓ conjImp_brouwerian_completeness
Derivable ConjImpAxiom φ
```

The bridge `LowerSet B` is a Heyting algebra (and hence a GHA), so any GHA-valid formula
evaluates to `⊤` there. The embedding lemma `brouwerianEmbeddingLemma` then converts this to
Brouwerian semilattice validity, which by completeness gives ConjImp derivability.

## Relationship to `ConservativeChain.lean`

`ConservativeChain.lean` imports IPL machinery (`HilbertConservativeGlivenko`,
`Conservative`) and builds the full IPL⊃MPL chain. This module is self-contained over the
MPL fragment and its subalgebras, avoiding any dependency on IPL conservativity lemmas.

## Main Results

- `GHAValid_implies_BrouwerianValid_direct`: GHA-validity implies Brouwerian validity for
  or-bot-free formulas, proved directly without routing through IPL.
- `hilbertMplConservativeOverConjImp_direct`: MPL is conservative over ConjImp for
  or-bot-free formulas, via the direct GHA→BSL bridge.
- `mplAxiom_iff_conjImpAxiom`: Biconditional: MinPropAxiom ↔ ConjImpAxiom for or-bot-free.
- `GHAValid_implies_BrouwerianBotValid_direct`: GHA-validity implies free-bot Brouwerian
  validity for or-free formulas.
- `hilbertMplConservativeOverConjImpBot_direct`: MPL is conservative over ConjImpBotMin for
  or-free formulas, via the direct GHA→free-bot-BSL bridge (fourth tower step).
- `mplAxiom_iff_conjImpBotMinAxiom`: Biconditional: MinPropAxiom ↔ ConjImpBotMinAxiom for
  or-free formulas.
- `hilbertMplConservativeOverImp_direct`: MPL is conservative over ImpAxiom for
  imp-top-only formulas, by composing the two direct steps.
- `mplAxiom_iff_impAxiom`: Biconditional: MinPropAxiom ↔ ImpAxiom for imp-top-only.
- `derivableMinOfDerivableConjImp`: Axiom subsumption: ConjImpAxiom ⊆ MinPropAxiom
  (inclusion direction).
- `derivableMinOfDerivableImp`: Axiom subsumption: ImpAxiom ⊆ MinPropAxiom (inclusion
  direction, via the ConjImp intermediate step).

## Algebraic Hierarchy

```
GHAValid ⊇ BrouwerianValid  (restricted to or-bot-free)
```

Every GHA-valid or-bot-free formula is Brouwerian-valid, because `LowerSet B` (for any
Brouwerian semilattice `B`) is a Heyting algebra (hence a GHA), and the principal downset
embedding `LowerSet.Iic : B → LowerSet B` converts Heyting algebra validity to Brouwerian
semilattice validity via `brouwerianEmbeddingLemma`.

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

/-! ## Direct MPL→ConjImp Conservativity -/

-- Suppress the `BrouwerianSemilattice.toHilbertAlgebra` forgetful instance for the next
-- theorem. Without this, importing `ImpConservative` (transitively via `FreeMeetExtension` →
-- `HilbertAlgebra`) creates a typeclass diamond for `Preorder B` in `LowerSet.Iic`,
-- causing `MPL.hilbert_alg_completeness.mp h (LowerSet B) ...` to return a term with
-- `HilbertAlgebra.instPartialOrder` that is rejected by `brouwerianEmbeddingLemma` which
-- expects `BrouwerianSemilattice.toSemilatticeInf.toPartialOrder`. Suppressing forces the
-- unique BSL-derived PartialOrder path.
attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra

/-- **GHA-to-Brouwerian validity bridge**: GHA-validity implies Brouwerian semilattice
validity for or-bot-free formulas, proved by a direct algebraic route without IPL.

The proof instantiates `GHAValid φ` at the free join completion `LowerSet B` (a Heyting
algebra, hence a GHA) with the principal downset embedding `LowerSet.Iic ∘ v : Atom → LowerSet B`
and bottom value `⊥`, then applies `brouwerianEmbeddingLemma` to convert the resulting
`AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤` to `BrouwerianEvaluate v φ = ⊤`.

This is the algebraic core of `hilbertMplConservativeOverConjImp_direct`, extracted as a
standalone lemma. See also `GHAValid_implies_BrouwerianValid_orBotFree` in
`ConservativeChain.lean`, which proves the same result by routing through IPL derivability.

References: [Nemitz1965], [Kohler1981]. -/
theorem GHAValid_implies_BrouwerianValid_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : GHAValid.{u, u} φ) : BrouwerianValid.{u, u} φ := by
  intro B _ v
  exact (brouwerianEmbeddingLemma v φ hOBF).mpr (h (H := LowerSet B) (LowerSet.Iic ∘ v) ⊥)

/-- **Direct MPL-to-ConjImp conservative extension theorem**: MPL is a conservative extension
of IPL⟨∧,→,⊤⟩ for or-bot-free formulas, proved via a direct algebraic route without IPL.

The proof composes:
1. `MPL.hilbert_alg_completeness.mp h` converts `Derivable MinPropAxiom φ` to `GHAValid φ`.
2. `GHAValid_implies_BrouwerianValid_direct` converts `GHAValid φ` to `BrouwerianValid φ` by
   instantiating at `LowerSet B` (a `HeytingAlgebra`, hence a `GeneralizedHeytingAlgebra`)
   and applying `brouwerianEmbeddingLemma`.
3. `conjImp_brouwerian_completeness hOBF` converts `BrouwerianValid φ` to
   `Derivable ConjImpAxiom φ`.

See also `hilbertMplConservativeOverConjImp` in `ConservativeChain.lean`, which proves the
same result by routing through `derivableMinOfDerivableInt` (MPL→IPL subsumption) followed
by `hilbertIplConservativeOverConjImp` (IPL→ConjImp conservativity). -/
theorem hilbertMplConservativeOverConjImp_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@ConjImpAxiom Atom) φ :=
  conjImp_brouwerian_completeness hOBF
    (GHAValid_implies_BrouwerianValid_direct hOBF (MPL.hilbert_alg_completeness.mp h))

/-! ## Direct MPL→ConjImpBotMin Conservativity -/

/-- **GHA-to-free-bot-Brouwerian validity bridge**: GHA-validity implies free-bot Brouwerian
semilattice validity for or-free formulas, proved by a direct algebraic route without IPL.

The proof instantiates `GHAValid φ` at the free join completion `LowerSet B` (a Heyting
algebra, hence a GHA) with the principal downset embedding `LowerSet.Iic ∘ v : Atom → LowerSet B`
and free bottom value `LowerSet.Iic bot_val`, then applies `brouwerianBotEmbeddingLemma` to
convert the resulting `AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ = ⊤` to
`BrouwerianBotEvaluate v bot_val φ = ⊤`.

This is the algebraic core of `hilbertMplConservativeOverConjImpBot_direct`. The key
difference from `GHAValid_implies_BrouwerianValid_direct` is that `bot_val` is free (no
`OrderBot` constraint), allowing `⊥` to be used in formulas without ex falso. -/
theorem GHAValid_implies_BrouwerianBotValid_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : GHAValid.{u, u} φ) : BrouwerianBotValid.{u, u} φ := by
  intro B _ v bot_val
  exact (brouwerianBotEmbeddingLemma v bot_val φ hOF).mpr
    (h (H := LowerSet B) (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val))

attribute [instance] BrouwerianSemilattice.toHilbertAlgebra

/-! ## Biconditional for MPL↔ConjImp -/

/-- **Biconditional**: for or-bot-free formulas, derivability in MinPropAxiom and
ConjImpAxiom coincide.

The forward direction is the direct conservativity `hilbertMplConservativeOverConjImp_direct`.
The backward direction lifts via the axiom subsumption chain
`ConjImpAxiom → MinPropAxiom` using `liftDerivationTree`. -/
theorem mplAxiom_iff_conjImpAxiom {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) :
    Derivable (@MinPropAxiom Atom) φ ↔ Derivable (@ConjImpAxiom Atom) φ :=
  ⟨hilbertMplConservativeOverConjImp_direct hOBF, fun ⟨d⟩ =>
    ⟨liftDerivationTree (fun _ hψ => hψ.toMinPropAxiom) d⟩⟩

/-! ## Direct MPL→ConjImpBotMin Conservativity (Chain Step 4) -/

/-- **Direct MPL-to-ConjImpBotMin conservative extension theorem**: MPL is a conservative
extension of MPL⟨∧,→,⊥,⊤⟩ for or-free formulas, proved via a direct algebraic route.

The proof composes:
1. `MPL.hilbert_alg_completeness.mp h` converts `Derivable MinPropAxiom φ` to `GHAValid φ`.
2. `GHAValid_implies_BrouwerianBotValid_direct` converts `GHAValid φ` to `BrouwerianBotValid φ`
   by instantiating at `LowerSet B` (a `HeytingAlgebra`, hence a `GeneralizedHeytingAlgebra`)
   with `bot_val = LowerSet.Iic bot_val` and applying `brouwerianBotEmbeddingLemma`.
3. `conjImpBotMin_brouwerianBot_completeness hOF` converts `BrouwerianBotValid φ` to
   `Derivable ConjImpBotMinAxiom φ`.

This is the fourth step of the MPL fragment tower:
`MPL⟨→,⊤⟩ ⊂ MPL⟨∧,→,⊤⟩ ⊂ MPL⟨∧,→,⊥,⊤⟩ ⊂ MPL`. -/
theorem hilbertMplConservativeOverConjImpBot_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@ConjImpBotMinAxiom Atom) φ :=
  conjImpBotMin_brouwerianBot_completeness hOF
    (GHAValid_implies_BrouwerianBotValid_direct hOF (MPL.hilbert_alg_completeness.mp h))

/-- **Biconditional**: for or-free formulas, derivability in MinPropAxiom and
ConjImpBotMinAxiom coincide.

The forward direction is the direct conservativity `hilbertMplConservativeOverConjImpBot_direct`.
The backward direction lifts via the axiom subsumption `ConjImpBotMinAxiom → MinPropAxiom`
using `liftDerivationTree` (`ConjImpConservative.lean`) and
`ConjImpBotMinAxiom.toMinPropAxiom` (`FragmentAxioms.lean`). -/
theorem mplAxiom_iff_conjImpBotMinAxiom {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) :
    Derivable (@MinPropAxiom Atom) φ ↔ Derivable (@ConjImpBotMinAxiom Atom) φ :=
  ⟨hilbertMplConservativeOverConjImpBot_direct hOF, fun ⟨d⟩ =>
    ⟨liftDerivationTree (fun _ hψ => hψ.toMinPropAxiom) d⟩⟩

/-! ## Direct MPL→Imp Conservativity (Composition) -/

/-- **Direct MPL-to-Imp conservative extension theorem**: MPL is a conservative extension
of IPL⟨→,⊤⟩ for imp-top-only formulas, proved by composing the two direct steps.

The proof composes:
1. `hilbertMplConservativeOverConjImp_direct` (MPL → ConjImp for or-bot-free; applies since
   imp-top-only implies or-bot-free via `IsImpTopOnly_implies_IsOrBotFree`).
2. `hilbertConjImpConservativeOverImp` (ConjImp → Imp for imp-top-only).

See also `hilbertMplConservativeOverImp` in `ConservativeChain.lean`, which proves the same
result via the IPL-routing path: MPL → IPL (subsumption) → Imp (conservativity). -/
theorem hilbertMplConservativeOverImp_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@ImpAxiom Atom) φ :=
  hilbertConjImpConservativeOverImp hITO
    (hilbertMplConservativeOverConjImp_direct (IsImpTopOnly_implies_IsOrBotFree φ hITO) h)

/-! ## Biconditional for MPL↔Imp -/

/-- **Biconditional**: for imp-top-only formulas, derivability in MinPropAxiom and
ImpAxiom coincide.

The forward direction is the direct conservativity `hilbertMplConservativeOverImp_direct`.
The backward direction lifts via the axiom subsumption chain
`ImpAxiom → ConjImpAxiom → MinPropAxiom` using `liftDerivationTree`. -/
theorem mplAxiom_iff_impAxiom {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) :
    Derivable (@MinPropAxiom Atom) φ ↔ Derivable (@ImpAxiom Atom) φ :=
  ⟨hilbertMplConservativeOverImp_direct hITO, fun ⟨d⟩ =>
    ⟨liftDerivationTree (fun _ hψ => hψ.toConjImpAxiom.toMinPropAxiom) d⟩⟩

/-! ## Axiom Subsumption: MPL contains ConjImp and Imp -/

/-- **Axiom subsumption**: ConjImpAxiom is contained in MinPropAxiom.

Any formula derivable in IPL⟨∧,→,⊤⟩ (ConjImpAxiom) is also derivable in MPL
(MinPropAxiom), since every ConjImp axiom is a MinProp axiom via `ConjImpAxiom.toMinPropAxiom`.

This is the inclusion direction `ConjImpAxiom ⊆ MinPropAxiom` in the chain
`ImpAxiom ⊆ ConjImpAxiom ⊆ MinPropAxiom`. -/
theorem derivableMinOfDerivableConjImp {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ConjImpAxiom Atom) φ) : Derivable (@MinPropAxiom Atom) φ :=
  let ⟨d⟩ := h; ⟨liftDerivationTree (fun _ hψ => hψ.toMinPropAxiom) d⟩

/-- **Axiom subsumption**: ImpAxiom is contained in MinPropAxiom.

Any formula derivable in IPL⟨→,⊤⟩ (ImpAxiom) is also derivable in MPL (MinPropAxiom),
since every Imp axiom lifts to a ConjImp axiom via `ImpAxiom.toConjImpAxiom` and then
to a MinProp axiom via `ConjImpAxiom.toMinPropAxiom`.

This is the inclusion direction `ImpAxiom ⊆ MinPropAxiom` in the chain
`ImpAxiom ⊆ ConjImpAxiom ⊆ MinPropAxiom`. -/
theorem derivableMinOfDerivableImp {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ImpAxiom Atom) φ) : Derivable (@MinPropAxiom Atom) φ :=
  let ⟨d⟩ := h; ⟨liftDerivationTree (fun _ hψ => hψ.toConjImpAxiom.toMinPropAxiom) d⟩

end Cslib.Logic.PL

end

end
