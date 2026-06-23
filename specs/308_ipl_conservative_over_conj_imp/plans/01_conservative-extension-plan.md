# Implementation Plan: IPL Conservative over IPL⟨∧,→,⊤⟩

## Task

Prove the conservative extension theorem: IPL is conservative over IPL⟨∧,→,⊤⟩ for or-bot-free
formulas. File: `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean`.

## Phase 1: Write and verify the implementation [COMPLETED]

### Overview

Create `ConjImpConservative.lean` with four theorems:

1. `hilbertIplConservativeOverConjImp` (main theorem)
2. `derivableConjImpOfDerivableInt` (subsumption direction)
3. `hilbertIplConservativeOverConjImp_iff` (biconditional)
4. `ipl_conservative_over_conjImp` (ND corollary)

### Proof strategy

**Main theorem** mirrors `hilbertIplConservativeOverMpl` from HilbertConservativeGlivenko.lean:
- `conjImp_brouwerian_complete hOBF` reduces to showing `BrouwerianValid φ`
- `intro B _ v` introduces a Brouwerian semilattice `B` and valuation
- `IPL.hilbert_alg_complete.mp h (H := LowerSet B) (LowerSet.Iic ∘ v)` applies IPL Heyting
  completeness at `LowerSet B`
- `brouwerianEmbeddingLemma v φ hOBF` bridges Brouwerian and Heyting semantics

**Subsumption direction** needs a generic axiom-monotonicity combinator `liftDerivation` on
PL derivation trees (4 constructors: ax, assumption, modus_ponens, weakening). The function
maps `ConjImpAxiom → IntPropAxiom` via `ConjImpAxiom.toMinPropAxiom.toIntPropAxiom`.

**Biconditional** is a direct 2-line combination.

**ND corollary** uses `derivableInIplIffDerivableInt` bridge (requires `[DecidableEq Atom]`).

### Imports needed

```
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko
```

### Barrel import update

Add `ConjImpConservative` entry to `Cslib.lean` after `HilbertConservativeGlivenko`.

### Verification steps

1. `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative`
2. `lake exe checkInitImports`
3. `lake exe lint-style`

### Estimated size

~75-85 lines total.
