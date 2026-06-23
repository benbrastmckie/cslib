# Implementation Summary: IPL Conservative over IPL⟨∧,→,⊤⟩

## Task

Proved the conservative extension theorem: IPL is conservative over IPL⟨∧,→,⊤⟩ for
or-bot-free formulas.

## File Created

`Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean`

## Theorems Proved

1. **`hilbertIplConservativeOverConjImp`**: Main theorem — if `φ` is IPL-derivable (Hilbert)
   and or-bot-free, then `φ` is IPL⟨∧,→,⊤⟩-derivable.
   - Proof: `conjImp_brouwerian_complete` + instantiate `HAValid` at `LowerSet B` +
     `brouwerianEmbeddingLemma`.

2. **`derivableConjImpOfDerivableInt`**: Subsumption — every ConjImpAxiom-derivable formula is
   IntPropAxiom-derivable. Uses new `liftDerivationTree` combinator.

3. **`hilbertIplConservativeOverConjImp_iff`**: Biconditional combining the two directions.

4. **`ipl_conservative_over_conjImp`**: ND corollary via `derivableInIplIffDerivableInt` bridge.

## Helper Added

**`liftDerivationTree`**: Generic axiom-monotonicity combinator on PL `DerivationTree`
(structural recursion on 4 constructors). Lifts `Axioms1`-derivations to `Axioms2`-derivations
given `∀ φ, Axioms1 φ → Axioms2 φ`.

## Barrel Import

Added `ConjImpConservative` entry to `Cslib.lean` (alphabetically between the `C` entries and
`HilbertConservativeGlivenko`).

## Verification

- `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative` — PASSED
- `lake exe lint-style` — PASSED (no warnings)
- `lake lint` — no warnings for the new file
- Axiom check: only `propext`, `Classical.choice`, `Quot.sound` (standard)
- Zero sorries, zero new axioms

## Plan Deviations

None. Implementation followed the plan exactly.
