# Implementation Summary: Task #322

- **Task**: 322 - MPL Conservative Extension Chain
- **Status**: [COMPLETED]
- **Phases Completed**: 3/3
- **Date**: 2026-06-24

## What Was Implemented

### Phase 1: Core Declarations (MplConservativeChain.lean)

Added 3 new theorems and refactored 1 existing theorem:

1. **`GHAValid_implies_BrouwerianValid_direct`** (NEW): Standalone validity-level bridge theorem
   that proves GHA-validity implies Brouwerian semilattice validity for or-bot-free formulas,
   using the direct algebraic route (instantiating at `LowerSet B`). Placed inside the
   `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra` region to avoid the
   typeclass diamond. Required explicit universe annotations `GHAValid.{u, u}` and
   `BrouwerianValid.{u, u}` to resolve a universe mismatch.

2. **`hilbertMplConservativeOverConjImp_direct`** (REFACTORED): Now delegates to
   `GHAValid_implies_BrouwerianValid_direct` rather than inlining the algebraic bridge.

3. **`derivableMinOfDerivableConjImp`** (NEW): Axiom subsumption theorem proving
   `ConjImpAxiom ⊆ MinPropAxiom` via `liftDerivationTree`. Placed outside the
   `attribute [-instance]` region as it uses pure tree manipulation.

4. **`derivableMinOfDerivableImp`** (NEW): Axiom subsumption theorem proving
   `ImpAxiom ⊆ MinPropAxiom` via `liftDerivationTree` with the two-step chain
   `ImpAxiom.toConjImpAxiom.toMinPropAxiom`. Placed outside the `attribute [-instance]` region.

Updated module docstring to list all 7 theorems.

### Phase 2: BibKey Entries (references.bib)

Added 2 BibTeX entries:
- `Nemitz1965`: "Implicative semi-lattices", Trans. Amer. Math. Soc. 117 (1965), pp. 128--142
- `Kohler1981`: "Brouwerian semilattices", Trans. Amer. Math. Soc. 268:1 (1981), pp. 103--126

Inserted after the `MacNeille1937` entry.

### Phase 3: CI Verification

- `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain`: PASSED
- `lake exe lint-style`: PASSED (no issues in our modified files)
- `lake lint` (for our module): PASSED (no warnings)
- Zero `sorry` in MplConservativeChain.lean: CONFIRMED
- No new axioms introduced: CONFIRMED (only standard Lean axioms: propext, Classical.choice, Quot.sound)
- Independence constraint: CONFIRMED (no IPL proof terms in MplConservativeChain.lean)
- BibKey entries present: CONFIRMED (both Nemitz1965 and Kohler1981 in references.bib)

Note: Pre-existing failures in `Tableau/Classical/Completeness.lean`,
`NaturalDeduction/Normalization.lean`, and `Tableau/Intuitionistic/Soundness.lean` are unrelated
to our changes and being tracked in tasks 323 and 324.

## Plan Deviations

1. **Universe annotations required**: The plan proposed `(h : GHAValid φ) : BrouwerianValid φ`
   without universe annotations, but Lean required explicit `GHAValid.{u, u}` and
   `BrouwerianValid.{u, u}` to resolve a universe mismatch when instantiating `h` at
   `LowerSet B`. The universe mismatch occurs because `GHAValid` and `BrouwerianValid` both
   use `Type*` (implicitly `Type u_1`), and `B` in the `BrouwerianValid` unfolded goal has its
   own universe `u_2`. Fixing by making both explicit to the same universe `u`.

2. **Theorem naming**: Plan mentioned `derivableConjImpOfDerivableMin` and
   `derivableImpOfDerivableMin` but these names represent the wrong direction (ConjImp/Imp FROM
   Min, which is the conservativity direction already covered by `hilbertMplConservativeOverConjImp_direct`).
   Used `derivableMinOfDerivableConjImp` and `derivableMinOfDerivableImp` instead (Min FROM
   ConjImp/Imp, which is the subsumption/inclusion direction). This matches the plan's stated
   goal of "axiom-lifting direction" and is consistent with the naming pattern used in
   ConservativeChain.lean.

## Artifacts

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`
  - Added: `GHAValid_implies_BrouwerianValid_direct`, `derivableMinOfDerivableConjImp`,
    `derivableMinOfDerivableImp`
  - Refactored: `hilbertMplConservativeOverConjImp_direct` (delegates to new theorem)
  - Updated: module docstring (lists all 7 theorems)
- `/home/benjamin/Projects/cslib/references.bib`
  - Added: `Nemitz1965`, `Kohler1981`
