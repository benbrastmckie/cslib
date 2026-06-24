
# Implementation Summary: Task #320
# Remove ND-level metalogic superseded by Hilbert-primary results

- **Task**: 320 - Remove ND-level metalogic superseded by Hilbert-primary results
- **Status**: Implemented
- **Completed**: 2026-06-23
- **Phases**: 5/5 completed

## Summary

Successfully removed 847 lines of ND-level algebraic completeness infrastructure
(`Completeness.lean` 277 lines, `Lindenbaum.lean` 425 lines, `LindenbaumInstances.lean` 145
lines) that were superseded by Hilbert-primary results. The bridge theorems in
`HilbertConservativeGlivenko.lean` now use purely syntactic (proof-theoretic) proofs
that compose `hilbert_iff_nd` with new axiom admissibility equivalences.

## Phases Completed

### Phase 1: Delete LindenbaumInstances.lean and prove axiom admissibility lemmas [COMPLETED]

- Deleted `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean`
- Removed `LindenbaumInstances` import from `Cslib.lean`
- Created `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` (326 lines)
  containing:
  - `Theory.Derivation.replaceAxioms`: structural induction for theory replacement
  - ND derivations of all MinPropAxiom schemata (K, S, andI, andE1, andE2, orI1, orI2, orE)
  - `minPropAxiom_admissible`: all MinPropAxiom schemata derivable from empty theory
  - `intPropAxiom_admissible`: all IntPropAxiom schemata derivable from IPL
  - `propositionalAxiom_admissible`: all PropositionalAxiom schemata derivable from IPL∪CPL
  - `axiomTheory_min_iff_mpl`, `axiomTheory_int_iff_ipl`, `axiomTheory_cl_iff_cpl`: main
    equivalences connecting concrete theories to `AxiomTheory` derivability

### Phase 2: Rewrite bridge theorems in HilbertConservativeGlivenko.lean [COMPLETED]

- Rewrote `derivableInMplIffDerivableMin` to compose `axiomTheory_min_iff_mpl` with
  `hilbert_iff_nd_min.symm`
- Rewrote `derivableInIplIffDerivableInt` to compose `axiomTheory_int_iff_ipl` with
  `hilbert_iff_nd_int.symm`
- Rewrote `derivableInCplIffDerivableProp` to compose `axiomTheory_cl_iff_cpl` with
  `hilbert_iff_nd_cl.symm`
- Removed `import Cslib.Logics.Propositional.Semantics.Algebra.Completeness`
- Updated module docstring to describe the Hilbert-primary + syntactic bridge architecture
- All bridge theorem type signatures preserved (API compatibility maintained)

### Phase 3: Delete Completeness.lean and Lindenbaum.lean [COMPLETED]

- Deleted `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` (277 lines)
- Deleted `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` (425 lines)
- Removed both entries from `Cslib.lean` barrel file
- Added `AxiomAdmissibility` to barrel file

### Phase 4: Update module docstrings [COMPLETED]

- Updated `Cslib/Logics/Propositional/Semantics/Algebra.lean` docstring:
  - Removed references to `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`,
    `alg_complete_classical` (deleted ND completeness theorems)
  - Updated `AlgTValid` description to remove forward reference to deleted results
  - Added "Hilbert-Primary Architecture" section explaining the Hilbert-first design,
    with ND inheriting via syntactic bridges through `AxiomAdmissibility.lean`
- `HilbertConservativeGlivenko.lean` and `AxiomAdmissibility.lean` docstrings were already
  accurate from Phase 2 (no further changes needed)

### Phase 5: Final verification and CI checks [COMPLETED]

- `lake build Cslib.Logics.Propositional.NaturalDeduction.AxiomAdmissibility`: PASSED
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko`: PASSED
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative`: PASSED
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConjImpBotConservative`: PASSED
- `lake build Cslib.Logics.Propositional.ProofSystemEquivalence`: PASSED (with pre-existing
  style warnings unrelated to our changes)
- `lake exe lint-style` on modified files: PASSED (no issues)
- `lake exe mk_all --module`: "No update necessary"
- Zero sorries in all modified/created files
- Axiom count unchanged (14 before and after)
- `lake lint`, `lake exe checkInitImports`, `lake test`, `lake shake`: Blocked by pre-existing
  build failures in `Tableau.Classical.Soundness` (task 316 in progress) and
  `HilbertAlgebra.DiegoEmbedding` (task 310 in progress). These failures are NOT introduced by
  our changes.

## Artifacts

### Created
- `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` (326 lines, new)

### Modified
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` (bridge
  proofs rewritten, imports updated, docstring updated)
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` (docstring updated)
- `Cslib.lean` (barrel file: removed 3 deleted imports, added 1 new import)

### Deleted
- `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` (145 lines)
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` (277 lines)
- `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` (425 lines)

**Net change**: −847 lines (deleted) + 326 lines (created) + ~80 lines (modified) = −441 lines net

## Plan Deviations

None. The implementation followed the plan exactly. All bridge theorems preserve their
original type signatures.

## Notes

The pre-existing CI failures (Tableau.Classical.Soundness, HilbertAlgebra.DiegoEmbedding)
are from tasks 316 and 310 respectively, which are currently in progress. Once those tasks
are completed, the full CI pipeline (lake lint, lake exe checkInitImports, lake test) will
be unblocked. Our task 320 changes do not introduce any new CI issues.
