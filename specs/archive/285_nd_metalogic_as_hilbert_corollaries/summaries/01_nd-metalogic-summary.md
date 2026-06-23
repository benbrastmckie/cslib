# Execution Summary: Refactor ND Metalogic API to Hilbert Corollaries

**Task**: 285
**Session**: sess_1782187168_2b1b69_285
**Date**: 2026-06-22

## Changes Made

### Phase 1: Remove ND-Primary Proofs and Rename Corollaries

**Conservative.lean** (`Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`):
- Removed `ipl_conservative_over_mpl` theorem (ND-primary proof)
- Removed unused imports: `Completeness`, `NaturalDeduction.Basic`
- Simplified `open` statement (removed `Theory`, `InferenceSystem`, `DerivableIn`)
- Updated module docstring to reference `HilbertConservativeGlivenko.lean` as the location of both the Hilbert-primary and ND corollary versions

**Glivenko.lean** (`Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`):
- Removed `glivenko` theorem (ND-primary proof)
- Removed unused imports: `Completeness`, `NaturalDeduction.Basic`
- Replaced import with `Cslib.Logics.Propositional.Semantics.Algebra` (transitive access to Defs)
- Simplified `open` statement (removed `InferenceSystem`, `DerivableIn`)
- Updated module docstring: renamed from "Glivenko's Theorem" to "Algebraic Glivenko Lemma", references `HilbertConservativeGlivenko.lean` for proof-theoretic results

**HilbertConservativeGlivenko.lean** (`Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`):
- Renamed `iplConservativeOverMpl'` to `ipl_conservative_over_mpl` (canonical ND name)
- Renamed `glivenko'` to `glivenko` (canonical ND name)
- Updated docstrings on renamed theorems to reflect canonical status
- Updated Hilbert-primary theorem docstrings to remove stale references
- Updated module docstring to document Hilbert-primary architecture and canonical ND names

### Phase 2: Documentation Updates

**ProofSystem.lean** (`Cslib/Foundations/Logic/ProofSystem.lean`):
- Replaced "Concrete instances require derivation trees (not yet ported) and are future work" with a "Metalogic" section documenting the Hilbert-primary completeness, conservative extension, and Glivenko theorems

**Algebra.lean** (`Cslib/Logics/Propositional/Semantics/Algebra.lean`):
- Added documentation about Hilbert-primary completeness theorems alongside existing ND completeness documentation
- Noted that Hilbert versions do not require `[DecidableEq Atom]`

### Phase 3: CI Verification

All passed:
- `lake build` -- 3038 jobs, zero errors
- `lake test` -- all tests pass
- `lake exe checkInitImports` -- no issues
- `lake exe lint-style` -- no style violations

## Architecture After Refactoring

| Module | Role |
|---|---|
| `Completeness.lean` | ND soundness + completeness (unchanged, needed by bridges) |
| `Conservative.lean` | Algebraic infrastructure only: IsBotFree, WithBot, coe_AlgEvaluate |
| `Glivenko.lean` | Algebraic Glivenko lemma + theory instances only |
| `HilbertConservativeGlivenko.lean` | **Canonical source**: Hilbert-primary theorems + bridges + ND corollaries |
| `HilbertCompleteness.lean` | Hilbert completeness (unchanged) |
| `HilbertLindenbaum.lean` | Hilbert Lindenbaum algebra (unchanged) |
