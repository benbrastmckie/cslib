# Implementation Plan: Refactor ND Metalogic API to Hilbert Corollaries

- **Task**: 285 - Refactor ND metalogical API so all ND results are Hilbert corollaries
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: Task 284 (completed -- Hilbert-primary theorems and bridges)
- **Research Inputs**: specs/285_nd_metalogic_as_hilbert_corollaries/reports/01_nd-metalogic-corollaries.md
- **Artifacts**: plans/01_nd-metalogic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Remove the ND-primary proofs of `ipl_conservative_over_mpl` (from Conservative.lean) and `glivenko` (from Glivenko.lean), rename the existing corollary versions in HilbertConservativeGlivenko.lean to the canonical names, and update documentation across the affected modules. This is a low-risk, self-contained refactoring: research confirmed zero downstream consumers outside `Semantics/Algebra/`, and the corollary signatures exactly match the originals (both require `[DecidableEq Atom]`).

### Research Integration

Key findings from the research report:
- Zero external breakage risk: no files outside `Semantics/Algebra/` import Conservative.lean or Glivenko.lean by name
- Two ND theorems targeted for removal: `ipl_conservative_over_mpl` in Conservative.lean and `glivenko` in Glivenko.lean
- Algebraic infrastructure in those files (IsBotFree, coe_AlgEvaluate, glivenko_algebraic, theory instances) must be preserved
- Corollary versions `iplConservativeOverMpl'` and `glivenko'` already exist in HilbertConservativeGlivenko.lean with identical signatures
- ND completeness theorems remain untouched (needed by bridge theorems)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly advance a specific ROADMAP.md item. It is an internal code quality refactoring within the propositional algebraic completeness infrastructure that establishes the Hilbert-primary architecture as the canonical source for conservative extension and Glivenko results. This solidifies the foundations layer for all downstream modal, temporal, and bimodal metalogic.

## Goals & Non-Goals

**Goals**:
- Remove ND-primary proofs from Conservative.lean and Glivenko.lean
- Promote corollary versions in HilbertConservativeGlivenko.lean to canonical names
- Update module documentation to reflect Hilbert-primary architecture
- Verify full CI pipeline passes

**Non-Goals**:
- Removing ND algebraic completeness theorems (needed by bridges)
- Changing Hilbert-primary theorem proofs
- Modifying bridge theorem implementations
- Touching any files outside `Semantics/Algebra/` and `ProofSystem.lean`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Name collision after rename | H | L | Research confirmed signatures identical; no external consumers |
| Circular import after moving theorems | H | L | Strategy keeps theorems in HilbertConservativeGlivenko.lean (imports flow one way) |
| Broken downstream build | M | L | Research confirmed zero external imports; verify with `lake build` |
| Documentation inconsistency | L | M | Explicit documentation update tasks in Phase 2 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Remove ND-Primary Proofs and Rename Corollaries [IN PROGRESS]

**Goal**: Remove the two ND-primary theorems and promote corollary versions to canonical names.

**Tasks**:
- [ ] Remove `ipl_conservative_over_mpl` theorem (lines 163-171) from Conservative.lean, keeping all algebraic infrastructure above it
- [ ] Update Conservative.lean module docstring to remove mention of `ipl_conservative_over_mpl` as a main result, noting the theorem now lives in HilbertConservativeGlivenko.lean
- [ ] Remove `glivenko` theorem (lines 125-140) from Glivenko.lean, keeping all algebraic infrastructure and theory instances above it
- [ ] Update Glivenko.lean module docstring to remove mention of `glivenko` as a main result, noting the theorem now lives in HilbertConservativeGlivenko.lean
- [ ] Rename `iplConservativeOverMpl'` to `ipl_conservative_over_mpl` in HilbertConservativeGlivenko.lean
- [ ] Rename `glivenko'` to `glivenko` in HilbertConservativeGlivenko.lean
- [ ] Update docstrings on the renamed theorems to reflect they are now the canonical ND versions
- [ ] Update the module docstring in HilbertConservativeGlivenko.lean to list the ND corollaries under their canonical names
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko` to verify compilation

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` -- remove `ipl_conservative_over_mpl`, update docstring
- `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean` -- remove `glivenko`, update docstring
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` -- rename corollaries, update docstrings

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` compiles
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Glivenko` compiles
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko` compiles

---

### Phase 2: Documentation Updates [NOT STARTED]

**Goal**: Update ProofSystem.lean and Algebra.lean documentation to reflect the Hilbert-primary architecture.

**Tasks**:
- [ ] Update ProofSystem.lean module docstring: remove the line stating "Concrete instances require derivation trees (not yet ported) and are future work" and replace with a note that Hilbert-level completeness, conservative extension, and Glivenko theorems are established in `Semantics/Algebra/`, with ND results derived as corollaries via algebraic bridges
- [ ] Update Algebra.lean parent module documentation to mention both ND and Hilbert completeness tiers, noting the Hilbert-primary versions do not require `[DecidableEq Atom]`

**Timing**: 0.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- update module docstring
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` -- update documentation

**Verification**:
- `lake build Cslib.Foundations.Logic.ProofSystem` compiles
- `lake build Cslib.Logics.Propositional.Semantics.Algebra` compiles

---

### Phase 3: CI Verification [NOT STARTED]

**Goal**: Run the full CI pipeline to confirm no regressions.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake test` (test suite)
- [ ] Run `lake exe checkInitImports` (import verification)
- [ ] Run `lake exe lint-style` (style linting)

**Timing**: 0.75 hours (mostly build time)

**Depends on**: 2

**Files to modify**:
- `Cslib.lean` -- update barrel import if `lake exe mk_all --module` reports changes (unlikely since no files added or removed)

**Verification**:
- All four CI commands pass with zero errors

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` -- truncated module compiles
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.Glivenko` -- truncated module compiles
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko` -- unified module compiles with renamed corollaries
- [ ] `lake build` -- full project zero errors
- [ ] `lake test` -- test suite passes
- [ ] `lake exe checkInitImports` -- all imports verified
- [ ] `lake exe lint-style` -- no style violations

## Artifacts & Outputs

- `specs/285_nd_metalogic_as_hilbert_corollaries/plans/01_nd-metalogic-plan.md` (this plan)
- Modified: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`
- Modified: `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`
- Modified: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`
- Modified: `Cslib/Foundations/Logic/ProofSystem.lean`
- Modified: `Cslib/Logics/Propositional/Semantics/Algebra.lean`

## Rollback/Contingency

All changes are confined to the `Semantics/Algebra/` directory plus two documentation files. If any phase fails:
- `git checkout -- Cslib/Logics/Propositional/Semantics/Algebra/` restores all algebraic files
- `git checkout -- Cslib/Foundations/Logic/ProofSystem.lean` restores ProofSystem documentation
- `git checkout -- Cslib/Logics/Propositional/Semantics/Algebra.lean` restores Algebra documentation
- No data migration or state cleanup is needed since this is a pure refactoring
