# Implementation Plan: Fix 25 simpNF Lint Errors

- **Task**: 212 - Fix 25 simp-related lint errors: 23 where the LHS of a simp lemma already simplifies and 2 where simp can prove the statement
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/212_lint_simp_issues/reports/01_simp-research.md
- **Artifacts**: plans/01_simp-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Remove `@[simp]` attributes from 25 declarations across 6 files in the Bimodal logic subsystem. These declarations trigger simpNF lint errors because derived connectives (defined as `abbrev`) unfold transparently, causing primitive constructor simp lemmas to fire on the LHS before the derived lemma can apply. All downstream usages are via explicit `rw`, `simp only`, or `.mp`/`.mpr` calls, so removing the global simp attribute has no effect on existing proofs.

### Research Integration

Research report (01_simp-research.md) confirmed:
- All 25 errors share a single root cause: `abbrev`-based derived connectives unfold before derived simp lemmas can fire
- 23 are "LHS already simplifies" errors, 2 are "simp can prove this" (redundant in global simp set)
- No downstream code depends on any of the 25 declarations being in the global simp set (verified by grep)
- Alternative approaches (restating LHS, `nolint simpNF`, changing `abbrev` to `def`) were analyzed and correctly rejected

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances repository CI health by eliminating lint errors. No specific ROADMAP.md items are directly targeted; this is maintenance/cleanup work supporting overall code quality.

## Goals & Non-Goals

**Goals**:
- Remove `@[simp]` from all 25 affected declarations
- Pass `lake build` with zero compilation errors
- Pass `lake lint` with zero simpNF errors from these 25 declarations
- Pass `lake test` with no regressions

**Non-Goals**:
- Restructuring derived connective definitions (out of scope, would be a breaking change)
- Fixing any other lint categories beyond simpNF
- Adding replacement `@[simp]` lemmas with normalized LHS (unnecessary per research)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Bare `simp` call somewhere depends on a removed lemma | Build failure | Very Low | Linter confirms LHS already simplifies via other simp lemmas, so bare `simp` already works without these |
| Removing `@[simp]` from one lemma breaks a downstream `simp` chain | Build failure | Very Low | Research verified all downstream usage is explicit (`rw`, `simp only`, `.mp`); run `lake build` to confirm |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Remove @[simp] Attributes from All 6 Files [COMPLETED]

**Goal**: Remove `@[simp]` from all 25 declarations that trigger simpNF lint errors.

**Tasks**:
- [ ] Edit `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` -- remove `@[simp]` from 2 declarations (lines ~58, ~63: `toBimodal_neg`, `toBimodal_diamond`)
- [ ] Edit `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` -- remove `@[simp]` from 1 declaration (line ~98: `toBimodal_neg`)
- [ ] Edit `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` -- remove `@[simp]` from 1 declaration (line ~67: `toBimodal_neg`)
- [ ] Edit `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` -- remove `@[simp]` from 9 declarations (lines ~163, ~167, ~171, ~191, ~195, ~199, ~203, ~207, ~211: `embedFormula_neg`, `embedFormula_and`, `embedFormula_or`, `embedFormula_diamond`, `embedFormula_someFuture`, `embedFormula_somePast`, `embedFormula_allFuture`, `embedFormula_allPast`, `embedFormula_always`)
- [ ] Edit `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` -- remove `@[simp]` from 4 declarations (lines ~68, ~80, ~119, ~131: `int_truth_allPast`, `int_truth_allFuture`, `int_truth_and`, `int_truth_top`)
- [ ] Edit `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` -- remove `@[simp]` from 8 declarations (lines ~90, ~95, ~101, ~107, ~114, ~121, ~128, ~136: `subst_neg`, `subst_and`, `subst_or`, `subst_diamond`, `subst_someFuture`, `subst_somePast`, `subst_allFuture`, `subst_allPast`)

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` -- remove 2 `@[simp]`
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` -- remove 1 `@[simp]`
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` -- remove 1 `@[simp]`
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` -- remove 9 `@[simp]`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` -- remove 4 `@[simp]`
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` -- remove 8 `@[simp]`

**Verification**:
- All 25 `@[simp]` attributes removed (no remaining `@[simp]` on the affected theorem names)

---

### Phase 2: Build and Lint Verification [IN PROGRESS]

**Goal**: Confirm that the attribute removals introduce no regressions and that all 25 simpNF errors are resolved.

**Tasks**:
- [ ] Run `lake build` and verify zero compilation errors
- [ ] Run `lake lint` and verify zero new simpNF errors from the 25 modified declarations
- [ ] Run `lake test` and verify all tests pass

**Timing**: 15 minutes (dominated by build time)

**Depends on**: 1

**Files to modify**: None (verification only)

**Verification**:
- `lake build` exits 0
- `lake lint` shows no simpNF errors for any of the 25 modified declarations
- `lake test` exits 0

## Testing & Validation

- [ ] `lake build` completes without errors
- [ ] `lake lint` shows zero simpNF errors for the 25 modified declarations
- [ ] `lake test` passes with no regressions
- [ ] Grep confirms no remaining `@[simp]` on the 25 affected theorem names

## Artifacts & Outputs

- `specs/212_lint_simp_issues/plans/01_simp-plan.md` (this plan)
- `specs/212_lint_simp_issues/summaries/01_simp-summary.md` (post-implementation)

## Rollback/Contingency

If any build or test failure occurs after attribute removal, restore `@[simp]` to the specific declaration(s) causing the failure using `git checkout -- <file>`. Given the mechanical nature of the change and the research confirmation that no downstream code depends on these attributes, rollback is unlikely to be needed.
