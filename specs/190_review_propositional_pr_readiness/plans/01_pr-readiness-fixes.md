# Implementation Plan: Task #190

- **Task**: 190 - Review propositional PR readiness
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/190_review_propositional_pr_readiness/reports/01_team-research.md
- **Artifacts**: plans/01_pr-readiness-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Address two concrete PR-readiness issues found during team research on the propositional logic module. Issue 1: convert the global unscoped `HasHilbertTree` instance in `DeductionTheorem.lean` to a `local instance` to prevent scope leakage. Issue 2: add `@[simp]` tags to 6 key soundness/completeness biconditional theorems across 4 files. After applying fixes, run the full CSLib CI pipeline to confirm the build remains green. Done when all changes compile clean and CI checks pass.

### Research Integration

Team research (4 teammates) confirmed:
- The propositional code is PR-ready with zero sorries and documentation exceeding repo average
- Noncomputable usage is fully justified, consistent with Modal/Temporal/Bimodal patterns
- Two actionable issues: global `HasHilbertTree` instance (medium) and missing `@[simp]` tags (low)
- Duplicated code patterns (Issue 3) and existing TODO in `NaturalDeduction/Basic.lean` (Issue 4) are informational only

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task aligns with the propositional logic module readiness for upstream PR. The roadmap lists propositional components as part of the porting effort from BimodalLogic to CSLib, with Propositional as the shared sub-logic layer imported by Modal, Temporal, and Bimodal.

## Goals & Non-Goals

**Goals**:
- Convert global `HasHilbertTree` instance to `local instance` in `DeductionTheorem.lean`
- Add `@[simp]` to 6 biconditional theorems across 4 files
- Verify all changes compile and pass CI pipeline

**Non-Goals**:
- Refactoring duplicated `letI` blocks (Issue 3 -- optional cleanup, not blocking)
- Fixing the `subs` TODO in `NaturalDeduction/Basic.lean` (pre-existing, unrelated to completeness)
- Universe polymorphism notation consistency (Issue 5 -- cosmetic only)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Adding `local` to instance breaks downstream callers | Medium | Low | Callers already use `letI` internally; the global instance is unused |
| `@[simp]` tags cause unexpected simp loops | Medium | Low | These are terminal biconditionals (iff between derivability and semantics), unlikely to loop |
| Build failure from unrelated upstream changes | Low | Low | Run `lake build` first to confirm baseline is green |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Fix Global HasHilbertTree Instance [COMPLETED]

**Goal**: Convert the global unscoped `HasHilbertTree` instance to a local instance to prevent scope leakage.

**Tasks**:
- [ ] In `DeductionTheorem.lean:56`, change `noncomputable instance` to `noncomputable local instance`
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.DeductionTheorem` to verify compilation

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - Add `local` qualifier to line 56 instance declaration

**Verification**:
- Module builds without errors
- Downstream modules (`StrongCompleteness`, `IntStrongCompleteness`, `MinStrongCompleteness`) still build (they use `letI` internally)

---

### Phase 2: Add @[simp] Tags to Biconditional Theorems [COMPLETED]

**Goal**: Add `@[simp]` attribute to 6 key soundness/completeness biconditional theorems to enable downstream `simp` usage.

**Tasks**:
- [ ] Add `@[simp]` to `prop_completeness_iff_tautology` in `StrongCompleteness.lean:547`
- [ ] Add `@[simp]` to `prop_strong_completeness_iff` in `StrongCompleteness.lean:508`
- [ ] Add `@[simp]` to `int_soundness_completeness` in `IntStrongCompleteness.lean:337`
- [ ] Add `@[simp]` to `int_strong_completeness_iff` in `IntStrongCompleteness.lean:296`
- [ ] Add `@[simp]` to `min_soundness_completeness` in `MinStrongCompleteness.lean:332`
- [ ] Add `@[simp]` to `min_strong_completeness_iff` in `MinStrongCompleteness.lean:282`
- [ ] Run scoped builds for each modified module

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - Add `@[simp]` to `prop_strong_completeness_iff` and `prop_completeness_iff_tautology`
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` - Add `@[simp]` to `int_strong_completeness_iff` and `int_soundness_completeness`
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` - Add `@[simp]` to `min_strong_completeness_iff` and `min_soundness_completeness`

**Verification**:
- All three modules build without errors or simp warnings

---

### Phase 3: Full CI Verification [COMPLETED]

**Goal**: Run the complete CSLib CI pipeline to confirm all changes are green.

**Tasks**:
- [ ] `lake build` -- full project build
- [ ] `lake test` -- run CslibTests suite
- [ ] `lake exe checkInitImports` -- verify Cslib.Init imports
- [ ] `lake exe lint-style` -- style linting
- [ ] `lake shake --add-public --keep-implied --keep-prefix` -- dependency analysis

**Timing**: 45 minutes (build time dominates)

**Depends on**: 1, 2

**Files to modify**: None (verification only)

**Verification**:
- All 5 CI commands exit with code 0
- No new warnings introduced

## Testing & Validation

- [ ] `lake build` succeeds with zero errors
- [ ] `lake test` passes all CslibTests
- [ ] `lake exe checkInitImports` confirms all files import Cslib.Init
- [ ] `lake exe lint-style` reports no style violations
- [ ] `lake shake` reports no unnecessary imports
- [ ] Downstream consumers of `DeductionTheorem.lean` still compile (verified by full `lake build`)

## Artifacts & Outputs

- `specs/190_review_propositional_pr_readiness/plans/01_pr-readiness-fixes.md` (this plan)
- Modified: `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- Modified: `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`
- Modified: `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean`
- Modified: `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean`

## Rollback/Contingency

All changes are mechanical single-line edits. If any phase fails:
- Phase 1: Revert `local` qualifier; investigate which caller depends on global instance scope
- Phase 2: Remove `@[simp]` from the offending theorem; investigate simp loop via `set_option trace.Meta.Tactic.simp true`
- Phase 3: If CI fails on unrelated code, isolate the failure and proceed with PR for propositional changes only
