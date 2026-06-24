# Implementation Plan: Fix CI Lint Warnings in CutElimination.lean

- **Task**: 327 - Fix CI lint warnings in CutElimination.lean
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/327_cutelim_lint_ci_fixes/reports/01_lint-ci-fixes.md
- **Artifacts**: plans/01_lint-ci-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Apply 10 mechanical lint fixes to `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` to eliminate all CI warnings. The fixes fall into three categories: adding a required comment to the `maxHeartbeats` override (1 fix), breaking long lines exceeding the 100-character limit (8 fixes), and renaming an unused variable to underscore (1 fix). No proof logic, type signatures, or imports change.

### Research Integration

The research report at `specs/327_cutelim_lint_ci_fixes/reports/01_lint-ci-fixes.md` identified all 10 warnings with exact line numbers, current content, and proposed fixes. A reference pattern for the maxHeartbeats comment was found in `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean:98-99`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Eliminate all 10 CI lint warnings from CutElimination.lean
- Pass `lake build` with zero warnings for the target module
- Pass full CI pipeline (`lake test`, `lake exe checkInitImports`, `lake exe lint-style`)

**Non-Goals**:
- Refactoring proof structure or logic (covered by task 328)
- Reducing maxHeartbeats override (covered by task 328)
- Addressing warnings in other files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line breaks cause Lean parse errors in mutual block | M | L | All breaks are at standard continuation points (after `:= by`, before function arguments); `lake build` verifies |
| Renaming `hB` to `_` breaks termination checker | H | L | Variable is used implicitly for `termination_by sizeOf C`; underscore preserves the binding; `lake build` verifies |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Apply All Lint Fixes [COMPLETED]

**Goal**: Fix all 10 CI lint warnings in CutElimination.lean

**Tasks**:
- [ ] Add explanatory comment after `set_option maxHeartbeats 800000 in` on line 112
- [ ] Break line 147 (`have hA` with `Proposition.and`) after `:= by`
- [ ] Break line 148 (`have hB` with `Proposition.and`) after `:= by`
- [ ] Break line 250 (`d₁a.mono`) before second parenthesized argument
- [ ] Break line 251 (`d₁b.mono`) before second parenthesized argument
- [ ] Break line 501 (`have hA` with `Proposition.imp`) after `:= by`
- [ ] Break line 502 (`have hB` with `Proposition.imp`) after `:= by`
- [ ] Break line 527 (`d₁'.mono` with `Finset.Subset.refl`) before second argument
- [ ] Break line 535 (`d₁'.mono` with `Finset.insert_subset_insert`) before second argument
- [ ] Rename unused variable `hB` to `_` on line 857
- [ ] Run `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` -- verify zero warnings
- [ ] Run `lake exe lint-style` -- verify no new violations
- [ ] Run `lake test` -- verify no regressions

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - All 10 lint fixes (maxHeartbeats comment, 8 line breaks, 1 variable rename)

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` produces zero warnings
- `lake exe lint-style` passes
- `lake test` passes

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` -- zero warnings
- [ ] `lake exe lint-style` -- no style violations in target file
- [ ] `lake test` -- all tests pass (no behavioral changes)
- [ ] `lake exe checkInitImports` -- import structure intact

## Artifacts & Outputs

- `specs/327_cutelim_lint_ci_fixes/plans/01_lint-ci-fixes.md` (this plan)
- `specs/327_cutelim_lint_ci_fixes/summaries/01_lint-ci-fixes-summary.md` (after implementation)

## Rollback/Contingency

All changes are in a single file. If any fix causes a build failure, revert with `git checkout -- Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` and apply fixes individually to isolate the problem.
