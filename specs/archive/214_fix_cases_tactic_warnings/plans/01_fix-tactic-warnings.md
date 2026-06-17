# Implementation Plan: Fix Tactic Goal-Count Warnings in Cases.lean

- **Task**: 214 - Fix tactic goal-count warnings in DedekindZ/Cases.lean
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/214_fix_cases_tactic_warnings/reports/01_cases-tactic-warnings.md
- **Artifacts**: plans/01_fix-tactic-warnings.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

All 4 tactic goal-count warnings are concentrated in a single theorem, `case1_psi_bool_only` (lines 196-221 of `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`). The warnings are caused by semicolon-chained `apply` calls that create unfocused goals. The fix replaces these chains with properly nested focus blocks using the standard CSLib `·` notation pattern. No proof logic changes are required -- only tactic tree restructuring.

### Research Integration

The research report identified:
- All 4 warnings occur in the `case1_psi_bool_only` theorem at lines 209-215
- Root cause: semicolon-chained `apply h_or` and `apply h_and` calls creating unfocused sibling goals
- Warning 1 (line 209, col 14): second `apply h_or` in `apply h_or; apply h_or`
- Warning 2 (line 210, col 17): second `apply h_and` in triple chain
- Warning 3 (line 210, col 30): third `apply h_and` in triple chain
- Warning 4 (line 215, col 17): second `apply h_and` in double chain
- Fix pattern: replace `;`-chains with nested `·` focus blocks (standard CSLib convention)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items are directly advanced by this warning-fix task.

## Goals & Non-Goals

**Goals**:
- Eliminate all 4 tactic goal-count warnings in `case1_psi_bool_only`
- Use properly nested `·` focus blocks consistent with CSLib conventions
- Preserve identical proof semantics (same `apply` and `exact` calls, same order)

**Non-Goals**:
- Refactoring other theorems in the file
- Changing proof strategy or tactics used
- Addressing any other warnings or lint issues outside this theorem

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Indentation error breaks proof | M | L | Verify with `lake build` after edit; use `lean_goal` to check proof state |
| Wrong nesting depth for focus blocks | M | L | Research report provides exact proposed restructuring; verify each subgoal closes correctly |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Restructure Tactic Focus Blocks [NOT STARTED]

**Goal**: Replace semicolon-chained `apply` calls with nested `·` focus blocks to eliminate all 4 goal-count warnings.

**Tasks**:
- [ ] Read lines 208-221 of `Cases.lean` to confirm current proof structure matches research report
- [ ] Replace line 209 (`apply h_or; apply h_or`) with two-level focus: `apply h_or` at top level, then `· apply h_or` for the first disjunct
- [ ] Replace line 210 (`· apply h_and; apply h_and; apply h_and`) with three nested focus levels: each `apply h_and` gets its own `·` block
- [ ] Replace line 215 (`· apply h_and; apply h_and`) with two nested focus levels
- [ ] Adjust the third top-level `·` block (the `hev_uf` case, lines 219-221) to be the second branch of the outer `apply h_or`
- [ ] Ensure all `exact` statements are correctly nested under their respective `apply` focus blocks
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases` to verify zero errors and zero warnings

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` - Restructure lines 208-221 of `case1_psi_bool_only` proof

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases` produces zero warnings and zero errors
- The proof still type-checks (no `sorry`, no new goals)
- The `exact` terms are unchanged from the original proof

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases` completes with zero warnings
- [ ] No new errors introduced in the file
- [ ] Proof semantics preserved (same `apply`/`exact` calls in same logical order)

## Artifacts & Outputs

- `specs/214_fix_cases_tactic_warnings/plans/01_fix-tactic-warnings.md` (this plan)
- `specs/214_fix_cases_tactic_warnings/summaries/01_fix-tactic-warnings-summary.md` (after implementation)

## Rollback/Contingency

Revert the edit with `git checkout -- Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`. The change is a single-file, single-theorem modification with no dependencies.
