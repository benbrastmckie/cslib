# Implementation Plan: Task #529

- **Task**: 529 - Add `@[nolint unusedArguments]` to KB5 Univ rules
- **Status**: [COMPLETED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/529_fix_lint_unused_args_kb5_univ_rules/reports/01_nolint-kb5-univ-rules.md
- **Artifacts**: plans/01_nolint-kb5-univ-rules.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two definitions in `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — `modalKb5BoxAllUniv`
(line 2179) and `modalKb5DiaNegAllUniv` (line 2196) — each take a fifth binder `_w : WorldIndex`
that is intentionally unused (the corrected-gate KB5 rule fires on cluster-nonemptiness and drops
the `w == 0` conjunct the frozen `*Full` helpers relied on). CSLib's `unusedArguments` environment
linter does not honor the underscore-prefix suppression convention, so `lake lint` reports exactly
two errors. The fix is a mechanical, single-line `@[nolint unusedArguments]` attribute insertion
above each `def`, matching two established in-repo precedents.

### Research Integration

The research report fully specifies the fix: exact declaration names, exact target lines (verified
against the current file at 2179 and 2196), and the precedent placement convention (attribute on
its own line, directly above `def`, after the closing docstring `-/`, no blank line between). Both
`def` lines are uniquely named, so exact-string edits are unambiguous. Precedents:
`CountermodelExtraction.lean:204` and `DenseMCS.lean:202`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Insert `@[nolint unusedArguments]` above `def modalKb5BoxAllUniv` (line 2179).
- Insert `@[nolint unusedArguments]` above `def modalKb5DiaNegAllUniv` (line 2196, +1 after first edit).
- `lake lint` passes clean (the two `unusedArguments` errors disappear; no new lint error).
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` still compiles.

**Non-Goals**:
- Removing or renaming the `_w : WorldIndex` binder (it is part of the uniform dispatcher signature and must be retained).
- Any change to the frozen `modalKb5BoxAllFull` (line 1539) / `modalKb5DiaNegAllFull` (line 1556) helpers or any other declaration.
- Any semantic change to the two target definitions' bodies.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Edit lands on the wrong (frozen `*Full`) declaration | H | L | Target the uniquely-named `Univ` `def` strings; `*Full` names differ and are excluded by scope |
| Second edit's line number shift causes a mismatch | L | L | Use exact-string Edit (not line numbers); the `DiaNegAllUniv` string is unaffected by the first insertion |
| Attribute introduces a new lint/build error | M | L | Verification gate runs both `lake lint` and the targeted `lake build` before completion |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Insert nolint attributes and verify [COMPLETED]

**Goal**: Add the two `@[nolint unusedArguments]` attributes and confirm lint passes and the module still builds.

**Tasks**:
- [x] Insert `@[nolint unusedArguments]` on its own line immediately above `def modalKb5BoxAllUniv (b : List ...` (line 2179), after the closing docstring `-/`, with no blank line between attribute and `def`.
- [x] Insert `@[nolint unusedArguments]` on its own line immediately above `def modalKb5DiaNegAllUniv (b : List ...` (line 2196), same placement convention.
- [x] Confirm the frozen `modalKb5BoxAllFull` / `modalKb5DiaNegAllFull` helpers are untouched.
- [x] Run `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` and confirm it compiles.
- [x] Run `lake lint` and confirm it passes clean (the two `unusedArguments` errors gone, no new errors).

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` - two single-line attribute insertions above the `Univ` KB5 rule defs

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` exits successfully.
- `lake lint` reports no `unusedArguments` error on `modalKb5BoxAllUniv` or `modalKb5DiaNegAllUniv`, and no new lint error is introduced.
- `git diff` shows exactly two added lines, both `@[nolint unusedArguments]`, with no change to `*Full` helpers.

---

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` compiles clean.
- [x] `lake lint` passes with no errors attributable to these declarations.
- [x] `git diff` confirms exactly two inserted attribute lines and no other changes.

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (two attribute lines added).
- Execution summary at `summaries/01_nolint-kb5-univ-rules-summary.md` (produced at implementation).

## Rollback/Contingency

The change is two additive lines. If `lake lint` or the targeted build fails after the edits,
revert the two insertions with `git checkout -- Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
(clean-tree exemption applies once the only local change is these two lines) and re-examine the
attribute name/placement against the `CountermodelExtraction.lean:204` precedent.
