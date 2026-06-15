# Implementation Plan: Task #203

- **Task**: 203 - Create first ~300 LOC PR for Temporal/ extending classical propositional logic
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: PR #648 (Connectives.lean) must be merged or branch based on feat/propositional-v2
- **Research Inputs**: specs/203_first_temporal_pr_classical_propositional/reports/01_temporal-pr-foundations.md
- **Artifacts**: plans/01_temporal-pr-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Extract lines 1-310 of the local `Cslib/Logics/Temporal/Syntax/Formula.lean` into a standalone PR-ready file for upstream submission to `leanprover/cslib`. The PR introduces the temporal formula inductive type with five primitives (`atom`, `bot`, `imp`, `untl`, `snce`), derived propositional connectives, a `TemporalConnectives` instance connecting to PR #648's typeclass hierarchy, and structural instances (`Countable`, `Infinite`, `Denumerable`, `ReflBEq`, `LawfulBEq`). The file must be adapted for upstream compatibility, pass all CSLib CI checks, and be submitted on a branch based off PR #648.

### Research Integration

Key findings from the research report:

- **Scope boundary**: Line 310 (`end BEqLaws`) is a clean section boundary separating propositional structure from temporal-specific content (complexity, swapTemporal, atoms collection).
- **Import minimization**: The `Finset` import can be removed since the `atoms` function is excluded from this PR subset.
- **PR #648 dependency**: `TemporalConnectives` from `Connectives.lean` is required. The PR must be based on PR #648's branch or wait for merge.
- **`module` keyword**: Lean v4.31.0-rc2 toolchain supports `module`. However, upstream `leanprover/cslib` toolchain must be verified.
- **Contribution roadmap**: This is PR 1 of ~9 planned temporal PRs.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- Temporal Syntax module development (T1: "Syntax")
- First upstream PR establishing the Temporal/ directory in leanprover/cslib

## Goals & Non-Goals

**Goals**:
- Extract exactly lines 1-310 of local `Formula.lean` into a PR-ready file
- Remove the `Finset` import (not needed for this subset)
- Verify the file builds cleanly in isolation (`lake build Cslib.Logics.Temporal.Syntax.Formula`)
- Pass all CSLib CI checks: `lake test`, `checkInitImports`, `lint-style`, `lake shake`
- Update `Cslib.lean` barrel import via `lake exe mk_all --module`
- Create PR branch based on PR #648's branch (`feat/propositional-v2` or equivalent)
- Prepare PR description following CSLib conventions

**Non-Goals**:
- Including temporal-specific content beyond line 310 (complexity, swapTemporal, derived temporal operators beyond someFuture/allFuture/somePast/allPast)
- Modifying Connectives.lean or any files from PR #648
- Submitting the PR to GitHub (that is done via `/pr` command separately)
- Creating the full Temporal contribution roadmap PR series

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #648 not yet merged; branch may diverge | H | M | Base PR branch on feat/propositional-v2; rebase if needed |
| Upstream toolchain does not support `module` keyword | H | L | Check upstream lean-toolchain; replace `module` with `namespace` + explicit imports if needed |
| `lake shake` flags unnecessary Mathlib imports | M | M | Run shake early (Phase 3); remove flagged imports |
| `@[expose] public section` attribute not recognized upstream | M | L | Verified via `Cslib.Init` import; should work since upstream also uses it |
| Burgess convention naming draws reviewer pushback | L | M | Module docstring already explains the convention thoroughly |
| `Encodable`/`Denumerable` instances may conflict with future Mathlib additions | L | L | These are specific to `Formula Atom`, unlikely to conflict |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Extract and Adapt PR File [COMPLETED]

**Goal**: Create the upstream-ready `Formula.lean` by extracting lines 1-310 and adapting imports.

**Tasks**:
- [ ] Create a working copy of lines 1-310 from `Cslib/Logics/Temporal/Syntax/Formula.lean`
- [ ] Remove the `Mathlib.Data.Finset.Basic` import (not needed for this subset)
- [ ] Verify all four required imports remain: `Cslib.Init`, `Cslib.Foundations.Logic.Connectives`, `Mathlib.Logic.Encodable.Basic`, `Mathlib.Logic.Denumerable`
- [ ] Ensure the file ends cleanly after `end BEqLaws` with the closing `end Cslib.Logic.Temporal`
- [ ] Verify the second `@[expose] public section` block (line 121) is properly closed
- [ ] Check that all docstrings, module-level documentation, and copyright header are present
- [ ] Save the adapted file (either as a separate branch file or in-place with careful git management)

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Extract and adapt lines 1-310 for PR submission

**Verification**:
- File contains exactly the content through `end BEqLaws` with proper closing
- No `Finset` import present
- All other imports intact
- Copyright header and module docstring present

---

### Phase 2: Build Verification and Import Cleanup [COMPLETED]

**Goal**: Verify the extracted file compiles and fix any build issues.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` to verify compilation
- [ ] If build fails, diagnose and fix issues (missing imports, namespace closures, etc.)
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import if the Temporal module line is missing
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to check for unnecessary imports
- [ ] Remove any imports flagged by `lake shake`
- [ ] Re-run `lake build Cslib.Logics.Temporal.Syntax.Formula` after any changes

**Timing**: 0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Fix any build issues or import changes
- `Cslib.lean` - May need update via `mk_all` to include new Temporal module

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` succeeds with no errors
- `lake shake` reports no unnecessary imports
- `Cslib.lean` includes `Cslib.Logics.Temporal.Syntax.Formula`

---

### Phase 3: Full CI Verification [COMPLETED]

**Goal**: Pass the complete CSLib CI pipeline to ensure PR readiness.

**Tasks**:
- [ ] Run `lake test` to verify CslibTests suite passes
- [ ] Run `lake exe checkInitImports` to verify `Cslib.Init` import compliance
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Fix any lint-style issues (line length, whitespace, etc.)
- [ ] Run full `lake build` to ensure no regressions in other modules
- [ ] Verify no downstream modules are broken by the import changes

**Timing**: 0.75 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Fix any lint issues

**Verification**:
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes (or `--fix` applied)
- Full `lake build` succeeds

---

### Phase 4: PR Branch and Description Preparation [COMPLETED]

**Goal**: Prepare the git branch and PR description for upstream submission.

**Tasks**:
- [ ] Create PR branch based on PR #648's branch (or main if #648 is merged)
- [ ] Stage only the PR-relevant files: `Cslib/Logics/Temporal/Syntax/Formula.lean` and `Cslib.lean` update
- [ ] Create `specs/203_first_temporal_pr_classical_propositional/pr-description.md` with:
  - Title: `feat(Logics/Temporal): temporal formula type with propositional structure`
  - Description covering: five-primitive type, derived connectives, `TemporalConnectives` instance, countability/BEq instances
  - Dependency note on PR #648
  - AI disclosure per CSLib policy
  - Contribution roadmap summary (this is PR 1 of ~9)
- [ ] Verify line count of the new file is approximately 310 lines

**Timing**: 0.75 hours

**Depends on**: 3

**Files to modify**:
- `specs/203_first_temporal_pr_classical_propositional/pr-description.md` - Create PR description

**Verification**:
- PR branch exists and is based on correct parent
- PR description follows CSLib conventions (`feat(Logics/Temporal):` prefix)
- AI disclosure included
- File line count is within target range (~310 LOC)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Syntax.Formula` compiles without errors
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes (Cslib.Init import verification)
- [ ] `lake exe lint-style` passes (style linting)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no issues
- [ ] Full `lake build` succeeds with no regressions
- [ ] File contains approximately 310 lines (within 10% of target)
- [ ] No `sorry` or vacuous definitions present

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Adapted PR-ready file (~310 LOC)
- `Cslib.lean` - Updated barrel import (if needed)
- `specs/203_first_temporal_pr_classical_propositional/pr-description.md` - PR description
- `specs/203_first_temporal_pr_classical_propositional/plans/01_temporal-pr-plan.md` - This plan

## Rollback/Contingency

The local `Formula.lean` already contains the full 582-line version. If the PR extraction causes issues:
1. Restore from git: `git checkout -- Cslib/Logics/Temporal/Syntax/Formula.lean`
2. If branch management fails, the work is limited to a single file extraction with no destructive changes to existing code
3. If upstream toolchain incompatibility is found (e.g., `module` keyword), replace with `namespace` pattern used in other CSLib files
