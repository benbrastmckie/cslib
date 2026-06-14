# Implementation Plan: Task #197

- **Task**: 197 - Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 198 (PR 198 / Connectives.lean) must be submitted or its branch available
- **Research Inputs**: specs/197_modal_upstream_initial_pr/reports/01_modal-upstream-pr-scope.md
- **Artifacts**: plans/01_modal-upstream-pr-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Prepare and submit a ~290 LOC upstream PR covering `Modal/Basic.lean` and `Modal/Denotation.lean`, which refactors the formula type from `{atom, not, and, diamond}` to `{atom, bot, imp, box}` primitives with derived connectives and updated denotational semantics. The PR is stacked on PR 198 (Connectives.lean) and must coordinate with the conflicting PR #607. Implementation involves creating a feature branch from upstream/main, applying the two files with adjusted imports, verifying CI passes, drafting the PR description, and initiating Zulip coordination.

### Research Integration

Key findings from the research report:
- Recommended scope is `Basic.lean` + `Denotation.lean` (~291 insertions, ~110 deletions)
- Hard dependency on PR 198 for `ModalConnectives` instance (3 lines)
- Import path `Cslib.Foundations.Data.Relation` must revert to `Cslib.Foundations.Relation.Euclidean`
- PR #607 conflict is HIGH RISK -- must discuss on Zulip before or concurrent with submission
- `LogicalEquivalence.lean` and `FromPropositional.lean` deferred to PRs 3 and 4

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "Modal proof system" and upstream contribution effort. The roadmap shows Modal/ as an independent peer module importing from Foundations and Propositional. This PR establishes the refactored Modal formula type that all subsequent Modal PRs (proof systems, metalogic) build upon.

## Goals & Non-Goals

**Goals**:
- Create a clean PR branch with `Basic.lean` + `Denotation.lean` compiling against upstream
- Adjust imports to use upstream's module paths (not local refactored paths)
- Pass all CI checks (lake build, checkInitImports, lint-style)
- Draft PR description with coordination notes for PR #607
- Create pr-description.md artifact in task directory

**Non-Goals**:
- Including `LogicalEquivalence.lean` (PR 3)
- Including `FromPropositional.lean` (PR 4)
- Resolving the PR #607 conflict (requires Zulip discussion)
- Modifying upstream's `Cube.lean` (no changes needed)
- Changing proof style to match upstream's `grind` usage (offer in PR description)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #607 merges first with incompatible primitives | H | M | Open Zulip discussion early; submit PR even if stacked (shows complete alternative) |
| Upstream Relation module path mismatch | M | H | Revert to `Cslib.Foundations.Relation.Euclidean`; verify `RightEuclidean`/`Serial` resolve |
| PR 198 not yet merged when submitting | M | H | Stack on PR 198 branch `feat/propositional-five-primitive`; note dependency in PR description |
| `DecidableEq`/`BEq` deriving fails on upstream Lean version | L | L | Remove deriving clause if needed; it is not critical for this PR's scope |
| `LogicalEquivalence.lean` import breaks with new `Basic.lean` | L | H | Document expected breakage in PR description; defer fix to PR 3 |

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

### Phase 1: Create PR Branch and Prepare Files [NOT STARTED]

**Goal**: Create a feature branch from upstream/main (or stacked on PR 198), copy the two target files with corrected imports, and verify basic structure.

**Tasks**:
- [ ] Fetch upstream/main and PR 198 branch state
- [ ] Create branch `feat/modal-formula-refactoring` from appropriate base (PR 198 branch if available, else upstream/main with Connectives.lean applied)
- [ ] Copy local `Cslib/Logics/Modal/Basic.lean` to the PR branch
- [ ] Replace import `Cslib.Foundations.Data.Relation` with `Cslib.Foundations.Relation.Euclidean` in `Basic.lean`
- [ ] Verify `Cslib.Foundations.Logic.Connectives` import resolves (from PR 198)
- [ ] Copy local `Cslib/Logics/Modal/Denotation.lean` to the PR branch
- [ ] Verify no other import path adjustments needed in `Denotation.lean`
- [ ] Ensure `Cube.lean` remains unmodified on the branch

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- import path adjustment
- `Cslib/Logics/Modal/Denotation.lean` -- copied as-is (imports only `Modal.Basic`)

**Verification**:
- Branch exists with correct base
- Both files have upstream-compatible import paths
- No references to `Cslib.Foundations.Data.Relation` remain

---

### Phase 2: CI Verification [NOT STARTED]

**Goal**: Run the full CI pipeline to confirm the PR compiles and passes all checks.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Modal.Basic` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.Denotation` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.Cube` -- must still compile unchanged
- [ ] Run `lake exe checkInitImports` -- verify root import file is correct
- [ ] Run `lake exe lint-style` -- pass style linting
- [ ] Verify `Relation.RightEuclidean`, `Relation.Serial`, `Std.Refl`, `Std.Symm`, `IsTrans` resolve from upstream imports
- [ ] Verify `ModalConnectives` instance compiles with PR 198 definitions
- [ ] Note expected failure: `lake build Cslib.Logics.Modal.LogicalEquivalence` (document in PR)
- [ ] If any failures, fix import paths or adjust code minimally

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- potential fixes from CI feedback
- `Cslib.lean` -- may need import line addition if checkInitImports requires it

**Verification**:
- `lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Denotation` exits 0
- `lake exe checkInitImports` exits 0
- `lake exe lint-style` exits 0
- `Cube.lean` still compiles

---

### Phase 3: PR Description and Submission Preparation [NOT STARTED]

**Goal**: Write the final PR description (pr-description.md), finalize commit messages, and prepare the PR for submission via `gh`.

**Tasks**:
- [ ] Write `specs/197_modal_upstream_initial_pr/pr-description.md` based on research report Section 5 draft
- [ ] Fill in actual PR 198 number (replace `#NNN` placeholders)
- [ ] Include breaking changes section with exact renames
- [ ] Include coordination notes for PR #607
- [ ] Include "AI Tools Used" disclosure
- [ ] Include "Contribution Roadmap" section showing planned follow-up PRs
- [ ] Create clean commit on the feature branch with appropriate message
- [ ] Push branch to origin

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- create/update final PR description

**Verification**:
- pr-description.md contains all required sections (Summary, Design Rationale, Breaking Changes, Relationship to Other PRs, Changed Files, AI Tools Used)
- No `#NNN` placeholder remains unresolved
- Branch is pushed and ready for `gh pr create`

---

### Phase 4: Submit PR and Initiate Zulip Coordination [NOT STARTED]

**Goal**: Submit the PR via GitHub CLI and post coordination message on Zulip regarding PR #607 conflict.

**Tasks**:
- [ ] Submit PR via `gh pr create` with title and body from pr-description.md
- [ ] Set PR base branch appropriately (PR 198 branch if stacking, else main)
- [ ] Add labels if available (e.g., `Modal`, `breaking-change`)
- [ ] Draft Zulip message for CSLib channel regarding primitive set coordination with PR #607
- [ ] Note the Zulip discussion link in the PR description (edit after posting)
- [ ] Record the PR URL in task artifacts

**Timing**: 15 minutes

**Depends on**: 3

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- add Zulip link after posting

**Verification**:
- PR is created and visible on GitHub
- PR description renders correctly
- Zulip thread exists or is drafted for posting

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Basic` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.Denotation` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.Cube` succeeds (unchanged file still compiles)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `ModalConnectives` instance resolves correctly
- [ ] No references to local-only import paths remain
- [ ] PR description is complete and accurate

## Artifacts & Outputs

- `specs/197_modal_upstream_initial_pr/plans/01_modal-upstream-pr-plan.md` (this plan)
- `specs/197_modal_upstream_initial_pr/pr-description.md` (PR description for submission)
- Feature branch `feat/modal-formula-refactoring` with clean commits
- GitHub PR URL (recorded in task artifacts after submission)

## Rollback/Contingency

If the PR branch fails CI:
1. Check if the failure is in `Basic.lean` imports -- revert to upstream import paths
2. Check if `ModalConnectives` instance fails -- option to defer instance (submit without it, add in follow-up)
3. If `DecidableEq` deriving fails on upstream's Lean version -- remove deriving clause
4. If PR #607 merges first and blocks this PR -- rebase onto PR #607's merged state and adapt

If Zulip discussion determines PR #607's approach should take priority:
1. Close this PR
2. Propose contributing our refactoring as a follow-up to PR #607 instead
3. Adapt primitives to align with PR #607's operator typeclass structure
