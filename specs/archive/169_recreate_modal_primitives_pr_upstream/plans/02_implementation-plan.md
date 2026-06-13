# Implementation Plan: Task #169

- **Task**: 169 - Recreate the Modal primitives refactor as a clean, small PR
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: PR #635 (open, not merged; branch origin/refactor/proposition-lukasiewicz)
- **Research Inputs**: specs/169_recreate_modal_primitives_pr_upstream/reports/01_clean-modal-pr-research.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Recreate closed PR #637 (Modal primitives refactor) as a clean, small PR. PR #637 was closed by maintainer chenson2018 because task 167's rebase onto fork/main ballooned it to ~100 commits. The actual PR content is 2 commits touching 10 files. Strategy: create branch `refactor/modal-primitives-v2` from PR #635's branch tip (`origin/refactor/proposition-lukasiewicz`), cherry-pick commit `3928feb4` (the Modal layer commit), verify the stacked diff is ~4 files / +343/-219, run full CI, push to fork, and write a PR description. The plan ends at [PR READY] -- the user runs `/merge` to submit.

### Research Integration

Key findings from research report 01_clean-modal-pr-research.md:
- PR #637 real content = 2 commits: 54a0945e (Propositional = PR #635 content) + 3928feb4 (Modal layer)
- Modal/Basic.lean imports Cslib.Foundations.Logic.Connectives (ModalConnectives typeclass) which only exists on PR #635's branch, not upstream/main
- Option A (stacked PR on #635) recommended: cherry-pick 3928feb4 onto PR #635 tip yields ~4 files, +343/-219
- LogicalEquivalence.lean MUST be included (upstream version uses Context constructors removed by the primitive change)
- 3 GrindLint entries needed in CslibTests/GrindLint.lean

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items explicitly tracked for this task. This task advances the Modal PRs topic by recovering the closed PR #637 as a reviewable stacked PR.

## Goals & Non-Goals

**Goals**:
- Create branch `refactor/modal-primitives-v2` from PR #635's branch tip
- Cherry-pick only the Modal commit (3928feb4) to produce a minimal stacked diff
- Verify stacked diff is ~4 files, +343/-219 lines
- Pass full CI pipeline (lake build, lake test, checkInitImports, lint-style)
- Push branch to origin (fork) and write pr-description.md
- Transition task to [PR READY]

**Non-Goals**:
- Submitting the PR (user does `/merge`)
- Modifying PR #635's content
- Rebasing onto fork/main (this was the root cause of #637's closure)
- Implementing Option C (standalone without Connectives dependency)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cherry-pick of 3928feb4 has merge conflicts against PR #635 tip | M | Medium | Conflicts would be minor (copyright header, Design Notes); resolve manually |
| PR #635 branch has diverged since research was conducted | M | Low | Fetch latest origin/refactor/proposition-lukasiewicz before branching |
| lake build fails due to upstream/Mathlib version drift | H | Low | Use PR #635's lake-manifest.json and toolchain as-is; if broken, update lakefile |
| Maintainer rejects stacked PR approach | M | Low | Fallback to Option C (strip ModalConnectives lines, standalone PR) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are fully sequential -- each depends on the prior phase succeeding.

### Phase 1: Create Worktree and Branch [COMPLETED]

**Goal**: Set up a git worktree so the main checkout stays on main, fetch latest remotes, and create the new branch from PR #635's tip.

**Tasks**:
- [ ] Fetch latest from origin and upstream: `git fetch origin && git fetch upstream`
- [ ] Create a dedicated worktree: `git worktree add ../cslib-wt-169 origin/refactor/proposition-lukasiewicz`
- [ ] Inside the worktree, create the new branch: `git checkout -b refactor/modal-primitives-v2`
- [ ] Verify starting point: confirm the worktree HEAD matches origin/refactor/proposition-lukasiewicz tip

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- No source files; git operations only

**Verification**:
- `git log --oneline -5` in worktree shows PR #635 commits at HEAD
- `git branch` shows `refactor/modal-primitives-v2` as current branch

---

### Phase 2: Cherry-pick Modal Commit and Verify Diff [COMPLETED]

**Goal**: Cherry-pick the Modal layer commit (3928feb4) and verify the stacked diff matches the expected ~4 files, +343/-219 scope.

**Tasks**:
- [ ] Cherry-pick commit 3928feb4: `git cherry-pick 3928feb4`
- [ ] If conflicts occur, resolve them (expected: minor conflicts in Modal files at most)
- [ ] Verify stacked diff: `git diff origin/refactor/proposition-lukasiewicz..HEAD --stat`
- [ ] Confirm diff shows approximately 4 files: Modal/Basic.lean, Modal/Denotation.lean, Modal/LogicalEquivalence.lean, CslibTests/GrindLint.lean
- [ ] Confirm line counts are in the ballpark of +343/-219 (some variance acceptable due to sugar changes from task 167)
- [ ] Review the diff content for correctness: `git diff origin/refactor/proposition-lukasiewicz..HEAD`

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - Primitives changed from {atom,not,and,diamond} to {atom,bot,imp,box} with derived connectives
- `Cslib/Logics/Modal/Denotation.lean` - Updated denotation proofs for new primitives
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - Complete rewrite using new Context constructors {hole,impL,impR,box}
- `CslibTests/GrindLint.lean` - 3 new #grind_lint skip entries

**Verification**:
- `git diff origin/refactor/proposition-lukasiewicz..HEAD --stat` shows ~4 files
- Total line change magnitude is approximately +343/-219 (allow for variance)
- `git log --oneline origin/refactor/proposition-lukasiewicz..HEAD` shows exactly 1 commit

---

### Phase 3: Full CI Verification and Push [IN PROGRESS]

**Goal**: Run the complete CI pipeline in the worktree to confirm the branch is green, then push to origin.

**Tasks**:
- [ ] Run `lake build` -- full project build
- [ ] Run `lake test` -- CslibTests suite
- [ ] Run `lake exe checkInitImports` -- verify Cslib.Init imports
- [ ] Run `lake exe lint-style` -- style linting
- [ ] If any CI check fails, fix the issue and amend or add a fixup commit
- [ ] Push branch to fork: `git push -u origin refactor/modal-primitives-v2`

**Timing**: 45 minutes (lake build dominates)

**Depends on**: 2

**Files to modify**:
- Potentially minor fixups if CI reveals issues (e.g., lint-style whitespace)

**Verification**:
- All four CI commands exit 0
- `git push` succeeds
- `git log --oneline origin/refactor/proposition-lukasiewicz..HEAD` shows 1-2 commits (cherry-pick + optional fixup)

---

### Phase 4: Write PR Description and Transition to PR READY [IN PROGRESS]

**Goal**: Write the PR description file, record base_branch in state.json metadata, and transition task status to [PR READY].

**Tasks**:
- [ ] Write `specs/169_recreate_modal_primitives_pr_upstream/pr-description.md` with:
  - Title: "refactor(Modal): Hilbert-style primitives for modal propositions"
  - Reference to closed PR #637 and maintainer feedback about size
  - State it is stacked on PR #635 (base branch: `refactor/proposition-lukasiewicz`)
  - Summarize the refactor: Modal primitives changed from {atom,not,and,diamond} to {atom,bot,imp,box} with derived connectives
  - Include diff stats from Phase 2
  - Note that LogicalEquivalence.lean was rewritten to use new Context constructors
- [ ] Record `base_branch: "refactor/proposition-lukasiewicz"` in the task's state.json entry or pr-description metadata
- [ ] Clean up worktree: `git worktree remove ../cslib-wt-169` (after confirming push succeeded)

**Timing**: 20 minutes

**Depends on**: 3

**Files to modify**:
- `specs/169_recreate_modal_primitives_pr_upstream/pr-description.md` (new file)

**Verification**:
- pr-description.md exists and contains all required elements
- Branch `refactor/modal-primitives-v2` exists on origin
- Worktree cleaned up

## Testing & Validation

- [ ] `git diff origin/refactor/proposition-lukasiewicz..refactor/modal-primitives-v2 --stat` shows ~4 files, ~+343/-219
- [ ] `lake build` exits 0
- [ ] `lake test` exits 0
- [ ] `lake exe checkInitImports` exits 0
- [ ] `lake exe lint-style` exits 0
- [ ] Branch pushed to origin (fork)
- [ ] pr-description.md written with correct stacked-PR metadata

## Artifacts & Outputs

- `specs/169_recreate_modal_primitives_pr_upstream/plans/02_implementation-plan.md` (this file)
- `specs/169_recreate_modal_primitives_pr_upstream/pr-description.md` (Phase 4 output)
- Branch `refactor/modal-primitives-v2` on origin (fork)

## Rollback/Contingency

- Delete remote branch: `git push origin --delete refactor/modal-primitives-v2`
- Remove worktree: `git worktree remove ../cslib-wt-169`
- Task reverts to [PLANNED]; no main branch changes affected
- Fallback to Option C (standalone PR without Connectives dependency) if stacked approach is rejected
