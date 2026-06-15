# Implementation Plan: Push Relevant Changes to PR 648

- **Task**: 216 - push_relevant_changes_to_pr_648
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: Task 202 (review_hilbert_classes_vs_pr648)
- **Research Inputs**: specs/216_push_relevant_changes_to_pr_648/reports/01_pr648-changes-review.md
- **Artifacts**: plans/01_pr648-push-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Push a single commit to the `feat/propositional-v2` PR branch that adds `Bool.lean` (110 lines, created by task 202) plus minor copyright/citation fixes to existing PR files, bringing PR 648 to ~339 additions across 5 files. The commit must contain exactly the right changes (no modal/temporal scope creep, no incomplete renames) and must build cleanly. After pushing, update the PR description to mention Bool.lean and its Zulip motivation. Done when the PR branch contains exactly the intended changes and the GitHub PR reflects the updated description.

### Research Integration

Research report `01_pr648-changes-review.md` provided the precise inclusion/exclusion decisions:
- **Include**: `Bool.lean` (new, 110 lines), its `Cslib.lean` import line, copyright year updates in `Defs.lean` and `NaturalDeduction/Basic.lean`, Chagrov reference in `Defs.lean`
- **Exclude**: Connectives.lean modal/temporal extensions, Defs.lean architecture section, NaturalDeduction/Basic.lean Gamma-to-G rename
- **LOC target**: ~339 additions (13% over 300, user-approved)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the CSLib PR pipeline for `Logics/Propositional/`. PR 648 is the first PR in the contribution roadmap described in ROADMAP.md under "Completed > Propositional Hilbert theorems" and feeds into the propositional semantics layer.

## Goals & Non-Goals

**Goals**:
- Push exactly Bool.lean + Cslib.lean import + minor fixes to the PR branch
- Keep PR at ~339 LOC additions (5 files)
- Ensure the commit builds cleanly on the PR branch
- Update PR description to mention Bool.lean and its Zulip context

**Non-Goals**:
- Modifying existing PR files beyond minor copyright/citation fixes
- Including modal/temporal connective extensions
- Resolving the Gamma-to-G rename (incomplete, would be inconsistent)
- Updating the PR's contribution roadmap numbering

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR branch has diverged from expected state | H | L | Verify branch state with `git diff upstream/main..origin/feat/propositional-v2` before modifying |
| Bool.lean has local-only dependencies that fail on PR branch | H | L | Task 202 verified Bool.lean builds; also verify on PR branch after checkout |
| Force-push loses existing PR commit | M | L | PR has 0 comments and 1 commit; create backup tag before force-push |
| Selective file extraction from main picks up wrong content | M | M | Use `git show` with specific commit hashes rather than branch HEAD; verify diff before committing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

### Phase 1: Prepare PR Branch with Selective Changes [NOT STARTED]

**Goal**: Check out the PR branch, apply exactly the right changes from local main, and create a single commit.

**Tasks**:
- [ ] Fetch latest state of all remotes (`git fetch origin && git fetch upstream`)
- [ ] Verify current PR branch state matches expectations (`git diff upstream/main..origin/feat/propositional-v2 --stat`)
- [ ] Create a safety backup tag on the current PR branch tip (`git tag backup/feat-propositional-v2-pre-216 origin/feat/propositional-v2`)
- [ ] Check out the PR branch (`git checkout feat/propositional-v2`)
- [ ] Copy `Bool.lean` from local main: `git show main:Cslib/Logics/Propositional/Semantics/Bool.lean > Cslib/Logics/Propositional/Semantics/Bool.lean`
- [ ] Add Bool.lean import to `Cslib.lean` (add `import Cslib.Logics.Propositional.Semantics.Bool` line)
- [ ] Apply copyright year update to `Defs.lean` (change copyright line to include 2026)
- [ ] Apply Chagrov reference to `Defs.lean` module doc
- [ ] Apply copyright year update to `NaturalDeduction/Basic.lean`
- [ ] Verify the diff is exactly what is expected: `git diff --stat` should show 3 modified files + 1 new file
- [ ] Stage all changes and commit with descriptive message referencing task 202 and Zulip context

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - NEW file (copy from main)
- `Cslib.lean` - Add Bool.lean import line
- `Cslib/Logics/Propositional/Defs.lean` - Copyright year + Chagrov reference
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - Copyright year

**Verification**:
- `git diff --stat` shows exactly the expected files
- `git diff upstream/main..HEAD` shows ~339 additions
- No modal/temporal content, no architecture section, no Gamma-to-G rename

---

### Phase 2: Build Verification and Push [NOT STARTED]

**Goal**: Verify the PR branch builds cleanly, then push to origin.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Bool` to verify Bool.lean compiles on PR branch
- [ ] Run `lake build Cslib.Logics.Propositional.Defs` and `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` to verify modified files
- [ ] If build passes, force-push to origin: `git push origin feat/propositional-v2 --force-with-lease`
- [ ] Verify push succeeded: `gh pr view 648 --repo leanprover/cslib --json additions,deletions,changedFiles`

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- None (git operations only)

**Verification**:
- `lake build` succeeds for all modified modules
- GitHub PR shows ~339 additions, ~105 deletions, 5 files
- Force-push completed without errors

---

### Phase 3: Update PR Description [NOT STARTED]

**Goal**: Update the PR description on GitHub to mention Bool.lean and its Zulip motivation.

**Tasks**:
- [ ] Read current PR description: `gh pr view 648 --repo leanprover/cslib --json body`
- [ ] Add Bool.lean entry to "Changed Files" section: `Cslib/Logics/Propositional/Semantics/Bool.lean` -- New: BoolValuation, BoolEvaluate, bridge lemma, decidability instance; responds to Zulip question from Matthew Doty
- [ ] Update PR description via `gh pr edit 648 --repo leanprover/cslib --body "..."`
- [ ] Verify updated description: `gh pr view 648 --repo leanprover/cslib`

**Timing**: 10 minutes

**Depends on**: 2

**Files to modify**:
- None (GitHub API operations only)

**Verification**:
- PR description includes Bool.lean entry
- PR description mentions Zulip context
- No other description content was lost

---

## Testing & Validation

- [ ] `git diff upstream/main..feat/propositional-v2 --stat` shows exactly 5 files changed
- [ ] Addition count is ~339 (within 10 of target)
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Bool` succeeds on PR branch
- [ ] No files outside the 5 expected are modified
- [ ] PR description on GitHub includes Bool.lean entry
- [ ] Backup tag exists at `backup/feat-propositional-v2-pre-216`

## Artifacts & Outputs

- `specs/216_push_relevant_changes_to_pr_648/plans/01_pr648-push-plan.md` (this file)
- Updated PR at https://github.com/leanprover/cslib/pull/648

## Rollback/Contingency

If the push introduces problems:
1. Reset PR branch to backup: `git push origin backup/feat-propositional-v2-pre-216:feat/propositional-v2 --force`
2. Delete backup tag after confirming rollback: `git tag -d backup/feat-propositional-v2-pre-216`
3. The local `main` branch is unaffected by any of these operations

If Bool.lean fails to build on the PR branch (missing dependency):
1. Check if `Cslib/Logics/Propositional/Semantics/Basic.lean` exists on the PR branch
2. If not, Bool.lean cannot be included in this PR (it belongs in a later PR)
3. Fall back to pushing only copyright/citation fixes (keeping PR at ~230 additions)
