# Implementation Plan: Rebase PR #649 onto PR #648

- **Task**: 232 - Rebase PR #649 onto PR #648 base branch
- **Status**: [NOT STARTED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_rebase-research.md
- **Artifacts**: plans/01_rebase-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Reset `feat/temporal-formula-propositional` to point at `feat/propositional-v2`, then selectively copy only the 5 temporal-specific files from the old monolithic commit (d2ad8c74). This eliminates the 11 unrelated shake/import cleanup files from the PR diff. After local verification, the branch is force-pushed and the GitHub PR base branch is changed from `main` to `feat/propositional-v2` so the PR diff shows only temporal-specific changes. Push and PR edit are user-review gates that require explicit confirmation before execution.

### Research Integration

Research report (01_rebase-research.md) identified the complete file classification: 5 files to KEEP (2 new temporal files, Connectives.lean, Cslib.lean, references.bib) and 11 files to DROP (HasFresh, LTS/Notation, CCS/Semantics, 4 LambdaCalculus, 3 Modal, Propositional/Defs). The report confirmed zero dependency risk and recommended Option A (clean branch + selective copy).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Temporal module area of the roadmap. The temporal syntax formula types (Temporal/Syntax/Formula.lean, LTL/Syntax/Formula.lean) and connective typeclasses (HasUntil, HasSince, HasNext) are foundational to the Temporal layer in the module dependency structure.

## Goals & Non-Goals

**Goals**:
- Reset feat/temporal-formula-propositional to be based on feat/propositional-v2
- Include only the 5 temporal-specific file changes in the rebased branch
- Produce a clean single commit on top of propositional-v2
- Verify the resulting diff matches expectations (2 new files, 3 modified files, 0 unrelated files)
- Update PR #649 base branch from `main` to `feat/propositional-v2` (user-review gate)

**Non-Goals**:
- Auto-executing push or PR edits without user confirmation
- Updating the GitHub PR description text
- Running the full CI pipeline (lake test, checkInitImports)
- Resolving any content issues in the temporal files themselves

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Overwriting local uncommitted work on feat/temporal-formula-propositional | H | L | Stash or verify clean working tree before starting |
| Cslib.lean manual edit misses correct insertion point | M | L | Verify by diffing against d2ad8c74 version; add only the 2 import lines |
| Connectives.lean from d2ad8c74 is missing propositional-v2 content | M | L | Research confirmed d2ad8c74 includes all propositional-v2 content (superset); copy is safe |
| Directory structure missing for new temporal files | L | M | Create directories with mkdir -p before file copy |
| PR base branch left as `main` after rebase | H | M | Phase 4 explicitly changes base via `gh pr edit 649 --base feat/propositional-v2`; without this the PR diff still shows all of PR #648's changes |

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

### Phase 1: Branch Preparation [NOT STARTED]

**Goal**: Reset feat/temporal-formula-propositional to point at feat/propositional-v2 tip

**Tasks**:
- [ ] Ensure working tree is clean (stash if needed)
- [ ] Fetch latest refs to ensure feat/propositional-v2 and feat/temporal-formula-propositional are up to date
- [ ] Record the old temporal branch tip (d2ad8c74) for reference
- [ ] Checkout feat/propositional-v2
- [ ] Force-move feat/temporal-formula-propositional to feat/propositional-v2 tip: `git branch -f feat/temporal-formula-propositional feat/propositional-v2`
- [ ] Checkout feat/temporal-formula-propositional

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- No file modifications; git ref operations only

**Verification**:
- `git log --oneline -3 feat/temporal-formula-propositional` shows propositional-v2 commits (194f0c3d, 7cc09612)
- `git diff feat/propositional-v2..feat/temporal-formula-propositional` is empty

---

### Phase 2: Selective File Copy and Commit [NOT STARTED]

**Goal**: Copy only temporal-specific content from old commit d2ad8c74 and create a clean commit

**Tasks**:
- [ ] Create directories for new files: `mkdir -p Cslib/Logics/Temporal/Syntax Cslib/Logics/LTL/Syntax`
- [ ] Copy new file: `git show d2ad8c74:Cslib/Logics/Temporal/Syntax/Formula.lean > Cslib/Logics/Temporal/Syntax/Formula.lean`
- [ ] Copy new file: `git show d2ad8c74:Cslib/Logics/LTL/Syntax/Formula.lean > Cslib/Logics/LTL/Syntax/Formula.lean`
- [ ] Copy modified file (full content, superset of propositional-v2): `git show d2ad8c74:Cslib/Foundations/Logic/Connectives.lean > Cslib/Foundations/Logic/Connectives.lean`
- [ ] Copy modified file (full content): `git show d2ad8c74:references.bib > references.bib`
- [ ] Edit Cslib.lean to add exactly 2 temporal import lines (`public import Cslib.Logics.LTL.Syntax.Formula` and `public import Cslib.Logics.Temporal.Syntax.Formula`) at the appropriate position among the existing imports
- [ ] Stage all 5 files: `git add Cslib/Logics/Temporal/Syntax/Formula.lean Cslib/Logics/LTL/Syntax/Formula.lean Cslib/Foundations/Logic/Connectives.lean Cslib.lean references.bib`
- [ ] Commit with message: `feat(Logics/Temporal): temporal formula type with propositional structure`

**Timing**: 10 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - New file (copy from d2ad8c74)
- `Cslib/Logics/LTL/Syntax/Formula.lean` - New file (copy from d2ad8c74)
- `Cslib/Foundations/Logic/Connectives.lean` - Full copy from d2ad8c74 (superset of propositional-v2)
- `references.bib` - Full copy from d2ad8c74 (includes temporal + docstring references)
- `Cslib.lean` - Manual edit to add 2 import lines only

**Verification**:
- `git log --oneline -1` shows the new commit on top of propositional-v2
- `git diff --stat feat/propositional-v2..feat/temporal-formula-propositional` shows exactly 5 files changed

---

### Phase 3: Diff Verification [NOT STARTED]

**Goal**: Confirm the rebased branch diff contains only temporal-specific changes and no unrelated files

**Tasks**:
- [ ] Run `git diff --stat feat/propositional-v2..feat/temporal-formula-propositional` and verify exactly 5 files listed
- [ ] Verify 2 new files present: Temporal/Syntax/Formula.lean, LTL/Syntax/Formula.lean
- [ ] Verify 3 modified files present: Connectives.lean, Cslib.lean, references.bib
- [ ] Verify 0 unrelated files (no HasFresh, LTS/Notation, CCS/Semantics, LambdaCalculus, Modal, Propositional/Defs)
- [ ] Spot-check Cslib.lean diff shows only the 2 temporal import line additions
- [ ] Spot-check Connectives.lean diff shows only temporal additions (HasUntil, HasSince, HasNext, bundled classes, docstring updates)

**Timing**: 5 minutes

**Depends on**: 2

**Files to modify**:
- None (read-only verification)

**Verification**:
- All checks pass; diff matches the expected output described in research report

---

### Phase 4: Push and Update PR Base Branch (USER REVIEW GATE) [NOT STARTED]

**Goal**: Force-push the rebased branch and change PR #649's base branch from `main` to `feat/propositional-v2` so GitHub shows only temporal-specific changes in the diff

**Tasks**:
- [ ] **STOP**: Present the diff summary to the user and wait for explicit confirmation before proceeding
- [ ] Force-push the rebased branch: `git push --force origin feat/temporal-formula-propositional`
- [ ] Change PR #649 base branch: `gh pr edit 649 --base feat/propositional-v2`
- [ ] Verify the PR now shows `feat/propositional-v2` as base: `gh pr view 649 --json baseRefName`

**Timing**: 5 minutes

**Depends on**: 3

**Files to modify**:
- None (remote operations only)

**Verification**:
- `gh pr view 649 --json baseRefName` returns `feat/propositional-v2`
- PR #649 diff on GitHub shows only the 5 temporal-specific file changes
- PR #649 is now correctly stacked on PR #648 per reviewer ctchou's request

**IMPORTANT**: This phase MUST NOT be auto-executed. The implementer must pause after Phase 3, present results, and get explicit user confirmation before running push and PR edit commands. Without the `gh pr edit 649 --base feat/propositional-v2` step, GitHub will continue showing the diff against `main`, which includes all of PR #648's propositional-v2 changes and defeats the purpose of the rebase.

## Testing & Validation

- [ ] `git diff --stat feat/propositional-v2..feat/temporal-formula-propositional` shows exactly 5 files
- [ ] No unrelated files appear in the diff (0 of the 11 DROP files)
- [ ] Cslib.lean diff shows only 2 added import lines
- [ ] Connectives.lean diff shows only temporal typeclass additions and docstring updates
- [ ] references.bib diff shows only temporal and Connectives-docstring bibliography entries
- [ ] User confirms diff before push (Phase 4 gate)
- [ ] After push: `gh pr view 649 --json baseRefName` returns `feat/propositional-v2`

## Artifacts & Outputs

- `plans/01_rebase-plan.md` (this file)
- Local branch `feat/temporal-formula-propositional` rebased onto `feat/propositional-v2` with a single clean commit
- PR #649 base branch updated to `feat/propositional-v2` (after user approval in Phase 4)

## Rollback/Contingency

If the rebase produces unexpected results before push:
1. The old commit d2ad8c74 is still reachable via `git reflog` and can be restored
2. Reset the branch back: `git checkout feat/temporal-formula-propositional && git reset --hard d2ad8c74`
3. Before Phase 4 executes, the remote branch remains unchanged as a safe fallback

If the PR base branch change causes issues after push:
1. Revert base branch: `gh pr edit 649 --base main`
2. Force-push old commit back: `git push --force origin d2ad8c74:feat/temporal-formula-propositional`
