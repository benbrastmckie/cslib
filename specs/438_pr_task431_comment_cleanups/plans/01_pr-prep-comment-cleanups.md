# Implementation Plan: Task #438

- **Task**: 438 - Upstream comment/docstring cleanups via a CSLib PR (pr_task431_comment_cleanups)
- **Status**: [PR READY]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/438_pr_task431_comment_cleanups/reports/01_pr-prep-comment-cleanups.md
- **Artifacts**: plans/01_pr-prep-comment-cleanups.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CONTRIBUTING.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a PR-preparation task, not a proof-development task. The sole in-scope code edit
(deletion of the stale `Term.subst_comm` commented-out TODO/sorry stub in `Basic.lean`) is
already committed locally at `35436d7e` and present at HEAD. The remaining work is
verification and PR-description authoring: confirm the deletion is present and comment-only,
confirm the diff against `upstream/main` is a clean single-file 9-line deletion, drop the
moot GNBA.lean item entirely, and produce a `pr-description.md` artifact with the recommended
title and body. Actual PR submission is out of scope (the `/pr` command is user-only).

### Research Integration

Key findings from `01_pr-prep-comment-cleanups.md` drive the entire plan:
- Only the `Basic.lean` stub deletion is upstreamable — a genuine, isolated, comment-only diff
  (0 insertions / 9 deletions vs `upstream/main`), still present in `upstream/main` at lines
  105-113.
- The GNBA.lean docstring reword is **MOOT and must NOT be in the PR**: `GNBA.lean` does not
  exist in `upstream/main`, and the reworded text was superseded by task 321's barrel-split
  refactor (commit `2344a765`). This item is dropped entirely.
- HEAD is 2459 commits ahead of `upstream/main`; the eventual PR branch must be built fresh
  off re-fetched `upstream/main` with only the `Basic.lean` change (do NOT cherry-pick
  `35436d7e` directly, since it also touches the pre-barrel-split GNBA.lean).
- Recommended title: `chore(LambdaCalculus): remove stale Term.subst_comm sorry stub`.
- Change is zero build/proof impact; no `sorry`/axioms/vacuous defs involved.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; roadmap consultation skipped. This task
advances CSLib upstream-hygiene work originating from the task 431 audit.

## Goals & Non-Goals

**Goals**:
- Verify the `Term.subst_comm` stub deletion is present and correct at HEAD in `Basic.lean`.
- Confirm the change is comment-only with zero build/proof impact.
- Confirm the diff vs re-fetched `upstream/main` is a clean single-file, 9-line deletion.
- Produce a `pr-description.md` artifact with the recommended title, comment-only-impact
  statement, AI-disclosure note, and reference to the task 431 audit.
- Transition the task to `[PR READY]` for the user-driven `/pr` step.

**Non-Goals**:
- Submitting the PR (the `/pr` command is user-only — NOT part of this plan).
- Creating or applying the fresh upstream branch (that is part of the user-only `/pr` step;
  this plan only documents the recommended branch-construction recipe in `pr-description.md`).
- Any change to `GNBA.lean` or its submodules (moot / out of scope — dropped entirely).
- Bundling additional doc-hygiene; research found no further in-scope markers in `Basic.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Accidentally including GNBA.lean in PR description scope | M | L | Explicitly document single-file scope; assert GNBA.lean is dropped; verify diff limited to `Basic.lean` |
| `upstream/main` moved and stub no longer present | L | L | `git fetch upstream` before diffing; if stub already removed upstream, mark task moot and note in handoff |
| Someone cherry-picks `35436d7e` directly for the PR branch | M | L | Document the correct fresh-branch recipe (`git checkout 35436d7e -- Basic.lean` onto `upstream/main`) explicitly in `pr-description.md` |
| Deletion mistakenly assumed to need a Mathlib rebuild | L | L | State comment-only / zero-build-impact explicitly; note CI is still run per CONTRIBUTING.md on the PR branch |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Verify In-Scope Change and Diff Against Upstream [COMPLETED]

**Goal**: Confirm the `Basic.lean` stub deletion is present, comment-only, and produces a
clean single-file diff against a re-fetched `upstream/main`; confirm GNBA.lean is out of scope.

**Tasks**:
- [x] Confirm no `subst_comm` / `TODO` / stale `sorry` stub remains at HEAD in
      `Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean` (`grep` returns nothing).
- [x] Run `git fetch upstream` to refresh the `upstream/main` ref.
- [x] Run `git diff --stat upstream/main..HEAD -- Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean`
      and confirm it reports 0 insertions / 9 deletions (clean, isolated).
- [x] Inspect `git diff upstream/main..HEAD -- .../Basic.lean` and confirm every removed line
      is a `--` comment or blank (no executable Lean removed) — zero build/proof impact.
- [x] Confirm `upstream/main:.../Cslib/Logics/LTL/Semantics/GNBA.lean` does not exist
      (`git cat-file -e` fails) — reconfirm GNBA.lean is out of scope and dropped.

**Verification results** (recorded 2026-07-01):
- `git fetch upstream` succeeded (network available); `upstream/main` advanced `2772f421..1edb3904`.
- `grep -n -E "subst_comm|TODO|sorry" Basic.lean` at HEAD: no matches (exit 1).
- `git diff --stat upstream/main..HEAD -- .../Basic.lean`: `1 file changed, 9 deletions(-)` (0 insertions / 9 deletions) -- exactly as expected.
- Full diff inspected: all 9 removed lines are the `-- TODO` / `-- theorem Term.subst_comm ...` comment block plus one blank line; zero executable Lean removed.
- `git cat-file -e upstream/main:Cslib/Logics/LTL/Semantics/GNBA.lean` fails with "exists on disk, but not in 'upstream/main'" -- GNBA.lean confirmed absent upstream and out of scope.
- `git rev-list --count upstream/main..HEAD` = 2460 (matches plan's "~2459 commits ahead" estimate).
- Source commit `35436d7e` confirmed: "chore: remove stale sorry-referencing comments flagged by task 431 audit".

**Timing**: 0.4 hours

**Depends on**: none

**Files to modify**:
- None (verification only; no source edits — the code change is already committed at `35436d7e`)

**Verification**:
- `grep` for stub markers in `Basic.lean` at HEAD returns no matches.
- `git diff --stat upstream/main..HEAD -- .../Basic.lean` shows exactly `0` insertions and
  `9` deletions.
- Every deleted line in the diff is a comment or blank line.
- `git cat-file -e upstream/main:Cslib/Logics/LTL/Semantics/GNBA.lean` fails (file absent upstream).

---

### Phase 2: Author pr-description.md and Mark [PR READY] [COMPLETED]

**Goal**: Produce the `pr-description.md` artifact with the recommended title and body, then
transition the task to `[PR READY]` for the user-driven `/pr` step.

**Tasks**:
- [x] Write `specs/438_pr_task431_comment_cleanups/pr-description.md` with:
      - Title: `chore(LambdaCalculus): remove stale Term.subst_comm sorry stub`
      - Body: statement that the change is comment-only with no build/proof impact
      - Reference to the task 431 audit as the source of the change
      - AI-disclosure note (per Mathlib/CSLib AI usage policy)
      - Scope statement: single file `Basic.lean` only; GNBA.lean explicitly excluded
      - Recommended branch-construction recipe for the user-only `/pr` step: fresh branch off
        re-fetched `upstream/main`, `git checkout 35436d7e -- .../Basic.lean`, commit; do NOT
        cherry-pick `35436d7e` directly.
      - Note that CI (`lake build`, `lake test`, `lake exe checkInitImports`,
        `lake exe lint-style`) should still be run on the PR branch per CONTRIBUTING.md.
- [x] Update `state.json` for task 438 to status `pr_ready` and regenerate TODO.md via
      `bash .claude/scripts/generate-todo.sh` (do NOT edit TODO.md directly).

**Result**: `pr-description.md` authored at
`specs/438_pr_task431_comment_cleanups/pr-description.md` with all required sections
(title, comment-only-impact statement, task 431 source reference, single-file scope
statement with GNBA.lean exclusion rationale, fresh-branch recipe using
`git checkout 35436d7e -- .../Basic.lean` onto re-fetched `upstream/main`, CI checklist,
and verbatim AI Tools Used disclosure). `state.json` updated to `status: "pr_ready"` for
project 438; `TODO.md` regenerated and confirmed to show `438 [PR READY]`.

**Timing**: 0.35 hours

**Depends on**: 1

**Files to modify**:
- `specs/438_pr_task431_comment_cleanups/pr-description.md` - new PR description artifact (create)
- `specs/state.json` - transition task 438 to `pr_ready`

**Verification**:
- `pr-description.md` exists and contains the recommended title, comment-only-impact statement,
  AI-disclosure note, task-431 reference, single-file scope statement, and branch recipe.
- Task 438 shows `[PR READY]` in TODO.md after regeneration.

## Testing & Validation

- [x] `Basic.lean` at HEAD contains no `subst_comm` / stale-`sorry` / TODO stub markers.
- [x] `git diff --stat upstream/main..HEAD -- .../Basic.lean` = 0 insertions / 9 deletions.
- [x] All deleted lines are comments or blank (zero build/proof impact).
- [x] GNBA.lean confirmed absent from `upstream/main` and excluded from PR scope.
- [x] `pr-description.md` produced with required content.
- [x] Task transitioned to `[PR READY]`.

## Artifacts & Outputs

- `specs/438_pr_task431_comment_cleanups/pr-description.md` (PR title + body for user-only /pr)
- Task status updated to `[PR READY]`
- Verification evidence recorded in the implementation summary

## Rollback/Contingency

- No source edits are made by this plan (the code change is already committed at `35436d7e`),
  so there is nothing to revert on the code side.
- If `pr-description.md` is malformed, delete and rewrite it — no other state is affected.
- If Phase 1 reveals the stub was already removed upstream (task became moot) or the diff is
  not clean, do NOT author a PR description; instead record the finding, keep the task in its
  current status, and surface a blocker in the orchestrator handoff for user review.
