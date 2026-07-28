# Implementation Plan: Task #578

- **Task**: 578 - Untrack and gitignore the ephemeral orchestrator runtime files currently committed in this repository
- **Status**: [COMPLETED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/578_untrack_ephemeral_orchestrator_runtime_files/reports/01_untrack-ephemeral-runtime-files.md
- **Artifacts**: plans/01_untrack-ephemeral-runtime-files.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

Apply the consumer-repo remediation defined by `.claude/context/standards/orchestrator-runtime-files.md` to this repository: append the standard's verbatim ephemeral-class block to the repo's own root `/.gitignore`, then untrack the already-committed ephemeral-class runtime files with `git rm --cached` (index-only, nothing leaves disk). The durable class (`.orchestrator-handoff.json`, bare `.return-meta.json`) is explicitly out of scope and must remain tracked and un-ignored. Definition of done: `bash .claude/scripts/check-runtime-file-tracking.sh` exits 0 with all three checks passing.

### Research Integration

The research report verified ground truth by executing the check script directly rather than inferring:
- Check A FAILS (root `.gitignore` has 19 lines, zero orchestrator/runtime patterns); Check B FAILS (34 tracked ephemeral paths, verified count — the task description's 35 was approximate, the loop-guard count is 17 not 18); Check C already PASSES.
- The verbatim 15-line block (6 comment lines + 9 glob patterns) was captured from the standard's "Consumer Repo Setup" section and re-verified against the source file during planning. It collides with no existing `.gitignore` line and structurally cannot match the durable class: `**/.return-meta-*.json` is the suffixed form only, and no pattern targets `.orchestrator-handoff.json`.
- No ordering hazard: this orchestration's own `specs/578_.../` directory (including its live `.orchestrator-loop-guard` and `.lock/holder.json`) is entirely untracked, so `git rm --cached` never applies to it. Gitignore-first matches the standard document's own section order and avoids a transient window of newly-unignored `??` entries.
- The report's Appendix contains the full 34-path list and the exact per-file remediation commands, ready for mechanical execution.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context; roadmap consultation was skipped. This plan neither reads nor modifies ROADMAP.md.

## Goals & Non-Goals

**Goals**:
- Add the verbatim ephemeral-class block from the standard's "Consumer Repo Setup" section to root `/.gitignore`.
- Untrack every currently-tracked ephemeral-class path via `git rm --cached` (and `git rm -r --cached` for the one `.lock/` directory).
- Reach `check-runtime-file-tracking.sh` exit 0 with Checks A, B, and C all passing.

**Non-Goals**:
- Deleting any file from disk. This is a git-index and `.gitignore` change only.
- Untracking or ignoring `.orchestrator-handoff.json` or bare `.return-meta.json` (durable class).
- Modifying `check-runtime-file-tracking.sh`, the standard document, or any other `.claude/` file.
- Resetting or repairing the stale cycle counts inside any committed loop guard (out of scope; untracking is the fix being asked for).
- Adapting, reordering, or "improving" the standard's block — it is copied verbatim.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A concurrent orchestration commits a new ephemeral file, making the 34-path list stale | M | L | Re-run the check script immediately before Phase 2 and drive off its live Check B output, not the hardcoded Appendix list |
| An over-broad glob ignores `.orchestrator-handoff.json` or bare `.return-meta.json`, breaking Check C | H | L | Paste the block verbatim (no edits); Phase 1 verification explicitly re-confirms Check C passes before proceeding |
| Wholesale `git add -A` / `git add specs/578_.../` re-tracks this run's own loop guard and `.lock/holder.json` | M | M | Stage only `.gitignore` plus the explicit `git rm --cached` removals; `git add -A` and `git commit -am` are forbidden per `.claude/rules/git-workflow.md` |
| A file is accidentally removed from disk instead of the index | H | L | Use only `git rm --cached` / `git rm -r --cached` (never bare `git rm`); Phase 2 verification spot-checks that sample paths still exist on disk |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Add the ephemeral-class block to root `.gitignore` [COMPLETED]

**Goal**: Root `/.gitignore` covers all nine ephemeral-class patterns, making Check A pass, with Check C still passing.

**Tasks**:
- [x] Read `.claude/context/standards/orchestrator-runtime-files.md` "Consumer Repo Setup" section and copy the fenced `gitignore` block character-for-character (6 comment lines + 9 glob patterns). *(completed)*
- [x] Append a blank-line separator followed by that block to the end of root `/.gitignore`. Do not edit, reorder, or reword any line; do not modify the existing 19 lines. *(completed: verified byte-identical prefix via git diff — only 16 new lines (1 blank + 15-line block) appended, 19 pre-existing lines untouched)*
- [x] Confirm no pattern for `.orchestrator-handoff.json` was introduced and that the return-meta pattern is the suffixed `**/.return-meta-*.json` form only. *(completed)*

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `.gitignore` - append the verbatim 15-line ephemeral-class block after existing content

**Verification**:
- `bash .claude/scripts/check-runtime-file-tracking.sh` reports **Check A passed** (all nine representative probes now report ignored) and **Check C still passed** (both durable probes report "not ignored"). Check B is expected to still FAIL at this point — that is Phase 2's job.
- `git check-ignore -v specs/578_untrack_ephemeral_orchestrator_runtime_files/.orchestrator-loop-guard` exits 0 (this run's own guard is now ignored, the intended effect).
- `git check-ignore -v specs/578_untrack_ephemeral_orchestrator_runtime_files/.return-meta.json` exits 1 (bare durable form is NOT ignored).
- `git status --short .gitignore` shows exactly one modified file.

---

### Phase 2: Untrack the tracked ephemeral files and verify all three checks [COMPLETED]

**Goal**: Zero ephemeral-class paths remain tracked, every untracked file is still present on disk, and the definition of done is met.

**Tasks**:
- [x] Re-run `bash .claude/scripts/check-runtime-file-tracking.sh` and capture its live Check B output — use the freshly-printed per-file remediation commands as the authoritative list (expected: the 34 paths in the research report's Appendix, but do not assume the count). *(completed: live output printed exactly 34 remediation commands, matching the report's Appendix)*
- [x] Execute the printed `git rm --cached "<path>"` command for every tracked ephemeral file, and `git rm -r --cached "specs/557_modal_tableau_refactor_abstractions_boneyard/.lock"` for the one `.lock/` directory. Never use bare `git rm`. *(completed: all 34 remediation commands executed verbatim, index-only)*
- [x] Confirm no command touched `.orchestrator-handoff.json` or any bare `.return-meta.json`. *(completed: grep of the remediation command list for both patterns returned no matches)*
- [x] Review `git status --short` and `git diff --staged --stat`: the staged set must be `.gitignore` plus the ephemeral-path index deletions and nothing else. Do not run `git add -A`, `git add .`, `git commit -am`, or `git add specs/578_.../`. *(completed: staged `.gitignore` via targeted `git add .gitignore`; `git diff --staged --name-only` shows exactly 35 files — `.gitignore` + the 34 deletions)*

**Timing**: 25 minutes

**Depends on**: 1

**Files to modify**:
- Git index only — the ~34 tracked ephemeral-class paths under `specs/` are removed from the index; their on-disk contents are untouched.

**Verification**:
- `bash .claude/scripts/check-runtime-file-tracking.sh` exits 0 with **all three checks passing** (Check A ignore coverage, Check B no tracked ephemeral files, Check C durable provenance not over-ignored). This is the definition of done.
- Spot-check that files survived on disk: `ls specs/317_propositional_tableau_completeness/.orchestrator-loop-guard specs/557_modal_tableau_refactor_abstractions_boneyard/.lock/holder.json specs/.events.lock` all succeed.
- `git ls-files specs | grep -E '(orchestrator-loop-guard|orchestrator-churn-state|drift-inspection|orchestrator-multi-state|return-meta-|events\.lock|/\.lock/)'` returns no matches.
- `git ls-files specs | grep -c 'orchestrator-handoff.json'` is unchanged from its pre-change value (durable class still tracked).

## Testing & Validation

- [x] `bash .claude/scripts/check-runtime-file-tracking.sh` exits 0 with Checks A, B, and C all reporting `passed`. *(completed)*
- [x] No file was deleted from disk: every path removed from the index still resolves via `ls`. *(completed: spot-checked 3 sample paths plus visually confirmed disk presence is unaffected by `--cached` removal)*
- [x] `git diff --staged --stat` shows only `.gitignore` (modified) plus index-only deletions of ephemeral-class paths. *(completed: 35 files, 16 insertions in .gitignore + 378 deletions across the 34 ephemeral paths)*
- [x] `git check-ignore` reports the durable class (`.orchestrator-handoff.json`, bare `.return-meta.json`) as NOT ignored. *(completed: Check C passed)*
- [x] Root `.gitignore`'s pre-existing 19 lines are byte-identical to before. *(completed: `diff` against `git show HEAD:.gitignore | head -19` reported no differences)*

## Artifacts & Outputs

- `.gitignore` — extended with the verbatim ephemeral-class block (6 comment lines + 9 glob patterns).
- Git index — ~34 ephemeral-class paths removed (files retained on disk).
- `specs/578_untrack_ephemeral_orchestrator_runtime_files/summaries/01_untrack-ephemeral-runtime-files-summary.md` — implementation summary.

## Rollback/Contingency

Both phases are trivially reversible and touch no file contents:

- **Revert the `.gitignore` edit**: `git checkout -- .gitignore` (only safe while nothing else is uncommitted in that file; otherwise remove the appended block by hand).
- **Re-track the untracked files**: `git add <path>` for each path removed from the index — the files were never deleted from disk, so re-adding restores the prior index state exactly.
- **After a commit**: `git revert <sha>` restores both the `.gitignore` state and the index entries in one step.

Contingency if Check C regresses after the `.gitignore` edit: the appended block was not verbatim. Remove the appended block, re-copy from the standard without modification, and re-verify before proceeding to Phase 2.
