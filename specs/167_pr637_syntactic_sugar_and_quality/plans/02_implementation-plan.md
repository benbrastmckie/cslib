# Implementation Plan: Task #167 -- PR #637 Syntactic Sugar and Quality Review

- **Task**: 167 - PR #637 (refactor/modal-primitives) syntactic sugar and quality review
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: 165 (syntactic sugar already merged to main)
- **Research Inputs**: specs/167_pr637_syntactic_sugar_and_quality/reports/01_pr637-research.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Rebase the `refactor/modal-primitives` branch (PR #637) onto `main` to incorporate task 165's syntactic sugar changes, resolve all 29 merge conflicts across 7 files using documented resolution rules, verify no remaining raw constructors in expression positions, run the full CSLib CI pipeline, and push to the PR branch. The rebase approach is chosen over cherry-pick because the conflicts are exclusively caused by the sugar divergence between branches -- rebasing cleanly integrates both sets of changes.

### Research Integration

Research report `01_pr637-research.md` provides:
- Complete file inventory: 13 files touched by PR, 7 with merge conflicts
- Exact sugar replacement table: 21 replacements across `Modal/Basic.lean` (18) and `Modal/LogicalEquivalence.lean` (3)
- Per-file conflict resolution rules (docstrings from PR, sugar from main, PR's `ImpBotDerived` rename, PR's cleaner proof style for `Denotation.lean`)
- Quality review: pre-existing typo (`Extention`) flagged as out-of-scope
- Pi-type binder constraint: `.imp` must stay raw in `change` tactic positions where `->` would parse as function arrow

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly addressed by this PR integration task.

## Goals & Non-Goals

**Goals**:
- Rebase `refactor/modal-primitives` onto `main` with all conflicts resolved correctly
- Apply all 21 syntactic sugar replacements (`.diamond`->`diamond`, `.neg`->`not`, `.and`->`and`, `.or`->`or`, `.imp`->`->`, `.box`->`box` in expression positions)
- Preserve PR's semantic contributions: `ImpBotDerived` rename, expanded docstrings, cleaner proof style in `Denotation.lean`
- Pass full CI pipeline (lake build, lake test, checkInitImports, lint-style)
- Push rebased branch to update PR #637

**Non-Goals**:
- Fix pre-existing `Extention` -> `Extension` typo (separate PR)
- Add new features or proofs beyond what PR #637 already includes
- Modify files not touched by PR #637

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Rebase conflict resolution error causes build failure | H | M | Follow per-file resolution rules from research; run `lake build` immediately after rebase |
| `Cslib.lean` import merge is complex (many imports added on main) | M | M | Take main's full import list, then add PR's 2 new entries; verify with `checkInitImports` |
| Sugar replacement in `change` tactic breaks proof | H | L | Research confirms all `change` positions use prefix operators (not `.imp`), which are safe |
| Force push to PR branch loses collaborator work | H | L | Use `--force-with-lease` to detect intervening pushes |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Rebase and Conflict Resolution [COMPLETED]

**Goal**: Rebase `refactor/modal-primitives` onto `main`, resolving all 29 merge conflicts across 7 files using the documented resolution rules.

**Tasks**:
- [x] Checkout `refactor/modal-primitives` branch
- [x] Run `git rebase main` to trigger the rebase
- [x] Resolve `Cslib.lean` conflicts (2 markers): take main's full import list, add PR's new imports (`Connectives`, `LogicalEquivalence`)
- [x] Resolve `Cslib/Foundations/Logic/Connectives.lean` conflicts (3 markers): take PR's `ImpBotDerived` rename and extended docstring
- [x] Resolve `Cslib/Logics/Modal/Basic.lean` conflicts (15 markers): take main's sugar notation in expression positions, take PR's expanded docstring and primitives documentation
- [x] Resolve `Cslib/Logics/Modal/Denotation.lean` conflicts (2 markers): take PR's cleaner proof style (`push Not`, bare `simp`, no `Proposition.neg` in simp)
- [x] Resolve `Cslib/Logics/Modal/LogicalEquivalence.lean` conflicts (5 markers): take PR's copyright (Montesi + Brast-McKie) and docstring, take main's sugar in `Context.fill` match arms *(deviation: altered -- add/add conflict required full file rewrite; final file uses PR's design philosophy (no typeclass) with main's sugar notation)*
- [x] Resolve `Cslib/Logics/Propositional/Defs.lean` conflicts (2 markers): take PR's docstring, keep main's `biconditional` notation line
- [x] Resolve `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` conflict (1 marker): take PR's docstring
- [x] Complete the rebase with `git rebase --continue`

**Timing**: 1 hour

**Depends on**: none

**Files to modify** (during conflict resolution):
- `Cslib.lean` -- import list merge
- `Cslib/Foundations/Logic/Connectives.lean` -- `ImpBotDerived` rename + docstring
- `Cslib/Logics/Modal/Basic.lean` -- sugar application (18 replacements) + docstring
- `Cslib/Logics/Modal/Denotation.lean` -- proof style preference
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- copyright + sugar (3 replacements)
- `Cslib/Logics/Propositional/Defs.lean` -- docstring + notation line
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- docstring

**Verification**:
- `git status` shows clean working tree (no conflict markers remaining)
- `git log --oneline main..HEAD` shows PR commits rebased on top of main
- `grep -rn '<<<<' Cslib/ Cslib.lean` returns empty (no residual conflict markers)

---

### Phase 2: Quality Scan and Full CI [COMPLETED]

**Goal**: Verify no remaining raw constructors in expression positions across all PR-touched files, then run the full CSLib CI pipeline.

**Tasks**:
- [x] Scan all 13 PR-touched files for remaining raw constructors in expression positions (`.imp`, `.bot`, `.neg`, `.and`, `.or`, `.box`, `.diamond` outside pattern match arms and Pi-type binders)
- [x] If any missed raw constructors found, apply sugar replacements and amend the relevant rebase commit or create a fixup commit *(deviation: skipped -- no raw constructors found in expression positions)*
- [x] Run `lake build` -- full project build
- [x] Run `lake test` -- CslibTests suite
- [x] Run `lake exe checkInitImports` -- verify Cslib.Init imports
- [x] Run `lake exe lint-style` -- style linting

**Timing**: 45 minutes (mostly build time)

**Depends on**: 1

**Files to modify**:
- Potentially any of the 13 PR-touched files if raw constructors are found (expected: none)

**Verification**:
- All four CI commands exit with code 0
- No raw constructors in expression positions across PR-touched files
- `lake build` produces no errors or warnings related to the changed files

---

### Phase 3: Push to PR Branch [COMPLETED]

**Goal**: Push the rebased branch to the remote, updating PR #637.

**Tasks**:
- [x] Verify the branch is `refactor/modal-primitives` and is ahead of `origin/refactor/modal-primitives`
- [x] Run `git push --force-with-lease origin refactor/modal-primitives`
- [x] Verify push succeeded and PR #637 shows updated commits

**Timing**: 5 minutes

**Depends on**: 2

**Files to modify**:
- None (git operation only)

**Verification**:
- `git push` exits with code 0
- `git log --oneline origin/refactor/modal-primitives..refactor/modal-primitives` shows no divergence (branch is at remote)

## Testing & Validation

- [x] `lake build` passes with no errors
- [x] `lake test` passes all CslibTests
- [x] `lake exe checkInitImports` passes
- [x] `lake exe lint-style` passes
- [x] No residual conflict markers in any file (`grep -rn '<<<<' .`)
- [x] All 21 sugar replacements applied (verified by absence of raw constructors in expression positions)
- [x] PR's `ImpBotDerived` rename preserved
- [x] PR's expanded docstrings preserved
- [x] PR's `Denotation.lean` proof style preserved

## Artifacts & Outputs

- `specs/167_pr637_syntactic_sugar_and_quality/plans/02_implementation-plan.md` (this file)
- `specs/167_pr637_syntactic_sugar_and_quality/summaries/02_implementation-summary.md` (after implementation)
- Updated PR #637 on GitHub with rebased commits

## Rollback/Contingency

- Before rebase: note the current `refactor/modal-primitives` HEAD SHA for recovery
- If rebase goes wrong: `git rebase --abort` returns to pre-rebase state
- If push goes wrong: `git push --force-with-lease` will refuse if remote has diverged
- If CI fails after rebase: fix the issue in a new commit on the branch, re-run CI, then push
- Full recovery: `git reset --hard {original-SHA}` restores the branch to its pre-rebase state
