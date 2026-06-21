# Implementation Plan: Task #255

- **Task**: 255 - Fix stale docstrings and comments left over from the task-254 LTL convention revision
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None (task-254 already completed)
- **Research Inputs**: specs/255_fix_stale_ltl_docstrings_post_task254/reports/01_stale-docstrings.md
- **Artifacts**: plans/01_stale-docstrings.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix four stale docstrings and comments across three LTL files that were left inconsistent after the task-254 LTL convention revision. All changes are docstring/comment or pattern-variable-name edits with zero proof impact. A single `lake build` pass confirms no regressions.

### Research Integration

The research report (01_stale-docstrings.md) verified all four issues against the source files and provided exact replacement text for each. Key findings:

1. **Embedding.lean:14-15** -- module docstring incorrectly implies LTL uses Burgess conventions; needs rewrite to explain that LTL uses standard convention and Temporal uses Burgess.
2. **Formula.lean:75** -- next constructor docstring uses ASCII `Xφ` instead of project Unicode `◯φ`.
3. **Embedding.lean:49** -- pattern variables `ψ φ` in the `untl` match arm are confusing relative to LTL's `φ₁ φ₂` constructor parameter names; rename to `φ₁ φ₂` for self-documenting code.
4. **OmegaRegular.lean:310** -- stale reference to `proof_wanted` placeholder that no longer exists; rephrase to explain retained unused hypotheses.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items are directly advanced by this documentation cleanup task. The LTL and Temporal modules are not listed in the Remaining section of the roadmap.

## Goals & Non-Goals

**Goals**:
- Fix all four stale docstrings/comments identified in the task description
- Ensure `lake build` passes after all edits

**Non-Goals**:
- Changing any proof logic or definitions
- Modifying files beyond the three identified (Embedding.lean, Formula.lean, OmegaRegular.lean)
- Auditing other LTL files for additional stale documentation (out of scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Pattern variable rename breaks build | M | L | The rename is local to a match arm; `lake build` verifies no downstream breakage |
| Unicode `◯` rendering issues | L | L | Character already used elsewhere in the project's LTL notation |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Apply All Four Docstring/Comment Fixes [NOT STARTED]

**Goal**: Edit the three source files to fix all four stale documentation issues.

**Tasks**:
- [ ] Edit `Cslib/Logics/LTL/Embedding.lean` lines 14-15: Rewrite module docstring from "mapping LTL's five primitives to their Burgess-temporal counterparts" to explain that LTL uses standard convention (`untl guard event`) while Temporal uses Burgess convention (`untl event guard`), and the embedding bridges the two
- [ ] Edit `Cslib/Logics/LTL/Syntax/Formula.lean` line 75: Change `Xφ` to `◯φ` in the next constructor docstring
- [ ] Edit `Cslib/Logics/LTL/Embedding.lean` line 49: Rename pattern variables from `ψ φ` to `φ₁ φ₂` in the `untl` match arm, updating the body references accordingly (`.untl φ₁ φ₂ => (toTemporal φ₂).reflexiveUntl (toTemporal φ₁)`)
- [ ] Edit `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` line 310: Replace "the signature matches the original `proof_wanted`" with "the signature retains them for uniformity with the inductive cases in `Formula.isRegular`"

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Embedding.lean` -- rewrite module docstring (lines 14-15) and rename pattern variables (line 49)
- `Cslib/Logics/LTL/Syntax/Formula.lean` -- update next constructor docstring notation (line 75)
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- remove stale proof_wanted reference (line 310)

**Verification**:
- Each edit matches the recommended replacement text from the research report
- All four issues addressed

---

### Phase 2: Build Verification [NOT STARTED]

**Goal**: Confirm that all edits are safe and the project builds without errors.

**Tasks**:
- [ ] Run `lake build` to verify no build regressions from the edits
- [ ] If build fails, diagnose and fix (expected: pass, since all changes are docstring/comment/pattern-variable-name only)

**Timing**: 10 minutes

**Depends on**: 1

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` exits with code 0
- No new warnings related to the edited files

## Testing & Validation

- [ ] `lake build` passes with zero errors
- [ ] All four docstring/comment issues from the task description are resolved
- [ ] No semantic changes to any proof or definition

## Artifacts & Outputs

- `specs/255_fix_stale_ltl_docstrings_post_task254/plans/01_stale-docstrings.md` (this plan)
- Modified files: `Embedding.lean`, `Formula.lean`, `OmegaRegular.lean`

## Rollback/Contingency

All changes are to docstrings, comments, and pattern variable names. If any edit causes an unexpected build failure, revert the individual edit via `git checkout -- <file>` and investigate. The edits are independent enough that partial application is safe.
