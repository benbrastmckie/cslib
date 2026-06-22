# Implementation Plan: Fix Style Issues in GNBA.lean

- **Task**: 257 - Fix style issues in GNBA.lean
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: 256
- **Research Inputs**: specs/257_fix_gnba_long_lines_and_style/reports/01_gnba-style.md
- **Artifacts**: plans/01_gnba-style.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix 7 lines exceeding 100 characters in GNBA.lean and remove a redundant instance declaration in OmegaRegular.lean. All changes are purely cosmetic (line breaks after `:` or `:=`, one `let` binding introduction) or dead-code removal (Mathlib already provides the instance). No proof logic is modified.

### Research Integration

The research report (01_gnba-style.md) confirmed all 7 long lines at their documented positions and provided exact fix strategies for each. Five lines use the standard "break after `:` or `:=`" pattern, one (line 912) requires a `let` binding for a `gnbaAcceptSet` subexpression, and one (line 1435) requires breaking `exact absurd` arguments across lines. The `instInhabitedSetAtom` instance in OmegaRegular.lean is redundant because Mathlib's `Set.instInhabited` is transitively imported.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap items directly addressed by this style-fix task.

## Goals & Non-Goals

**Goals**:
- Break all 7 lines in GNBA.lean that exceed 100 characters
- Remove the redundant `instInhabitedSetAtom` instance from OmegaRegular.lean
- Pass `lake build`, `lake exe lint-style`, and `lake exe checkInitImports` after all changes

**Non-Goals**:
- Refactoring proof logic or tactic structure
- Addressing any style issues beyond the 7 documented long lines
- Modifying any files other than GNBA.lean and OmegaRegular.lean

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Instance deletion breaks build | M | L | Fall back to anonymous instance `instance : Inhabited (Set Atom) := <empty>` |
| Line breaks change Lean semantics | L | L | All breaks are at syntactic boundaries (after `:`, `:=`, or before arguments); verify with `lake build` |
| Line numbers shifted by task 256 | M | L | Research confirmed lines are at documented positions; verify before editing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Fix Long Lines in GNBA.lean [COMPLETED]

**Goal**: Break all 7 lines exceeding 100 characters using the strategies identified in research.

**Tasks**:
- [ ] Line 912: Insert `let chi_i := (Formula.untlFinset phi).toList.get ...` before the `if` and use the binding in the condition
- [ ] Line 929: Break `have hK_ne` after `:=` onto next indented line
- [ ] Line 1023: Break `have hprev_advance` type signature after `:` onto next indented line
- [ ] Line 1352: Break `have hP_min_exists` after `:` and beta-reduce the lambda to `t_min >= t /\ B t_min in ...`
- [ ] Line 1421: Break `haveI hd_P_dec` type after `:` onto next indented line
- [ ] Line 1427: Break `have hd_min_minimal` type after `:` onto next indented line
- [ ] Line 1435: Break `exact absurd` arguments across two lines (argument on continuation line)
- [ ] Verify no lines exceed 100 characters: `awk 'length > 100' Cslib/Logics/LTL/Semantics/GNBA.lean`

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` - 7 line-break edits

**Verification**:
- `awk 'length > 100' Cslib/Logics/LTL/Semantics/GNBA.lean` returns empty output
- `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds

---

### Phase 2: Fix Instance Naming in OmegaRegular.lean [COMPLETED]

**Goal**: Remove the redundant `instInhabitedSetAtom` instance (and its docstring) from OmegaRegular.lean.

**Tasks**:
- [ ] Delete lines 141-142 (docstring + `instInhabitedSetAtom` declaration)
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` to verify
- [ ] If build fails, fall back to anonymous instance: `instance : Inhabited (Set Atom) := <empty>`

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` - Delete instance (or make anonymous)

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` succeeds
- `grep -n instInhabitedSetAtom Cslib/Logics/LTL/Semantics/OmegaRegular.lean` returns empty

## Testing & Validation

- [ ] `awk 'length > 100' Cslib/Logics/LTL/Semantics/GNBA.lean` returns no output
- [ ] `lake build` succeeds for both modified files
- [ ] `lake exe lint-style` reports no new violations
- [ ] `lake exe checkInitImports` passes

## Artifacts & Outputs

- `plans/01_gnba-style.md` (this plan)
- `summaries/01_gnba-style-summary.md` (after implementation)

## Rollback/Contingency

All changes are in exactly two files. Revert with `git checkout -- Cslib/Logics/LTL/Semantics/GNBA.lean Cslib/Logics/LTL/Semantics/OmegaRegular.lean` if any change causes unexpected build failures.
