# Implementation Plan: Fix GenericMCSBridge Docstrings

- **Task**: 287 - Convert block comments in GenericMCSBridge.lean to module docstrings
- **Status**: [COMPLETED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/287_fix_generic_mcs_bridge_docstrings/reports/01_docstring-conversion.md
- **Artifacts**: plans/01_docstring-conversion-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Convert a single plain block comment (`/- ... -/`) to a module docstring (`/-! ... -/`) in
`Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` at line 115. Research confirmed that
only one edit is needed: the NOTE block at lines 115-122 uses plain comment syntax instead
of the `/-!` module docstring format required by CSLib documentation conventions. The copyright
header (lines 1-5) and main module docstring (lines 12-113) are already correct.

### Research Integration

Research report (`reports/01_docstring-conversion.md`) confirmed:
- The file has three comment blocks; only the NOTE block at lines 115-122 needs conversion
- The fix is a single-character insertion: add `!` after `/-` on line 115
- No compilation risk -- docstring format has no effect on build
- All other files in `Cslib/Logics/Modal/` use `/-!` for module-level documentation

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task improves documentation consistency in the Modal module, supporting the overall
roadmap goal of maintaining clean, well-documented CSLib modules during the BimodalLogic port.

## Goals & Non-Goals

**Goals**:
- Convert the NOTE block at line 115 from `/- ... -/` to `/-! ... -/`
- Ensure the fix passes CSLib CI (`lake build`, `lake exe lint-style`)

**Non-Goals**:
- Modifying the copyright header (correctly uses plain `/- ... -/`)
- Modifying the main module docstring (already uses `/-! ... -/`)
- Changing any content within the comment blocks

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Edit breaks compilation | L | L | Docstring syntax change has no semantic effect; verify with `lake build` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Convert NOTE Block to Module Docstring [COMPLETED]

**Goal**: Change the plain block comment at line 115 to a module docstring

**Tasks**:
- [ ] Edit line 115 of `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`: change `/- NOTE:` to `/-! NOTE:`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge`
- [ ] Run `lake exe lint-style` to confirm no style violations

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - Insert `!` after `/-` on line 115

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` succeeds
- `lake exe lint-style` passes
- Line 115 reads `/-! NOTE:` instead of `/- NOTE:`

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` compiles without errors
- [ ] `lake exe lint-style` reports no violations for the file
- [ ] The copyright header at lines 1-5 still uses plain `/- ... -/`
- [ ] The main module docstring at lines 12-113 still uses `/-! ... -/`

## Artifacts & Outputs

- `plans/01_docstring-conversion-plan.md` (this file)
- Modified `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`

## Rollback/Contingency

Revert the single-character edit on line 115 (change `/-!` back to `/-`). Since this is a
documentation-only change with no semantic effect, rollback is trivial.
