# Implementation Plan: Task #260

- **Task**: 260 - Add module-level documentation contrasting LTL and Temporal convention differences
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: Task 255 (completed -- updated LTL/Embedding.lean docstrings)
- **Research Inputs**: specs/260_add_ltl_temporal_convention_contrast_docs/reports/01_convention-docs.md
- **Artifacts**: plans/01_convention-docs.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add cross-referencing documentation to three Lean files so that readers of any one module can quickly locate the other module and understand the convention difference (standard Pnueli vs Burgess) for the `untl` operator. All changes are insertions into existing `/-! ... -/` module docstring blocks. No Lean code is modified and there are zero proof obligations, so this is a pure documentation task with no build risk beyond docstring syntax.

### Research Integration

The research report (01_convention-docs.md) confirmed:
- LTL/Syntax/Formula.lean documents guard/event roles but lacks any cross-reference to Temporal's Burgess convention.
- Temporal/Syntax/Formula.lean documents the Burgess convention but lacks a formal cross-reference to LTL.
- LTL/Embedding.lean already has excellent convention-bridging documentation (updated by task 255) and needs no changes.
- Foundations/Logic/Connectives.lean has no module-routing note explaining which bundled classes serve which logic modules.
- No barrel file is needed; the module docstring in LTL/Syntax/Formula.lean is the correct insertion point.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly advance any specific Remaining roadmap item. It improves documentation quality across the LTL, Temporal, and Foundations/Logic modules, supporting long-term maintainability of the porting effort.

## Goals & Non-Goals

**Goals**:
- Add a "Convention Note" section to LTL/Syntax/Formula.lean explaining standard vs Burgess convention and referencing Embedding.lean
- Add a "Convention Note" section to Temporal/Syntax/Formula.lean cross-referencing LTL's standard convention and Embedding.lean
- Add a "Module Routing" section to Foundations/Logic/Connectives.lean explaining which typeclasses serve which logic modules
- All three files pass `lake build` after edits

**Non-Goals**:
- Modifying any Lean code or proofs
- Creating a barrel file for the LTL module
- Editing LTL/Embedding.lean (already complete from task 255)
- Changing notation or operator definitions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring syntax error breaks build | L | L | Each edit is plain text inside `/-! -/` blocks; verify with `lake build` |
| Inserted text exceeds 100-char line limit | L | M | Follow CSLib style: wrap lines at 100 chars |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Add Convention Documentation to Three Files [COMPLETED]

**Goal**: Insert cross-referencing convention notes into the module docstrings of all three target files.

**Tasks**:
- [ ] In `Cslib/Logics/LTL/Syntax/Formula.lean`, insert a "Convention Note" section after the "Derived Operators" section (approx. line 51) explaining: LTL uses standard (Pnueli) convention (`untl guard event`); Temporal uses Burgess convention (`untl event guard`); `Cslib.Logics.LTL.Embedding` bridges the two via `reflexiveUntl`
- [ ] In `Cslib/Logics/Temporal/Syntax/Formula.lean`, insert a "Convention Note" section after the "Derived Temporal Operators" section (approx. line 57) explaining: this module uses Burgess convention; LTL uses standard convention; see `Cslib.Logics.LTL.Embedding` for the bridge
- [ ] In `Cslib/Foundations/Logic/Connectives.lean`, insert a "Module Routing" section after the "Design" section (approx. line 53) explaining: `FutureTemporalConnectives`/`LTLConnectives` (`HasUntil`, `HasNext`) serve LTL (standard convention); `TemporalConnectives` (`HasUntil`, `HasSince`) serve Temporal (Burgess convention); `BimodalConnectives` serve Bimodal; `HasUntil` is shared with argument order determined by the concrete instance

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - insert convention note in module docstring
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - insert convention cross-reference in module docstring
- `Cslib/Foundations/Logic/Connectives.lean` - insert module routing note in module docstring

**Verification**:
- Each inserted block is well-formed text within the existing `/-! ... -/` comment
- No Lean code is modified

---

### Phase 2: Build Verification [COMPLETED]

**Goal**: Confirm all three edited files compile without errors.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.LTL.Syntax.Formula`
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula`
- [ ] Run `lake build Cslib.Foundations.Logic.Connectives`
- [ ] If any build fails, fix the docstring syntax error and re-verify

**Timing**: 10 minutes

**Depends on**: 1

**Files to modify**:
- None (verification only; fixes only if build errors arise)

**Verification**:
- All three `lake build` commands exit 0

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Syntax.Formula` succeeds
- [ ] `lake build Cslib.Logics.Temporal.Syntax.Formula` succeeds
- [ ] `lake build Cslib.Foundations.Logic.Connectives` succeeds
- [ ] Each new docstring section is readable and accurately describes the convention difference

## Artifacts & Outputs

- `specs/260_add_ltl_temporal_convention_contrast_docs/plans/01_convention-docs.md` (this plan)
- Modified: `Cslib/Logics/LTL/Syntax/Formula.lean`
- Modified: `Cslib/Logics/Temporal/Syntax/Formula.lean`
- Modified: `Cslib/Foundations/Logic/Connectives.lean`

## Rollback/Contingency

All changes are additive text insertions in module docstring blocks. Revert with `git checkout -- Cslib/Logics/LTL/Syntax/Formula.lean Cslib/Logics/Temporal/Syntax/Formula.lean Cslib/Foundations/Logic/Connectives.lean`.
