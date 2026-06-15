# Implementation Plan: Task #196

- **Task**: 196 - refactor_connectives_mathlib_bot
- **Status**: [COMPLETED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/196_refactor_connectives_mathlib_bot/reports/01_mathlib-section-research.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Research verified that the pr-description.md Mathlib section (lines 88-96) has already been updated by two prior task 196 commits (ad0adde3 and ed23a7e6) and is accurate. All six claims in the current text were verified against the codebase: Mathlib Bot/HImp are pure notation classes, CSLib uses uniform Has* naming across 833+ references, four concrete formula types provide direct Bot instances, and HImp has incompatible field name, notation, and fixity. No code or documentation changes are required. The sole implementation phase is a final verification pass confirming the section is accurate before marking the task complete.

### Research Integration

The research report (01_mathlib-section-research.md) verified each claim in the current Mathlib section against the codebase:
1. Mathlib Bot and HImp are `@[notation_class]` in `Mathlib.Order.Notation` -- confirmed
2. CSLib uses uniform Has* naming (HasBot, HasImp, HasAnd, HasOr) across Foundations/Logic -- confirmed (833+ references)
3. Four infrastructure files (Axioms.lean, ProofSystem.lean, Consistency.lean, BigConj.lean) use these classes -- confirmed
4. Four concrete formula types provide direct Bot instances for notation -- confirmed
5. HImp field name (`himp` vs `imp`), notation (`=>` vs `->`), and fixity (`infixr:60` vs `infix:30`) prevent replacement -- confirmed
6. Mathlib has no logical connective equivalents for HasAnd/HasOr -- confirmed

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not advance any items on ROADMAP.md. It is a documentation-only task scoped to the pr-description.md Mathlib section within the propositional upstream PR (task 188).

## Goals & Non-Goals

**Goals**:
- Verify the pr-description.md Mathlib section is accurate and complete
- Confirm no code changes are needed (no bridge instance, no class replacement)
- Mark task 196 as complete

**Non-Goals**:
- Rewriting the Mathlib section (already accurate per research)
- Modifying any Lean source files
- Adding bridge instances or replacing Has* classes with Mathlib equivalents

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Mathlib section was modified since research | L | L | Re-read file at implementation time to confirm content |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Verify Mathlib Section and Complete [COMPLETED]

**Goal**: Confirm the pr-description.md Mathlib section matches the verified content from research and mark the task complete.

**Tasks**:
- [ ] Read pr-description.md lines 88-96 and confirm they match the research-verified text
- [ ] Confirm no other sections of pr-description.md reference the bridge instance or need updating
- [ ] Mark task 196 as complete with completion summary

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `specs/188_first_propositional_upstream_pr/pr-description.md` - Read-only verification (no changes expected)

**Verification**:
- The Mathlib section text matches the six verified claims from research
- No stale references to bridge instances remain in pr-description.md
- Task 196 status updated to completed in state.json

## Testing & Validation

- [ ] Mathlib section (lines 88-96) matches research-verified content
- [ ] No references to "bridge instance" remain in pr-description.md (removed in prior commits)
- [ ] No Lean source files were modified (documentation-only task)

## Artifacts & Outputs

- plans/02_implementation-plan.md (this file)
- summaries/02_verification-summary.md (expected output)

## Rollback/Contingency

No rollback needed -- this plan involves verification only with no file modifications. If the Mathlib section is found to be inaccurate (contradicting research findings), revert to research phase to identify discrepancies.
