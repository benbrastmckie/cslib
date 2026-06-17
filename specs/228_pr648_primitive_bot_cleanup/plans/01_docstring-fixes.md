# Implementation Plan: Task #228

- **Task**: 228 - PR #648 primitive bot cleanup
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None (PR #648 branch must be checked out)
- **Research Inputs**: reports/01_pr648-review-findings.md
- **Artifacts**: plans/01_docstring-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix two documentation issues in PR #648 (feat/propositional-v2) identified during review. The `intuitionisticCompletion` docstring incorrectly says "Attach a bottom element" when bot is now a primitive constructor, and the `Connectives.lean` module docstring conflates generators with operations by saying "five-primitive propositional signature" instead of "five constructors." Both are single-line text edits with no code changes.

### Research Integration

The research report (01_pr648-review-findings.md) identified exactly two documentation issues and confirmed all other PR changes are correctly aligned. Finding 1 concerns misleading language about "attaching" bot when it is already a constructor. Finding 2 concerns algebraic terminology that conflates generators with signature operations. Both have precise recommended replacement text.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

Not assessed -- this is a minor docstring cleanup task within an existing PR and does not advance any roadmap items.

## Goals & Non-Goals

**Goals**:
- Update `intuitionisticCompletion` docstring to reflect primitive bot semantics
- Fix "five-primitive propositional signature" terminology in `Connectives.lean`
- Pass CI verification after edits

**Non-Goals**:
- Simplifying `intuitionisticCompletion` implementation (removing `WithBot` wrapper)
- Changing any Lean code or proofs
- Addressing any issues beyond the two identified docstring problems

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring change breaks line-length lint | L | L | Check `lake exe lint-style` output |
| Wrong branch checked out | H | L | Verify branch before editing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Fix intuitionisticCompletion Docstring [COMPLETED]

**Goal**: Replace the misleading "Attach a bottom element" docstring with text that accurately describes the function's behavior under primitive bot.

**Tasks**:
- [ ] Open `Cslib/Logics/Propositional/Defs.lean`
- [ ] Locate the `intuitionisticCompletion` definition docstring
- [ ] Replace the docstring with: `/-- Extend a theory T to an intuitionistic theory over a larger atom type by adding the principle of explosion. The atom type is extended with WithBot to ensure the result is over a strictly larger language. -/`

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Replace docstring on `intuitionisticCompletion`

**Verification**:
- Docstring no longer mentions "Attach a bottom element"
- New text accurately describes atom type extension and explosion principle

---

### Phase 2: Fix Connectives.lean Signature Terminology [COMPLETED]

**Goal**: Replace "five-primitive propositional signature" with "five constructors" to avoid conflating generators with algebraic operations.

**Tasks**:
- [ ] Open `Cslib/Foundations/Logic/Connectives.lean`
- [ ] Locate the module docstring containing "five-primitive propositional signature"
- [ ] Change "five-primitive propositional signature" to "five constructors"

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - Fix terminology in module docstring

**Verification**:
- Docstring no longer says "signature" in reference to constructors
- New text says "five constructors" which accurately describes the Lean inductive type

---

### Phase 3: CI Verification [COMPLETED]

**Goal**: Confirm that docstring-only changes pass the full CI pipeline.

**Tasks**:
- [ ] Run `lake build` to verify no build errors
- [ ] Run `lake exe lint-style` to check style compliance
- [ ] Run `lake exe checkInitImports` to verify import consistency

**Timing**: 15 minutes

**Depends on**: 1, 2

**Files to modify**:
- None (verification only)

**Verification**:
- All CI commands exit with code 0
- No new warnings or errors introduced

## Testing & Validation

- [ ] `lake build` passes without errors
- [ ] `lake exe lint-style` passes without warnings on modified files
- [ ] `lake exe checkInitImports` passes
- [ ] Manual review confirms docstrings are accurate and clear

## Artifacts & Outputs

- `specs/228_pr648_primitive_bot_cleanup/plans/01_docstring-fixes.md` (this plan)
- Modified: `Cslib/Logics/Propositional/Defs.lean` (docstring)
- Modified: `Cslib/Foundations/Logic/Connectives.lean` (docstring)

## Rollback/Contingency

Revert with `git checkout -- Cslib/Logics/Propositional/Defs.lean Cslib/Foundations/Logic/Connectives.lean` to restore original docstrings.
