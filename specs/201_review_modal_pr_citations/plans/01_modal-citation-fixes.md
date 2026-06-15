# Implementation Plan: Fix Modal PR Citation Errors

- **Task**: 201 - Review modal PR citations
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None (task 197 PR not yet submitted; fixes apply to current main)
- **Research Inputs**: reports/01_modal-citation-review.md
- **Artifacts**: plans/01_modal-citation-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Research identified two classes of citation error in the Modal/ and Foundations/Logic/ docstrings: (1) four occurrences of `[ChagrovZakharyaschev1997] Section 1.1` that should read `Section 3.1` (Section 1.1 covers classical propositional logic; the modal language with box as primitive is defined in Section 3.1), and (2) two docstrings that cite `[Blackburn2001] Chapter 1` as evidence that box is the canonical primitive, when in fact Blackburn Definition 1.9 uses diamond as primitive. All changes are to Lean 4 doc-comments only -- no proof code is modified. Done when all six citation sites are corrected, `lake build` passes, and `lake exe lint-style` reports no new issues.

### Research Integration

Key findings from report 01_modal-citation-review.md:
- ChagrovZakharyaschev1997 Section 1.1 is classical propositional logic; modal box is defined in Section 3.1
- Blackburn2001 Chapter 1 Definition 1.9 defines diamond as primitive, box as derived
- Both conventions (box-first, diamond-first) are widespread; neither is universally "canonical"
- Research recommends option (c): acknowledge both conventions, cite Chagrov for box-first, cite Blackburn for the duality
- Connectives.lean line 53 has a separate "Chapter 1" reference to ChagrovZakharyaschev that should be "Chapter 3"

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task maintains documentation quality for the Modal/ module listed in the ROADMAP under the completed "Modal metalogic" component. No roadmap items are directly advanced.

## Goals & Non-Goals

**Goals**:
- Fix all four `Section 1.1` -> `Section 3.1` references for ChagrovZakharyaschev1997
- Fix the `Chapter 1` -> `Chapter 3` reference for ChagrovZakharyaschev1997 in Connectives.lean line 53
- Reword Blackburn2001 attribution to accurately reflect that Blackburn uses diamond as primitive while CSLib follows the box-first convention of Chagrov & Zakharyaschev
- Verify build and style lint pass after all edits

**Non-Goals**:
- Adding new citations (e.g., Burgess1984 for tense logic roadmap) -- out of scope for this task
- Modifying any proof code or definitions
- Changing BibTeX entries in references.bib (all entries are already correct)
- Adding citations to Denotation.lean (research confirmed none are needed)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring edit breaks Lean 4 doc-comment syntax | M | L | Run `lake build` after each file edit |
| Rewording Blackburn attribution introduces inaccuracy | M | L | Follow research recommendation (c) precisely; cross-check against literature files |
| Style lint failures from line-length changes | L | M | Check `lake exe lint-style` after edits; wrap lines at 100 chars |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Fix All Citation Errors [NOT STARTED]

**Goal**: Correct all six citation sites across Basic.lean and Connectives.lean.

**Tasks**:
- [ ] Edit `Cslib/Logics/Modal/Basic.lean` lines 29-30: Reword the Blackburn/Chagrov citation block. Replace the claim that box is "the canonical primitive modal operator ... following [Blackburn2001] Chapter 1 and [ChagrovZakharyaschev1997] Section 1.1" with wording that acknowledges both conventions. Suggested replacement: "Box and diamond are interdefinable in classical modal logic ([Blackburn2001] Chapter 1). CSLib adopts box as primitive following [ChagrovZakharyaschev1997] Section 3.1, where box is the primitive modal connective."
- [ ] Edit `Cslib/Logics/Modal/Basic.lean` lines 94-95: Change `[ChagrovZakharyaschev1997] Section 1.1` to `[ChagrovZakharyaschev1997] Section 3.1` in the diamond docstring. Also update the Blackburn reference to note the duality rather than claiming box primacy.
- [ ] Edit `Cslib/Foundations/Logic/Connectives.lean` lines 72-73 (HasBox docstring): Reword to match the corrected attribution pattern. Change `[ChagrovZakharyaschev1997] Section 1.1` to `Section 3.1` and clarify the Blackburn citation.
- [ ] Edit `Cslib/Foundations/Logic/Connectives.lean` line 53: Change `Chapter 1` to `Chapter 3` in the module-level references list for ChagrovZakharyaschev1997.
- [ ] Edit `Cslib/Foundations/Logic/Connectives.lean` lines 112-113 (ModalConnectives docstring): Change `[ChagrovZakharyaschev1997] Section 1.1` to `Section 3.1` and update the Blackburn reference.

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - Fix 2 citation blocks (module docstring lines 28-30, diamond docstring lines 94-95)
- `Cslib/Foundations/Logic/Connectives.lean` - Fix 3 citation sites (HasBox docstring line 72, module references line 53, ModalConnectives docstring line 112)

**Verification**:
- Each edited docstring cites `Section 3.1` (not `Section 1.1`) for ChagrovZakharyaschev1997
- Blackburn2001 is cited for the box/diamond duality, not as evidence of box-as-primitive
- `lake build Cslib.Logics.Modal.Basic` and `lake build Cslib.Foundations.Logic.Connectives` both pass

---

### Phase 2: Build Verification and Style Lint [NOT STARTED]

**Goal**: Verify all changes compile and pass CSLib CI checks.

**Tasks**:
- [ ] Run `lake build` (full project build) to verify no compilation breakage
- [ ] Run `lake exe lint-style` to verify no style violations from rewording (line length, trailing whitespace)
- [ ] If lint-style reports issues, fix line wrapping and re-run
- [ ] Spot-check that all 5 edit sites have correct text by grepping for remaining `Section 1.1` references

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- None expected (verification only); may need minor line-wrapping fixes in the two edited files

**Verification**:
- `lake build` exits 0
- `lake exe lint-style` exits 0
- `grep -rn "Section 1.1" Cslib/Logics/Modal/ Cslib/Foundations/Logic/Connectives.lean` returns no results
- `grep -rn "Chapter 1" Cslib/Foundations/Logic/Connectives.lean` returns no results referencing ChagrovZakharyaschev

## Testing & Validation

- [ ] `lake build` passes with zero errors
- [ ] `lake exe lint-style` passes with zero new violations
- [ ] No remaining `Section 1.1` references to ChagrovZakharyaschev1997 in Modal/ or Connectives.lean
- [ ] No remaining claim that Blackburn2001 Chapter 1 uses box as primitive
- [ ] Connectives.lean references list cites `Chapter 3` (not `Chapter 1`) for ChagrovZakharyaschev1997

## Artifacts & Outputs

- `specs/201_review_modal_pr_citations/plans/01_modal-citation-fixes.md` (this plan)
- `specs/201_review_modal_pr_citations/summaries/01_modal-citation-fixes-summary.md` (after implementation)

## Rollback/Contingency

All changes are to doc-comments only with no proof modifications. If any edit causes unexpected build failures, revert with `git checkout -- Cslib/Logics/Modal/Basic.lean Cslib/Foundations/Logic/Connectives.lean`.
