# Implementation Plan: Task #199 -- PR Citation Review

- **Task**: 199 - Review PR citations for accuracy and completeness
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/199_review_pr_citations/reports/01_pr-citation-review.md
- **Artifacts**: plans/01_pr-citation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This task adds verified citations to Lean source files and supporting documents for the propositional logic PR (task 198). Research identified two missing BibTeX entries (Bentzen2023, Trufas2024), one invented label in `Defs.lean` ("full-connective tradition"), and a minor pronoun error in the PR description. All changes are docstring-level or bibliographic -- no proof code is modified. The task is complete when `references.bib` has both new entries, the Defs.lean docstring is grounded in verified literature, the PR description pronoun is fixed, and `lake build` passes.

### Research Integration

The research report (01_pr-citation-review.md) verified all existing citations against primary sources in `specs/literature/`. Key findings integrated into this plan:
- Bentzen2023 and Trufas2024 citations in PR description are accurate but lack `references.bib` entries
- "full-connective tradition" in Defs.lean line 21 is an invented label with no literature precedent
- Johansson1937 quotes are accurate (with standard notation modernization)
- Church1956 placement is tangential but acceptable as-is (low priority, no action required)
- All 10 existing Lean-source BibKeys are present and complete in references.bib

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add Bentzen2023 and Trufas2024 BibTeX entries to `references.bib`
- Replace the invented "full-connective tradition" label in `Defs.lean` with literature-grounded language
- Fix "his" to "their" in PR description line 55 (Bentzen2023 has three authors)
- Ensure `lake build` passes after all Lean file changes
- Update `pr-description.md` to reflect any citation changes in Lean files

**Non-Goals**:
- Adding BibTeX entries for future roadmap references (Post1921, Henkin1949, Tarski1930, Godel1930, FromJacobsen2022)
- Modifying Church1956 placement in reference blocks (acceptable as-is)
- Adding new inline citations beyond what the research verified
- Modifying any proof code or theorem statements

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| BibTeX entry formatting mismatch with existing style | L | L | Use existing entries as template; match indentation, field ordering |
| Defs.lean docstring edit breaks Lean doc parser | M | L | Run `lake build` after edit to verify |
| Incorrect BibTeX fields (e.g., wrong DOI or page numbers) | M | L | Cross-check against primary sources in specs/literature/ |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Add BibTeX Entries to references.bib [COMPLETED]

**Goal**: Add verified Bentzen2023 and Trufas2024 entries to `references.bib` in alphabetical order, matching the existing entry style.

**Tasks**:
- [ ] Read `specs/literature/bentzen_2023.md` to verify author names, title, publication venue, year, and DOI
- [ ] Read `specs/literature/trufas_2024.md` to verify author name, title, publication venue, year, and DOI
- [ ] Cross-check drafted entries from `specs/192_research_verify_literature_refs_pr_188/reports/02_teammate-b-findings.md` against primary sources
- [ ] Add `@inproceedings{Bentzen2023, ...}` entry to `references.bib` in alphabetical position (after AngluinLaird1988, before Blackburn2001)
- [ ] Add `@inproceedings{Trufas2024, ...}` entry to `references.bib` in alphabetical position (after TroelstraVanDalen1988, before any entry starting with U or later)
- [ ] Verify entry formatting matches existing style (2-space indent, field ordering, DOI format)

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` - Add two new BibTeX entries

**Verification**:
- Both entries present in `references.bib` with correct BibKeys
- Entries are in alphabetical order within the file
- Fields match primary source data (author, title, year, DOI)

---

### Phase 2: Fix Defs.lean Docstring [COMPLETED]

**Goal**: Replace the invented "full-connective tradition" label at line 21 of `Defs.lean` with literature-grounded language that properly credits Johansson1937 and uses only verifiable claims.

**Tasks**:
- [ ] Read current docstring in `Cslib/Logics/Propositional/Defs.lean` lines 15-68
- [ ] Replace lines 19-23 (the paragraph containing "full-connective tradition") with the research-recommended replacement text that references Gentzen1935, Prawitz1965, Johansson1937, and TroelstraVanDalen1988 with proper context
- [ ] Verify the replacement text does not introduce any citation not already in the References section of the same file
- [ ] Run `lake build Cslib.Logics.Propositional.Defs` to verify the docstring change does not break compilation

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Replace invented label in module docstring (lines 19-23)

**Verification**:
- "full-connective tradition" no longer appears in the file
- Replacement text references only BibKeys that exist in the file's References section and in `references.bib`
- `lake build Cslib.Logics.Propositional.Defs` succeeds

---

### Phase 3: Update PR Description and Final Verification [COMPLETED]

**Goal**: Fix the pronoun error in the PR description, ensure PR description reflects the updated Lean file citations, and run final build verification.

**Tasks**:
- [ ] In `specs/198_submit_propositional_upstream_pr/pr-description.md`, change "his Lean formalization" to "their Lean formalization" at line 55-56
- [ ] Review the PR description to ensure it is consistent with the updated Defs.lean docstring (no references to "full-connective tradition")
- [ ] Run `lake build` (full project) as final verification that all changes compile cleanly

**Timing**: 20 minutes

**Depends on**: 2

**Files to modify**:
- `specs/198_submit_propositional_upstream_pr/pr-description.md` - Fix pronoun "his" to "their" (line 55-56)

**Verification**:
- "his Lean formalization" no longer appears in the PR description
- PR description is consistent with updated Lean file citations
- `lake build` succeeds (full project)

## Testing & Validation

- [ ] `lake build` passes after all changes
- [ ] `grep -c 'Bentzen2023' references.bib` returns 1
- [ ] `grep -c 'Trufas2024' references.bib` returns 1
- [ ] `grep 'full-connective' Cslib/Logics/Propositional/Defs.lean` returns no results
- [ ] `grep 'his Lean formalization' specs/198_submit_propositional_upstream_pr/pr-description.md` returns no results
- [ ] All BibKeys referenced in Lean file docstrings have corresponding entries in `references.bib`

## Artifacts & Outputs

- `references.bib` - Updated with Bentzen2023 and Trufas2024 entries
- `Cslib/Logics/Propositional/Defs.lean` - Fixed docstring (no proof changes)
- `specs/198_submit_propositional_upstream_pr/pr-description.md` - Fixed pronoun
- `specs/199_review_pr_citations/plans/01_pr-citation-plan.md` - This plan

## Rollback/Contingency

All changes are in documentation and bibliography -- no proof code is modified. If any change causes issues:
- `git checkout -- references.bib` to revert BibTeX additions
- `git checkout -- Cslib/Logics/Propositional/Defs.lean` to revert docstring
- `git checkout -- specs/198_submit_propositional_upstream_pr/pr-description.md` to revert PR description
