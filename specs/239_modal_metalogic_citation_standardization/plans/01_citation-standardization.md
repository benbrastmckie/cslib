# Implementation Plan: Standardize Modal/Metalogic Citations to Lean4Doc Bib Link Format

- **Task**: 239 - Standardize all citations in Modal/Metalogic to use Lean4Doc bib link format
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_citation-standardization.md
- **Artifacts**: plans/01_citation-standardization.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This plan converts approximately 50 files under `Cslib/Logics/Modal/Metalogic/` from six non-standard citation formats to the Lean4Doc bib link format already established in `StrongCompleteness.lean` files. The work is mechanical text replacement across module docstrings (`/-! ... -/`), section headers (`/-! -/`), and declaration docstrings (`/-- ... -/`). No Lean code logic changes are required. The two relevant bib keys (`Blackburn2001` and `ChagrovZakharyaschev1997`) already exist in `references.bib`.

### Research Integration

Research report `reports/01_citation-standardization.md` identified six non-standard citation format variants (F1--F6) across the codebase, catalogued all ~50 affected files with their current and target citations, and confirmed that both required bib keys exist in `references.bib`. The report provides per-file conversion tables for Soundness.lean (15 files), Completeness.lean (15 files), and infrastructure files (DeductionTheorem, MCS, DerivationTree).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task supports the "Modal metalogic" row in the Roadmap's Completed section by standardizing documentation quality across the entire `Logics/Modal/Metalogic/` module. No new roadmap items are advanced, but documentation quality is improved for existing completed components.

## Goals & Non-Goals

**Goals**:
- Convert all `## References` section citations to `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], <ref>` format
- Replace all undefined "BRV" abbreviations with `[Blackburn2001]` references
- Remove all internal `* Cslib/...` file path references from `## References` sections
- Remove all stale `* BimodalLogic/...` cross-repo references from `## References` sections
- Convert inline "Blackburn" shorthand in body text to `[Blackburn2001]` format

**Non-Goals**:
- Modifying any Lean proof code or logic
- Changing citations in files outside `Cslib/Logics/Modal/Metalogic/`
- Adding new bib entries to `references.bib`
- Reformatting `StrongCompleteness.lean` files (already correct format)
- Converting inline code comments (`-- comment` style) unless they contain BRV in docstring context

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring syntax error breaking `lake build` | M | L | Run `lake build` after each phase to catch errors early |
| Missing a non-standard citation variant | L | L | Research report catalogued all 6 variants; grep verification after each phase |
| Removing internal refs that had no literature replacement | L | L | Only remove from `## References`; internal refs are not literature and are handled by Lean4Doc imports |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Convert Soundness.lean and Completeness.lean References Sections [IN PROGRESS]

**Goal**: Convert all `## References` bullet points in the 30 Soundness/Completeness system files from plain-text format to Lean4Doc bib link format.

**Tasks**:
- [ ] Convert 15 Soundness.lean files under `Systems/{K,K4,K5,K45,KB5,T,TB,S4,S5,D,D4,D5,D45,DB,B}/Soundness.lean` -- replace F1/F2 format citations with `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], <specific-ref>`
- [ ] Convert 14 Completeness.lean files under `Systems/{K,K4,K5,K45,KB5,T,TB,S4,S5,D,D4,D5,D45,DB}/Completeness.lean` -- replace F1/F2/F3 format citations with bib link format
- [ ] Add missing `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` reference to S4/Completeness.lean and S5/Completeness.lean References sections (currently implicit)
- [ ] Convert core `Soundness.lean` References section (remove internal ref, keep/convert literature refs)
- [ ] Convert core `Completeness.lean` References section

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean` (15 files) - convert References citations
- `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean` (14 files) - convert References citations
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - convert/clean References section
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - convert/clean References section

**Verification**:
- `grep -r "Blackburn, de Rijke, Venema" Cslib/Logics/Modal/Metalogic/Systems/` returns no results in `## References` sections
- `grep -r '"Modal Logic"' Cslib/Logics/Modal/Metalogic/Systems/` returns no results (F2 variant eliminated)

---

### Phase 2: Remove Internal and Cross-Repo References [NOT STARTED]

**Goal**: Remove all `* Cslib/...` internal path references and `* BimodalLogic/...` cross-repo references from `## References` sections across all Modal/Metalogic files.

**Tasks**:
- [ ] Remove `* Cslib/...` lines from core files: `Soundness.lean`, `StrongCompleteness.lean`, `DeductionTheorem.lean`, `DerivationTree.lean`, `MCS.lean`
- [ ] Remove `* Cslib/...` lines from all 15 StrongCompleteness system files (already have correct literature citations but contain internal refs)
- [ ] Remove `* Cslib/...` lines from Soundness and Completeness system files (any remaining after Phase 1)
- [ ] Remove `* BimodalLogic/...` lines from `DeductionTheorem.lean`, `DerivationTree.lean`, `MCS.lean`
- [ ] Clean up any `## References` sections that become empty after removal (remove the section header)

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - remove internal ref
- `Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean` - remove internal ref
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - remove internal + BimodalLogic refs
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - remove internal + BimodalLogic refs
- `Cslib/Logics/Modal/Metalogic/MCS.lean` - remove internal + BimodalLogic refs
- `Cslib/Logics/Modal/Metalogic/Systems/*/StrongCompleteness.lean` (~15 files) - remove internal refs
- Additional system Soundness/Completeness files with remaining internal refs

**Verification**:
- `grep -rn "^\* Cslib/" Cslib/Logics/Modal/Metalogic/` returns no results
- `grep -rn "^\* BimodalLogic/" Cslib/Logics/Modal/Metalogic/` returns no results

---

### Phase 3: Replace BRV and Inline Blackburn References [NOT STARTED]

**Goal**: Replace all undefined "BRV" abbreviations and inline "Blackburn" shorthand with proper `[Blackburn2001]` references throughout module docstrings, section headers, and declaration docstrings.

**Tasks**:
- [ ] Replace "BRV" in module docstrings (`/-! ... -/`) of core `Completeness.lean` and system Completeness files (K, K45, T, TB) with `[Blackburn2001]`
- [ ] Replace "BRV" in section headers (`/-! ## ... -/`) of Soundness files (K, K4, S4, T, TB, K45, KB5) with `[Blackburn2001]`
- [ ] Replace "BRV" in declaration docstrings (`/-- ... -/`) and section headers of K/Completeness.lean (6 occurrences), T/Completeness.lean (4 occurrences), TB/Completeness.lean (5 occurrences)
- [ ] Replace inline "Blackburn et al." and "Blackburn" shorthand references in body text of Soundness and Completeness module docstrings with `[Blackburn2001]` format (e.g., `(Blackburn et al. Table 4.1)` becomes `([Blackburn2001] Table 4.1)`)
- [ ] Handle the one inline code comment at K/Completeness.lean:111 -- replace "BRV" with `[Blackburn2001]` since no file defines the abbreviation

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - replace BRV in docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` - replace BRV (3 occurrences) + inline Blackburn refs
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Completeness.lean` - replace BRV
- `Cslib/Logics/Modal/Metalogic/Systems/T/Completeness.lean` - replace BRV + inline refs
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Completeness.lean` - replace BRV + inline refs
- `Cslib/Logics/Modal/Metalogic/Systems/K/Soundness.lean` - replace BRV in section header
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Soundness.lean` - replace BRV in section header
- `Cslib/Logics/Modal/Metalogic/Systems/S4/Soundness.lean` - replace BRV in section header
- `Cslib/Logics/Modal/Metalogic/Systems/T/Soundness.lean` - replace BRV in section header
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Soundness.lean` - replace BRV in section header
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Soundness.lean` - replace BRV in section header
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Soundness.lean` - replace BRV in section header
- Various Soundness/Completeness files with inline "Blackburn" shorthand in body text (~10 files)

**Verification**:
- `grep -rn "BRV" Cslib/Logics/Modal/Metalogic/` returns no results
- `grep -rn "(Blackburn " Cslib/Logics/Modal/Metalogic/` returns no results (inline shorthand eliminated)
- `grep -rn "Blackburn et al\." Cslib/Logics/Modal/Metalogic/` returns no results

---

### Phase 4: Build Verification and Final Audit [NOT STARTED]

**Goal**: Verify that all changes compile cleanly and that no non-standard citations remain.

**Tasks**:
- [ ] Run `lake build` to verify no docstring syntax errors were introduced
- [ ] Run comprehensive grep audit for remaining non-standard citations:
  - `grep -rn "Blackburn, de Rijke" Cslib/Logics/Modal/Metalogic/` (F1/F2/F3 remnants)
  - `grep -rn '"Modal Logic"' Cslib/Logics/Modal/Metalogic/` (F2 remnants)
  - `grep -rn "BRV" Cslib/Logics/Modal/Metalogic/` (F5 remnants)
  - `grep -rn "BimodalLogic/" Cslib/Logics/Modal/Metalogic/` (F6 remnants)
  - `grep -rn "^\* Cslib/" Cslib/Logics/Modal/Metalogic/` (internal refs)
- [ ] Verify all `[Blackburn2001]` and `[ChagrovZakharyaschev1997]` references use correct bib key spelling
- [ ] Spot-check 3-5 converted files against the StrongCompleteness.lean exemplar format

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3

**Files to modify**: None (verification only; fixes applied in earlier phases if issues found)

**Verification**:
- `lake build` succeeds with no errors
- All audit greps return zero results for non-standard patterns
- Spot-checked files match the exemplar format exactly

## Testing & Validation

- [ ] `lake build` passes with no errors after all phases
- [ ] Zero remaining instances of plain-text Blackburn/Chagrov citations in `## References` sections
- [ ] Zero remaining "BRV" occurrences in any docstring or section header
- [ ] Zero remaining `* Cslib/...` or `* BimodalLogic/...` lines in `## References` sections
- [ ] All `[Blackburn2001]` references use the correct bib key (not `Blackburn2002` or other variants)
- [ ] StrongCompleteness.lean files remain unchanged (already correct)

## Artifacts & Outputs

- `specs/239_modal_metalogic_citation_standardization/plans/01_citation-standardization.md` (this plan)
- `specs/239_modal_metalogic_citation_standardization/summaries/01_citation-standardization-summary.md` (post-implementation)
- ~50 modified `.lean` files under `Cslib/Logics/Modal/Metalogic/`

## Rollback/Contingency

All changes are docstring-only text replacements with no logic impact. If any phase introduces build errors, the specific file edits can be reverted with `git checkout -- <file>` since no code changes are interleaved. The entire changeset can be reverted with `git revert` on the task commit(s).
