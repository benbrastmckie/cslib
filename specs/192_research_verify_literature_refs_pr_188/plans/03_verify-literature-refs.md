# Implementation Plan: Task #192

- **Task**: 192 - Research verify literature refs PR 188
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md, reports/02_team-research.md
- **Artifacts**: plans/03_verify-literature-refs.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

This plan addresses verified literature citation issues across three surfaces: `references.bib`, Lean source file docstrings, and the PR description for task 188. Two rounds of team research (4 teammates each) identified 7 specific citation problems ranging from critical (misleading Church section 24 attribution, missing McKinsey 1939 citation) to low severity (tangential references in reference blocks). The implementation edits concrete text in 5 files, adds 7 BibTeX entries, and updates the literature README, with a final `lake build` verification to confirm docstring changes do not break compilation.

### Research Integration

Round 1 (01_team-research.md) established claim verification across 7 literature claims with verdicts and recommended replacement text. Round 2 (02_team-research.md) verified claims against full-content primary source markdown conversions and produced: (1) exact replacement text for 7 PR description sections, (2) 7 drafted BibTeX entries, (3) a recommended Defs.lean docstring fix, and (4) sources.md file-availability updates. All Round 1 findings were confirmed and strengthened by Round 2 primary source verification.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Fix misleading/inaccurate literature claims in PR description (Church section 24 scope, Gentzen/Prawitz "imp" attribution, "superset of PR #607" framing)
- Add missing McKinsey 1939 citation to the "Why bot Should Be Primitive" section
- Add 7 new BibTeX entries to references.bib for sources cited in research/sources.md but missing from the bibliography
- Replace the invented "full-connective tradition" label in Defs.lean with accurate attribution
- Update sources.md file-availability markers for 4 entries
- Maintain compilation: all docstring changes must pass `lake build`

**Non-Goals**:
- Rewriting proof code or modifying any Lean definitions/theorems
- Adding new Lean files or changing the Cslib.lean barrel import
- Verifying TroelstraVanDalen1988 section references (book unavailable locally)
- Changing citations in files outside the PR 188 scope (Equivalence.lean, Axioms.lean, Derivation.lean are not modified)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring edits break Lean parsing | H | L | Run `lake build` on affected modules after each edit; doc-comments are whitespace-sensitive only around `/-!` delimiters |
| BibTeX entry formatting inconsistent with existing entries | M | L | Follow the exact formatting style of existing entries in references.bib (field ordering, indentation, escape conventions) |
| PR description changes misrepresent the author's intent | M | M | Changes are strictly accuracy corrections from verified primary sources; preserve the original argumentative structure |
| Research report recommendations contain errors | M | L | Both rounds confirmed findings independently across 4 teammates each; cross-check any questionable recommendation against the primary source .md files in specs/literature/ |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Update references.bib with new BibTeX entries [NOT STARTED]

**Goal**: Add 7 missing BibTeX entries for sources cited in the research reports and sources.md but absent from references.bib.

**Tasks**:
- [ ] Read current references.bib to confirm which 7 entries are still missing (Bentzen2023, Trufas2024, Post1921, Henkin1949, Tarski1930, Godel1930, FromJacobsen2022)
- [ ] Add each entry following the formatting conventions of existing entries: field ordering (author, title, journal/booktitle, volume, number, pages, year, doi/url), consistent indentation (2-space), proper LaTeX escaping for special characters
- [ ] Maintain alphabetical ordering by BibKey (the file currently uses approximate alphabetical order)
- [ ] Verify all 7 new entries have complete bibliographic data as drafted in Round 2 Teammate B findings

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` -- add 7 new entries: Bentzen2023, Trufas2024, Post1921, Henkin1949, Tarski1930, Godel1930, FromJacobsen2022

**Verification**:
- All 7 BibKeys present in references.bib
- No duplicate entries
- Entries follow existing formatting conventions
- File parses correctly (no BibTeX syntax errors)

---

### Phase 2: Update Lean source file docstrings [NOT STARTED]

**Goal**: Fix the inaccurate "full-connective tradition" label in Defs.lean and ensure all reference blocks in PR 188 scope files are accurate.

**Tasks**:
- [ ] In `Cslib/Logics/Propositional/Defs.lean` lines 19-22: replace "following the standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition" with accurate wording per Round 2 Teammate C recommendation: reference natural deduction style ([Gentzen1935], [Prawitz1965]) and the constructive mathematics tradition ([Johansson1937], [TroelstraVanDalen1988]) where negation abbreviates implication-to-falsum
- [ ] In `Cslib/Logics/Propositional/Defs.lean` reference block (lines 59-67): add McKinsey1939 and Wajsberg1938 entries (these are cited in the companion file Connectives.lean and should be listed here for completeness, since Defs.lean discusses the five-primitive design)
- [ ] In `Cslib/Foundations/Logic/Connectives.lean`: verify reference block (lines 42-53) is already correct -- it already cites McKinsey, Wajsberg, Heyting, Johansson, Prawitz, TroelstraVanDalen, Church, Gentzen, Chagrov. No changes expected
- [ ] In `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`: verify reference block (lines 56-63) is accurate -- it cites Johansson, Prawitz, TroelstraVanDalen Section 10.4, Gentzen. No changes expected
- [ ] Run `lake build Cslib.Logics.Propositional.Defs` to verify docstring changes compile

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` -- lines 19-22 (description text), lines 59-67 (reference block)

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` succeeds
- No invented labels ("full-connective tradition") remain in docstrings
- McKinsey1939 and Wajsberg1938 appear in Defs.lean reference block

---

### Phase 3: Revise pr-description.md for accuracy and conciseness [NOT STARTED]

**Goal**: Apply the 7 priority revisions from Round 2 Teammate D to fix misleading claims, remove false attributions, and improve diplomatic framing.

**Tasks**:
- [ ] Priority 1 (CRITICAL): In "Why bot Should Be Primitive" section (lines 48-53), replace the Church section 24 citation paragraph. Lead with McKinsey 1939 independence proof, demote Church section 24 to a general reference for primitive connective choice, add Prawitz alongside TroelstraVanDalen
- [ ] Priority 2 (HIGH): In "Summary" bullet 2 (line 20), replace "standard notation per Gentzen/Prawitz" with CSLib internal consistency argument ("matching CSLib's existing convention in Bimodal and Temporal formula types, and aligning constructor names with rule name prefixes: impI/impE, cf. andI/andE1, orI1/orE")
- [ ] Priority 3 (HIGH): Rewrite "Naming: imp vs impl" section (lines 55-59). Replace "no major proof theory reference uses this abbreviation" (false -- Bentzen 2023 uses `impl`) with the positive CSLib-uniformity argument
- [ ] Priority 4 (MEDIUM): In "Relationship to PR #607" section (line 69), replace "Our PR is a superset of PR #607" with "Our Connectives.lean builds on the per-operator typeclass direction of PR #607" and add merge coordination language
- [ ] Priority 5 (MEDIUM): Add new "Relationship to PR #536" section acknowledging overlapping file modifications with merge coordination offer
- [ ] Priority 6 (MEDIUM): In "AI Tools Used" section (lines 109-112), add human verification statement: "The mathematical content, proof architecture, and design decisions were verified by the author. All Lean code compiles with no sorries."
- [ ] Priority 7 (LOW): In "Contribution Roadmap" section (line 85), soften "mirrors the structure of" to "draws from" for TroelstraVanDalen Chapter 2

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `specs/188_first_propositional_upstream_pr/pr-description.md` -- 7 sections revised

**Verification**:
- No claims about "standard notation per Gentzen/Prawitz" remain
- No "superset of PR #607" language remains
- McKinsey 1939 is cited in the "Why bot Should Be Primitive" section
- Church section 24 is qualified as a general (classical) reference, not as supporting the five-primitive intuitionistic design
- "imp vs impl" section uses CSLib-internal consistency argument, not false historical claims
- AI disclosure includes human verification statement
- PR #536 acknowledged

---

### Phase 4: Update sources.md and final verification [NOT STARTED]

**Goal**: Update file-availability markers in sources.md and run final build verification across all modified files.

**Tasks**:
- [ ] In `specs/literature/README.md`: update Gentzen 1935 from `[PDF]` to `[PDF] [MD]` (markdown conversion exists)
- [ ] In `specs/literature/README.md`: update Church 1956 from `[NO FILE]` to `[MD]` (church_1956.md exists)
- [ ] In `specs/literature/README.md`: update Trufas 2024 from `[PDF]` to `[PDF] [MD]` (trufas_2024.md exists)
- [ ] In `specs/literature/README.md`: update Mendelson 2016 from `[NO FILE]` to `[MD]` (mendelson_2016.md exists)
- [ ] Run `lake build Cslib.Logics.Propositional.Defs` and `lake build Cslib.Foundations.Logic.Connectives` to confirm all Lean files compile after docstring changes
- [ ] Spot-check that all BibKeys cited in the modified Lean files exist in references.bib

**Timing**: 30 minutes

**Depends on**: 2, 3

**Files to modify**:
- `specs/literature/README.md` -- 4 availability marker updates

**Verification**:
- `lake build` succeeds on all modified Lean modules
- All availability markers match actual file existence in specs/literature/
- Every BibKey referenced in modified files has a corresponding entry in references.bib

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Defs` compiles without errors
- [ ] `lake build Cslib.Foundations.Logic.Connectives` compiles without errors
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` compiles without errors (if modified)
- [ ] All 7 new BibTeX entries present in references.bib with correct formatting
- [ ] No invented labels ("full-connective tradition", "standard notation per Gentzen/Prawitz") remain in any modified file
- [ ] McKinsey 1939 cited in both Defs.lean reference block and pr-description.md "Why bot" section
- [ ] pr-description.md contains no factually false claims per research findings
- [ ] specs/literature/README.md availability markers match filesystem reality

## Artifacts & Outputs

- `references.bib` -- 7 new entries added
- `Cslib/Logics/Propositional/Defs.lean` -- docstring corrected
- `specs/188_first_propositional_upstream_pr/pr-description.md` -- 7 sections revised
- `specs/literature/README.md` -- 4 availability markers updated
- `specs/192_research_verify_literature_refs_pr_188/plans/03_verify-literature-refs.md` -- this plan

## Rollback/Contingency

All changes are to documentation (docstrings, BibTeX, markdown). If any change causes a `lake build` failure, the offending docstring edit can be reverted independently. No Lean code is modified, so there is no risk of breaking proofs or definitions. Git revert of individual commits is sufficient for rollback.
