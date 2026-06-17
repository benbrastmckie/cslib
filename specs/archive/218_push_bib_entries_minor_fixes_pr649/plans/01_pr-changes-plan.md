# Implementation Plan: Task #218

- **Task**: 218 - Push missing bib entries and minor fixes to PR #649
- **Status**: [IMPLEMENTING]
- **Effort**: 0.5 hours
- **Dependencies**: PR #649 branch (feat/temporal-formula-propositional) must be checked out
- **Research Inputs**: specs/218_push_bib_entries_minor_fixes_pr649/reports/01_pr-changes-research.md
- **Artifacts**: plans/01_pr-changes-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Restore 7 missing BibTeX entries and the architecture docstring to PR #649's branch. Research confirmed that the Gamma-to-G rename and copyright date updates are already present on the PR branch, so only two changes remain: (1) add 7 bib entries to `references.bib` that exist on main but were lost when the PR branch forked, and (2) restore the `## Architecture` docstring section in `Defs.lean`.

### Research Integration

Key findings from the research report:
- All 7 bib entries (Church1956, Gentzen1935, Johansson1937, McKinsey1939, Prawitz1965, TroelstraVanDalen1988, Wajsberg1938) exist on main but are absent from the PR branch
- The `## Architecture` section was removed from `Defs.lean` on the PR branch and needs restoration
- The Gamma-to-G rename in NaturalDeduction/Basic.lean is already done -- no work needed
- Copyright date updates are already done -- no work needed

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly addressed by this task (PR maintenance task).

## Goals & Non-Goals

**Goals**:
- Restore 7 missing bib entries to `references.bib` on the PR branch in alphabetical order
- Restore the `## Architecture` docstring section in `Defs.lean` on the PR branch

**Non-Goals**:
- Addressing `ChagrovZakharyaschev1997` or `Heyting1930` removal (these are out of scope for this task; PR #648 should carry them)
- Modifying any Lean proof code
- Any changes to NaturalDeduction/Basic.lean (Gamma rename already complete)
- Any copyright header changes (already complete)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Merge conflicts in references.bib | M | L | Entries are alphabetically ordered; conflicts are trivial to resolve |
| Docstring placement incorrect in Defs.lean | L | L | Research report identifies exact placement: after `## Main definitions`, before `## Notation` |
| ChagrovZakharyaschev1997 / Heyting1930 still needed | M | M | Verify PR #648 carries them; flag if not |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Restore 7 Bib Entries [NOT STARTED]

**Goal**: Add the 7 missing BibTeX entries to `references.bib` on the PR branch

**Tasks**:
- [ ] Checkout `feat/temporal-formula-propositional` branch
- [ ] Extract the 7 bib entries from main's `references.bib` (Church1956, Gentzen1935, Johansson1937, McKinsey1939, Prawitz1965, TroelstraVanDalen1988, Wajsberg1938)
- [ ] Insert each entry into the PR branch's `references.bib` in correct alphabetical position
- [ ] Verify all 7 entries are present and correctly formatted

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` - Add 7 missing BibTeX entries in alphabetical order

**Verification**:
- `grep -c 'Church1956\|Gentzen1935\|Johansson1937\|McKinsey1939\|Prawitz1965\|TroelstraVanDalen1988\|Wajsberg1938' references.bib` returns 7

---

### Phase 2: Restore Architecture Docstring [NOT STARTED]

**Goal**: Restore the `## Architecture` section in `Defs.lean`'s module docstring

**Tasks**:
- [ ] Read the `## Architecture` section content from main's `Cslib/Logics/Propositional/Defs.lean`
- [ ] Insert the section into the PR branch's `Defs.lean` module docstring after `## Main definitions` and before `## Notation`
- [ ] Verify the docstring is correctly placed

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Restore `## Architecture` docstring section

**Verification**:
- `grep -c 'Architecture' Cslib/Logics/Propositional/Defs.lean` returns at least 1
- `lake build Cslib.Logics.Propositional.Defs` compiles without errors

## Testing & Validation

- [ ] All 7 bib entries present in `references.bib` on PR branch
- [ ] Architecture section present in Defs.lean module docstring
- [ ] `lake build` succeeds for affected modules
- [ ] No unintended changes to other files

## Artifacts & Outputs

- plans/01_pr-changes-plan.md (this file)
- Modified `references.bib` with 7 restored entries
- Modified `Cslib/Logics/Propositional/Defs.lean` with restored architecture docstring

## Rollback/Contingency

Git revert the commit on the PR branch. All changes are additive (inserting entries and docstring), so reverting is straightforward.
