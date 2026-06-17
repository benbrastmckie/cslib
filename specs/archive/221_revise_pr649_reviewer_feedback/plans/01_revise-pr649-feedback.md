# Implementation Plan: Revise PR #649 Based on Reviewer Feedback

- **Task**: 221 - revise_pr649_reviewer_feedback
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None (PR #649 branch already rebased on upstream/main post-#536)
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/01_revise-pr649-feedback.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

PR #649 (feat/temporal-formula-propositional) requires revision based on reviewer feedback from PRs #648 and #649. The work spans six categories: removing LTL semantics (per thomaskwaring's split request), replacing 14 German-language citations across 4 Lean files with Avigad2022 and Prawitz1965, adding a new bib entry, verifying IsClassical/IsIntuitionistic consistency with merged PR #536, revising the PR description with balanced design rationale, and fixing the imp naming justification. Definition of done: all Lean files updated, `lake build` passes, PR description revised addressing all reviewer concerns.

### Research Integration

Team research (4 teammates, reports/01_team-research.md) identified that the task is more tractable than the description suggests: three of ctchou's four PR #649 objections are already addressed, the `imp` naming is correct and needs only a better justification, and bot-as-primitive has strong prior art support. Key gaps found: reference replacement scope is larger than expected (14 citations in Lean file docstrings, not just PR description), IsClassical/IsIntuitionistic definitions may be inconsistent with merged PR #536, and the and/or primitives inconsistency between Connectives.lean and actual formula types should be noted.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Remove LTL/Semantics/Satisfies.lean from PR #649 and update Cslib.lean import
- Replace all German-language references in Lean file docstrings with modern English alternatives
- Add Avigad2022 bib entry to references.bib
- Verify build consistency with merged PR #536
- Revise PR description addressing all six categories of reviewer feedback
- Justify `imp` naming with independent evidence (upstream merged code, external libraries)

**Non-Goals**:
- Resolving PR #648's merge conflict (separate task)
- Implementing the split-out LTL semantics in a follow-up PR
- Resolving the and/or primitives inconsistency between Connectives.lean and formula types
- Active coordination with fmontesi on PR #607 overlap (strategic, not blocking)
- Addressing thomaskwaring's design objections by changing the bot-as-primitive design

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| IsClassical/IsIntuitionistic inconsistency with PR #536 causes build failure | H | M | Run `lake build` early in Phase 2; if inconsistent, fix type signatures before other edits |
| Removing LTL semantics file breaks other imports | M | L | Check for transitive imports before deletion; `lake build` verifies |
| Reference replacement introduces docstring formatting errors | L | L | Review each file's docstring syntax after editing; `lake build` catches syntax errors |
| thomaskwaring rejects PR despite balanced rationale | M | M | Target ctchou as primary reviewer (supportive); thomaskwaring's buy-in desirable but not strictly required |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Remove LTL Semantics and Update References [NOT STARTED]

**Goal**: Remove the LTL semantics file per thomaskwaring's split request, replace all German-language citations with modern English alternatives, and add the Avigad2022 bib entry.

**Tasks**:
- [ ] Delete `Cslib/Logics/LTL/Semantics/Satisfies.lean` from the working tree
- [ ] Remove the corresponding import from `Cslib.lean` (the `import Cslib.Logics.LTL.Semantics.Satisfies` line)
- [ ] Check for any other files importing `Cslib.Logics.LTL.Semantics.Satisfies` and remove those imports
- [ ] Replace German references in `Cslib/Foundations/Logic/Connectives.lean` docstrings: Johansson1937 -> Avigad2022, Wajsberg1938 -> Avigad2022, Heyting1930 -> Avigad2022, Gentzen1935 -> Prawitz1965/Avigad2022
- [ ] Replace German references in `Cslib/Logics/Propositional/Defs.lean` docstrings: Johansson1937 -> Avigad2022, Gentzen1935 -> Prawitz1965/Avigad2022
- [ ] Replace German references in `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` docstrings: Johansson1937 -> Avigad2022, Gentzen1935 -> Prawitz1965/Avigad2022
- [ ] Replace German references in `Cslib/Logics/Propositional/Axioms.lean` docstrings as needed
- [ ] Add Avigad2022 entry to `references.bib` (Cambridge University Press, 2022, ISBN 978-1-108-84072-1)
- [ ] Retain German refs (Johansson1937, Gentzen1935, etc.) in references.bib as historical sources -- only remove from docstrings

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` - delete
- `Cslib.lean` - remove LTL semantics import
- `Cslib/Foundations/Logic/Connectives.lean` - replace German refs in docstrings
- `Cslib/Logics/Propositional/Defs.lean` - replace German refs in docstrings
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - replace German refs in docstrings
- `Cslib/Logics/Propositional/Axioms.lean` - replace German refs in docstrings
- `references.bib` - add Avigad2022 entry

**Verification**:
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` no longer exists
- No German-language BibKey citations remain in Lean file docstrings (grep for Johansson1937, Gentzen1935, Wajsberg1938, Heyting1930)
- Avigad2022 entry present in references.bib
- McKinsey1939 retained (English-language, not a German reference)

---

### Phase 2: Build Verification and Consistency Check [NOT STARTED]

**Goal**: Verify that the branch builds cleanly after Phase 1 changes and confirm IsClassical/IsIntuitionistic definitions are consistent with merged PR #536.

**Tasks**:
- [ ] Run `lake build` to verify the branch compiles after LTL semantics removal and reference edits
- [ ] If build errors occur related to LTL semantics imports, fix remaining transitive import references
- [ ] Inspect IsClassical/IsIntuitionistic definitions in the branch vs upstream post-#536 -- check whether theory-parameterized (old) or inference-system-based (new) definitions are used
- [ ] If inconsistency found, update the definitions to match the inference-system-based form from PR #536
- [ ] Run `lake build` again if any fixes were needed to confirm clean build
- [ ] Run `lake exe checkInitImports` to verify Cslib.Init imports
- [ ] Run `lake exe lint-style` to check style compliance

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - potentially fix IsClassical/IsIntuitionistic if inconsistent
- Any other files with build errors after Phase 1 changes

**Verification**:
- `lake build` succeeds with no errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- IsClassical/IsIntuitionistic definitions are consistent with upstream post-#536

---

### Phase 3: Revise PR Description [NOT STARTED]

**Goal**: Write a comprehensive, balanced PR description that addresses all reviewer feedback categories: stacking on #536, semantics split, bot-as-primitive rationale, imp naming justification, deferred items, and updated references.

**Tasks**:
- [ ] Draft PR description structure: summary, motivation, changes included, changes deferred, design discussion
- [ ] Document stacking relationship: PR #649 rebased on upstream/main including merged PR #536
- [ ] Note semantics split: LTL.Semantics.Satisfies removed per thomaskwaring's request, follow-up PR planned (coordinate with #587 Models typeclass)
- [ ] Write balanced bot-as-primitive rationale: (a) uniform treatment across classical/intuitionistic/minimal, (b) temporal/modal embedding where bot appears in derived definitions, (c) compatibility with CSLib's Modal formula type. Explicitly acknowledge thomaskwaring's WithBot.some point and explain how design accommodates it
- [ ] Write imp naming justification citing independent evidence: upstream merged `Propositional/Defs.lean:87` uses `imp`, FormalizedFormalLogic/Foundation uses `imp` for constructors, constructor vs derived definition distinction
- [ ] Note deferred items: LTS transitions (ctchou point 3), omega-executions, LTL semantics
- [ ] Note coordination context: PR #607 (fmontesi) logical operators, PR #587 (thomaskwaring) Models typeclass
- [ ] List updated references: German -> English replacement summary
- [ ] Acknowledge ctchou's already-addressed review points (future-only temporal operators, Encodable/Countable removal)
- [ ] Write the PR description as `specs/221_revise_pr649_reviewer_feedback/pr-description.md`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `specs/221_revise_pr649_reviewer_feedback/pr-description.md` - new file, PR description draft

**Verification**:
- PR description addresses all six categories from the task description
- Bot-as-primitive rationale acknowledges trade-offs without conceding design
- imp naming justified by independent evidence, not unmerged PRs
- All deferred items explicitly listed
- No German-language references cited in description

---

### Phase 4: Final Validation and PR Update [NOT STARTED]

**Goal**: Run the full CI verification pipeline, apply the PR description to the actual GitHub PR, and ensure everything is ready for review.

**Tasks**:
- [ ] Run full CI pipeline: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for dependency analysis
- [ ] Review all changed files for consistency and completeness
- [ ] Verify no German reference BibKeys remain in any Lean file docstrings (final grep)
- [ ] Verify LTL/Semantics/Satisfies.lean is not referenced anywhere in the codebase
- [ ] Update the actual PR #649 description on GitHub using the drafted pr-description.md content

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- No new file modifications expected (verification phase)
- GitHub PR #649 description updated via `gh` CLI

**Verification**:
- All CI checks pass: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- `lake shake` produces no unexpected dependency issues
- `grep -r "Johansson1937\|Gentzen1935\|Wajsberg1938\|Heyting1930" Cslib/` returns no matches in docstrings
- `grep -r "LTL.Semantics.Satisfies" .` returns no matches
- PR #649 description on GitHub reflects the revised content

## Testing & Validation

- [ ] `lake build` succeeds with no errors after all changes
- [ ] `lake test` passes the CslibTests suite
- [ ] `lake exe checkInitImports` verifies Cslib.Init imports
- [ ] `lake exe lint-style` passes style checks
- [ ] No German-language BibKeys in Lean file docstrings (grep verification)
- [ ] No references to deleted LTL/Semantics/Satisfies.lean anywhere in codebase
- [ ] PR description covers all six reviewer feedback categories
- [ ] Avigad2022 entry present in references.bib with correct metadata

## Artifacts & Outputs

- `specs/221_revise_pr649_reviewer_feedback/plans/01_revise-pr649-feedback.md` (this plan)
- `specs/221_revise_pr649_reviewer_feedback/pr-description.md` (PR description draft)
- Modified Lean files with updated references
- Updated `references.bib` with Avigad2022
- Updated GitHub PR #649 description

## Rollback/Contingency

- All changes are on the PR #649 feature branch; `git stash` or `git reset` can revert
- If `lake build` fails after IsClassical/IsIntuitionistic fix, the branch can be restored to pre-edit state via git
- If the bot-as-primitive rationale does not satisfy reviewers, the design itself is not changed -- only the PR description needs further revision
- German references remain in `references.bib` even after docstring removal, so no historical information is lost
