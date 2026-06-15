# Implementation Plan: Draft PR description for Modal/ upstream refactoring

- **Task**: 197 - Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: PR #648 (`feat/propositional-v2`, OPEN) for Connectives.lean foundation
- **Research Inputs**: reports/01_modal-upstream-pr-scope.md, reports/02_literature-grounded-analysis.md, reports/03_team-research.md, reports/04_pr649-comparison-classical-signature.md, reports/06_modal-pr-landscape.md
- **Artifacts**: plans/08_modal-upstream-pr-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr

## Overview

Prepare a `pr-description.md` artifact for the Modal/ upstream PR that refactors `Modal/Proposition` from the `{atom, not, and, diamond}` signature to `{atom, bot, imp, box}`, stacking on PR #648 (`feat/propositional-v2`). The PR description must diplomatically coordinate with PRs #607, #648, #649, #528, and #535, using a tone modeled on PR #648's description -- structured, literature-backed, and courteous toward fmontesi's foundational work. The plan is defined as done when `specs/197_modal_upstream_initial_pr/pr-description.md` is written, reviewed for quality, and the task transitions to [PR READY]. Branch creation, code changes, CI verification, and PR submission happen separately via `/pr`.

### Research Integration

Five research reports inform this plan (version 5):

- **Report 01** (01_modal-upstream-pr-scope.md): Established the ~291 insertion / ~110 deletion scope for Basic.lean + Denotation.lean. Identified the `ModalConnectives` dependency on Connectives.lean.
- **Report 02** (02_literature-grounded-analysis.md): Discovered PR #647 was CLOSED. Confirmed all 7 BibKeys verified in `references.bib`. Provided Burgess 1984 evidence supporting box-as-primitive.
- **Report 03** (03_team-research.md): Team research confirmed three-file scope (Basic + Denotation + LogicalEquivalence = ~355 LOC). Established that LogicalEquivalence.lean MUST be included because changing Basic.lean constructors breaks upstream's `Context` type. Identified PR #607 alignment opportunity.
- **Report 04** (04_pr649-comparison-classical-signature.md): Compared PR #649 patterns and conventions. Confirmed `Connectives.lean` must be extended with `HasBox`/`ModalConnectives` (~25 LOC). Extracted quality convention requirements (BibKey format, `## Main definitions`, `## Notation` sections). Established the stacking pattern used by PR #649.
- **Report 06** (06_modal-pr-landscape.md): Audited the upstream PR landscape as of 2026-06-15. Found no competing modal signature-change PRs. Confirmed PR #607 (fmontesi) is stalled with CHANGES_REQUESTED since 2026-05-29. Recommended stacking on PR #648 directly (not #649) for a two-PR dependency chain. Identified `HasImpl` vs `HasImp` naming conflict with PR #607. Established diplomatic framing strategy for PR description.

### Revision Notes (v4 to v5)

This revision narrows the plan to match the `pr` task type scope. The previous plan (v4, plans/07_modal-upstream-pr-plan.md) had 4 phases covering branch creation, code changes, CI verification, and PR submission. A `pr` task type produces ONLY a `pr-description.md` file -- it does not create branches, modify source files, run CI, or submit the PR. Those operations are handled by the `/pr` command separately. The revised plan has 2 phases totaling 1.5 hours, focused entirely on analyzing the expected diff and drafting the PR description.

### Roadmap Alignment

This plan advances the following from `specs/ROADMAP.md`:
- Modal module (`Logics/Modal/`) upstream contribution -- the formula type refactoring is a prerequisite for all subsequent Modal/ PRs
- Foundations/Logic/Connectives.lean extension with modal typeclass hierarchy

## Goals & Non-Goals

**Goals**:
- Analyze the expected diff scope across four files (Connectives.lean, Basic.lean, Denotation.lean, LogicalEquivalence.lean) to inform the PR description
- Draft `specs/197_modal_upstream_initial_pr/pr-description.md` with all required sections: Summary, Design Rationale, Relationship to Other PRs, Breaking Changes, Changed Files, Contribution Roadmap, AI Tools Used
- Include diplomatic coordination language for PRs #607, #648, #649, #528, #535 modeled on PR #648's tone
- Include proof-theoretic justification for box-as-primitive with BibKey citations (Blackburn2001, ChagrovZakharyaschev1997, Burgess1984)
- Acknowledge fmontesi's foundational work on PRs #528/#535
- Follow CSLib CONTRIBUTING.md conventions and PR #648's quality standards
- Transition task to [PR READY] upon completion

**Non-Goals**:
- Creating a feature branch or modifying any `.lean` source files
- Running `lake build`, `lake test`, or any CI verification commands
- Pushing to any remote repository
- Submitting the PR via `gh pr create`
- Modifying `Connectives.lean`, `Basic.lean`, `Denotation.lean`, or `LogicalEquivalence.lean`
- Verifying that `Cube.lean` still compiles
- Stacking on PR #649 (this PR stacks on #648 directly)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR description tone perceived as dismissive of fmontesi's work | H | M | Model tone on PR #648; explicitly acknowledge PRs #528/#535; frame refactoring as building on fmontesi's foundation |
| Incorrect diff statistics in description | M | L | Cross-reference research reports 01 and 03 for verified LOC counts; note approximate nature |
| Missing or incorrect BibKey citations | M | L | Verify cited keys (Blackburn2001, ChagrovZakharyaschev1997, Burgess1984) exist in task 201's corrected `references.bib` |
| PR description mischaracterizes relationship to PR #607 | H | M | Read PR #607 and chenson2018's review comment; present `HasImp`/`HasImpl` as a one-line alignment, not a conflict |
| Description becomes outdated if PR #648 evolves | L | L | Note stacking dependency clearly; description can be updated during `/pr` execution |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Analyze Diff Scope and Draft PR Description [COMPLETED]

**Goal**: Read the local modal files and upstream state to understand the exact diff, then write the complete `pr-description.md` artifact.

**Tasks**:
- [ ] Read local `Cslib/Logics/Modal/Basic.lean`, `Denotation.lean`, `LogicalEquivalence.lean` to understand current local state
- [ ] Read `Cslib/Foundations/Logic/Connectives.lean` to understand current `HasBox`/`ModalConnectives` additions needed
- [ ] Review PR #648 description (fetched during planning) for tone and structure model
- [ ] Review `specs/188_first_propositional_upstream_pr/pr-description.md` for template structure
- [ ] Review PR #607 via `gh pr view 607 -R leanprover/cslib` for diplomatic framing context
- [ ] Draft `specs/197_modal_upstream_initial_pr/pr-description.md` with:
  - **Title**: `feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}`
  - **Summary**: Three-sentence description of the refactoring (four files, classical-only signature, extends Connectives.lean)
  - **Design Rationale**:
    - "Why box, not diamond?" -- necessitation and K axiom are pure proof rules on box; diamond is `neg (box (neg phi))`; cite Blackburn2001, ChagrovZakharyaschev1997, Burgess1984
    - "Why bot and imp as primitives?" -- same argument as PR #648 (substitution stability, constraint-free derived connectives)
  - **Relationship to Other PRs** (critical diplomatic section):
    - PR #648: stacking dependency, extends Connectives.lean
    - PR #649: sibling relationship, both independent of each other
    - PR #607: diplomatic framing of `HasImpl`/`HasImp` naming, acknowledge consolidation aligns with chenson2018's review feedback
    - PRs #528/#535: acknowledge fmontesi's foundational work
  - **Breaking Changes**: constructor renames (`not` -> derived `neg`, `and` -> derived `and`, `diamond` -> derived `diamond`; Context `{notC, andL, andR, diamondC}` -> `{impL, impR, box}`)
  - **Changed Files**: per-file summaries for all four files
  - **Contribution Roadmap**: planned follow-up PRs
  - **AI Tools Used**: same disclosure pattern as PR #648
  - **`## Main definitions`**: list key definitions introduced/modified
  - **`## Notation`**: list scoped operators with precedence
  - **`## References`**: BibKey format citations

**Timing**: 60 minutes

**Depends on**: none

**Files to create**:
- `specs/197_modal_upstream_initial_pr/pr-description.md`

**Verification**:
- PR description contains all required sections
- Diplomatic "Relationship to Other PRs" section covers #607, #648, #649, #528, #535
- BibKey citations are accurate (Blackburn2001, ChagrovZakharyaschev1997, Burgess1984)
- Tone matches PR #648 (structured, literature-backed, diplomatic)
- No references to branch creation, CI commands, or PR submission

---

### Phase 2: Quality Review and Finalization [COMPLETED]

**Goal**: Review the drafted PR description for accuracy, completeness, and diplomatic tone, then finalize.

**Tasks**:
- [ ] Verify all BibKey citations reference entries that exist in `references.bib` (Blackburn2001, ChagrovZakharyaschev1997, Burgess1984, Johansson1937 if cited)
- [ ] Verify breaking changes section accurately reflects the constructor renames from research reports
- [ ] Verify "Relationship to Other PRs" section is diplomatically worded -- acknowledges fmontesi's PRs #528/#535, frames consolidation positively, notes `HasImp`/`HasImpl` as a one-line alignment
- [ ] Cross-check diff statistics (~355 insertions / ~222 deletions) against research reports 01 and 03
- [ ] Verify the description follows CSLib CONTRIBUTING.md conventions (if available upstream)
- [ ] Ensure `## Main definitions`, `## Notation`, `## References` sections use BibKey format matching PR #648's style
- [ ] Remove any accidental references to branch operations, CI commands, or PR submission from the description
- [ ] Final read-through for tone consistency with PR #648

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- quality fixes if needed

**Verification**:
- All BibKey citations verified
- Diplomatic tone consistent throughout
- No operational commands (git, lake, gh) appear in the description
- Description is self-contained and ready for use by `/pr` command

---

## Testing & Validation

- [ ] `pr-description.md` exists at `specs/197_modal_upstream_initial_pr/pr-description.md`
- [ ] Description contains all required sections: Summary, Design Rationale, Relationship to Other PRs, Breaking Changes, Changed Files, Contribution Roadmap, AI Tools Used
- [ ] All BibKey citations (Blackburn2001, ChagrovZakharyaschev1997, Burgess1984) reference valid entries
- [ ] Diplomatic framing covers PRs #607, #648, #649, #528, #535
- [ ] Description tone matches PR #648 (structured, literature-backed, acknowledges fmontesi)
- [ ] No references to branch creation, CI verification, or PR submission appear in the plan or description
- [ ] Description is suitable for direct use by `/pr` command

## Artifacts & Outputs

- `specs/197_modal_upstream_initial_pr/plans/08_modal-upstream-pr-plan.md` (this plan)
- `specs/197_modal_upstream_initial_pr/pr-description.md` (PR description artifact -- sole deliverable)

## Rollback/Contingency

If the PR description is found to be inaccurate after `/pr` creates the branch and runs CI:
1. Update `pr-description.md` with corrected diff statistics or section content
2. Re-run `/pr` to regenerate the PR with the updated description

If PR #648 evolves significantly before this PR is submitted:
1. Re-read PR #648's current state via `gh pr view 648 -R leanprover/cslib`
2. Update the "Relationship to Other PRs" section accordingly
3. Verify stacking dependency description is still accurate

If diplomatic tone is criticized during PR review:
1. Revise language per reviewer feedback
2. Strengthen acknowledgment of fmontesi's contributions
3. Seek direct feedback from fmontesi via Zulip if needed
