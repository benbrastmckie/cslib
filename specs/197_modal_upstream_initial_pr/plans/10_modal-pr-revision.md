# Implementation Plan: Revise pr-description.md per team research findings

- **Task**: 197 - Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: PR #648 merges as-is (assumed settled)
- **Research Inputs**: reports/09_team-research.md
- **Artifacts**: plans/10_modal-pr-revision.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

The existing `pr-description.md` was produced by the prior plan (plans/08, v5) and is broadly accurate against local code. Team research (report 09) identified 8 targeted updates needed before submission. This plan covers revising `pr-description.md` to address all 8 action items -- resolving `FromPropositional.lean` scope, adding PR #587 coordination, replacing 1930s citations with modern references in the PR body, adding Kyle Miller and fmontesi references to the contribution roadmap, strengthening `imp` naming rationale, updating PR #607 status, and adding a branch isolation note. The plan is defined as done when the revised `pr-description.md` passes a completeness check against all 8 items and the task transitions to [PR READY].

### Research Integration

Report 09 (09_team-research.md) provides the 8 action items driving this revision:

1. **HIGH**: Resolve `FromPropositional.lean` -- either include in scope (5th file) or verify it compiles unchanged and explicitly exclude
2. **HIGH**: Add PR #587 (thomaskwaring, DRAFT) to "Relationship to Other PRs" -- creates same `Connectives.lean` path with semantic typeclasses
3. **MEDIUM**: Replace 1930s citations (Johansson1937, Wajsberg1938, McKinsey1939) with modern references in PR body; keep in references.bib
4. **MEDIUM**: Add Kyle Miller S5 mention to contribution roadmap (he will port S5 completeness after this PR merges)
5. **MEDIUM**: Reference fmontesi's InferenceSystem suggestion in proof system roadmap item
6. **LOW**: Strengthen `imp` naming rationale -- state directly as #648's settled convention
7. **LOW**: Update PR #607 status from "stalled" to "active" (fmontesi responded 2026-06-16)
8. **LOW**: Add branch isolation note for `/pr` (exclude ProofSystem/, Metalogic/)

### Prior Plan Reference

The prior plan (plans/08, v5) had 2 phases totaling 1.5 hours: diff analysis + content drafting, then quality review. Both phases completed successfully, producing the current `pr-description.md`. Effort calibration: the initial drafting took the full 1.5 hours; this revision is simpler (targeted edits to an existing file) so 1 hour is realistic. The prior plan validated that the 4-file scope and stacking-on-#648 approach are correct.

### Roadmap Alignment

This plan advances:
- Modal module (`Logics/Modal/`) upstream contribution -- the formula type refactoring PR is a prerequisite for all subsequent Modal/ PRs
- `Foundations/Logic/Connectives.lean` extension with modal typeclass hierarchy

## Goals & Non-Goals

**Goals**:
- Address all 8 action items from report 09 in `pr-description.md`
- Resolve `FromPropositional.lean` scope question (include or explicitly exclude)
- Add PR #587 to the coordination section
- Replace 1930s citations with modern references in the PR body text
- Add Kyle Miller S5 and fmontesi InferenceSystem references to the contribution roadmap
- Strengthen `imp` naming as a settled convention from #648
- Update PR #607 status and add branch isolation guidance
- Transition task to [PR READY]

**Non-Goals**:
- Modifying any `.lean` source files
- Creating branches, running builds, or submitting the PR
- Rewriting the entire pr-description.md (targeted edits only)
- Removing 1930s citations from `references.bib` (only from the PR body text)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `FromPropositional.lean` decision is ambiguous -- include vs exclude | M | M | Check if file compiles against new primitives; if yes, exclude with note; if no, include in scope and update diff stats |
| Adding PR #587 introduces diplomatic complexity | M | L | Use neutral language: "creates the same file path with a different approach" -- no value judgment |
| Removing 1930s citations weakens design rationale | L | L | Lead with Blackburn2001 and ChagrovZakharyaschev1997 which cover the same ground; 1930s refs remain in references.bib |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Apply All 8 Revisions to pr-description.md [NOT STARTED]

**Goal**: Edit `pr-description.md` to address all 8 action items from research report 09.

**Tasks**:
- [ ] Read `Cslib/Logics/Modal/FromPropositional.lean` to determine if it compiles against the new `{atom, bot, imp, box}` primitives (check imports and constructor usage)
- [ ] Decide: if `FromPropositional.lean` uses only the public API (derived connectives, not constructors), exclude it with an explicit note; if it pattern-matches on old constructors, include it in scope and update diff statistics
- [ ] Add a new subsection `### PR #587: Connectives.lean Coordination` under "Relationship to Other PRs" describing thomaskwaring's DRAFT PR that creates `Connectives.lean` with semantic typeclasses
- [ ] In "Design Rationale > Why bot and imp as primitives?" section, replace inline references to Johansson1937, Wajsberg1938, McKinsey1939 with Blackburn2001 and ChagrovZakharyaschev1997 (the 1930s citations stay in the References section for attribution)
- [ ] Add Kyle Miller S5 completeness work as a future item in the "Contribution Roadmap" section (item between PR 3 and PR 4, or as a note on PR 3)
- [ ] Add fmontesi's InferenceSystem suggestion as a note on the proof system roadmap item (PR 3)
- [ ] In the PR #607 subsection, update language from implying "stalled" to reflecting active status (fmontesi responded "Should be ok now" on 2026-06-16)
- [ ] Strengthen `imp` naming rationale: replace "aligning to HasImp is a one-line change" framing with direct statement that `imp` is #648's settled convention
- [ ] Add a "Branch Isolation" note (either in Changed Files or as a new section) clarifying that `ProofSystem/`, `Metalogic/`, and `Cube.lean` are excluded from this PR's branch

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- all 8 targeted edits

**Verification**:
- All 8 action items from report 09 have corresponding edits
- `FromPropositional.lean` is either added to Changed Files or explicitly noted as out-of-scope
- PR #587 appears in the Relationship to Other PRs section
- No 1930s citations remain as primary justification in the PR body (may remain in References)
- Kyle Miller and fmontesi InferenceSystem are mentioned in the Contribution Roadmap

---

### Phase 2: Completeness Check and Finalization [NOT STARTED]

**Goal**: Verify the revised pr-description.md against all 8 action items, ensure consistency, and transition task to [PR READY].

**Tasks**:
- [ ] Re-read the revised `pr-description.md` end-to-end
- [ ] Verify each of the 8 action items has been addressed (checklist pass):
  - [ ] Item 1: `FromPropositional.lean` resolved
  - [ ] Item 2: PR #587 mentioned
  - [ ] Item 3: 1930s citations replaced in body
  - [ ] Item 4: Kyle Miller S5 in roadmap
  - [ ] Item 5: fmontesi InferenceSystem in roadmap
  - [ ] Item 6: `imp` naming rationale strengthened
  - [ ] Item 7: PR #607 status updated
  - [ ] Item 8: Branch isolation note present
- [ ] Verify diplomatic tone consistency (no dismissive language toward any contributor)
- [ ] Verify diff statistics are still accurate (update if `FromPropositional.lean` was added)
- [ ] Verify no operational commands (git, lake, gh) appear in the description

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- corrections if any item was missed

**Verification**:
- All 8 items confirmed addressed
- Tone is consistent with PR #648 style
- Description is ready for `/pr` command

---

## Testing & Validation

- [ ] `pr-description.md` exists and contains all required sections (Summary, Design Rationale, Relationship to Other PRs, Breaking Changes, Changed Files, Contribution Roadmap, AI Tools Used, Main Definitions, Notation, References)
- [ ] All 8 action items from report 09 are addressed
- [ ] `FromPropositional.lean` scope is explicitly resolved (included or excluded with rationale)
- [ ] PR #587 appears in Relationship to Other PRs
- [ ] No 1930s citations used as primary justification in the PR body text
- [ ] Kyle Miller S5 and fmontesi InferenceSystem appear in Contribution Roadmap
- [ ] `imp` naming stated as settled #648 convention
- [ ] PR #607 status reflects active state
- [ ] Branch isolation guidance present
- [ ] Diplomatic tone consistent throughout

## Artifacts & Outputs

- `specs/197_modal_upstream_initial_pr/plans/10_modal-pr-revision.md` (this plan)
- `specs/197_modal_upstream_initial_pr/pr-description.md` (revised PR description -- sole deliverable)

## Rollback/Contingency

The existing `pr-description.md` is tracked in git. If revisions introduce errors:
1. Revert to the pre-revision version via `git checkout -- specs/197_modal_upstream_initial_pr/pr-description.md`
2. Re-apply only the verified subset of edits
3. If `FromPropositional.lean` inclusion causes scope creep beyond ~300 LOC target, exclude it with a note that it will be addressed in a follow-up PR
