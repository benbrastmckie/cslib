# Implementation Plan: Task #197

- **Task**: 197 - Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: PR #647 (Propositional) status resolution; PR #607 coordination
- **Research Inputs**: specs/197_modal_upstream_initial_pr/reports/01_modal-upstream-pr-scope.md, specs/197_modal_upstream_initial_pr/reports/02_literature-grounded-analysis.md
- **Artifacts**: plans/02_modal-upstream-pr-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Prepare and submit a ~290 LOC upstream PR covering `Modal/Basic.lean` and `Modal/Denotation.lean`, which refactors the formula type from `{atom, not, and, diamond}` to `{atom, bot, imp, box}` primitives with derived connectives and updated denotational semantics. The critical change since the prior plan is that PR #647 (Propositional, containing `Connectives.lean`) was closed without merge on 2026-06-14, so the Modal PR can no longer stack on it. The plan must first resolve this dependency -- either by re-submitting PR #647 or by deferring the `ModalConnectives` typeclass instance -- and must initiate Zulip coordination about the primitive set disagreement with PR #607 before submission, not after.

### Research Integration

Two research reports inform this plan:

- **Report 01** (01_modal-upstream-pr-scope.md): Established the ~291 insertion / ~110 deletion scope across Basic.lean and Denotation.lean. Identified the hard dependency on PR 198 for the `ModalConnectives` instance (3 lines: one import, one instance declaration). Flagged the PR #607 conflict as HIGH RISK and recommended deferring `LogicalEquivalence.lean` and `FromPropositional.lean` to later PRs.

- **Report 02** (02_literature-grounded-analysis.md): Discovered PR #647 was CLOSED without merge (no review comments, suggesting self-closure). Confirmed all 7 BibKeys verified in `references.bib`. Provided Burgess 1984 evidence strongly supporting box-as-primitive via tense logic analogy (G/H as subjects of K axiom and necessitation). Noted PR #607 review feedback favors single-file typeclasses (aligns with our `Connectives.lean`). Recommended Zulip coordination before PR submission.

### Prior Plan Reference

The prior plan (01_modal-upstream-pr-plan.md) had 4 sequential phases: (1) Create PR Branch, (2) CI Verification, (3) PR Description, (4) Submit PR + Zulip. It assumed PR 198/647 was merged or available for stacking, which is no longer the case. The prior plan placed Zulip coordination last (Phase 4), but research shows this should happen first given the PR #607 primitive set disagreement. Effort estimate of 3 hours was reasonable but slightly low given the new Zulip coordination requirement. The prior plan's CI verification checklist was thorough and is largely preserved.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Resolve the PR #647 dependency: decide whether to re-submit Propositional PR first or defer the `ModalConnectives` instance
- Initiate Zulip discussion on primitive set choice before PR submission, with literature-backed arguments
- Create a clean PR branch with `Basic.lean` + `Denotation.lean` compiling against upstream
- Adjust imports to use upstream module paths (revert `Cslib.Foundations.Data.Relation` to `Cslib.Foundations.Relation.Euclidean`)
- Pass all CI checks (lake build, checkInitImports, lint-style)
- Draft a PR description incorporating Burgess 1984 citation and grind transparency argument
- Create `pr-description.md` artifact in task directory

**Non-Goals**:
- Including `LogicalEquivalence.lean` (deferred to PR 3)
- Including `FromPropositional.lean` (deferred to PR 4)
- Fully resolving the PR #607 conflict (requires community consensus)
- Modifying upstream's `Cube.lean` (no changes needed)
- Changing proof style to match upstream's `grind` usage (offer in PR description if requested)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #647 closure blocks Modal PR indefinitely | H | M | Investigate closure reason; if self-closed, re-submit with fixes; if reviewer-closed, defer ModalConnectives instance (Option 3) |
| PR #607 merges with incompatible `{not, and, diamond}` primitives | H | M | Open Zulip thread early with Burgess 1984 + Blackburn citations; present box-as-primitive as literature-grounded alternative |
| Upstream `Relation` module path mismatch | M | H | Revert to `Cslib.Foundations.Relation.Euclidean`; verify `RightEuclidean`/`Serial` resolve |
| Proof style rejected by reviewers (explicit vs grind) | M | L | Note in PR description that explicit proofs avoid transparency issues reported in PR #607 review; offer to convert if requested |
| `grind =_` vs `grind =` attribute causes Cube.lean breakage | L | L | Test on PR branch; revert to `=_` if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Resolve PR #647 Dependency and Initiate Zulip Coordination [NOT STARTED]

**Goal**: Determine why PR #647 was closed, decide the branching strategy for the Modal PR, and open the Zulip discussion about primitive set choice before any code work begins.

**Tasks**:
- [ ] Check PR #647 on GitHub: read closure details, check for any comments or CI failures that triggered closure
- [ ] If self-closed: identify the issue and decide whether to re-submit PR #647 immediately (preferred) or defer
- [ ] If reviewer-closed: adopt Option 3 (submit Modal PR without `ModalConnectives` instance, deferring to follow-up after `Connectives.lean` acceptance)
- [ ] Decide branching strategy based on outcome:
  - If re-submitting PR #647: create Modal branch stacked on PR #647's branch
  - If deferring ModalConnectives: create Modal branch from upstream/main directly, removing the `Connectives.lean` import and 3-line instance
- [ ] Draft Zulip message for CSLib channel about:
  - Primitive set choice: `{atom, bot, imp, box}` vs `{atom, not, and, diamond}` (cite Blackburn 2001 Ch. 1, Chagrov-Zakharyaschev 1997 S. 1.1, Burgess 1984 Kt axiomatization)
  - Single-file `Connectives.lean` vs per-operator files (PR #607 reviewers favored consolidation)
  - Explicit proofs vs `grind` (note transparency issues from PR #607 review)
- [ ] Post the Zulip message (or prepare for user to post manually)
- [ ] Record the strategy decision and Zulip thread link in task notes

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- None (investigation and communication phase)

**Verification**:
- Strategy decision is documented (re-submit PR #647 or defer ModalConnectives)
- Zulip message is drafted or posted with literature citations
- Branch base is determined (PR #647 branch or upstream/main)

---

### Phase 2: Create PR Branch and Prepare Files [NOT STARTED]

**Goal**: Create a feature branch with the two target files, adjusting imports per the strategy decision from Phase 1.

**Tasks**:
- [ ] Fetch upstream/main: `git fetch upstream`
- [ ] Create branch `feat/modal-formula-refactoring` from the determined base:
  - If stacking on PR #647: branch from `feat/propositional-five-primitive`
  - If standalone: branch from `upstream/main`
- [ ] Copy local `Cslib/Logics/Modal/Basic.lean` to the PR branch
- [ ] Replace import `Cslib.Foundations.Data.Relation` with `Cslib.Foundations.Relation.Euclidean` in `Basic.lean`
- [ ] If deferring ModalConnectives (Option 3):
  - Remove `import Cslib.Foundations.Logic.Connectives` line
  - Remove the 3-line `ModalConnectives` instance block
  - Add a TODO comment noting the instance will be registered after Connectives.lean merges
- [ ] If stacking on PR #647:
  - Verify `Cslib.Foundations.Logic.Connectives` import resolves
  - Keep the `ModalConnectives` instance as-is
- [ ] Copy local `Cslib/Logics/Modal/Denotation.lean` to the PR branch
- [ ] Verify no other import path adjustments needed in `Denotation.lean`
- [ ] Ensure `Cube.lean` remains unmodified on the branch
- [ ] Check `grind =_` vs `grind =` attribute on `derivation_def` -- match upstream convention

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- import path adjustment, possible ModalConnectives removal
- `Cslib/Logics/Modal/Denotation.lean` -- copied with verified imports

**Verification**:
- Branch exists with correct base
- Both files have upstream-compatible import paths
- No references to `Cslib.Foundations.Data.Relation` remain
- If Option 3: no reference to `Cslib.Foundations.Logic.Connectives` remains

---

### Phase 3: CI Verification [NOT STARTED]

**Goal**: Run the full CI pipeline to confirm the PR compiles and passes all checks.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Modal.Basic` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.Denotation` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.Cube` -- must still compile unchanged
- [ ] Run `lake exe checkInitImports` -- verify root import file is correct
- [ ] Run `lake exe lint-style` -- pass style linting
- [ ] Verify `Relation.RightEuclidean`, `Relation.Serial`, `Std.Refl`, `Std.Symm`, `IsTrans` resolve from upstream imports
- [ ] If stacking on PR #647: verify `ModalConnectives` instance compiles with PR 198 definitions
- [ ] Note expected failure: `lake build Cslib.Logics.Modal.LogicalEquivalence` (document in PR)
- [ ] If any failures, fix import paths or adjust code minimally
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` on modified files to check for unused imports

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- potential fixes from CI feedback
- `Cslib.lean` -- may need import line addition if checkInitImports requires it

**Verification**:
- `lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Denotation` exits 0
- `lake exe checkInitImports` exits 0
- `lake exe lint-style` exits 0
- `Cube.lean` still compiles

---

### Phase 4: Draft PR Description with Literature-Backed Arguments [NOT STARTED]

**Goal**: Write the final PR description incorporating Burgess 1984 citation, grind transparency argument, and PR #607 coordination notes.

**Tasks**:
- [ ] Write `specs/197_modal_upstream_initial_pr/pr-description.md` based on Report 01 Section 5 draft
- [ ] Add "Design Rationale" section with literature citations:
  - Blackburn et al. (2001) Ch. 1: box as primitive modal operator
  - Chagrov and Zakharyaschev (1997) S. 1.1: box as primitive
  - Burgess (1984): Kt axiomatization uses G/H (universal/necessity operators) as subjects of K axiom and necessitation -- confirms box as natural primitive
  - Bentzen (2023), Trufas (2024): five-primitive signature precedent
- [ ] Add "Proof Style" note addressing PR #607 grind transparency issue:
  - Our proofs use explicit term-mode / lightweight tactics
  - Avoids the transparency issues @thomaskwaring reported with grind and typeclass notation layers
  - Offer to convert to grind if reviewers prefer
- [ ] Add "Relationship to Other PRs" section:
  - PR #647 (Propositional): dependency status and strategy chosen in Phase 1
  - PR #607 (fmontesi): note the primitive set difference, link to Zulip discussion
- [ ] Include "Breaking Changes" section with exact renames and constructor changes
- [ ] Include "Contribution Roadmap" section showing PR 3 (LogicalEquivalence) and PR 4 (FromPropositional)
- [ ] Include "AI Tools Used" disclosure
- [ ] Fill in actual PR numbers (replace any `#NNN` placeholders)

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- create or update final PR description

**Verification**:
- PR description contains all required sections (Summary, Design Rationale, Breaking Changes, Relationship to Other PRs, Changed Files, AI Tools Used)
- No `#NNN` placeholder remains unresolved
- Burgess 1984, Blackburn 2001, Chagrov-Zakharyaschev 1997 citations are present
- Zulip discussion link is referenced (or placeholder for it)

---

### Phase 5: Submit PR and Record Artifacts [NOT STARTED]

**Goal**: Submit the PR via GitHub CLI, finalize Zulip coordination, and record all artifacts.

**Tasks**:
- [ ] Create clean commit(s) on the feature branch with message: `feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}`
- [ ] Push branch to origin: `git push -u origin feat/modal-formula-refactoring`
- [ ] Submit PR via `gh pr create` with title and body from pr-description.md
- [ ] Set PR base branch appropriately:
  - If stacking on PR #647: base = `feat/propositional-five-primitive`
  - If standalone: base = `main`
- [ ] Add labels if available (e.g., `Modal`, `breaking-change`)
- [ ] Update pr-description.md with the actual PR URL and Zulip thread link
- [ ] Verify PR description renders correctly on GitHub
- [ ] Record the PR URL in task artifacts

**Timing**: 15 minutes

**Depends on**: 3, 4

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- add PR URL and Zulip link

**Verification**:
- PR is created and visible on GitHub
- PR description renders correctly with all sections
- Zulip thread exists or is drafted
- Task artifacts are updated with PR URL

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Basic` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.Denotation` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.Cube` succeeds (unchanged file still compiles)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] If stacking: `ModalConnectives` instance resolves correctly
- [ ] No references to local-only import paths remain
- [ ] PR description is complete and accurately reflects the diff
- [ ] Zulip discussion is posted with literature citations

## Artifacts & Outputs

- `specs/197_modal_upstream_initial_pr/plans/02_modal-upstream-pr-plan.md` (this plan)
- `specs/197_modal_upstream_initial_pr/pr-description.md` (PR description for submission)
- Feature branch `feat/modal-formula-refactoring` with clean commits
- GitHub PR URL (recorded in task artifacts after submission)
- Zulip thread URL (recorded after posting)

## Rollback/Contingency

If Phase 1 determines PR #647 cannot be re-submitted (e.g., upstream rejection of Connectives.lean approach):
1. Proceed with Option 3 (Modal PR without ModalConnectives instance)
2. Defer typeclass registration to a follow-up PR after Connectives.lean acceptance
3. The formula type refactoring (the core value of this PR) is independent of the typeclass layer

If CI fails on the PR branch:
1. Check import path mismatches -- revert to upstream's `Cslib.Foundations.Relation.Euclidean`
2. Check if `DecidableEq`/`BEq` deriving fails on upstream's Lean version -- remove deriving clause
3. If ModalConnectives instance fails and we are stacking -- fall back to Option 3

If PR #607 merges before this PR:
1. Rebase onto PR #607's merged state
2. Adapt the formula type to coexist with PR #607's operator typeclasses
3. Present our approach as an alternative refactoring in the Zulip discussion

If Zulip discussion shows community preference for `{not, and, diamond}` primitives:
1. Close this PR
2. Propose contributing our explicit proof style as improvements to PR #607's framework
3. Adapt to the community-chosen primitive set
