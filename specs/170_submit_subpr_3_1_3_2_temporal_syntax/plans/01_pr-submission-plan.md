# Implementation Plan: Submit Sub-PR 3.1 (Temporal Formula Type)

- **Task**: 170 - Submit Sub-PR 3.1: Temporal formula type
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: Task 138 (Connectives.lean / PR #635 must be open as base)
- **Research Inputs**: specs/170_submit_subpr_3_1_3_2_temporal_syntax/reports/01_pr-submission-research.md
- **Artifacts**: plans/01_pr-submission-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Create a clean PR branch `pr3/temporal-syntax` based on `refactor/proposition-lukasiewicz` (PR #635's branch), containing only Formula.lean (~582 lines), the barrel import entry in Cslib.lean, and two new references.bib entries. The PR stacks on PR #635 because Formula.lean imports `Cslib.Foundations.Logic.Connectives` which only exists on that branch. Citation format in Formula.lean must be updated from informal text to BibKey format per CSLib standards. Context.lean, BigConj.lean, and Subformulas.lean are explicitly out of scope (deferred to task 160 / Sub-PR 3.2).

### Research Integration

Key findings from report 01_pr-submission-research.md:
- PR #635 is open but not yet merged upstream; branch strategy must stack on it
- Formula.lean imports `Cslib.Foundations.Logic.Connectives` for `TemporalConnectives` -- hard dependency
- references.bib is missing `Kamp1968` and `GabbayPnueliShelahStavi1980` entries
- CI checks: `lake build --wfail --iofail`, `lake test`, `mk_all --check --module`, `checkInitImports`, `lint-style-action`
- The existing `pr3/temporal-formula` branch carries the full fork diff (80+ files) and cannot be reused
- CONTRIBUTING.md requires AI usage disclosure in the PR description

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the "Temporal syntax infrastructure" roadmap item listed under Completed:
- `Temporal syntax infrastructure (Context, BigConj, Subformulas)` in `Logics/Temporal/Syntax/`
- Formula.lean is the core type that underpins the entire Temporal module tree

## Goals & Non-Goals

**Goals**:
- Create a clean branch `pr3/temporal-syntax` from `refactor/proposition-lukasiewicz`
- Cherry-pick/extract only `Formula.lean` (582 lines) into the branch
- Add barrel import `Cslib.Logics.Temporal.Syntax.Formula` to `Cslib.lean`
- Add `Kamp1968` and `GabbayPnueliShelahStavi1980` BibTeX entries to `references.bib`
- Update Formula.lean citation format from informal to BibKey
- Pass all CI checks (lake build, lake test, mk_all, checkInitImports, lint-style)
- Submit PR to `leanprover/cslib` with proper description and AI disclosure

**Non-Goals**:
- Including Context.lean, BigConj.lean, or Subformulas.lean (those are Sub-PR 3.2 / task 160)
- Addressing eric-wieser's Bot/HImp comment on PR #635 (that is task 138's concern)
- Waiting for PR #635 to merge before submitting (stacked PRs are accepted)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #635 not yet merged, blocking reviewability | M | H | Clearly state dependency in PR description; stacked PRs are accepted practice in cslib |
| Formula.lean produces warnings under --wfail | H | L | File compiles cleanly on fork main; verify on PR branch before submission |
| mk_all --check fails due to missing barrel entry | H | L | Phase 2 adds the Cslib.lean entry; verify with mk_all before PR |
| checkInitImports fails for transitive import | M | L | Formula.lean has `public import Cslib.Init` via Connectives; verify explicitly |
| BibKey format incorrect or lint-style rejects it | M | L | Follow exact format from existing files (Modal/Basic.lean, Propositional/Defs.lean) |
| PR #607 (fmontesi/connectives) merges first, breaking imports | H | L | Monitor #607 status; our PR depends on #635 not #607 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are sequential because each depends on the branch state from the prior phase.

---

### Phase 1: Create clean PR branch [COMPLETED]

**Goal**: Create `pr3/temporal-syntax` branch from `refactor/proposition-lukasiewicz` with only Formula.lean added.

**Tasks**:
- [ ] Fetch latest upstream and origin remotes (`git fetch upstream && git fetch origin`)
- [ ] Create branch `pr3/temporal-syntax` from `refactor/proposition-lukasiewicz` (`git checkout -b pr3/temporal-syntax refactor/proposition-lukasiewicz`)
- [ ] Copy `Formula.lean` from fork main: `git checkout main -- Cslib/Logics/Temporal/Syntax/Formula.lean`
- [ ] Create directory if needed: `mkdir -p Cslib/Logics/Temporal/Syntax/`
- [ ] Verify the file is present and has expected content (~582 lines)
- [ ] Stage and commit: `git add Cslib/Logics/Temporal/Syntax/Formula.lean`

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - add (cherry-pick from main)

**Verification**:
- Branch exists based on `refactor/proposition-lukasiewicz`
- Only Formula.lean is added relative to the base branch
- `git diff refactor/proposition-lukasiewicz --name-only` shows only the new file(s)

---

### Phase 2: Update references and citations [COMPLETED]

**Goal**: Add missing BibTeX entries to references.bib and convert Formula.lean citations to BibKey format.

**Tasks**:
- [ ] Add `Kamp1968` BibTeX entry to `references.bib` (in alphabetical position after `Jech2003` or similar K-entries)
- [ ] Add `GabbayPnueliShelahStavi1980` BibTeX entry to `references.bib` (in alphabetical position after `FisherEtAl2019` or similar G-entries)
- [ ] Update Formula.lean `## References` section from informal format to BibKey format:
  - Change to: `* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]`
  - Change to: `* [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi, *On the temporal analysis of fairness*][GabbayPnueliShelahStavi1980]`
- [ ] Add barrel import to `Cslib.lean`: insert `public import Cslib.Logics.Temporal.Syntax.Formula` in alphabetical position (after `Logics.Propositional.NaturalDeduction.Basic`, before `MachineLearning.PACLearning.Defs`)
- [ ] Stage and commit all changes

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `references.bib` - add 2 BibTeX entries
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - update References section
- `Cslib.lean` - add 1 barrel import entry

**Verification**:
- `grep -c "Kamp1968" references.bib` returns 1
- `grep -c "GabbayPnueliShelahStavi1980" references.bib` returns 1
- `grep "Cslib.Logics.Temporal.Syntax.Formula" Cslib.lean` finds the entry
- Formula.lean References section uses `[BibKey]` bracket format

---

### Phase 3: CI verification [COMPLETED]

**Goal**: Run all CI checks locally and fix any issues before PR submission.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` (or full `lake build --wfail --iofail`) to verify no build errors or warnings
- [ ] Run `lake test` to ensure no test regressions
- [ ] Run `lake exe mk_all --check --module` to verify barrel completeness
- [ ] Run `lake exe checkInitImports` to verify Init import chain
- [ ] Run `lake exe lint-style` (or equivalent lint check) to verify style compliance
- [ ] Fix any issues found and re-run failed checks
- [ ] Commit any fixes

**Timing**: 30 minutes (includes build time)

**Depends on**: 2

**Files to modify**:
- Any files that need fixes from CI check failures (likely none)

**Verification**:
- All 5 CI checks pass with exit code 0
- No warnings in build output (--wfail is strict)

---

### Phase 4: Submit PR [COMPLETED]

**Goal**: Push branch and create PR on `leanprover/cslib` with proper description and dependency declaration.

**Tasks**:
- [ ] Push branch to origin: `git push origin pr3/temporal-syntax`
- [ ] Create PR via `gh pr create` with:
  - Title: `feat(Logics/Temporal/Syntax): temporal formula type`
  - Base branch: `refactor/proposition-lukasiewicz` (PR #635's branch) to show minimal diff
  - Body including: summary, dependency on PR #635, file list, AI disclosure per CONTRIBUTING.md
- [ ] Verify PR appears correctly on GitHub and diff shows only the temporal additions (not the full PR #635 diff)
- [ ] Record PR URL in task artifacts

**Timing**: 15 minutes

**Depends on**: 3

**Files to modify**:
- None (git operations only)

**Verification**:
- PR is created and visible on GitHub
- PR description mentions dependency on PR #635
- PR diff shows only Formula.lean, Cslib.lean changes, and references.bib additions relative to the base branch
- AI disclosure is present in the PR description

## Testing & Validation

- [ ] `lake build --wfail --iofail` passes with zero warnings
- [ ] `lake test` passes
- [ ] `lake exe mk_all --check --module` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `git diff refactor/proposition-lukasiewicz --stat` shows only Formula.lean, Cslib.lean, references.bib
- [ ] PR diff on GitHub matches expected scope (no extra files from fork)

## Artifacts & Outputs

- `specs/170_submit_subpr_3_1_3_2_temporal_syntax/plans/01_pr-submission-plan.md` (this plan)
- PR URL on `leanprover/cslib` (created in Phase 4)
- Clean branch `pr3/temporal-syntax` pushed to origin

## Rollback/Contingency

- **Branch contamination**: If the branch picks up unintended files, delete and recreate: `git branch -D pr3/temporal-syntax` and start Phase 1 over
- **CI failures**: Fix issues on the branch and force-push (acceptable for pre-review PRs)
- **PR #635 changes**: If PR #635 is force-pushed or rebased, rebase `pr3/temporal-syntax` on the updated branch: `git rebase refactor/proposition-lukasiewicz`
- **Scope creep**: If reviewer asks for Context/BigConj/Subformulas, those are task 160 (separate PR) -- respond directing to Sub-PR 3.2
