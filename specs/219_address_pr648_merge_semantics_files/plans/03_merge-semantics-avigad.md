# Implementation Plan: Address PR #648 Review

- **Task**: 219 - Address PR #648 review: merge Semantics files, update references
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: PR #536 must merge before rebase (Phase 5)
- **Research Inputs**: reports/02_team-research.md
- **Artifacts**: plans/03_merge-semantics-avigad.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

PR #648 received CHANGES_REQUESTED from ctchou with three directives: merge Semantics/Basic.lean and Bool.lean into a single file, update attribution references from Chagrov/Zakharyaschev to Avigad, and coordinate with overlapping PRs (#536, #587, #607). The implementation requires working on the `feat/propositional-v2` branch, cherry-picking changes from main that have landed since the PR was filed, performing the file merge and reference updates, and posting PR comments that address ctchou's ambiguous "Bool.lean alone is enough" remark. Done when: merged file compiles, `references.bib` conflict resolved with Avigad2023 added, PR comments posted, and CI passes.

### Research Integration

Team research (4 teammates) identified: (1) `Basic.lean` is the correct merge target (zero import changes across 5 consuming files), (2) ctchou's comment has an ambiguous Interpretation B ("drop Evaluate entirely") that must be explicitly rebutted, (3) `references.bib` has pre-existing merge conflict markers that block any commit to that file, (4) active cross-PR tagging is required (not just PR description notes), and (5) the `Connectives.lean` path collision with PR #587 is the critical coordination issue.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Merge `Semantics/Bool.lean` into `Semantics/Basic.lean` with clean section organization
- Resolve `references.bib` merge conflict and add `Avigad2023` entry
- Update docstring citations from Chagrov/Zakharyaschev to Avigad chapters 2-3
- Cherry-pick relevant changes from main onto the PR branch
- Post PR response addressing both interpretations of ctchou's comment
- Tag fmontesi and thomaskwaring in PR #648 for cross-PR coordination
- Mention Kripke.lean as planned follow-up in PR response

**Non-Goals**:
- Resolving the HasImp vs HasImpl naming debate (requires Zulip discussion)
- Modifying files outside PR #648 scope (SemanticConsequence.lean Chagrov refs stay)
- Addressing modal formula primitive type conflict (post-#648 strategic action)
- Rebasing on upstream main (separate phase, blocked on PR #536 merge)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `references.bib` merge conflict resolution breaks other entries | H | M | Inspect all conflict markers, resolve conservatively, verify with `lake exe lint-style` |
| Cherry-pick from main introduces conflicts with PR branch | M | M | Cherry-pick incrementally, resolve per-commit, build after each |
| ctchou interprets response as dismissive of Interpretation B | H | L | Provide concrete technical justification (StrongCompleteness.lean MCS argument) |
| PR #536 merges during implementation, creating rebase conflicts | M | M | Complete all local work first, rebase as final step |
| Bool.lean merge breaks downstream imports | H | L | Verified: no files import Semantics.Bool except Bool.lean itself |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Resolve references.bib Merge Conflict and Add Avigad2023 [NOT STARTED]

**Goal**: Clean up the pre-existing merge conflict in `references.bib` and add the Avigad reference entry.

**Tasks**:
- [ ] Switch to `feat/propositional-v2` branch
- [ ] Inspect the 3 merge conflict markers in `references.bib` (around Fitting1969 and Trufas2024)
- [ ] Resolve all conflict markers, keeping both sides where appropriate
- [ ] Add `Avigad2023` BibTeX entry following CSLib convention (`{AuthorSurname}{Year}`)
- [ ] Verify `references.bib` parses cleanly (no remaining conflict markers)
- [ ] Run `lake exe lint-style` to check if BibKey validation passes

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` - Resolve conflicts, add Avigad2023

**Verification**:
- `grep -c '<<<<<<' references.bib` returns 0
- `grep 'Avigad2023' references.bib` finds the new entry
- `lake exe lint-style` passes (or confirms BibKey refs are not validated by lint)

---

### Phase 2: Merge Bool.lean into Basic.lean [NOT STARTED]

**Goal**: Absorb `Semantics/Bool.lean` content into `Semantics/Basic.lean`, delete `Bool.lean`, and update the root import file.

**Tasks**:
- [ ] Read current content of `Semantics/Basic.lean` (~64 lines) and `Semantics/Bool.lean` (~110 lines)
- [ ] Create merged file in `Semantics/Basic.lean` with section organization: Prop-valued (Valuation, Evaluate, simp lemmas, Tautology) then Bool-valued (BoolValuation, BoolEvaluate, simp lemmas) then Bridge (BoolEvaluate_eq_iff, decidability)
- [ ] Promote Design Notes from Bool.lean's docstring to the merged file's module docstring
- [ ] Update docstring citations: replace Chagrov/Zakharyaschev Section 1.2 with Avigad chapters 2-3 using `[Avigad2023]` BibKey
- [ ] Ensure imports: only `import Cslib.Logics.Propositional.Defs` (no self-import of deleted file)
- [ ] Delete `Semantics/Bool.lean`
- [ ] Remove `import Cslib.Logics.Propositional.Semantics.Bool` from `Cslib.lean` (root import file)
- [ ] Build with `lake build` to verify no import errors

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Basic.lean` - Absorb Bool.lean content, update docstring
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - Delete
- `Cslib.lean` - Remove Bool import line

**Verification**:
- `lake build` succeeds
- `Semantics/Bool.lean` does not exist
- `grep 'Semantics.Bool' Cslib.lean` returns nothing
- All 5 downstream files still compile (they import `Semantics.Basic` unchanged)

---

### Phase 3: Commit and Push Review Changes to PR Branch [NOT STARTED]

**Goal**: Ensure the PR branch contains exactly the review-addressed changes and nothing outside the PR's scope.

**Tasks**:
- [ ] Verify PR scope is limited to the files the PR already touches plus `references.bib`:
  - `Cslib/Foundations/Logic/Connectives.lean`
  - `Cslib/Logics/Propositional/Defs.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
  - `Cslib/Logics/Propositional/Semantics/Basic.lean` (now merged)
  - `Cslib.lean` (Bool import removed)
  - `references.bib` (Avigad2023 added)
- [ ] Confirm no files outside PR scope were modified (e.g., Metalogic/, ProofSystem/, Kripke.lean are follow-up PRs, not this one)
- [ ] Commit Phase 1-2 changes on `feat/propositional-v2`
- [ ] Run `lake build` to verify the PR branch compiles cleanly
- [ ] Push to origin

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- None beyond what Phases 1-2 already changed

**Verification**:
- `lake build` succeeds on PR branch
- `git diff --name-only upstream/main..feat/propositional-v2` shows only in-scope files
- No Metalogic/ProofSystem/Kripke files appear in the diff

---

### Phase 4: Draft PR Response and Coordination Comments [NOT STARTED]

**Goal**: Write draft response and coordination comments for user review before posting.

**Tasks**:
- [ ] Draft PR #648 response to ctchou addressing:
  - File merge completed (Bool.lean absorbed into Basic.lean)
  - Explicit rebuttal of Interpretation B: StrongCompleteness.lean uses `fun p => atom p in S` which is Prop-valued (MCS set membership has no DecidablePred); BoolEvaluate serves the computable layer; bridge lemma connects them
  - Avigad reference added, docstrings updated
  - Kripke.lean exists locally as planned follow-up
  - SemanticConsequence.lean retains Chagrov refs for specific theorems (1.16, 2.43), will address in follow-up
- [ ] Draft coordination comment for thomaskwaring noting: (1) Connectives.lean path collision with PR #587, (2) Valuation.interp needs updating for five-primitive Proposition type
- [ ] Draft coordination comment for fmontesi noting: HasImp/HasImpl naming divergence with PR #607
- [ ] Write all drafts to task directory for user review

**Timing**: 30 minutes

**Depends on**: 2, 3

**Files to create**:
- `specs/219_address_pr648_merge_semantics_files/drafts/pr648-response.md` - Main review response
- `specs/219_address_pr648_merge_semantics_files/drafts/pr648-coordination.md` - Comments for thomaskwaring and fmontesi

**Verification**:
- Draft files exist and cover all review points
- User reviews and posts comments manually

---

### Phase 5: Rebase on Upstream After PR #536 Merges [NOT STARTED]

**Goal**: Rebase the PR branch on upstream/main after PR #536 merges, resolving any conflicts.

**Tasks**:
- [ ] Check if PR #536 has merged: `gh pr view 536 --json state`
- [ ] If merged: fetch upstream and rebase (`git fetch upstream && git rebase upstream/main`)
- [ ] If not merged: mark this phase as BLOCKED and document dependency
- [ ] Resolve any rebase conflicts (likely in `Defs.lean` and `NaturalDeduction/Basic.lean` where both PRs touch IsIntuitionistic/IsClassical)
- [ ] Run full CI verification: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Force-push the rebased PR branch (with user confirmation)

**Timing**: 45 minutes

**Depends on**: 4

**Files to modify**:
- Potentially any files touched by both #536 and #648 during conflict resolution

**Verification**:
- `lake build` passes
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- PR branch is up to date with upstream/main

## Testing & Validation

- [ ] `lake build` succeeds on PR branch after all changes
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No merge conflict markers remain in any files (`grep -r '<<<<<<' .`)
- [ ] `Semantics/Bool.lean` is deleted and not referenced anywhere
- [ ] `references.bib` contains `Avigad2023` entry
- [ ] Merged `Basic.lean` docstring references Avigad, not Chagrov
- [ ] PR #648 has response comment addressing ctchou's review
- [ ] Cross-PR coordination comments posted for #587 and #607

## Artifacts & Outputs

- `specs/219_address_pr648_merge_semantics_files/plans/03_merge-semantics-avigad.md` (this plan)
- Modified `Cslib/Logics/Propositional/Semantics/Basic.lean` (merged file)
- Deleted `Cslib/Logics/Propositional/Semantics/Bool.lean`
- Modified `references.bib` (conflicts resolved, Avigad2023 added)
- Modified `Cslib.lean` (Bool import removed)
- PR #648 response comment and cross-PR coordination comments

## Rollback/Contingency

- If file merge breaks downstream compilation: restore `Bool.lean` from git, revert `Basic.lean` changes
- If `references.bib` resolution introduces errors: `git checkout references.bib` and resolve manually
- If cherry-picks create unresolvable conflicts: skip conflicting commits, note in PR response for follow-up
- If PR #536 does not merge in reasonable time: submit PR #648 without rebase, note the dependency in PR description
- All changes are on the `feat/propositional-v2` branch -- main is unaffected
