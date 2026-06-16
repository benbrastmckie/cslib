# Implementation Plan: Fix CI and Rebase PR #649 on PR #648

- **Task**: 223 - review_fix_pr_649_rebase_on_648
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: PR #648 approval (external, blocks Phase 3 only)
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/02_fix-ci-rebase.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

PR #649 (`feat/temporal-formula-propositional`) fails CI because two theorems (`Proposition.instBot_eq`, `Proposition.instTop_eq`) in `Cslib/Logics/Propositional/Defs.lean` auto-include the `[DecidableEq Atom]` section variable without using it. The `--wfail` flag (warnings-as-errors) added by `lean-action@v1` via PR #536 promotes these unused-variable warnings to build errors. The fix is to delete the two theorems (which PR #648 already removed in its updated version), address substantive reviewer feedback (remove `snce`, redesign `LTL.Satisfies`, remove irrelevant typeclasses), and then cleanly rebase onto PR #648's head once it is approved. The plan follows a three-phase sequential approach recommended by the team research synthesis.

### Research Integration

The team research report (`reports/01_team-research.md`, 4 teammates, standard mode) was the primary input. Key findings integrated:
- Root cause: `instBot_eq`/`instTop_eq` unused section variable warnings promoted to errors by `--wfail`
- Resolution: Delete theorems rather than `omit` annotation (aligns with PR #648's direction)
- Sequencing: Fix CI first, then address reviewer requests, then rebase (minimizes conflict surface and avoids double-work from rebasing onto unapproved PR #648)
- Conflict resolution table for 5 files with overlapping edits between PR #648 and PR #649

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Temporal module layer in the CSLib roadmap dependency structure. PR #649 adds `Temporal.Formula`, `LTL.Formula`, and `LTL.Satisfies`, which are prerequisites for the Temporal syntax, semantics, and proof system components listed under "Remaining" in ROADMAP.md. Completing this PR unblocks downstream temporal completeness work.

## Goals & Non-Goals

**Goals**:
- Fix the CI failure on PR #649 so the build passes
- Address all substantive reviewer requests from ctchou (remove `snce`, redesign `LTL.Satisfies`, remove irrelevant typeclasses)
- Rebase PR #649 cleanly onto PR #648's head when PR #648 is approved
- Maintain clean git history with proper stacking (temporal commits on top of propositional)

**Non-Goals**:
- Modifying PR #648 content (out of scope; that PR has its own review cycle)
- Implementing full LTS-based temporal semantics (may be deferred to follow-up PR per reviewer suggestion)
- Resolving PR #607 (fmontesi HasImpl) or PR #413 (mell-o-tron LTL) coordination issues
- Adding new temporal features beyond what PR #649 currently proposes

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #648 changes again after ctchou re-review | H | M | Defer rebase to Phase 3 (only after PR #648 approval); CI fix and reviewer changes are independent |
| `LTL.Satisfies` redesign breaks downstream imports | M | L | Check for downstream usage before removing; offer to defer to follow-up PR if complex |
| Rebase produces Lean elaboration errors beyond merge conflicts | H | M | Run `lake build` after each conflict resolution; use research conflict resolution table as guide |
| `instBot_eq`/`instTop_eq` are used by other files | M | L | Run grep across entire `Cslib/` directory before deletion |
| PR #648 is not approved for an extended period | M | M | Phases 1-2 are independent of PR #648 state; Phase 3 simply waits |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 (+ external: PR #648 approval) |

Phases within the same wave can execute in parallel.

### Phase 1: Fix CI Failure [NOT STARTED]

**Goal**: Delete the two theorems causing the `--wfail` build failure and verify the build passes.

**Tasks**:
- [ ] Check out the `feat/temporal-formula-propositional` branch
- [ ] Verify no downstream usage of `instBot_eq` or `instTop_eq` with `grep -r "instBot_eq\|instTop_eq" Cslib/`
- [ ] Delete `Proposition.instBot_eq` and `Proposition.instTop_eq` from `Cslib/Logics/Propositional/Defs.lean` (approximately lines 106-111)
- [ ] Run `lake build` to verify the fix resolves the CI failure
- [ ] Run `lake exe lint-style` and `lake exe checkInitImports` to verify no style or import issues
- [ ] Commit the fix and push to `feat/temporal-formula-propositional`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Delete `instBot_eq` and `instTop_eq` theorems

**Verification**:
- `lake build` completes without errors or warnings-as-errors
- `grep -r "instBot_eq\|instTop_eq" Cslib/` returns no results (no downstream breakage)
- CI pipeline passes on push

---

### Phase 2: Address Reviewer Requests [NOT STARTED]

**Goal**: Implement all substantive changes requested by ctchou in the PR #649 review.

**Tasks**:
- [ ] Remove `snce` (since) past-time operator from `Temporal.Formula` in `Cslib/Logics/Temporal/Syntax/Formula.lean` or equivalent file added by PR #649
- [ ] Remove any `snce`-related lemmas, instances, or pattern matches that reference the since operator
- [ ] Redesign or remove `LTL.Satisfies`: either rewrite to use LTS-based semantics (if scope permits) or remove entirely and note in PR that it will be a follow-up
- [ ] Remove irrelevant typeclass instances: `Encodable`, `Countable`, `Infinite`, `Denumerable` from temporal formula types
- [ ] Run `lake build` after each change to verify no regressions
- [ ] Run full CI pipeline locally: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Commit changes and push to `feat/temporal-formula-propositional`
- [ ] Request re-review from ctchou on PR #649

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (or PR #649's temporal formula file) - Remove `snce` operator
- `Cslib/Logics/LTL/Formula.lean` (or PR #649's LTL formula file) - Remove irrelevant typeclasses
- `Cslib/Logics/LTL/Satisfies.lean` (or PR #649's LTL satisfies file) - Redesign or remove omega-word semantics

**Verification**:
- `lake build` passes cleanly
- `grep -r "snce\|Encodable\|Countable\|Infinite\|Denumerable" Cslib/Logics/Temporal/ Cslib/Logics/LTL/` confirms removals
- CI pipeline passes (lake test, checkInitImports, lint-style)

---

### Phase 3: Rebase onto PR #648 [NOT STARTED]

**Goal**: Cleanly rebase `feat/temporal-formula-propositional` onto `feat/propositional-v2` head, resolving all merge conflicts correctly.

**Tasks**:
- [ ] Confirm PR #648 is approved or merged (do not proceed if still `CHANGES_REQUESTED`)
- [ ] Fetch latest `feat/propositional-v2` from upstream
- [ ] Run `git rebase feat/propositional-v2` on `feat/temporal-formula-propositional`
- [ ] Resolve conflicts in `Cslib/Logics/Propositional/Defs.lean`: take PR #648's version as base; `instBot_eq`/`instTop_eq` already removed in Phase 1
- [ ] Resolve conflicts in `Cslib/Foundations/Logic/Connectives.lean`: take PR #648's 71-line version as base; add temporal typeclasses (`HasUntil`, `HasNext`, temporal bundles) on top
- [ ] Resolve conflicts in `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`: keep PR #648's version (includes `instIsIntuitionisticIntuitionisticCompletion`); verify PR #649's changes do not drop it
- [ ] Resolve conflicts in `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`: ensure `IPL (Atom := Atom)` style is consistent with PR #648's Defs.lean
- [ ] Resolve conflicts in `references.bib`: include `Avigad2022` from PR #648 plus temporal refs from PR #649
- [ ] Verify `Cslib.lean` root import file has correct ordering: PR #648's Connectives import position plus PR #649's 3 temporal imports
- [ ] Run `lake build` to verify no Lean elaboration errors after rebase
- [ ] Run full CI pipeline: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Force-push with `--force-with-lease` to `feat/temporal-formula-propositional`

**Timing**: 1.5 hours

**Depends on**: 2 (and external: PR #648 approval)

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Conflict resolution (take PR #648 version)
- `Cslib/Foundations/Logic/Connectives.lean` - Conflict resolution (PR #648 base + temporal classes)
- `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` - Conflict resolution (keep PR #648 instance)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - Conflict resolution (style consistency)
- `references.bib` - Merge both PRs' references
- `Cslib.lean` - Merge import ordering

**Verification**:
- `lake build` passes cleanly after rebase
- `git log --oneline feat/propositional-v2..feat/temporal-formula-propositional` shows only temporal-specific commits
- CI pipeline passes on force-push
- No dropped instances (verify `instIsIntuitionisticIntuitionisticCompletion` exists in Theory.lean)

## Testing & Validation

- [ ] `lake build` passes after each phase
- [ ] `lake test` passes after Phase 2 and Phase 3
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No unused section variable warnings in `Defs.lean`
- [ ] CI pipeline at GitHub Actions passes for PR #649
- [ ] `grep -r "instBot_eq\|instTop_eq" Cslib/` returns no results
- [ ] `snce` operator fully removed from temporal types
- [ ] Irrelevant typeclasses (`Encodable`, `Countable`, `Infinite`, `Denumerable`) removed
- [ ] After rebase, commit history is clean (temporal commits on top of propositional)

## Artifacts & Outputs

- `specs/223_review_fix_pr_649_rebase_on_648/plans/02_fix-ci-rebase.md` (this plan)
- `specs/223_review_fix_pr_649_rebase_on_648/summaries/02_fix-ci-rebase-summary.md` (upon completion)
- Modified files on `feat/temporal-formula-propositional` branch (pushed to origin)

## Rollback/Contingency

- **Phase 1 rollback**: `git revert` the deletion commit if downstream breakage is discovered (unlikely given grep verification)
- **Phase 2 rollback**: Each reviewer change is committed separately; revert individual commits as needed
- **Phase 3 rollback**: Before rebasing, note the pre-rebase HEAD SHA. If rebase produces irrecoverable elaboration errors: `git rebase --abort` or `git reset --hard <pre-rebase-SHA>`. The `--force-with-lease` flag prevents overwriting others' work on the remote.
- **Full rollback**: The original branch state (`5785ebbd`) can be restored at any point via `git reset --hard 5785ebbd` on the local branch (do not force-push without user confirmation).
