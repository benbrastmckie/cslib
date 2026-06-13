# Research Report: Task #169

**Task**: 169 - Recreate the Modal primitives refactor as a clean, small PR against upstream leanprover/cslib main
**Started**: 2026-06-12T22:15:00-07:00
**Completed**: 2026-06-12T22:45:00-07:00
**Effort**: 1.5h research
**Dependencies**: PR #635 (open, not merged)
**Sources/Inputs**: Local git history, upstream/main, refactor/modal-primitives branch, GitHub PR #635 and #637
**Artifacts**: - specs/169_recreate_modal_primitives_pr_upstream/reports/01_clean-modal-pr-research.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- PR #637 was closed because it ballooned to ~100 commits due to task 167 rebasing onto fork/main (38+ personal commits). The actual PR-scope changes are only 2 commits (54a0945e, 3928feb4) touching 10 files total.
- The clean Modal PR requires PR #635 to merge first (or be bundled): Modal/Basic.lean imports `Cslib.Foundations.Logic.Connectives` which doesn't exist on upstream/main yet.
- **Recommended strategy**: Create a new branch `refactor/modal-primitives-v2` from upstream/main, cherry-pick ONLY the Modal-scope commit (3928feb4), and replace the Connectives import with a stripped version OR stack the PR on PR #635's branch.
- The pure Modal-only diff (against upstream/main after #635 merges) is: **4 files, +343/-219 lines** (562 total changed lines) — well within "not too big to review" scope.
- PR #635 itself is **6 files, ~+520/-110 lines** — also small and reviewable.

## Context & Scope

### Upstream State (as of 2026-06-12)

`upstream/main` is 5 commits ahead of the local `main`:
- `d6c0b903` feat(Data/PFunctor): add free monad of a polynomial functor (#477)
- `1f601a24` chore: bump mathlib to 8589236, fix breaking changes (#628)
- `616e04b0` doc: prefer +/- for Boolean `optConfig` (#620)
- `e3991ff2` feat: logical equivalence for modal logic (#535)
- `edfa9742` Add chenson2018 explicitly to logic CODEOWNERS

`upstream/main` Modal/ directory contains 4 files:
- `Cslib/Logics/Modal/Basic.lean` (277 lines, primitives: `{atom, not, and, diamond}`)
- `Cslib/Logics/Modal/Cube.lean` (unaffected by primitive change)
- `Cslib/Logics/Modal/Denotation.lean` (51 lines, grind-based proofs)
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (132 lines, uses `{not, andL, andR, diamond}` Context, added by PR #535)

`upstream/main` does NOT have `Cslib/Foundations/Logic/Connectives.lean`.

### PR #635 Status

PR #635 ("refactor: Proposition type to bot/imp primitives") is **OPEN** on branch `refactor/proposition-lukasiewicz`. It has NOT merged.
Files: Cslib.lean (+1), Cslib/Foundations/Logic/Connectives.lean (new, 114 lines), Cslib/Foundations/Logic/InferenceSystem.lean (2+2-), Cslib/Logics/Propositional/Defs.lean (86+52-), Cslib/Logics/Propositional/NaturalDeduction/Basic.lean (108-reform), references.bib (62+).
Diff size: ~376 lines changed total.

### PR #637 Closure

Chenson2018 closed PR #637 with this comment:
> "Hi @benbrastmckie. Thanks again for your interest in contributing, but a PR of this size is not feasible to review, independent of any concerns about AI usage. I think that #635 where you've split out a small first PR is a step in the right direction."

The "size" issue was caused by task 167 rebasing the branch onto fork/main, adding 38+ personal commits. The maintainer's message affirms PR #635 is the right direction.

## Findings

### The Two Real PR Commits

The `refactor/modal-primitives` branch history shows the PR's own commits are:

```
3928feb4 refactor(Modal): Hilbert-style primitives for modal propositions  [Modal layer]
54a0945e refactor: Proposition to bot/imp primitive basis                  [= PR #635 content]
7b8fc12f doc: prefer +/- for Boolean `optConfig` (#620)                    [upstream]
b09f64bb feat: logical equivalence for modal logic (#535)                  [upstream]
ed44f28b Add chenson2018 explicitly to logic CODEOWNERS                    [upstream]
```

These two commits (54a0945e + 3928feb4) are the ENTIRE PR content. They were made on top of upstream-equivalent state, so they have clean diffs relative to upstream.

**Commit 54a0945e** (Propositional refactor = PR #635 content):
- `Cslib/Foundations/Logic/Connectives.lean` (+22/-6, adds BimodalConnectives)
- `Cslib/Logics/Propositional/Defs.lean` (+5/-2)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (+2/-1)

**Commit 3928feb4** (Modal primitives refactor = PR #637 content):
- `Cslib/Logics/Modal/Basic.lean` (+19/-3 from prior commit state = +123/−277 from upstream)
- `Cslib/Logics/Modal/Denotation.lean` (+8/-1)
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (+158/-121 from prior = complete rewrite)

### Diff Statistics vs Upstream

| Scope | Files | +lines | -lines | Total |
|-------|-------|--------|--------|-------|
| PR #635 alone (vs upstream) | 6 | +520 | +110 | ~376 lines |
| Modal PR alone (vs upstream after #635) | 4 | +343 | −219 | 562 lines |
| Combined (vs upstream/main) | 10 | +863 | −329 | 1192 lines |

### Connectives.lean Dependency

The Modal PR REQUIRES `Cslib/Foundations/Logic/Connectives.lean` because:
1. `Modal/Basic.lean` has `public import Cslib.Foundations.Logic.Connectives`
2. `Modal/Basic.lean` registers `instance : ModalConnectives (Proposition Atom)`

Without Connectives.lean, the Modal PR won't compile. Three options:

**Option A (RECOMMENDED)**: Stack the Modal PR on PR #635's branch. Create branch from tip of `origin/refactor/proposition-lukasiewicz`, cherry-pick only the Modal commit. When viewed against upstream/main this shows both changes, but when reviewed as a stacked PR (base = PR #635 branch) it shows only 4 files.

**Option B**: Bundle Connectives.lean into the Modal PR directly (self-contained, 10 files total, 1192 lines changed). Slightly more complex because it overlaps with PR #635.

**Option C**: Strip the ModalConnectives instance (only 2 lines in Basic.lean). Creates a 4-file self-contained Modal PR (~562 lines). This loses the typeclass instance but makes the PR standalone and reviewable without waiting for #635.

### Notation Compatibility

Upstream/main's `Propositional/Defs.lean` already has scoped notation (`∧`, `∨`, `→`, `¬`, `⊥`, `⊤`) but these are for the Propositional layer. The Modal layer PR adds its own `⊥`, `→`, `¬`, `∧`, `∨`, `◇`, `□`, `↔` scoped notation in `Modal/Basic.lean`.

After the primitive change, the upstream `LogicalEquivalence.lean` (added by PR #535) MUST be updated in the same PR because it uses `{not, andL, andR, diamond}` Context constructors that no longer exist. The PR's new `LogicalEquivalence.lean` uses `{hole, impL, impR, box}` Context constructors.

### Cube.lean Not Affected

`Cslib/Logics/Modal/Cube.lean` uses the `logic` function (set of valid propositions) but never pattern-matches on proposition constructors. It compiles without changes after the primitive change.

### GrindLint Changes

The PR adds 3 `#grind_lint skip` entries to `CslibTests/GrindLint.lean`:
```
#grind_lint skip Cslib.Logic.Modal.neg_denotation
#grind_lint skip Cslib.Logic.Modal.Satisfies.and_iff_and
#grind_lint skip Cslib.Logic.Modal.Satisfies.or_iff_or
```

### Maintainer Preferences

From PR #637 closing comment and PR #635 body:
- chenson2018 wants PRs "not too big to review"
- PR #635 was called "a step in the right direction"
- PR #635 at ~376 lines changed is the right size target
- A pure Modal PR at ~562 lines changed is acceptable (slightly bigger but single topic)
- Combined PRs at ~1192 lines are borderline for "not too big"

## Decisions

1. **Use commit 3928feb4 as source of truth** for the Modal PR content (it was verified CI-green at that commit, and is the upstream-relative version with proper authorship)
2. **Preferred approach is Option A (stacked)**: Create branch from PR #635 tip, add one Modal commit via cherry-pick or manual file copy. This gives the maintainer the cleanest possible review (4 Modal files only when viewed as stacked PR)
3. **Fallback approach is Option C (standalone)**: Strip the 2 ModalConnectives lines from Basic.lean, create a self-contained 4-file PR. Acceptable if PR #635 review is slow.
4. **Do NOT rebase onto fork/main again** — this was the root cause of PR #637's bloat. Create branch from upstream/main or PR #635 tip ONLY.

## Implementation Plan for Clean PR Creation

### Branch Construction (Option A — Stacked on PR #635)

```bash
# Start from PR #635's branch tip
git checkout -b refactor/modal-primitives-v2 origin/refactor/proposition-lukasiewicz

# Cherry-pick only the Modal commit (commits from upstream already in PR #635 branch)
git cherry-pick 3928feb4

# Verify: expected diff is 4 files (~562 lines)
git diff origin/refactor/proposition-lukasiewicz..HEAD --stat
```

**Expected diff stat (stacked view)**:
```
Cslib/Logics/Modal/Basic.lean              |  ~123 changes
Cslib/Logics/Modal/Denotation.lean         |   ~34 changes
Cslib/Logics/Modal/LogicalEquivalence.lean |  ~164 changes
CslibTests/GrindLint.lean                  |    +3
```

### Branch Construction (Option C — Standalone)

```bash
# Start from upstream/main
git fetch upstream
git checkout -b refactor/modal-primitives-v2 upstream/main

# Copy the 4 Modal files from commit 3928feb4
git checkout 3928feb4 -- \
  Cslib/Logics/Modal/Basic.lean \
  Cslib/Logics/Modal/Denotation.lean \
  Cslib/Logics/Modal/LogicalEquivalence.lean \
  CslibTests/GrindLint.lean

# Strip the Connectives import and ModalConnectives instance from Basic.lean
# (2 lines: remove `public import Cslib.Foundations.Logic.Connectives`
#           remove the ModalConnectives instance block)

# Verify CI compiles
lake build Cslib.Logics.Modal
```

### Verification Steps (Both Options)

```bash
lake test
lake exe checkInitImports
lake exe lint-style
lake shake --add-public --keep-implied --keep-prefix
```

## Risks & Mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Cherry-pick of 3928feb4 has conflicts | Medium | The commit only changes 3 Modal files; conflicts would be minor (copyright header, Design Notes in LogicalEquivalence.lean) |
| LogicalEquivalence.lean rewrite breaks downstream | Low | `Proposition.Equiv` is not used outside Modal/ in upstream codebase |
| PR #635 delays review of Modal PR | Medium | Use Option C (standalone) if #635 is stalled |
| Maintainer wants even smaller PR | Low | Could split LogicalEquivalence.lean into separate PR, leaving just Basic.lean + Denotation.lean (~2 files) |
| ModalConnectives instance removed in Option C creates API gap | Low | Can be re-added later after #635 merges, or submitted as follow-up |

## Context Extension Recommendations

- **Topic**: PR stacking strategy for cslib contributions
- **Gap**: No documented guidance on stacked PRs vs. standalone PRs for cslib
- **Recommendation**: Add a note to `.claude/context/repo/project-overview.md` about the cslib maintainer's preference for small, standalone PRs and the stacked-PR workflow

## Appendix

### Search Queries Used
- `git log --oneline refactor/modal-primitives` — identified the 2 real PR commits
- `git diff upstream/main..3928feb4 --stat` — measured PR scope
- `gh pr view 635 --repo leanprover/cslib --json ...` — PR #635 status and files
- `gh pr view 637 --repo leanprover/cslib --json ...` — PR #637 closing comment
- `git show upstream/main:Cslib/Foundations/Logic/Connectives.lean` — confirmed file absent

### Key File SHA References
- Commit 3928feb4: Modal PR content (CI-green, upstream-relative)
- Commit 54a0945e: Propositional PR content (= PR #635 content)
- Branch `origin/refactor/proposition-lukasiewicz`: PR #635 current branch tip
- `upstream/main`: leanprover/cslib main at time of research
