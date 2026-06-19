# Research Report: Task #197

**Task**: 197 - modal_upstream_initial_pr
**Started**: 2026-06-15T09:00:00Z
**Completed**: 2026-06-15T09:45:00Z
**Session**: sess_1781531573_4cdbb4
**Standards**: report-format.md

## Executive Summary

- The upstream PR landscape has **no direct competing PRs** for the modal formula-type refactoring: the only OPEN PR touching `Modal/Basic.lean` is PR #607 (fmontesi), which proposes typeclass wrappers over the *existing* `{atom, not, and, diamond}` primitives rather than replacing them, and is currently blocked by CHANGES_REQUESTED from chenson2018 since 2026-05-29 with no further update.
- PR #648 (OPEN, our propositional connective typeclasses) and PR #649 (OPEN, our temporal formula type) are the two upstream PRs we own, both stacking independently off `main`; neither has received any reviewer comments yet.
- The key naming conflict is `HasImpl` (PR #607, fmontesi) vs `HasImp` (our PR #648/649). PR #607's CHANGES_REQUESTED status and the chenson2018 feedback suggesting "one file for all these" rather than per-operator files creates an opening for our `Connectives.lean` single-file approach to win on ergonomics grounds.
- The planned Modal PR should explicitly reference PR #607 in its description, framing our refactoring as a convergence path that makes the per-operator typeclass question moot (the refactored `Proposition` uses `imp` natively, removing the need for `HasImpl.impl` as an alias).
- The Modal PR should stack on PR #648 (`feat/propositional-v2`) in the same manner that PR #649 stacks on it — carrying #648's `Connectives.lean` changes and branching from its head. This keeps the Modal PR independent of the temporal additions in PR #649, making it simpler to review and merge independently.
- No Zulip discussion threads were found in issue comments about the Modal signature direction specifically; the coordination opportunity is in the PR description itself.

## Context & Scope

This research audits the upstream `leanprover/cslib` PR landscape as of 2026-06-15 to determine:
1. Which PRs touch `Modal/` or `Connectives.lean` and in what state
2. What naming conflicts exist between our approach and active PRs
3. The recommended stacking and coordination strategy for the planned Modal PR

The planned Modal PR proposes: refactoring `Modal/Proposition` from `{atom, not, and, diamond}` to `{atom, bot, imp, box}` primitives, updating `Denotation.lean` match cases, updating `LogicalEquivalence.lean` Context constructors, and extending `Connectives.lean` with `HasBox`/`ModalConnectives` (~25 LOC). This is documented in plan v3: `plans/05_modal-upstream-pr-plan.md`.

## Findings

### PR Inventory: Modal-Related PRs

#### PR #528 — feat: Modal Logic (MERGED, 2026-04-29)
- **Author**: fmontesi
- **Files**: `Cslib/Logics/Modal/Basic.lean` (new file, 486 insertions)
- **What it did**: Introduced the current upstream `Modal/Basic.lean` with `{atom, not, and, diamond}` primitives, the `Model`/`Satisfies`/`Judgement` structures, all modal cube axioms (K, T, B, 4, 5, D), and the `TheoryEq` definition.
- **Relevance**: This is the origin of the `{atom, not, and, diamond}` signature our plan proposes to refactor.

#### PR #535 — feat: logical equivalence for modal logic (MERGED, 2026-05-02)
- **Author**: fmontesi
- **Files**: `Cslib/Logics/Modal/LogicalEquivalence.lean` (new), `Cslib/Logics/Modal/Basic.lean` (minor)
- **What it did**: Added `LogicallyEquivalent`, proved it is a `Congruence` and `LogicalEquivalence` for logic K. The `Proposition.Context` type has constructors `{hole, notC, andL, andR, diamondC}` matching the original `{not, and, diamond}` primitives.
- **Relevance**: Our Modal PR MUST update `LogicalEquivalence.lean` because changing Basic.lean's primitives breaks this `Context` type. Plan v3 already accounts for this.

#### PR #607 — feat(Logic): logical operators (OPEN, CHANGES_REQUESTED)
- **Author**: fmontesi
- **Status**: OPEN — `reviewDecision: CHANGES_REQUESTED` by chenson2018 since 2026-05-29; last updated 2026-06-01, no further author response visible.
- **Files changed**: `Cslib.lean`, `Cslib/Foundations/Logic/Operators/{And,Box,Diamond,Iff,Impl,Not,Or,Tensor}.lean` (8 new files), `Cslib/Logics/Modal/Basic.lean`, `Cslib/Logics/Propositional/Defs.lean`
- **What it proposes**: Creates 8 separate operator typeclass files under `Foundations/Logic/Operators/`. Each file defines one class: `HasAnd`, `HasBox`, `HasDiamond`, `HasIff`, `HasImpl`, `HasNot`, `HasOr`, `HasTensor`. `Modal/Basic.lean` is updated to register instances of these classes while **keeping the existing `{atom, not, and, diamond}` constructor set** — it adds typeclass wrappers over the existing constructors rather than changing them. `Propositional/Defs.lean` also registers instances.
- **Key naming detail**: PR #607 uses `HasImpl` (field: `impl`) and `HasBox` (field: `box`). Our approach uses `HasImp` (field: `imp`) from the consistent naming in Bimodal/Temporal formula types. `HasBox` is compatible — same name and semantics.
- **Reviewer feedback (chenson2018)**:
  - "Would it be better to just have one file for these? If they're just notation typeclasses it seems unlikely to be heavyweight and they're likely to be used together." — directly suggests consolidation into a single file (our `Connectives.lean` approach).
  - "Are these `simp`/`grind =` lemmas all backwards?" — the direction of unfolding lemmas (notation → constructor vs constructor → notation) needs resolution.
  - "This should not be undone, `grind?` still fails here." — a specific regression in the `dual` theorem fix.
- **Conflict assessment**: The naming `HasImpl` vs `HasImp` is a real conflict if both files exist. However, PR #607 has CHANGES_REQUESTED and has been stalled since June 1. Our `Connectives.lean` with `HasImp` was introduced in PR #648 (which PR #607 predates). If PR #648 merges first, PR #607 would need to align to `HasImp`.
- **Structural conflict**: PR #607's approach keeps `{not, and, diamond}` as Modal primitives; our PR changes them to `{bot, imp, box}`. These are **mutually incompatible** at the constructor level — only one approach can win for the current `Proposition` type. Our approach is the substantive refactoring; PR #607 is an overlay.

#### PR #648 — feat(Logics/Propositional): five-primitive formula type (OPEN, no reviews)
- **Author**: benbrastmckie (our PR)
- **Status**: OPEN, no inline comments or reviews received as of 2026-06-15.
- **Files changed**: `Cslib.lean`, `Cslib/Foundations/Logic/Connectives.lean` (new), `Cslib/Logics/Propositional/Defs.lean`, `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- **What it proposes**: New `Connectives.lean` with `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`; refactors `Proposition` to `{atom, bot, imp, and, or}`.
- **Relevance to Modal PR**: Modal PR should stack on this branch (`feat/propositional-v2`) to have access to `Connectives.lean`, in the same manner that PR #649 stacks on it. This keeps the Modal PR independent of temporal additions.

#### PR #649 — feat(Logics/Temporal): temporal formula type (OPEN, no reviews)
- **Author**: benbrastmckie (our PR, stacking target for Modal PR)
- **Status**: OPEN, no inline comments or reviews received as of 2026-06-15.
- **Base branch**: `main` (not PR #648's branch — PR #649's `feat/temporal-formula-propositional` branch carries all of PR #648's changes plus the temporal additions, so it is effectively stacked even though the GitHub base is `main`).
- **Files changed**: Same 4 files as PR #648 plus `Cslib/Logics/Temporal/Syntax/Formula.lean` and `references.bib`.
- **What it proposes**: Extends `Connectives.lean` with `HasUntil`, `HasSince`, `TemporalConnectives`; adds `Formula.lean` with temporal formula type.
- **Relevance**: PR #649 demonstrates the stacking pattern the Modal PR should follow — branching from PR #648's `feat/propositional-v2` and carrying its `Connectives.lean` changes. The Modal PR should stack on #648 directly (not #649) to remain independent of temporal additions.

#### Closed PRs (ours, for context)
- **PR #636** (CLOSED 2026-06-12): Superseded by #637.
- **PR #637** (CLOSED 2026-06-12): `refactor(Modal): bot/imp/box primitives` — 366,642 additions due to branch carrying entire history. Closed after chenson2018's comment: "A PR of this size is not feasible to review."
- **PR #635** (CLOSED 2026-06-12): Lukasiewicz Proposition refactoring (superseded by #648).
- **PR #633** (CLOSED 2026-06-11): 7,894 line PR with complete propositional logic. Closed after size feedback.
- **PR #629, #630** (CLOSED): Earlier iterations of foundations PR.

### Upstream State of Modal Files

The current upstream `main` branch has exactly 4 files in `Cslib/Logics/Modal/`:
- `Basic.lean` — `{atom, not, and, diamond}` primitives (fmontesi/PR #528 state)
- `Cube.lean` — 15 modal logics and their relationships
- `Denotation.lean` — denotational semantics
- `LogicalEquivalence.lean` — `Context` with `{hole, notC, andL, andR, diamondC}` constructors

`Cslib/Foundations/Logic/Connectives.lean` does **not exist** in upstream `main`. It exists only in our PR branches (`feat/propositional-v2`, `feat/temporal-formula-propositional`).

### PR #607 Conflict: Detailed Analysis

The table below compares the two approaches on `Connectives.lean`/`Operators/` for the implication class:

| Dimension | PR #607 (fmontesi) | Our PRs (#648, #649) |
|-----------|-------------------|---------------------|
| File structure | 8 separate files under `Operators/` | Single `Connectives.lean` |
| Implication class | `HasImpl` (field: `impl`) | `HasImp` (field: `imp`) |
| Box class | `HasBox` (field: `box`) | `HasBox` (field: `box`) — compatible |
| Namespace | `Cslib.Logic` | `Cslib.Logic` — compatible |
| Modal/Basic approach | Adds typeclass instances; keeps `{not, and, diamond}` | Refactors to `{bot, imp, box}`; adds typeclass instance |
| Reviewer status | CHANGES_REQUESTED (stalled ~2 weeks) | No reviews yet |

The `HasBox` class is **naming-compatible** between the two PRs. The conflict is in `HasImpl` vs `HasImp` and in the fundamental modal signature question.

### No Additional Modal PRs Detected

A full search (`gh pr list -R leanprover/cslib --search "modal" --state all --limit 50`) found no other contributors with OPEN PRs touching `Modal/`. The two merged PRs (#528, #535) are fmontesi's original contributions. No OPEN issues about modal logic direction were found.

### PR #574 — more lemmas on Euclidean relations (MERGED, 2026-05-19)

- **Author**: chenson2018
- **Relevance**: PR #607 for Euclidean relation import path change. Our plan v3 already accounts for updating the import from `Cslib.Foundations.Data.Relation` to `Cslib.Foundations.Relation.Euclidean` (which PR #632 relation-split also affects).

### PR #587 — Notation typeclasses and models (DRAFT)

- **Author**: thomaskwaring
- **Status**: DRAFT — proposes `Models`, `ParamModels`, `InterpModels` typeclasses for semantic abstraction.
- **Conflict**: Described in PR #648's description as "orthogonal" (syntactic vs semantic levels). No direct conflict with the Modal PR plan.

## Decisions

1. **PR #607 does not block our plan**: PR #607 is CHANGES_REQUESTED and stalled. Our Modal PR can proceed independently. We should explicitly acknowledge PR #607 in our PR description, noting that our `Connectives.lean` consolidates the same functionality into one file (addressing chenson2018's structural feedback on #607 proactively).

2. **Stack on `feat/propositional-v2` (PR #648)**: The Modal PR branch should be created from PR #648's branch (`feat/propositional-v2`), in the same manner that PR #649 stacks on it. This gives access to `Connectives.lean` with `PropositionalConnectives` while keeping the Modal PR independent of temporal additions — simpler to review and merge independently. The `HasBox`/`ModalConnectives` addition to `Connectives.lean` is purely additive on top of #648's propositional classes.

3. **`HasBox` naming is already compatible**: PR #607 uses `HasBox` with field `box`. Our plan also uses `HasBox` with field `box`. No renaming needed.

4. **`HasImpl` vs `HasImp` conflict**: If PR #607 ever merges (requires resolution of CHANGES_REQUESTED), the naming would conflict. However: (a) PR #607 is currently blocked, (b) chenson2018's own feedback suggests consolidating to one file (our approach), and (c) fmontesi is both PR #607's author and a requested reviewer on PR #648 — he can align #607 to `HasImp` if #648 merges first. Our Modal PR description should note this lineage.

5. **LogicalEquivalence.lean must be included**: Confirmed again — current upstream `Context` has `{notC, andL, andR, diamondC}` constructors; these break when `{not, and, diamond}` constructors are removed from `Proposition`.

## Recommendations

### 1. Submit Modal PR Stacked on PR #648 (Primary Recommendation)

**Strategy**: Create branch `feat/modal-formula-classical` from `feat/propositional-v2` (PR #648), following the same stacking pattern as PR #649. Add `HasBox`/`ModalConnectives` to `Connectives.lean`, then overwrite the three Modal files with our `{bot, imp, box}` versions. This keeps the Modal PR independent of temporal additions, making it reviewable and mergeable on its own.

**Why now**: PR #648 and #649 have been OPEN with no reviewer activity. Submitting the Modal PR now establishes our intent before #607's author can restart their work with incompatible signatures. Stacking on #648 (not #649) means the Modal PR can merge as soon as #648 merges, without waiting for #649.

**PR description framing**: Explicitly reference PR #607, noting that our approach addresses chenson2018's structural feedback (single file vs 8 files), and that `HasImpl` → `HasImp` is a one-character rename aligning with CSLib's Bimodal/Temporal naming convention. Frame the classical signature refactoring as enabling the typeclass approach (once primitives are `{bot, imp, box}`, the `HasImp`/`HasBox` instances work without impedance mismatch from derived-vs-primitive confusion).

### 2. Address the `HasImpl` vs `HasImp` Conflict Proactively

In the Modal PR description, include a section:

> **Relationship to PR #607**: PR #607 by @fmontesi introduces per-operator typeclasses under `Operators/`. Our `Connectives.lean` consolidates this into a single file (as suggested in the review). The only naming difference is `HasImpl`/`impl` vs `HasImp`/`imp`; `HasBox`/`box` is identical. The `imp` naming is used in CSLib's Bimodal and Temporal formula types, and aligns constructor names with rule name prefixes (`impI`/`impE`). If #607 moves forward, updating `HasImpl` → `HasImp` is a one-line change.

### 3. Coordinate with fmontesi via Zulip Before or Concurrent with PR Submission

Since fmontesi is the original `Modal/` author (PRs #528, #535), is a requested reviewer on #648 and #649, and is the author of the competing PR #607, a Zulip message on the CSLib channel pointing to our Modal PR and referencing the signature debate would be appropriate. The message should:
- Link to the PR
- Acknowledge PR #607's approach and our rationale for `HasImp` over `HasImpl`
- Invite feedback on `HasBox` (compatible) and `ModalConnectives` bundled class design

The appropriate Zulip channel is [CSLib > Modal Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic) or equivalent.

### 4. Two-PR Dependency Chain (Not Three)

The Modal PR stacks on PR #648 directly, giving a two-PR dependency chain (#648 → Modal). PR #649 (temporal) is a sibling, not a prerequisite — both #649 and the Modal PR independently stack on #648. The PR description should note the dependency on #648 and request review in that order.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #607 resumes and CHANGES_REQUESTED are addressed before our Modal PR | H | L | Our PR establishes prior art for `HasImp`/single-file approach; fmontesi as reviewer on #648/#649 is already engaged with our naming choices |
| chenson2018 prefers PR #607's per-operator file approach | H | L | chenson2018 explicitly asked "would it be better to just have one file?" — our consolidation is aligned with their feedback |
| PR #648 receives breaking feedback (e.g., `HasImp` → `HasImpl`) before Modal PR is reviewed | M | M | Monitor #648 comments; Modal PR should be ready to rebase if naming changes |
| Three-PR dependency chain (#648 → #649 → Modal) delays review | M | M | All three PRs note the dependency; request sequential review; no blocking CI issues expected |
| Upstream changes to `Cube.lean` or `Denotation.lean` between now and PR submission | L | L | Both files exist and are stable; CI build will catch regressions |

## Appendix

### Commands Used

```bash
gh pr list -R leanprover/cslib --search "modal" --state all --limit 50
gh pr list -R leanprover/cslib --state all --limit 100
gh pr view 528 -R leanprover/cslib
gh pr view 535 -R leanprover/cslib
gh pr view 607 -R leanprover/cslib
gh pr view 637 -R leanprover/cslib
gh pr view 648 -R leanprover/cslib
gh pr view 649 -R leanprover/cslib
gh pr diff 607 -R leanprover/cslib --name-only
gh pr diff 607 -R leanprover/cslib  # (sampled for Operators/ and Modal/Basic changes)
gh api repos/leanprover/cslib/pulls/607/comments
gh api repos/leanprover/cslib/contents/Cslib/Foundations/Logic/Connectives.lean  # → 404 (not in main)
gh api repos/benbrastmckie/cslib/git/blobs/<sha>  # (for temporal branch Connectives.lean)
```

### PR Status Summary Table

| PR | Title | State | Author | Files Touching Modal/ |
|----|-------|-------|--------|----------------------|
| #528 | feat: Modal Logic | MERGED | fmontesi | Basic.lean (added) |
| #535 | feat: logical equivalence for modal logic | MERGED | fmontesi | LogicalEquivalence.lean (added), Basic.lean |
| #607 | feat(Logic): logical operators | OPEN (CHANGES_REQUESTED) | fmontesi | Basic.lean (typeclass wrappers, keeps {not,and,diamond}) |
| #636 | refactor(Modal): bot/imp/box (lukasiewicz) | CLOSED | benbrastmckie | Basic.lean, Denotation, LogicalEquivalence |
| #637 | refactor(Modal): bot/imp/box primitives | CLOSED | benbrastmckie | Basic.lean, Denotation, LogicalEquivalence |
| #648 | feat(Propositional): five-primitive formula type | OPEN (no reviews) | benbrastmckie | None directly; adds Connectives.lean |
| #649 | feat(Temporal): temporal formula type | OPEN (no reviews) | benbrastmckie | None directly; extends Connectives.lean |
| Planned | refactor(Modal): classical {bot,imp,box} primitives | Not submitted | benbrastmckie | Basic.lean, Denotation.lean, LogicalEquivalence.lean |

### References

- PR #528: https://github.com/leanprover/cslib/pull/528
- PR #535: https://github.com/leanprover/cslib/pull/535
- PR #607: https://github.com/leanprover/cslib/pull/607
- PR #648: https://github.com/leanprover/cslib/pull/648
- PR #649: https://github.com/leanprover/cslib/pull/649
- Local plan v3: `specs/197_modal_upstream_initial_pr/plans/05_modal-upstream-pr-plan.md`
