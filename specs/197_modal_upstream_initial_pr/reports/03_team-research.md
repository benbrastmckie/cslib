# Research Report: Task #197

**Task**: Scope initial Modal/ upstream PR (~300 LOC)
**Date**: 2026-06-14
**Mode**: Team Research (4 teammates)

## Summary

Team research reveals three critical findings that fundamentally reshape the modal PR strategy: (1) PR #648's `Connectives.lean` does NOT include `HasBox`/`ModalConnectives` — the planned stacking strategy breaks, (2) upstream's `LogicalEquivalence.lean` already exists and MUST be updated in any PR that changes `Basic.lean` constructors, and (3) PR #607 (fmontesi's operator typeclasses) is stalled with unaddressed reviewer concerns that our approach directly resolves. The recommended path is: Zulip coordination with fmontesi first, then a convergence PR of ~355 LOC covering `Basic.lean` + `Denotation.lean` + `LogicalEquivalence.lean` (leaving no broken upstream files).

## Key Findings

### 1. ModalConnectives Gap (Critical — from Critic)

PR #648 (`feat/propositional-v2`) contains only `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`. It does NOT contain `HasBox` or `ModalConnectives` — those were added to local `Connectives.lean` after the propositional PR was created. The plan's assumption that stacking on PR #648 provides `ModalConnectives` is false.

**Resolution options** (ranked):
1. **Defer ModalConnectives** (Strategy 3): Remove the 3-line instance from `Basic.lean`, submit the formula refactoring without typeclass registration. Add it in a follow-up after Connectives.lean expands.
2. **Bundle ~30 LOC subset**: Include just `HasBot`/`HasImp`/`HasBox`/`ModalConnectives` in the modal PR itself, making it self-contained.
3. **Expand PR #648**: Add `HasBox`/`ModalConnectives` to the propositional PR before it merges (risky — changes scope of an already-submitted PR).

### 2. LogicalEquivalence.lean Must Be Included (Critical — from Horizons + Critic)

Upstream already has `LogicalEquivalence.lean` (~117 lines) with `Proposition.Context` constructors `{not, andL, andR, diamond}`. Changing `Basic.lean` primitives breaks this file immediately. The prior plan deferred it to "PR 3" but that's not viable — upstream CI would fail on merge.

**Resolution**: Include `LogicalEquivalence.lean` in the PR scope. The local version is actually shorter (84 vs 132 LOC) and drops a framework dependency — a net simplification.

### 3. PR #607 Alignment Opportunity (Strategic — from Primary + Horizons)

PR #607 (fmontesi) has `CHANGES_REQUESTED` for 13+ days with no response. Key reviewer concerns:
- chenson2018 wants **fewer files** (one file, not 8 separate `Operators/*.lean`) — our `Connectives.lean` does exactly this
- chenson2018 identified **grind/simp direction problems** — our explicit proof style avoids this entirely
- fmontesi is **uncertain** about the architecture ("I don't know yet")

Our PR can be framed as a convergence proposal addressing #607's open concerns, not a competitor.

### 4. Import Path Fix Required (from Primary)

PR #632 (merged 2026-06-13) moved `Cslib.Foundations.Data.Relation` to `Cslib.Foundations.Relation.Euclidean`. The PR branch must use the new path — the local fork hasn't absorbed this split.

### 5. Cube.lean Likely Safe but Unverified (from Critic)

Cube.lean uses no formula constructors directly (no pattern matching on `.not`, `.and`, `.diamond`). However, the `grind =_` vs `grind =` direction change on `derivation_def` has not been tested. The plan should include a contingency for Cube.lean failures.

### 6. Unanalyzed Upstream Branch (from Critic)

The `upstream/modal-equiv` remote branch exists but appears in none of the research or plans. Should be investigated before submission.

## Synthesis

### Conflicts Resolved

1. **LOC scope (Teammate A vs B)**: Teammate A recommended ~290 LOC (Basic + Denotation). Teammate B offered 5 options from 244 to 385 LOC. Teammate D showed LogicalEquivalence must be included. **Resolution**: ~355 LOC (Basic + Denotation + LogicalEquivalence) — exceeds the 300 target but leaves no broken files. The net change is actually negative (more deletions than insertions).

2. **ModalConnectives strategy (all teammates)**: All teammates identified the dependency gap. Teammate B's Strategy 3 (defer) is the cleanest for the initial PR. Teammate D's convergence framing doesn't require ModalConnectives in this PR — it can come in the PR that extends Connectives.lean with `HasBox`.

3. **Submission timing (Teammate A vs D)**: Teammate A says wait for PR #648 feedback. Teammate D says coordinate on Zulip before any code. **Resolution**: Do both — Zulip conversation first (addresses #607 and introduces the primitive set discussion), then submit the modal PR after #648 gets initial feedback.

### Gaps Identified

1. **No CI verification on PR branch**: The entire plan is speculative until `lake build` runs on an actual branch based on `upstream/main`.
2. **`upstream/modal-equiv` branch unanalyzed**: Unknown risk.
3. **`grind =_` vs `grind =` on Cube.lean**: Direction change may cause silent failures.
4. **PR description doesn't warn about `derivation_def` direction change** in breaking changes.

### Recommendations

**Recommended PR scope** (~355 LOC, 3 modified files + 1 import line):
1. `Cslib/Logics/Modal/Basic.lean` — refactor to `{atom, bot, imp, box}` primitives, WITHOUT `ModalConnectives` instance (defer to follow-up)
2. `Cslib/Logics/Modal/Denotation.lean` — update match cases for new primitives
3. `Cslib/Logics/Modal/LogicalEquivalence.lean` — update Context constructors for new primitives
4. `Cslib.lean` — no change needed (files already exist upstream)

**Pre-submission checklist** (NEW):
1. Draft Zulip message to fmontesi framing convergence with #607
2. Fix `Cslib.Foundations.Data.Relation` → `Cslib.Foundations.Relation.Euclidean` import
3. Investigate `upstream/modal-equiv` branch
4. Build and test on actual PR branch (verify Cube.lean compiles)
5. Document `LogicalEquivalence.lean` update and `derivation_def` direction change in PR description
6. Wait for PR #648 initial feedback before submitting

**Strategic framing**: "We share PR #607's operator-typeclass vision. We propose a consolidated single-file approach (addressing chenson2018's review concern) with a primitive set that supports non-classical extensions and matches the standard textbook treatment."

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Upstream PR review + landscape | completed | high |
| B | Local codebase + scoping options | completed | high |
| C | Critic: gaps and blind spots | completed | high |
| D | Strategic alignment + horizons | completed | high |

## References

- PR #648: https://github.com/leanprover/cslib/pull/648
- PR #607: https://github.com/leanprover/cslib/pull/607
- PR #632: Relation module split (merged)
- PR #536: thomaskwaring's inference system refactoring
- PR #587: thomaskwaring's notation+models (draft)
- Teammate findings: `specs/197_modal_upstream_initial_pr/reports/03_teammate-{a,b,c,d}-findings.md`
