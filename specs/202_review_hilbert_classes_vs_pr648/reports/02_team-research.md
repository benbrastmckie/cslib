# Team Research Report: PR #648 Comprehensive Review

**Task**: 202 — Comprehensive review of cslib PR #648
**Date**: 2026-06-15
**Mode**: Team Research (4 teammates)
**Session**: sess_1781542911_02c650

## Summary

Four research teammates investigated PR #648 from complementary angles: primary reviewer feedback analysis (A), alternative design patterns (B), critical gaps and blind spots (C), and strategic alignment (D). The investigation was prompted by a reviewer comment at Zulip message near/603367168, which **none of the teammates could retrieve** due to Zulip requiring JavaScript rendering and authentication. All findings below are grounded in PR analysis, codebase examination, and GitHub API data — not the specific Zulip comment.

The PR is well-designed and follows Lean 4 best practices. The most actionable findings are: (1) a live naming conflict with PR #607 (`HasImp` vs `HasImpl`), (2) internal task references that must be removed, (3) modal/temporal scope creep in a "propositional" PR, and (4) strategic opportunities for Zulip engagement with the new logic area maintainer.

---

## Critical Gap: Zulip Comment Unread

All four teammates attempted to fetch `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/603367168` and failed. The Lean Prover Zulip requires JavaScript rendering and API authentication. This is the same limitation documented in task 207 for a different Zulip URL.

**Implication**: The specific reviewer concern that motivated this research round is unknown. All analysis below provides a framework for likely concerns based on PR content, reviewer history, and codebase analysis — but the user must read the actual Zulip message to ground the response.

---

## Key Findings

### 1. Live Naming Conflict with PR #607 (HIGH priority)

**All four teammates** identified this as the top concern. PR #607 (Montesi, the lead maintainer) defines `class HasImpl` with field `impl`; PR #648 defines `class HasImp` with field `imp`. Both modify `Defs.lean`, creating a hard merge conflict.

**Technical assessment** (unanimous across teammates): `HasImp`/`imp` is the stronger convention because:
- CSLib's four existing formula types (Modal, Temporal, Bimodal, Propositional) all use `imp`
- Rule naming convention (`impI`/`impE`) aligns with `imp`
- PR #648 renames `Proposition.impl` → `Proposition.imp`, making `HasImpl` inconsistent after the rename

**PR #607 context** (from D): Currently has CHANGES_REQUESTED status. The reviewer discussion on #607 actually favored a consolidated single file (like PR #648's `Connectives.lean`) over per-operator files. This means PR #648's architecture is more aligned with reviewer preferences than PR #607 itself.

**Recommended action**: Make the technical argument for `HasImp` explicitly in the Zulip thread, before PR #607 is finalized. The argument is strong and should be made early.

### 2. Internal Task References Must Be Removed (HIGH priority)

**Teammate C** found that `Connectives.lean` contains references to "task 173" — an internal project management reference meaningless to upstream reviewers. These must be replaced with substantive descriptions of the actual dependency (the four concrete formula types in other logics need updating before `PropositionalConnectives` can extend `HasAnd`/`HasOr`).

**Affected lines**: Lines 39 and 108 of `Connectives.lean`.

### 3. Modal/Temporal Scope Creep (MEDIUM priority)

**Teammate C** identified that the PR title says "propositional" but `Connectives.lean` defines `HasBox`, `HasUntil`, `HasSince`, `ModalConnectives`, `TemporalConnectives`, and `BimodalConnectives` — infrastructure for logic systems not in the PR's scope. Reviewers may question whether introducing modal/temporal infrastructure belongs in a propositional PR.

**Mitigating context** (from B and D): These classes are needed for the subsequent PR (#649, Temporal) and establish the connective hierarchy that all four logic types share. However, the optics of introducing modal/temporal classes in a "propositional" PR are problematic.

**Options**: (1) Accept the scope and justify it in the PR description, (2) split `Connectives.lean` to have propositional-only classes in the PR and modal/temporal classes in a separate PR, (3) rename the PR to reflect the broader scope.

### 4. `PropositionalConnectives` Bundle Design (MEDIUM priority)

The bundle extends only `HasBot` and `HasImp`, excluding `HasAnd`/`HasOr`. All three analysis teammates (A, B, C) discussed this.

**Consensus**: The minimal bundle is technically correct — modal/temporal formula types lack primitive `and`/`or`, so forcing them through the bundle would be wrong. The Hilbert-system perspective requires only `{bot, imp}` for classical propositional logic.

**Risk**: Upstream reviewers may ask "why introduce a bundled class that omits and/or from propositional connectives?" The answer is sound but needs clear communication.

### 5. `HasBot` vs Mathlib's `Bot` Dual Registration (LOW-MEDIUM priority)

The PR registers both `HasBot` and Lean 4 core's `Bot` on `Proposition Atom`, creating two parallel `bot` fields that resolve to the same value. Teammates A, B, and C all noted this.

**Technical options** (from A):
- Option 1: `class HasBot (F : Type*) extends Bot F` — makes `HasBot` a subclass
- Option 2: Remove separate `Bot` instance, derive `[HasBot F] → Bot F` automatically
- Option 3: Keep current approach and justify the separation

**Consensus**: Current approach is defensible (CSLib's `HasBot` is for proof system polymorphism, `Bot` is for notation), but could be cleaner. Have a prepared response if a reviewer raises it.

### 6. No Review Comments on PR #648 Yet (STRATEGIC)

**Teammate D** confirmed via GitHub API: PR #648 has 0 review submissions, 0 inline comments, 0 issue-level comments as of research time. It was submitted ~15 hours ago. The requested reviewers (arademaker, chenson2018, fmontesi) have not acted.

**Strategic implication**: Do not preemptively change the PR. Wait for actual feedback. The Zulip comment may or may not translate to formal PR review comments.

### 7. Design Patterns Are Well-Validated (CONFIDENCE-BUILDING)

**Teammate B** conducted an extensive survey of alternative approaches:
- Per-operator typeclass pattern mirrors Mathlib's `Lattice` hierarchy exactly
- Mathlib's `HeytingAlgebra`/`HImp` is complementary (semantic level), not competing (syntactic level)
- No competing propositional logic proof system exists in Mathlib — CSLib fills a genuine gap
- The two-layer ND+Hilbert architecture follows standard proof theory textbook structure
- Waring's `ContextualInferenceSystem` is orthogonal and complementary, not conflicting

---

## Synthesis

### Conflicts Resolved

No significant conflicts between teammates. All four converged on the same top concern (PR #607 naming conflict) and the same critical gap (Zulip comment unread). The teammates provided complementary perspectives that reinforce each other.

### Gaps Identified

1. **Zulip message content** — The motivating reviewer comment could not be read. This is the single most important gap.
2. **PRs #536 and #587 interaction** — Teammate C noted these Waring PRs touch overlapping files but no content analysis was done on compatibility.
3. **Instance resolution performance** — No `lean_profile_proof` testing was done to verify the typeclass hierarchy doesn't slow down instance resolution.
4. **`lake shake` verification** — Import minimization not verified for modified files.

### Recommendations

**Immediate actions** (before reading Zulip comment):
1. Remove "task 173" references from `Connectives.lean` — replace with substantive descriptions
2. Prepare the `HasImp` vs `HasImpl` technical argument for Zulip discussion

**After reading Zulip comment**:
3. Address the specific reviewer concern (unknown until comment is read)
4. Decide on modal/temporal scope: keep in PR and justify, or split out

**Strategic** (1-2 weeks):
5. Engage @arademaker (new logic area maintainer, 5 days in role) proactively on Zulip
6. Make the `HasImp` naming argument in the Zulip thread before PR #607 finalizes
7. Consider formalizing a "Propositional and Modal Logic" working group proposal

---

## Teammate Contributions

| Teammate | Angle | Status | Key Contribution |
|----------|-------|--------|-----------------|
| A | Primary (reviewer feedback) | Completed | Mapped 5 likely reviewer concerns to code, provided response templates |
| B | Alternatives (best practices) | Completed | Validated design against Mathlib patterns, confirmed CSLib fills real gap |
| C | Critic (gaps/blind spots) | Completed | Found internal task refs, scope mismatch, untested interactions with PRs #536/#587 |
| D | Horizons (strategic) | Completed | Mapped governance structure, identified working group opportunity, confirmed correct PR sizing |

---

## References

- PR #648: https://github.com/leanprover/cslib/pull/648
- PR #607: https://github.com/leanprover/cslib/pull/607 (Montesi, competing connectives)
- PR #633: https://github.com/leanprover/cslib/pull/633 (original large PR, closed)
- PR #536: https://github.com/leanprover/cslib/pull/536 (Waring, IsClassical/IsIntuitionistic refactor)
- PR #587: https://github.com/leanprover/cslib/pull/587 (Waring, notation typeclasses and models)
- PR #649: https://github.com/leanprover/cslib/pull/649 (this fork, Temporal, stacked on #648)
- Zulip thread: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic
- Task 202 prior research: specs/202_review_hilbert_classes_vs_pr648/reports/01_hilbert-classes-comparison.md
