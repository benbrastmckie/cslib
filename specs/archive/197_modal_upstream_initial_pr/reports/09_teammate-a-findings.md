# Teammate A Findings: Task 197 Revision Assessment (Primary Angle)

- **Task**: 197 — Scope initial Modal/ upstream PR (~300 LOC)
- **Role**: Teammate A (Primary Angle)
- **Focus**: What needs to be revised in the pr-description.md given everything that has changed
- **Date**: 2026-06-17

---

## Key Findings

### 1. The Good News: The Core Work Is Already Done Correctly

The local codebase already reflects the desired post-refactoring state. `Cslib/Logics/Modal/Basic.lean`
already uses `{atom, bot, imp, box}` as primitives (not the original `{atom, not, and, diamond}`).
`Denotation.lean` and `LogicalEquivalence.lean` already use the updated constructors.
`Connectives.lean` already has `HasBox` and `ModalConnectives`. The pr-description.md therefore
accurately describes the diff that exists in the local branch. The scope (~355 insertions / ~222
deletions across four files) is still accurate.

### 2. PR #648 Has Changed But the Stacking Relationship Is Intact

The existing pr-description.md's description of the stacking relationship is broadly correct,
but several key details need updating:

**What changed in PR #648:**
- `bot` is now a primitive constructor (was discussed as being a primitive). The local Modal/Basic.lean
  already reflects this (it uses `.bot` as a constructor), so no code change is needed.
- Semantics (`Basic.lean`, `Bool.lean`) were removed from PR #648 and deferred to a follow-up.
  The pr-description.md does not mention PR #648 including semantics, so this is already consistent.
- The pr-description.md's summary section says PR #648 introduced `Connectives.lean` with
  `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives` — this is accurate for the
  current state of #648.
- `imp` naming (not `impl`) is confirmed in the current local branch. The pr-description.md
  uses `imp` consistently. Good.
- PR #648 now explicitly mentions a **file path conflict** with PR #587 (thomaskwaring's draft
  PR), also creating `Cslib/Foundations/Logic/Connectives.lean`. This coordination note is
  missing from the pr-description.md and should be added.

**Critical new coordination item (PR #587):**
PR #587 (thomaskwaring, DRAFT, 491 additions) creates `Cslib/Foundations/Logic/Connectives.lean`
with different content (notation typeclasses and models). PR #648's description now explicitly
notes: "Proposing a joint design thread before either PR's next revision." The Modal PR's
description should acknowledge this three-way coordination (PRs #607, #648, #587) rather than
the two-way coordination (#607, #648) currently described.

### 3. PR #648 Status: CHANGES_REQUESTED — Stacking Risk Is Real

PR #648 has CHANGES_REQUESTED from ctchou. The open issues from reviewers are:

- **thomaskwaring's `imp` vs `impl` question**: Still unresolved. The reviewer notes that the
  existing Modal/ uses `impl`, and the local branch has already changed to `imp`. If reviewers
  ask for a revert to `impl`, that would require code changes to `Modal/Basic.lean` as well
  (currently using `imp`). The pr-description.md handles this with a diplomatic note, which
  is appropriate, but the risk should be acknowledged more directly.
- **`bot` as primitive**: ctchou likes it; thomaskwaring is skeptical (prefers bot-as-atom).
  The fundamental debate is not resolved. However, the local code already commits to bot-as-
  primitive, so if thomaskwaring's position prevails and PR #648 is forced to revert, the
  Modal PR would need corresponding code changes.
- **PR #587 coordination**: ctchou's original review comment mentioned coordinating with #587.
  PR #648's revised description now acknowledges this. The Modal PR should also mention #587.

**Risk assessment**: The probability that PR #648 is significantly revised again is medium-high.
The unresolved `imp` vs `impl` debate and the three-way `Connectives.lean` file conflict (#607,
#648, #587) could require multiple rounds. Submitting the Modal PR while #648 has
CHANGES_REQUESTED introduces review queue complexity.

### 4. The Naming Section Needs a Substantive Update

The pr-description.md's "PR #607: Coordination Note" section says:

> "The only naming difference between PR #607 and our approach is `HasImpl`/`impl` (PR #607) vs
> `HasImp`/`imp` (our PRs)."

This is now outdated. What the section needs to say is:

- Both PR #607 and PR #648 define `Connectives.lean`-style typeclasses; PR #648 is the active
  contender (not #607, which is stalled with CHANGES_REQUESTED since 2026-05-29).
- PR #587 (thomaskwaring) is a third competitor creating the same `Connectives.lean` file path.
  The three-way coordination needs resolution before any of these PRs can merge.
- The Modal PR stacks on the resolution of this three-way coordination.

### 5. The `impl` vs `imp` Naming: Current Status

**Key finding**: The existing upstream `Modal/Basic.lean` (post-PRs #528/#535 merge) uses
`impl` (thomaskwaring confirmed this: "the actually existing example (Modal) uses 'impl'").
The local branch changed this to `imp`. If reviewers ask for the local branch to revert from
`imp` to `impl`, the Modal PR code would need updating. This is explicitly flagged in the
pr-description.md but the text implies the risk is minor ("one-line change"). In reality, the
choice affects the naming throughout Basic.lean, Denotation.lean, and LogicalEquivalence.lean.

The pr-description.md currently says: "If PR #607 moves forward, aligning to `HasImp` is a
one-line change." This is slightly misleading — it would be a rename throughout the file, not
truly one line. More importantly, `imp` vs `impl` is now primarily a PR #648 vs PR #607
question, not a "Modal PR aligning to #607" question.

### 6. Scope Accuracy: Still ~300-360 LOC

The four-file scope is correct:
- `Connectives.lean`: ~25 LOC addition (HasBox + ModalConnectives)
- `Basic.lean`: ~291 insertions, the largest change
- `Denotation.lean`: ~85 lines (already updated to {bot, imp, box} match cases)
- `LogicalEquivalence.lean`: ~84 lines (already updated to {impL, impR, box} constructors)

Total is approximately 355 insertions / 222 deletions (as stated in the description). This
estimate remains accurate.

### 7. New PRs to Coordinate With: Task 227 (Algebraic Completeness)

Since the plan was written, task 227 (algebraic completeness for propositional logic) has
created a new file: `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean`. This is
a local file (not yet in an upstream PR) that builds on the propositional formula type. It does
not directly affect the Modal PR scope, but it is evidence that the propositional work is
active and evolving. Task 229 (typeclass diamond resolution) is also active, working on the
`BimodalConnectives` bridge instance in `Connectives.lean`. Changes from task 229 could
affect `Connectives.lean` before the Modal PR is submitted.

### 8. What the pr-description.md Gets Right

The following sections are accurate and do not need revision:
- Title and Summary
- Design Rationale (box vs diamond, bot and imp as primitives)
- Main Definitions and Notation table
- Breaking Changes section (constructor renames are correct)
- Changed Files (four-file list is correct)
- Contribution Roadmap
- References (uses English-language references including Avigad — note: the references section
  lists non-English works like Johansson1937 and Wajsberg1938; ctchou had a concern about this
  for PR #648, but these were not in PR #648's scope — for the Modal PR they appear in the
  "Why bot and imp" rationale section and should be noted as historical references, not primary
  sources, to preempt the same concern)

---

## Recommended Approach

### Revision Priority: Medium (3 targeted updates needed)

**Update 1: Add PR #587 to the "Relationship to Other PRs" section (HIGH PRIORITY)**

Add a new subsection or update the PR #607 section to mention PR #587 (thomaskwaring, DRAFT)
which creates the same `Cslib/Foundations/Logic/Connectives.lean` file path. The Modal PR's
`Connectives.lean` extension of `HasBox`/`ModalConnectives` is contingent on the three-way
coordination between PRs #607, #648, and #587 resolving the file path and design question.

**Update 2: Soften the `imp` vs `impl` language (MEDIUM PRIORITY)**

Replace "one-line change" with more accurate language acknowledging that `imp` vs `impl`
is a rename throughout the Modal files and is an open question on PR #648 itself. Frame it
as: the Modal PR adopts whatever naming convention #648 settles on, since this PR stacks on #648.

**Update 3: Note the CHANGES_REQUESTED status of PR #648 (LOW-MEDIUM PRIORITY)**

The pr-description.md says "stacks on PR #648 (open)" without noting the CHANGES_REQUESTED
status. Adding a brief note that the user is actively addressing reviewer feedback would set
appropriate expectations for reviewers of the Modal PR.

### What Does NOT Need Revision

- The four-file scope and LOC estimates — these are accurate
- The bot-as-primitive rationale — this is defensible and consistent with ctchou's preference
- The Contribution Roadmap — still accurate
- The BibKey citations — verified as correct (Blackburn2001, ChagrovZakharyaschev1997, Burgess1984)
- The Johansson1937/Wajsberg1938 references in the "Why bot and imp" section — these appear in
  the Design Rationale section and are appropriate as historical attribution; the concern from
  ctchou was specifically about primary references, not historical attribution

### Strategic Recommendation

**Hold the Modal PR submission until PR #648 resolves the `Connectives.lean` three-way
coordination** (PRs #607, #648, #587). The design of `Connectives.lean` is the shared
foundation; submitting the Modal PR while that foundation is actively contested risks requiring
a full rebase if the file structure or naming changes.

The pr-description.md is in good shape for internal reference and should be updated with the
three targeted revisions above. It is not ready for actual PR submission until PR #648 either
merges or reaches reviewer consensus on the file structure question.

---

## Evidence/Examples

### Evidence 1: Local Modal files already reflect refactoring

`Cslib/Logics/Modal/Basic.lean` (line 63-72) shows:
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Proposition Atom)
  | box (φ : Proposition Atom)
```
This matches exactly what the pr-description.md says the PR introduces. The code changes are
already complete in the local branch.

### Evidence 2: PR #587 is a new coordination requirement

PR #648's description (fetched 2026-06-17) now includes:
> "PR #587 (thomaskwaring): Both PRs create `Cslib/Foundations/Logic/Connectives.lean` with
> different content. Semantics are deferred here so no conflict on models, but the file path
> needs coordination. Proposing a joint design thread before either PR's next revision."

This coordination issue was not mentioned in any previous research report for task 197.

### Evidence 3: thomaskwaring confirmed `impl` naming concern

thomaskwaring's PR #648 review comment:
> "citing 'CSLib's existing formula types' as your own as-yet-unmerged work is not exactly
> convincing. Indeed the actually existing example (Modal) uses 'impl'."

This confirms the upstream Modal/ currently uses `impl` (pre-local-branch), and the renaming
to `imp` is a pending design decision that requires reviewer buy-in.

### Evidence 4: Connectives.lean already contains HasBox and ModalConnectives

`Cslib/Foundations/Logic/Connectives.lean` (lines 67-140 approximately) already defines
`HasBox`, `ModalConnectives`, `HasUntil`, `HasSince`, `HasNext`, `FutureTemporalConnectives`,
`LTLConnectives`, `TemporalConnectives`, and `BimodalConnectives`. The file is more extensive
than the pr-description.md implies — it contains the full temporal hierarchy as well. The
pr-description.md only mentions the `HasBox`/`ModalConnectives` additions (25 LOC), which is
correct in terms of what the Modal PR specifically adds, but the full context is larger.

---

## Confidence Level

**High** — All findings are based on direct file inspection and live GitHub PR queries. The
current state of the local branch, PR #648, PR #607, and PR #587 were all verified in this
session (2026-06-17). The three targeted revision recommendations (add PR #587 mention, soften
`imp` vs `impl` language, note CHANGES_REQUESTED status) are grounded in concrete evidence.

**Uncertainty**: The trajectory of PR #648 reviewer consensus is inherently uncertain. The
`imp` vs `impl` question and `Connectives.lean` three-way coordination could resolve quickly
(reviewers accept the current approach) or require substantial rework (forced revert to `impl`
or complete restructuring of `Connectives.lean`). The strategic hold recommendation reflects
this uncertainty.
