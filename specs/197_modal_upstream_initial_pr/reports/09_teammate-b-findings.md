# Teammate B Findings: Alternative Approaches for Modal PR (Task #197)

**Role**: Teammate B — Alternative Approaches
**Date**: 2026-06-17
**Focus**: Alternative stacking strategies, scoping, timing, coordination, and algebraic direction

---

## Key Findings

### 1. PR #648's Situation Has Changed Materially Since Report 06

The previous landscape report (06) stated that PR #648 "has no reviewer activity." That has changed:
- **ctchou** left a CHANGES_REQUESTED review on 2026-06-15 (yesterday relative to today).
- **thomaskwaring** left an extensive comment on 2026-06-16 with significant pushback on bot-as-primitive, the imp/impl naming, and requesting semantics be split out (semantics were already stripped by the time of this comment, so the semantics concern is already resolved in the latest push).
- The user responded on 2026-06-16 defending bot-as-primitive and acknowledging open questions.
- thomaskwaring's pushback on bot-as-primitive is substantive (not a stylistic quibble): he argues bot should remain an atom with `[Bot Atom]` constraints, and cites `WithBot.some` use in conservativity results.

**Implication**: PR #648 is now in active negotiation. The bot-as-primitive question is genuinely unresolved upstream. The Modal PR's plan (which stacks on #648 and inherits its bot-as-primitive design) is exposed to this uncertainty.

### 2. PR #607 Is Now Active Again

PR #607 was updated on 2026-06-16 (yesterday). fmontesi added the comment "Should be ok now" in response to ctchou's 2026-06-01 suggestion to consolidate into 3 files (Modal, Tensor, Propositional). This means:
- PR #607 is **no longer stalled** — fmontesi appears to have addressed at least one reviewer concern.
- The previous assessment that #607 was "stalled since June 1" is outdated.
- PR #607 still has chenson2018's CHANGES_REQUESTED open, but fmontesi is actively responding.

**Implication**: The window where PR #607 was clearly losing to our approach has closed. PR #607 is now an active competitor again, and fmontesi has partially addressed the main structural objection.

### 3. PR #649 Also Has CHANGES_REQUESTED

PR #649 (temporal formula type) now has:
- ctchou's CHANGES_REQUESTED review (2026-06-16): wants future-only temporal operators first, LTS omega-execution integration, no `Encodable`/`Countable` instances.
- The user responded on 2026-06-16 addressing these points (removing `LTL.Satisfies`, deferring `Encodable`).

PR #649 is also in active revision. The plan's assumption that stacking on #649 provides a stable base is now riskier — the branch is changing.

### 4. PR #587 (thomaskwaring) Is the Hidden Competing File

PR #587 by thomaskwaring also creates `Cslib/Foundations/Logic/Connectives.lean` (same filename as our PR #648). This was noted in PR #648's description but treated as "orthogonal." With three PRs (#607, #648, #587) all creating content under `Cslib/Foundations/Logic/`, the reviewer community is going to need to align on a single architecture before any of them merges. thomaskwaring's PR focuses on semantic typeclasses (Models, ParamModels, InterpModels) while #648 focuses on syntactic connective typeclasses — but the file path conflict is real.

### 5. ctchou's 3-File Proposal for PR #607 Operators

ctchou suggested on 2026-06-01 consolidating PR #607's 8 files to 3: Modal (box + diamond), Tensor, Propositional. fmontesi's "Should be ok now" comment on 2026-06-16 suggests he may have done this. If fmontesi restructured #607 to use 3 files and kept `HasBox`/`HasDiamond` in a Modal file, this is directly competitive with adding `HasBox` to our `Connectives.lean`. The two approaches are now converging structurally (both use fewer files), but still differ in the bot/imp naming and whether diamond is primitive.

---

## Alternative Approaches Assessed

### Alternative A: Stack Independently of #648 (Target main Directly)

The Modal PR could be rebased directly onto upstream `main` (not `feat/propositional-v2`) and bring its own minimal connective typeclass additions inline.

**What this would look like**: Add `HasBox`/`ModalConnectives` to either a new `Cslib/Foundations/Logic/ModalConnectives.lean` or inline in `Basic.lean` itself. The PR would not depend on #648's `Connectives.lean` or its bot-as-primitive design choice.

**Advantages**:
- Completely decoupled from the bot-as-primitive dispute in #648.
- Can be reviewed and merged independently — no queue behind #648, #649.
- If #648 gets rejected entirely (e.g., if reviewers insist on bot-as-atom), the Modal PR survives.
- Direct submission is faster.

**Disadvantages**:
- Does not participate in the unified typeclass hierarchy that #648 is trying to establish.
- The `PropositionalConnectives` bundled class would not be available, making `ModalConnectives` less elegant.
- Possible duplication if #648 later merges with a different structure.
- Conflicts directly with PR #607 if #607 addresses its CHANGES_REQUESTED and advances.

**Confidence**: Medium. This is viable but sacrifices the ecosystem coherence that makes the typeclass approach valuable.

### Alternative B: Scope Down to Just Basic.lean + Denotation.lean (No Connectives Extension)

The minimum viable Modal PR would only update `Basic.lean` (formula type refactoring) and `Denotation.lean` (match cases). This defers both `LogicalEquivalence.lean` and `Connectives.lean` changes.

**Problem**: As established in the team research (Report 03), omitting `LogicalEquivalence.lean` leaves upstream CI broken because `Context` constructors reference the removed `{not, and, diamond}` constructors. This alternative is **not viable as stated**.

A variant is possible: keep `LogicalEquivalence.lean` in scope but drop all Connectives.lean changes. This reduces the PR to 3 files (Basic, Denotation, LogicalEquivalence) without any typeclass hierarchy additions.

**Advantages**:
- Purely internal to `Cslib/Logics/Modal/` — no dependency on #648 or the connective typeclass debate.
- The 3-file scope is definitively reviewable as a standalone refactoring.
- Unblocks the formula type question even if #607/#648 argument continues for months.

**Disadvantages**:
- The `ModalConnectives` typeclass integration is deferred — the Modal formula type won't participate in the shared hierarchy until a follow-up.
- If the community converges on PR #607's `HasBox`/`HasDiamond` pair (both primitive), adding `HasBox` alone later would be awkward.

**Confidence**: High as a near-term submission strategy. This is the lowest-risk path to getting the formula type refactoring into upstream.

### Alternative C: Collaborate with fmontesi Instead of Competing

Rather than submitting a competing PR, the user could reach out to fmontesi via Zulip and offer to co-author a merged approach that satisfies both the PR #607 reviewer concerns and the user's formula-type refactoring goals.

**What coordination would produce**: A joint PR that:
- Uses fmontesi's `{atom, not, and, diamond}` → user's `{atom, bot, imp, box}` refactoring
- Uses ctchou's 3-file structure (Modal operators, Tensor, Propositional) rather than the single `Connectives.lean`
- Addresses chenson2018's grind/simp direction concern (user's approach avoids `grind` for notation unfolding)

**Advantages**:
- fmontesi is a project regular with review authority; co-authorship immediately gives the PR credibility.
- Eliminates the competitive dynamic and the naming conflict (fmontesi can agree to `HasImp` vs `HasImpl`).
- The combined PR would be stronger than either alone.

**Disadvantages**:
- Requires fmontesi's buy-in and coordination time — timeline is unpredictable.
- User loses some control over design decisions (e.g., whether diamond stays primitive).
- fmontesi's PR #607 may move forward regardless, forcing the user's hand anyway.

**Confidence**: Medium as a strategy. Zulip outreach is recommended regardless, but full co-authorship is contingent on fmontesi's interest.

### Alternative D: Adopt Algebraic Semantics Approach (Thomas Waring Direction)

Thomas Waring mentioned that his intuitionistic completeness proof derives from algebraic semantics (Heyting algebras), and he suggests defining interpretation in any `GeneralizedHeytingAlgebra`. For modal logic, this would mean a Boolean algebra semantics for classical modal logic, with the Kripke semantics derived as a consequence.

**What this would look like**: The Modal PR would not just refactor `Basic.lean` but would also introduce (or plan to introduce) a `Semantics/Algebra/` approach alongside the existing Kripke semantics in `Denotation.lean`.

**Relationship to current plan**: The Lindenbaum.lean file visible in the git status (`?? Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean`) suggests this direction is already being explored for propositional logic.

**Advantages**:
- Aligns with thomaskwaring's direction (who has strong review credibility).
- Algebraic completeness proofs are often cleaner than canonical model arguments for modal logic.
- Could unify with thomaskwaring's `HeytingModel` approach from PR #587.

**Disadvantages**:
- Significantly increases scope beyond ~300 LOC.
- The modal algebraic semantics direction (Boolean algebras + relation algebras for modal logic) is more complex than propositional.
- Risk of the PR getting too large and being asked to split again (prior history with PR #633).
- The formula type refactoring is prerequisite for algebraic semantics regardless — this is a follow-up concern, not an alternative for the initial PR.

**Confidence**: Low as an alternative for the initial Modal PR. Relevant as a direction for PR 3 or 4 in the roadmap, not the initial formula type PR.

### Alternative E: Submit Modal PR After #648's Bot Question Resolves

Wait for the bot-as-primitive vs bot-as-atom debate to conclude in #648 before submitting the Modal PR.

**Advantages**:
- If reviewers insist on bot-as-atom in #648, the Modal PR can be adapted to use `[Bot Atom]` constraints before submission.
- Avoids submitting a PR that has to be immediately rebased due to #648 changes.

**Disadvantages**:
- Timeline is unpredictable. The thomaskwaring/ctchou conversation on #648 may take weeks to resolve.
- Meanwhile, PR #607 continues to advance and may merge first with incompatible primitives.
- The 3-file scope (Basic, Denotation, LogicalEquivalence) is independent of the bot-as-primitive question if we drop the `Connectives.lean` dependency (Alternative B above).

**Confidence**: Low as a "wait indefinitely" strategy. A bounded wait (2 weeks) is reasonable; indefinite deferral is not.

---

## Recommended Approach

**Primary recommendation: Alternative B (3-file scope, direct rebase on main, no Connectives.lean dependency) + Zulip coordination first.**

The critical insight is that the Modal PR's connection to the bot-as-primitive dispute is optional. The formula type refactoring (`{not, and, diamond}` → `{bot, imp, box}`) in Basic.lean + Denotation.lean + LogicalEquivalence.lean is a standalone change that does not require `Connectives.lean` to exist. The `ModalConnectives` typeclass instance can be deferred to a follow-up PR once the Connectives.lean architecture debate resolves.

**Concrete revised plan**:
1. Rebase the modal branch directly on upstream/main (not feat/propositional-v2 or feat/temporal-formula-propositional).
2. Scope the PR to 3 files: Basic.lean, Denotation.lean, LogicalEquivalence.lean.
3. Do NOT include any Connectives.lean changes in this PR.
4. Post to Zulip's Modal Logic thread acknowledging #607's activity and proposing the formula type refactoring as a prerequisite that both approaches (fmontesi's typeclass wrappers and user's `Connectives.lean` approach) can build on.
5. Submit only after a positive Zulip signal (or after a 2-week waiting period without response).

**Why not stack on #648**: The bot-as-primitive question is now actively contested (thomaskwaring 2026-06-16), and stacking the Modal PR on a PR under active negotiation creates instability. The 3-file Modal refactoring does not need `PropositionalConnectives` or `HasBot`/`HasImp` — it can stand alone.

**Why not collaborate with fmontesi (Alternative C) as the primary path**: fmontesi's PR #607 is active again ("Should be ok now" on 2026-06-16) but still has chenson2018's CHANGES_REQUESTED open. The user should open a Zulip conversation but should not wait indefinitely for co-authorship coordination. If fmontesi is interested, great; if not, the standalone 3-file PR is self-sufficient.

**Regarding the `HasBox` question specifically**: If PR #607 resolves its CHANGES_REQUESTED and proposes `HasBox` in a Modal operators file (following ctchou's 3-file structure), our Modal PR's Connectives.lean addition would conflict. By keeping `HasBox` out of the initial Modal PR, we avoid this conflict entirely and let the operators-file debate resolve on its own timeline.

---

## Evidence/Examples

**PR #648 bot-as-primitive contest (thomaskwaring 2026-06-16)**:
> "If `⊥` is included in minimal logic it behaves precisely like the atomic formulae, so why not represent it as such? ... Adding an extra constructor makes all the proofs, and more importantly definitions, more verbose. EG in your semantics development you have to have separate fields in the Kripke structure for the entailment relation on atoms and `⊥`, which are exact duplicates."

This is a fundamental design objection, not a cosmetic concern. The bot-as-primitive question is genuinely open.

**PR #607 fmontesi re-activation (2026-06-16)**:
> "Should be ok now." (responding to ctchou's 3-file consolidation suggestion)

This is the first fmontesi activity on #607 since June 1 — PR #607 is no longer stalled.

**ctchou's 3-file proposal for #607 (2026-06-01)**:
> "I propose 3 files: Modal containing box and diamond. Tensor by itself. Propositional for the rest. BTW, do we need parameterized box and diamond for HML?"

If fmontesi has restructured to 3 files, the `HasBox`/`HasDiamond` pair now lives in a Modal operators file — structurally different from our `HasBox`-only addition to `Connectives.lean`, and keeping diamond as a primitive operator rather than derived.

**PR #587 thomaskwaring Connectives.lean conflict**:
PR #587 also creates `Cslib/Foundations/Logic/Connectives.lean` with semantic content (Models, ParamModels, InterpModels). PR #648 creates the same file with syntactic content (HasBot, HasImp, etc.). The reviewer community will need to decide how to merge these before either merges. Keeping the Modal PR independent of this conflict is strategically sound.

---

## Confidence Level

**High confidence** on the following:
- The PR #648 bot-as-primitive debate is now active and unresolved as of 2026-06-16.
- PR #607 is no longer stalled — fmontesi made updates on 2026-06-16.
- The 3-file scope (Basic + Denotation + LogicalEquivalence) is viable without Connectives.lean dependency.
- Zulip coordination should precede submission.

**Medium confidence** on the following:
- Whether fmontesi restructured #607 to 3 files (ctchou's suggestion) — "Should be ok now" suggests yes, but the PR diff was not re-examined in detail.
- Whether a 2-week wait for #648 resolution is sufficient before the Modal PR must adapt.

**Low confidence** on the following:
- Whether the community will converge on `HasBox` alone (user's approach) vs `HasBox`/`HasDiamond` pair (PR #607 approach with both as primitives) — this depends on whether reviewers accept the diamond-as-derived encoding for classical modal logic.
- Whether thomaskwaring would support bot-as-atom over bot-as-primitive for the Modal formula type (his #648 comment is about propositional; modal is a separate case).
