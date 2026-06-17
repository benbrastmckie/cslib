# Coordination Plan: Modal/ Upstream PR

Draft Zulip follow-ups. Review and revise before posting.

---

## 1. Zulip Message: Modal Logic Thread

**Purpose**: Follow up on the [earlier post](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/602410242) with concrete scope, respond to ctchou's coordination question, reference fmontesi's InferenceSystem suggestion.

**When**: When the Modal PR is ready to submit (after #648 merges).

Following up on @ctchou's [coordination question](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/602410242) and my earlier post about the Modal follow-up to PR #648:

**Scope:** The Modal PR is ~355 LOC across four files — Basic.lean, Denotation.lean, LogicalEquivalence.lean, and the `HasBox`/`ModalConnectives` extension in Connectives.lean. It retains the `Model`/`Satisfies`/`Judgement` structure from @fmontesi's PRs #528/#535 unchanged. Semantics are deferred to a follow-up exploring @thomaskwaring's `GeneralizedHeytingAlgebra` direction (see the Propositional Logic thread).

**Proof systems:** The subsequent PR will add a Hilbert axiomatization for K, with completeness. I'm planning to use the `InferenceSystem` API as @fmontesi suggested — defining a parametric inductive with axiom schemes for the modal cube, then instantiating per fragment (K, T, B, 4, 5, S4, S5, etc.). This should let us leverage the ordering results already in `Modal/Cube` to derive cross-system implications nearly for free.

@fmontesi — happy to align on naming (`imp` vs `impl`) and structure — your call on what works best.

I'll post the PR link here once it's submitted.

---

## 2. Zulip Message: Propositional Logic Thread (follow-up)

**Purpose**: Acknowledge Matthew's Dedekind-MacNeille contribution, discuss how `bot_val` resolves the conservative extension question, confirm next steps on algebraic semantics.

**When**: After PR #648 review stabilizes, or proactively to keep the conversation warm.

A couple of follow-ups on the technical points:

@Matthew Doty — the Dedekind-MacNeille completion strengthening Thomas's theorem to `HeytingAlgebra` is very nice. Thomas is right that the MPL-to-IPL conservative extension doesn't follow directly, since the completion preserves `v ⊥ ≠ ⊥` valuations. But I think `bot_val` resolves this: the MPL completeness theorem quantifies over `(v, bot_val)` with `bot_val` unconstrained, while the IPL specialization adds `bot_val = ⊥` (forced by the efq axioms). The Dedekind-MacNeille completion then gives the conservative extension for IPL over MPL, since any `GeneralizedHeytingAlgebra` countermodel lifts to a `HeytingAlgebra` countermodel that still satisfies `bot_val = ⊥`. I've deferred the semantics files from PR #648 — the follow-up will explore Thomas's `GeneralizedHeytingAlgebra` direction, which should accommodate both the `Prop`-valued metatheory and `BoolEvaluate` for DPLL. Happy to coordinate on the interface so your SAT work can stack on it.

@Thomas Waring — your [cslib_SKI development](https://github.com/thomaskwaring/cslib_SKI/blob/kripke/Cslib/Logics/Propositional/Semantics/Heyting.lean) of algebraic semantics is the cleanest version of this I've seen — the `v ⊨ T` framing in the general completeness theorem is exactly right. As mentioned on the PR, I've removed the semantics files and would like to pursue this direction in a follow-up. The `bot_val` parameter composes naturally: the general theorem quantifies over `(v, bot_val)`, the `v ⊨ T` hypothesis does the work, and specializing to IPL forces `bot_val = ⊥`.

---

## 3. Recommended Revisions to Posted Content

### Fix: Zulip Modal post — wrong PR #607 URL

The [Zulip Modal post](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic) (2026-06-11) links PR #607 to `leanprover-community/mathlib4/pull/607` instead of `leanprover/cslib/pull/607`. This points to a completely different PR on a different repo. Edit the Zulip message to fix both occurrences.

### No changes needed

- **PR #648 comment** — Clean. Responds to specific feedback, links to the Zulip substitution invariance argument, acknowledges Thomas's GeneralizedHeytingAlgebra direction.
- **PR #607 comment** — Tone is good after our revisions. Uses "I'd welcome your input" rather than prescribing what fmontesi should do.
- **PR #587 comment** — Collaborative, offers two concrete options (coexist or split), praises Thomas's algebraic completeness without soliciting a joint PR.
- **Zulip Propositional post** (message 604219492) — Strong technical argument for bot-as-primitive, good closing tone ("curious to get your thoughts").

### Revisions needed in pr-description.md before submission

The pr-description.md has tone problems in the PR #607 section that mirror what we already fixed in the PR comments:

1. **Lines 108–109**: "our `Connectives.lean` single-file approach directly addresses that comment" — positions your PR as the answer to chenson2018's feedback on fmontesi's PR. Reframe as noting the overlap without claiming credit for solving it.

2. **Lines 121–122**: "We offer this PR as the substantive refactoring; PR #607's typeclass instances can then be updated to match the new `{bot, imp, box}` constructors straightforwardly." — Same presumptuous framing we fixed in the coordinate.md comment. Soften to note the structural incompatibility and invite coordination, rather than asserting which PR should adapt.

3. **Lines 53–54**: 1930s citations (Johansson1937, Wajsberg1938, McKinsey1939) still appear as primary justification in "Why bot and imp as primitives?" — ctchou already pushed back on German-language 1930s references in #648. Lead with Blackburn2001/ChagrovZakharyaschev1997 and reference the [Zulip substitution invariance argument](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/604219492) instead. Keep 1930s refs in the References section for attribution.

4. **Box-as-primitive argument** (lines 29–34): Could be strengthened with the deeper point developed in this session — `□` pairs naturally with `→` (both primitive), while `◇` pairs with `∨` (derived from `→` and `⊥`), so box is the primitive that composes cleanly with the minimal signature.

These should be incorporated as a 9th action item in plan 10, or addressed alongside items 3, 6, and 7 which already touch the same sections.
