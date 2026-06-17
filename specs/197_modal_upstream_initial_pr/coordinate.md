# Coordination Plan: Modal/ Upstream PR

This document collects all external coordination actions for the Modal PR — comments to post on GitHub PRs and the Zulip thread. Review and revise before posting.

## PR Landscape Summary

| PR | Author | Status | Relationship |
|----|--------|--------|-------------|
| #528 | fmontesi | MERGED | Introduced Modal/Basic.lean — our PR builds on this |
| #535 | fmontesi | MERGED | Introduced Modal/LogicalEquivalence.lean — our PR updates this |
| #587 | thomaskwaring | OPEN (DRAFT) | Creates `Foundations/Logic/Connectives.lean` with semantic typeclasses (Models, ParamModels, InterpModels). File path conflict with our #648. |
| #607 | fmontesi | OPEN | Logical operator typeclasses. Active again as of 2026-06-16. Uses `HasImpl`/`HasBox`/`HasDiamond`. |
| #648 | benbrastmckie | OPEN | Our propositional PR. Stacking dependency for the Modal PR. |
| #649 | benbrastmckie | OPEN | Our temporal PR. Sibling — no dependency either direction. |

---

## 1. Comment on PR #648 (our propositional PR)

**Purpose**: Respond to thomaskwaring's bot-as-primitive concern with the algebraic argument from task 227.

**When**: Next review cycle, or proactively to help close the design question.

> The algebraic completeness work I've been developing confirms that primitive `⊥` is needed for the free algebra property. The key line is `| .bot => .bot` in `subst` — `⊥` is a nullary operation in the signature, fixed by every substitution. This isn't a convention; it follows from the definition of algebra homomorphism. With bot-as-atom, every substitution theorem requires a side condition `σ(⊥) = ⊥`, and the free monad on `Atom` is no longer free.
>
> This matters concretely for the propositional Lindenbaum algebra and the completeness proofs over `GeneralizedHeytingAlgebra` (which Thomas rightly suggested as the right semantic target). The three-tier hierarchy — JohanssonAlgebra (MPL), HeytingAlgebra (IPL), BooleanAlgebra (CPL) — requires `⊥` as a primitive nullary operation at the base level.
>
> Happy to share the algebraic semantics work once this PR and the modal follow-up land.

---

## 2. Comment on PR #607 (fmontesi's logical operators)

**Purpose**: Acknowledge the revived PR, note convergence, signal willingness to coordinate on naming.

**When**: After PR #648 merges or approaches approval.

> Hi @fmontesi — I see you've addressed ctchou's 3-file consolidation suggestion. That's great.
>
> I wanted to flag that our PR #648 introduces `Connectives.lean` with a single-file approach to connective typeclasses (`HasBot`, `HasImp`, `HasAnd`, `HasOr`), which addresses the same consolidation concern chenson2018 raised in this PR. A planned Modal follow-up extends it with `HasBox`/`ModalConnectives`.
>
> The main difference is naming: `HasImpl`/`impl` here vs `HasImp`/`imp` in #648. Both work; `imp` aligns with the rule name prefix convention (`impI`/`impE`). I'm happy to align whichever way reviewers prefer.
>
> The formula type refactoring in the Modal PR (`{atom, not, and, diamond}` → `{atom, bot, imp, box}`) changes the constructor set your typeclass instances wrap. Once that lands, your instances would need updating to match the new constructors, which should be straightforward. Happy to coordinate — would a Zulip thread work better for hashing out the details?

---

## 3. Comment on PR #587 (thomaskwaring's notation typeclasses)

**Purpose**: Acknowledge the file path overlap on `Connectives.lean` and propose coordination.

**When**: After PR #648 merges or when #587 moves from DRAFT to review.

> Hi Thomas — I noticed this PR creates `Foundations/Logic/Connectives.lean` with semantic typeclasses (Models, ParamModels, InterpModels), and our PR #648 creates the same file path with syntactic connective typeclasses (HasBot, HasImp, etc.). PR #648's description already flags this.
>
> The content is complementary rather than conflicting — yours addresses the semantic/model side, ours addresses the syntactic/connective side. They could coexist in the same file or be split into `Connectives.lean` (syntax) and `Models.lean` (semantics). Happy to coordinate on the file organization.
>
> Your `GeneralizedHeytingAlgebra` suggestion for propositional semantics is something I'm actively pursuing — the algebraic completeness work derives Kripke completeness from algebraic semantics, exactly as you described for intuitionistic logic. Your `InterpModels` pattern may be the right abstraction for that.

---

## 4. Zulip Message: Modal Logic Thread

**Purpose**: Update the community on the Modal PR plan, respond to ctchou's coordination question, acknowledge Kyle Miller and SnO2WMaN, reference fmontesi's InferenceSystem suggestion.

**When**: When the Modal PR is ready to submit (after #648 merges).

> Hi all — following up on the coordination question from @ctchou.
>
> **Where things stand:**
>
> PR #648 (propositional refactor) is in review — it introduces `Connectives.lean` with connective typeclasses and a five-constructor propositional formula type with primitive `⊥`. Once that lands, a follow-up refactors `Modal/Basic.lean` from the current `{atom, not, and, diamond}` to `{atom, bot, imp, box}`. The change is ~355 LOC across four files (Basic.lean, Denotation.lean, LogicalEquivalence.lean, and the `HasBox`/`ModalConnectives` extension in Connectives.lean). It retains the `Model`/`Satisfies`/`Judgement` structure from @fmontesi's PRs #528/#535 unchanged.
>
> **Why box-as-primitive:** The K axiom and necessitation rule are pure proof rules on `□`. Diamond is derived as `◇φ := ¬□¬φ` (classical). This is the dual of the current upstream choice (which derives box via `¬◇¬φ`). A separate `HasDia` primitive can be added later for intuitionistic modal logics (IK, CK).
>
> **Proof systems:** The subsequent PR will add a Hilbert axiomatization for K, with completeness. I'm planning to use the `InferenceSystem` API as @fmontesi suggested — defining a parametric inductive with axiom schemes for the modal cube, then instantiating per fragment (K, T, B, 4, 5, S4, S5, etc.). This should let us leverage the ordering results already in `Modal/Cube` to derive cross-system implications nearly for free.
>
> **Coordination notes:**
> - @Kyle Miller — your S5 completeness formalization looks compatible. The `{atom, bot, imp, box}` type maps cleanly to your `Form` type (`.ff` → `.bot`, `.impl` → `.imp`, `.box` → `.box`). Once the formula type PR lands, porting should be straightforward. Happy to coordinate on API compatibility.
> - @SnO2WMaN — FFL's GL completeness work is impressive. GL sits outside the standard modal cube (Löb's axiom replaces 4+5), so it would be a natural follow-up contribution once the basic K/T/B/4/5 framework is established. The universe issues you mentioned shouldn't arise for propositional modal logic, but would become relevant for first-order extensions as @thomaskwaring noted.
> - @fmontesi — our Connectives.lean approach aligns with your PR #607's direction but uses a single-file layout following @chenson2018's consolidation suggestion. Happy to align on naming (`imp` vs `impl`) and structure.
>
> I'll post the PR link here once it's submitted.

---

## Sequencing

1. **Now**: Review and revise this document
2. **When PR #648 is approved**: Post comment on PR #607 (section 2) and PR #587 (section 3)
3. **When PR #648 merges**: Submit the Modal PR and post the Zulip message (section 4)
4. **If bot-as-primitive debate reopens**: Post the algebraic argument on PR #648 (section 1)
