# Coordination Plan: Modal/ Upstream PR

This document collects all external coordination actions for the Modal PR — comments to post on GitHub PRs and the Zulip threads. Review and revise before posting.

## PR Landscape Summary

| PR | Author | Status | Relationship |
|----|--------|--------|-------------|
| #528 | fmontesi | MERGED | Introduced Modal/Basic.lean — our PR builds on this |
| #535 | fmontesi | MERGED | Introduced Modal/LogicalEquivalence.lean — our PR updates this |
| #587 | thomaskwaring | OPEN (DRAFT) | Creates `Foundations/Logic/Connectives.lean` with semantic typeclasses (Models, ParamModels, InterpModels). File path conflict with our #648. |
| #607 | fmontesi | OPEN | Logical operator typeclasses. Active again as of 2026-06-16. Uses `HasImpl`/`HasBox`/`HasDiamond`. |
| #648 | benbrastmckie | OPEN | Our propositional PR. Rebased on #536; semantics deferred; `Connectives.lean` added; bot primitive. Stacking dependency for the Modal PR. |
| #649 | benbrastmckie | OPEN | Our temporal PR. Sibling — no dependency either direction. |

### Active Collaborators (from Propositional Logic Zulip thread)

| Person | Interest | Status |
|--------|----------|--------|
| Thomas Waring | Algebraic semantics over `GeneralizedHeytingAlgebra`, `HasInterp` abstraction (PR #587), MPL/IPL conservative extension | Actively engaged; has parallel development on [cslib_SKI branch](https://github.com/thomaskwaring/cslib_SKI/blob/kripke/Cslib/Logics/Propositional/Semantics/Heyting.lean) |
| Matthew Doty | DPLL/SAT, Tseitin transformation, Harrison's Handbook port, probability logic | Actively engaged; has [Tseitin branch](https://github.com/xcthulhu/cslib/blob/xcthulhu/tseitin/Cslib/Logics/Propositional/SAT/Tseitin.lean); contributed Dedekind-MacNeille completion proof |

---

## Design Consensus (from Propositional Logic Zulip thread, 2026-06-12 to 2026-06-17)

The Zulip discussion has substantially resolved the key design questions for PR #648:

### 1. Bot-as-primitive: CONSENSUS

All three active participants now agree `bot` should be a primitive constructor, not an atom:
- **Matthew**: "I do agree with Ching-Tsun Chou about a separate `bot` constructor" and "I'm still a proponent of an explicit falsum in the base syntax (and thus EFQ)"
- **Thomas**: Agrees with the algebra framing; his concern about MPL completeness is addressed by `bot_val`
- **Benjamin** (message 604219492): Made the full algebraic argument — substitution invariance, free algebra property, `bot_val` as the MPL parameter

The substitution-invariance argument is now public on Zulip and does not need to be re-argued on the PR unless the debate reopens there.

### 2. Prop vs Bool semantics: DEFERRED

Semantics files (`Basic.lean`, `Bool.lean`) removed from PR #648 per Thomas's request. The question is deferred to a follow-up PR exploring Thomas's `GeneralizedHeytingAlgebra` direction.

Zulip thread positions for the follow-up:
- `Prop`-valued `Evaluate` preferred as primary evaluator (uniform with Kripke/modal semantics)
- `Bool`-valued `BoolEvaluate` needed alongside for computable procedures (DPLL/SAT)
- Matthew proposed collapsing to Bool-only via `Classical.propDecidable`; Benjamin and Thomas both argued for keeping `Prop` for uniformity with modal/temporal Kripke semantics
- Matthew acknowledged Thomas's `HasInterp` as "a good abstraction" that handles both cases

### 3. GeneralizedHeytingAlgebra semantics: CONVERGENCE

Thomas's algebraic completeness theorem over `GeneralizedHeytingAlgebra` is acknowledged as elegant:
```
theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```
Benjamin agreed this `v |= T` framing is "orthogonal to the `Proposition` type design — we can and should adopt [it] regardless." This three-tier hierarchy — `GeneralizedHeytingAlgebra` (MPL), `HeytingAlgebra` (IPL), `BooleanAlgebra` (CPL) — aligns with the existing `bot_val` approach: the general theorem quantifies over `(v, bot_val)`, and specializing to IPL forces `bot_val = bot` via efq axioms.

Matthew contributed a Dedekind-MacNeille completion proof strengthening Thomas's theorem to `HeytingAlgebra`, though the `bot` handling for the MPL-to-IPL conservative extension is still open.

---

## 1. Comment on PR #648 (our propositional PR) — POSTED

**Posted**: [2026-06-17](https://github.com/leanprover/cslib/pull/648#issuecomment-4723358642)

**What the comment covers:**
- Rebased on upstream/main after #536 merged; reconciled `IsIntuitionistic`/`IsClassical` with InferenceSystem-parameterized versions, removing `[Bot Atom]`
- Semantics files (`Basic.lean`, `Bool.lean`) removed from this PR per Thomas's request — deferred to a follow-up exploring Thomas's `GeneralizedHeytingAlgebra` direction
- `Connectives.lean` added with per-operator typeclasses (`HasBot`, `HasImp`, `HasAnd`, `HasOr`)
- `imp` vs `impl` naming: renamed to `imp` for FFL consistency, offered to revert if reviewers prefer `impl`
- Bot-as-primitive argument (substitution invariance, free monad, `bot_val` vs bot-as-atom), with link to the [full Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/604219492)
- `top := bot imp bot` definition (replaces `a imp a` which required `[Inhabited Atom]`)
- German references replaced with Avigad (2022) per ctchou

**Current PR state after this comment:**
- No semantics files — the `Prop`/`Bool`/`GeneralizedHeytingAlgebra` question is deferred
- `[Bot Atom]` eliminated throughout (bot is now primitive)
- `Connectives.lean` present with syntactic typeclasses
- Awaiting reviewer response on `imp`/`impl` naming and the revised structure

**Open threads to watch:**
- ctchou or Thomas may push back on removing semantics files (ctchou had suggested `Bool.lean` alone would suffice)
- The `imp`/`impl` naming question needs resolution before merge

---

## 2. Comment on PR #607 (fmontesi's logical operators)

**Purpose**: Acknowledge fmontesi's renewed engagement on #607, note overlap with #648, coordinate on naming and direction.

**When**: After PR #648 review stabilizes or when #607 moves toward approval.

Hi @fmontesi — good to see this PR active again. I wanted to flag some overlap with PR #648 so we can coordinate.

PR #648 introduces `Connectives.lean` with a single-file approach to connective typeclasses (`HasBot`, `HasImp`, `HasAnd`, `HasOr`), following @chenson2018's consolidation suggestion. A planned Modal follow-up would extend it with `HasBox`/`ModalConnectives`.

The main naming difference is `HasImpl`/`impl` here vs `HasImp`/`imp` in #648. I went with `imp` for consistency with FormalizedFormalLogic and the rule name prefix convention (`impI`/`impE`), but offered to revert on the PR — happy to align whichever way you and other reviewers prefer.

The Modal follow-up also plans a constructor refactoring (`{atom, not, and, diamond}` to `{atom, bot, imp, box}`), which would affect how typeclass instances are written. I'd welcome your input on whether that direction works or if we should adapt our approach — would a Zulip thread work better for hashing out the details?

---

## 3. Comment on PR #587 (thomaskwaring's notation typeclasses)

**Purpose**: Acknowledge the file path overlap on `Connectives.lean` and coordinate, referencing the active Zulip discussion.

**When**: After PR #648 merges or when #587 moves from DRAFT to review.

Hi Thomas — building on our Zulip discussion in the Propositional Logic thread:

I noticed this PR creates `Foundations/Logic/Connectives.lean` with semantic typeclasses (Models, ParamModels, InterpModels), and our PR #648 creates the same file path with syntactic connective typeclasses (HasBot, HasImp, etc.). PR #648's description already flags this.

The content is complementary rather than conflicting — yours addresses the semantic/model side, ours addresses the syntactic/connective side. They could coexist in the same file or be split into `Connectives.lean` (syntax) and `Models.lean` (semantics). Happy to coordinate on the file organization.

Your algebraic completeness theorem over `GeneralizedHeytingAlgebra` with the `v |= T` framing is exactly the right generalization — as I mentioned on Zulip, that architecture is orthogonal to the formula type design and we should adopt it. Once #648 lands, I'd be happy to collaborate on integrating the algebraic semantics layer, either by adapting your [cslib_SKI branch](https://github.com/thomaskwaring/cslib_SKI/blob/kripke/Cslib/Logics/Propositional/Semantics/Heyting.lean) or coordinating on a joint PR.

---

## 4. Zulip Message: Modal Logic Thread

**Purpose**: Update the community on the Modal PR plan, respond to ctchou's coordination question, reference fmontesi's InferenceSystem suggestion.

**When**: When the Modal PR is ready to submit (after #648 merges).

Hi all — following up on the coordination question from @ctchou.

**Where things stand:**

PR #648 (propositional refactor) is in review — it introduces `Connectives.lean` with connective typeclasses and a five-constructor propositional formula type with primitive `bot`. Semantics are deferred to a follow-up PR exploring @thomaskwaring's `GeneralizedHeytingAlgebra` direction (see the Propositional Logic thread). Once #648 lands, a follow-up refactors `Modal/Basic.lean` from the current `{atom, not, and, diamond}` to `{atom, bot, imp, box}`. The change is ~355 LOC across four files (Basic.lean, Denotation.lean, LogicalEquivalence.lean, and the `HasBox`/`ModalConnectives` extension in Connectives.lean). It retains the `Model`/`Satisfies`/`Judgement` structure from @fmontesi's PRs #528/#535 unchanged.

**Why box-as-primitive:** With box as the primitive, necessitation is a pure rule — `⊢ φ → ⊢ □φ` — mentioning only `box`. With diamond primitive, necessitation becomes an interaction law: `⊢ φ → ⊢ ¬◇¬φ` (requiring `neg`), or expanding the defined `neg`, `⊢ φ → ⊢ (◇(φ → ⊥)) → ⊥` (requiring `dia`, `imp`, and `bot`). The K axiom is similar: `□(φ → ψ) → □φ → □ψ` uses only `box` and `imp`, while its diamond dual mixes more connectives. Diamond is derived as `dia p := neg (box (neg p))` (classical) — the dual of the current upstream choice. A separate `HasDia` primitive can be added later for intuitionistic modal logics (IK, CK).

**Proof systems:** The subsequent PR will add a Hilbert axiomatization for K, with completeness. I'm planning to use the `InferenceSystem` API as @fmontesi suggested — defining a parametric inductive with axiom schemes for the modal cube, then instantiating per fragment (K, T, B, 4, 5, S4, S5, etc.). This should let us leverage the ordering results already in `Modal/Cube` to derive cross-system implications nearly for free.

**Coordination notes:**
- @fmontesi — the Connectives.lean approach in #648 aligns with #607's direction but uses a single-file layout following @chenson2018's consolidation suggestion. Happy to align on naming (`imp` vs `impl`) and structure — your call on what works best.

I'll post the PR link here once it's submitted.

---

## 5. Zulip Message: Propositional Logic Thread (follow-up)

**Purpose**: Acknowledge Matthew's Dedekind-MacNeille contribution, discuss how `bot_val` resolves the conservative extension question, confirm next steps on algebraic semantics.

**When**: After PR #648 review stabilizes, or proactively to keep the conversation warm.

A couple of follow-ups on the technical points:

@Matthew Doty — the Dedekind-MacNeille completion strengthening Thomas's theorem to `HeytingAlgebra` is very nice. Thomas is right that the MPL-to-IPL conservative extension doesn't follow directly, since the completion preserves `v ⊥ ≠ ⊥` valuations. But I think `bot_val` resolves this: the MPL completeness theorem quantifies over `(v, bot_val)` with `bot_val` unconstrained, while the IPL specialization adds `bot_val = ⊥` (forced by the efq axioms). The Dedekind-MacNeille completion then gives the conservative extension for IPL over MPL, since any `GeneralizedHeytingAlgebra` countermodel lifts to a `HeytingAlgebra` countermodel that still satisfies `bot_val = ⊥`. I've deferred the semantics files from PR #648 — the follow-up will explore Thomas's `GeneralizedHeytingAlgebra` direction, which should accommodate both the `Prop`-valued metatheory and `BoolEvaluate` for DPLL. Happy to coordinate on the interface so your SAT work can stack on it.

@Thomas Waring — your [cslib_SKI development](https://github.com/thomaskwaring/cslib_SKI/blob/kripke/Cslib/Logics/Propositional/Semantics/Heyting.lean) of algebraic semantics is the cleanest version of this I've seen — the `v ⊨ T` framing in the general completeness theorem is exactly right. As mentioned on the PR, I've removed the semantics files and would like to pursue this direction in a follow-up. The `bot_val` parameter composes naturally: the general theorem quantifies over `(v, bot_val)`, the `v ⊨ T` hypothesis does the work, and specializing to IPL forces `bot_val = ⊥`.

---

## Sequencing

1. ~~**Post comment on PR #648**~~ — DONE ([2026-06-17](https://github.com/leanprover/cslib/pull/648#issuecomment-4723358642))
2. **Now**: Review and revise this document
3. **Soon**: Post Propositional Logic Zulip follow-up (section 5) to keep collaboration momentum
4. **When PR #648 review stabilizes**: Post comment on PR #607 (section 2) and PR #587 (section 3)
5. **When PR #648 merges**: Submit the Modal PR and post the Modal Zulip message (section 4)
6. **Awaiting**: Reviewer response on `imp`/`impl` naming and revised PR structure

**Note (2026-06-17)**: PR #607 is active again — fmontesi re-engaged as of 2026-06-16. The earlier assessment of #607 as "stalled" no longer holds. Section 2 timing and tone should account for parallel progress on #607; avoid framing that assumes our direction takes precedence over the original Modal/ author's.
