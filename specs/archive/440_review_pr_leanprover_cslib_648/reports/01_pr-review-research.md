# PR Review Research: feat(Logics/Propositional): five-primitive formula type with primitive bot

**Task**: #440
**Date**: 2026-07-24
**Focus**: Verify resolution of ctchou's CHANGES_REQUESTED review (2026-06-15) against the 2026-06-29/07-13 rework, and draft the outstanding-items picture for a reviewer reply.

## Sources Fetched

| Source | Type | Status |
|--------|------|--------|
| https://github.com/leanprover/cslib/pull/648 | GitHub PR | Fetched (7 review entries, 3 conversation comments, 10 inline comments) |
| (description) | User Context | Included |
| Zulip `#CSLib > Propositional Logic` (referenced from PR, not a declared source) | Supplementary | Fetched opportunistically (35 messages, `~/.zuliprc` is configured) — see note below |

**Note on Zulip**: no `zulip_thread` source was present in this task's `sources` array, so no Zulip fetch was required by contract. However, the PR body and comments repeatedly link a specific Zulip thread (`leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic`) as the venue where the bot/efq design compromise was actually negotiated with thomaskwaring, so it was fetched opportunistically since credentials were already configured. Treat it as background corroboration, not a formally-tracked source.

## PR Overview

- **Title**: feat(Logics/Propositional): five-primitive formula type with primitive bot
- **Author**: benbrastmckie
- **State**: OPEN (not merged). `reviewDecision: CHANGES_REQUESTED`. `mergeable: false` / `mergeable_state: dirty` — **the branch currently has merge conflicts against `main`**, a new fact not mentioned in the task description and worth flagging before any reply to ctchou.
- **Branch**: `feat/propositional-v2` (fork `benbrastmckie/cslib`) -> `main`
- **URL**: https://github.com/leanprover/cslib/pull/648
- **Created**: 2026-06-14. **Last updated**: 2026-07-13 (last push, commit `4834be23`).
- **Files touched (current head)**: `Cslib/Logics/Propositional/Defs.lean`, `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`, `references.bib`. Note: `Cslib/Logics/Propositional/` at the PR head now contains only `Defs.lean` and `NaturalDeduction/` — no `Semantics/` directory.

### PR Description Summary

Adds `bot` as a primitive constructor of `Proposition` (removing all `[Bot Atom]` constraints) and promotes ex falso quodlibet (`efq`) to a primitive `Derivation` constructor, making **IPL the base logic**. Minimal logic (MPL) is explicitly deferred to a separate PR. Reconciled with merged PR #536. Renames `impl`→`imp`/`impI`/`impE`. Semantics is explicitly **not** included in this PR (deferred, per thomaskwaring's request). Connective typeclasses (`HasBot`/`HasImp`/etc., previously in a `Connectives.lean`) were removed — coordinated instead via #607. References list Avigad 2022 first, followed by Prawitz 1965, Troelstra & van Dalen 1988, and Gentzen 1935 last. Body includes an "AI Tools Used" disclosure (Claude Code used for refactor/rebase/CI verification, "all mathematical decisions reviewed").

## Review Feedback Summary

### Review by ctchou — CHANGES_REQUESTED

**Submitted**: 2026-06-15T23:41:08Z

> Some general comments:
> * I like the idea of adding \bot as a primitive.
> * I don't understand why we need both Semantics/Basic.lean and Semantics/Bool.lean. I think the latter alone is enough. Later we can add (for example) Kripke semantics for intuitionistic propositional logic.
> * It is not helpful to the readers to refer to old papers from the 1930s, some of which are in German. A good modern reference is Jeremy Avigad's textbook... whose chapters 2 and 3 covers everything in this PR.
> * You should definitely coordinate this PR with #607 and #587. #536 is ready to merge, so you should wait for it.

This is the only review from ctchou and it has not been updated or re-submitted since. **`reviewDecision` is still `CHANGES_REQUESTED`** as of this research (2026-07-24) — no re-review has occurred despite substantial rework on 2026-06-29 through 2026-07-13.

### Review by thomaskwaring — APPROVED

**Submitted**: 2026-07-06T13:26:27Z

> this looks pretty good to me! i'd like opinions from other logic contributors, but on the whole i'd be happy for this to be merged.

This approval came after a detailed conversation-comment critique from thomaskwaring on 2026-06-16 (see below) and 5 inline nitpicks (also 2026-06-16/07-06, addressed by the author on 2026-07-13). Note thomaskwaring explicitly deferred to "other logic contributors" (i.e., did not treat his own approval as sufficient for merge) — this is presumably ctchou, whose CHANGES_REQUESTED still stands.

### Author review batch (benbrastmckie) — 5× COMMENTED, empty body

**Submitted**: 2026-07-13T15:42:28Z–15:42:34Z

These are the author's own review-thread replies to thomaskwaring's 5 inline comments (see Inline Code Comments below); GitHub records them as a review with an empty top-level body because all content was posted as inline replies.

## Inline Code Comments

### `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

**thomaskwaring** (2026-07-06): "i think the comment about not needing an axiom for explosion is unnecessary & possibly confusing"
**benbrastmckie** (2026-07-13, reply): "Done — removed that clause from the module docstring." **Resolved.**

**thomaskwaring** (2026-07-06): "the part about 'primitives' is i think covered by the docstrings of the constructors"
**benbrastmckie** (2026-07-13, reply): "Done — dropped the 'Primitives:' list; it's covered by the constructor docstrings." **Resolved.**

**thomaskwaring** (2026-07-06): "are the explicit arguments necessary here? if so what broke about the old proof?" (on `Theory.Derivation.subs`)
**benbrastmckie** (2026-07-13, reply): "Good catch — the explicit arguments weren't necessary on the simple recursive arms, so I've reverted those to plain constructor patterns... Builds cleanly." **Resolved.**

### `Cslib/Logics/Propositional/Defs.lean`

**thomaskwaring** (2026-07-06): "i don't have a strong opinion on `imp` vs `impl`, so long as after #607 lands it is consistent across the library (noting eg `Modal` has `impl` also)"
**benbrastmckie** (2026-07-13, reply): "Agreed — leaving `imp` as-is for now; I'll reconcile the naming with the rest of the library once #607 lands." **Open/deferred by design** — naming consistency is explicitly pushed to post-#607 cleanup, not resolved now.

**thomaskwaring** (2026-07-06): "no need for the comment about inference rule vs axiom here — that was only relevant for the old design"
**benbrastmckie** (2026-07-13, reply): "Done — removed that note from the `IPL` docstring." **Resolved.**

## Conversation Comments

**thomaskwaring** (2026-06-16T07:01:11Z) — long substantive critique: argues for keeping `⊥` as an atom (`[Bot Atom]`) rather than primitive (precedent in *Lectures on the Curry-Howard Correspondence*; extra constructor bloats semantics duplication; non-bottom-preserving substitutions matter for conservativity results, e.g. `WithBot.some`); disputes `top := a → a` framing; says citing CSLib's own unmerged `Modal` naming convention as precedent is unconvincing (Modal actually uses `impl`); asks to split semantics into a separate PR; **agrees with ctchou on citing literature in English — "the Gentzen paper is my bad, I read it in translation."**

**benbrastmckie** (2026-06-16T20:34:53Z) — first-round reply: rebased on #536, removed `[Bot Atom]`; **removed Semantics files entirely** per thomaskwaring's request (deferred to follow-up); **replaced German-language references with Avigad (2022)** per ctchou; added a new `Connectives.lean` (`HasBot`/`HasImp`/etc.) aligned with #607; kept `imp` naming; defended primitive-`bot` design at length; noted `top := ⊥ → ⊥` change. (This intermediate state still had `Connectives.lean` — later removed in the 2026-06-29 rework.)

**benbrastmckie** (2026-06-30T18:20:24Z) — second-round reply, addressed to ctchou specifically, summarizing the 2026-06-29 rework:
- **Scope/semantics**: "#648 is now just the IPL-base foundation... I've removed both semantics files (`Semantics/Basic.lean` and `Semantics/Bool.lean`) from this PR... which also resolves your point about not needing both."
- **References**: "I've added Avigad's textbook as the lead modern reference... I've kept Gentzen, Prawitz, and Troelstra & van Dalen, but de-emphasized Gentzen (now last) and replaced its German title with an English gloss, so the 1930s German paper is no longer quoted. Happy to drop it entirely if you'd prefer."
- **Coordination**: "#536 has merged and this branch is rebased on top of it. Removing the semantics and the connective typeclasses from #648 also removes its overlap with #587... and #607... I'll leave reviews on those to help them land."
- Closes: "Happy to wait for other maintainers' input on the ⊥/efq design before a full re-review."

**This 2026-06-30 comment is effectively an existing draft reply to ctchou**, but it predates the 07-02/07-13 follow-up commits (naming/binder cleanup, thomaskwaring's approval) and ctchou has still not responded to it — no re-review, no reply, no reaction recorded since.

## Zulip Discussion (supplementary, not a declared source)

Stream `CSLib`, topic `Propositional Logic`, 35 messages, 2026-06-12 through 2026-06-29 (nothing after the 2026-06-29 GitHub PR update — consistent with the PR's own timeline). Key thread of relevance to this task:

- 2026-06-15: Benjamin raises the `[Bot Atom]`-vs-primitive issue and opens #648.
- 2026-06-16 to 06-25: Extended three-way discussion (Benjamin, Thomas Waring, Matthew Doty) over `bot`-as-atom vs primitive, `Evaluate`/algebraic-semantics design (`GeneralizedHeytingAlgebra` vs `Bool`), and conservativity of IPL over MPL via `WithBot`. Matthew Doty explicitly sides with ctchou: "I do agree with @Ching-Tsun Chou about a separate bot constructor" (06-16), then later reverses toward wanting explicit falsum/EFQ (06-17).
- **2026-06-22T18:54 — Chris Henson**: "@Benjamin Brast-McKie Is your above message written by an LLM? If so, this is not allowed by the AI policy of this Zulip." Benjamin's reply (06-22T19:45): "I use AI for drafting but review the outputs before posting. I improved the message above and will avoid AI for drafting in the future." **Flag**: this is an AI-policy compliance concern raised by a maintainer specifically about Zulip drafting; it is distinct from (but adjacent to) the PR's own "AI Tools Used" disclosure section, and is not mentioned anywhere in the task description. Worth being aware of before drafting further Zulip or PR replies with AI assistance.
- 2026-06-28 (Thomas Waring) — the actual design-compromise proposal: "if we are going to have ⊥ as a primitive, we should also have efq... minimal logic becomes IPL⟨→,∧,∨,⊤⟩... It seems very unnatural to me to have a constructor with no semantics."
- 2026-06-29T18:44 (Benjamin Brast-McKie) — accepts the compromise: "I've implemented it in #648: ⊥ is a primitive constructor and efq is now a primitive rule, so IPL is the base logic... I've set minimal logic aside for now." This is the Zulip-side confirmation of the 2026-06-29 rework (commit `e4267aec`) that the task description references.

No Zulip activity from ctchou is present in this thread at all — his only recorded input on the bot/efq/semantics/references questions is the 2026-06-15 GitHub review.

## Additional Context

Task description (verbatim intent): address ctchou's CHANGES_REQUESTED review from 2026-06-15 against the state of the PR as of the 2026-06-29 rework, verifying: (1) the Gentzen1935/German-reference concern, (2) Semantics redundancy, (3) that no re-review has occurred and a reply to ctchou is needed, (4) coordination with #536 (merged)/#587/#607.

## Findings Against the Four Outstanding Items

### 1. References — Gentzen1935 / "don't cite 1930s German papers, use Avigad"

**Status: substantially resolved, one loose end.** Checked `references.bib` and `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` at the current PR head (commit `4834be23`):
- `Avigad2022` is present in `references.bib` and cited **first** in Basic.lean's implementation-notes reference list (line 52: `[Avigad2022], [TroelstraVanDalen1988], [Prawitz1965], [Gentzen1935]`) and again as the first bulleted reference (line 63).
- The `Gentzen1935` bib entry's `title` field was changed from the original German title to **"Investigations into Logical Deduction"** — the standard English title of Szabo's translation in *The Collected Papers of Gerhard Gentzen* (commit `1956d75b`, "chore(references): English citation for Gentzen 1935"). Basic.lean line 66 cites it as `[G. Gentzen, *Investigations into Logical Deduction*][Gentzen1935]` — no German text appears anywhere in the rendered citation.
- Gentzen1935 is **not removed**, only de-emphasized (moved to last position). The 2026-06-30 PR comment explicitly flags this as a judgment call still open to the reviewer: "Happy to drop it entirely if you'd prefer."

**Remaining action**: this is a values/preference call for ctchou, not a technical gap — the "German title" literal complaint is fixed (English translation title now used throughout), but whether to keep citing a 1930s paper at all (via its English-translation edition) is unresolved. A reply to ctchou should present this as: "German title removed / English-translation citation used; happy to drop the citation entirely if you still object to citing it at all."

### 2. Semantics redundancy (Semantics/Basic.lean vs Semantics/Bool.lean)

**Status: resolved by removal, not reduction.** ctchou's ask was "I don't understand why we need both... I think [Bool.lean] alone is enough." The 2026-06-29 rework removed **both** files — confirmed live: `Cslib/Logics/Propositional/` at the PR head contains only `Defs.lean` and `NaturalDeduction/`, no `Semantics/` directory at all. The 2026-06-30 PR comment states this explicitly: "which also resolves your point about not needing both." This was independently corroborated by thomaskwaring's 2026-06-16 comment ("Please split the semantics development into a separate PR") — i.e., two reviewers converged on the same requirement and the author's response (full removal, deferred to a follow-up PR) oversatisfies rather than just resolves ctchou's narrower ask.

**No outstanding action** — confirm in the reply to ctchou that semantics is fully out of scope for #648 now, and will return in a follow-up PR (per thomaskwaring's request, the resolution direction — algebraic semantics over `GeneralizedHeytingAlgebra` — was subsequently discussed at length on Zulip through 2026-06-17, but that discussion belongs to the deferred follow-up, not #648).

### 3. No re-review since rework; reviewDecision still CHANGES_REQUESTED

**Status: confirmed, action needed.** `gh pr view 648 --json reviewDecision` returns `CHANGES_REQUESTED` as of 2026-07-24. ctchou has not posted any review, comment, or reaction since 2026-06-15. A partial reply already exists in the conversation comments — the 2026-06-30 comment addressed "@ctchou" by name and walked through scope/semantics/references/coordination — but:
- It predates the 2026-07-02 naming/binder cleanup and the 2026-07-13 docstring fixes (both driven by thomaskwaring's inline comments, not ctchou's).
- It predates thomaskwaring's 2026-07-06 approval.
- The PR is currently **`mergeable_state: dirty`** (merge conflicts against `main`) — this should probably be resolved (rebase) before or alongside requesting re-review, since ctchou re-reviewing a PR that can't merge cleanly is wasted motion.

**Action for the implementation phase**: draft an updated `@ctchou` reply/ping that (a) consolidates the 2026-06-30 summary, (b) notes thomaskwaring's subsequent approval and the naming-consistency deferral to #607, (c) explicitly re-poses the Gentzen-citation judgment call, and (d) flags that the branch needs a rebase before merge. This should be a **new** comment (or an edit/ping on the existing thread), not a silent assumption that the 2026-06-30 comment already covers it — ctchou has given no indication of having seen either.

### 4. Coordination with #536 (merged), #587, #607

**Status: #536 confirmed merged; #587 and #607 both still open, no cross-review found yet.**
- **#536** ("refactor(Logics/Propositional): classical and intuitionistic inference systems"): `merged: true`, merged 2026-06-16T06:46:52Z. #648 is rebased on top of it per both the PR body and the 2026-06-30 comment. **Satisfied**, as the task description already notes.
- **#587** ("feat(Foundations/Logic): Notation typeclasses and models", fmontesi/thomaskwaring-adjacent): still **open**, `mergeable_state: unknown`. The 2026-06-30 comment states removing semantics/connectives from #648 "removes its overlap with #587... I'll leave reviews on those to help them land" — but no evidence was found (in PR comments, reviews, or the Zulip thread) that benbrastmckie has actually left a review on #587. This looks like a stated intention, not yet an executed action — worth verifying directly on #587 before claiming coordination is complete.
- **#607** ("feat(Logic): logical operators", fmontesi): still **open**, `mergeable_state: unknown`. Same pattern: #648's PR body explicitly discusses design compatibility with #607 ("I'll leave a review on #607") and the inline-comment thread on `imp`/`impl` naming is explicitly deferred to "once #607 lands." No confirmed review from benbrastmckie found on #607 either.

**Remaining action**: the coordination story for #587/#607 is "no longer overlapping + stated intent to review," not "actively coordinated." If a reply to ctchou claims coordination is handled, it should be phrased carefully — e.g., "the design overlap was removed; I intend to review #587/#607" rather than implying completed cross-review, unless independent verification on those PRs shows otherwise (out of scope for this research pass — recommend a quick check of #587/#607 review threads before finalizing the reply).

## Open Questions

1. Should the `Gentzen1935` citation be dropped entirely, or is the English-translation title sufficient to satisfy ctchou's original objection? (Author has offered either; ctchou has not responded since the fix.)
2. Will ctchou re-review now that thomaskwaring has approved and the semantics/reference concerns are addressed, or is a fresh ping required to prompt it?
3. Has benbrastmckie actually posted reviews on #587 and #607 as stated in the 2026-06-30 comment? (Not verified in this pass.)
4. Should the merge-conflict (`mergeable_state: dirty`) be resolved (rebase onto current `main`) before or alongside requesting ctchou's re-review?
5. Is the `imp` vs `impl` naming inconsistency (relative to `Modal`'s `impl`) something ctchou also cares about, or is it purely a thomaskwaring/#607-deferred matter?

## Requested Changes

From ctchou's CHANGES_REQUESTED review (2026-06-15), cross-referenced against current state:
1. ~~Don't have both `Semantics/Basic.lean` and `Semantics/Bool.lean`~~ — **done** (both removed).
2. ~~Don't cite 1930s German-language papers; use Avigad's textbook~~ — **done** (Avigad2022 added and cited first; Gentzen1935 now cited via its English-translation title, not removed).
3. **Coordinate with #607 and #587; wait for #536** — **#536 done** (merged, rebased on top); **#587/#607 coordination is stated intent, not independently verified as executed** in this research pass.

No further explicit change requests from thomaskwaring beyond the 5 inline docstring/binder nitpicks, all marked "Done" by the author on 2026-07-13.

## Next Steps

1. Draft (or re-send) a targeted `@ctchou` reply on PR #648 consolidating: semantics fully removed, references fixed (Avigad added, Gentzen English-titled, offer to drop it), #536 merged/rebased, and #587/#607 status — and explicitly ask for re-review now that thomaskwaring has approved.
2. Resolve the current merge conflict (`mergeable_state: dirty`) — rebase `feat/propositional-v2` onto current `main` — ideally before or in the same push as the ctchou reply, so a re-review isn't immediately stale.
3. Independently verify whether reviews have actually been left on #587 and #607, to make the coordination claim in the ctchou reply accurate rather than aspirational.
4. Optionally settle the `imp`/`impl` naming question once #607 lands, per thomaskwaring's inline comment (not blocking for this PR).
