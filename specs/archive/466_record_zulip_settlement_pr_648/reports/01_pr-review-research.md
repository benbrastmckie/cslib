# PR Review Research: PR #648 — five-primitive formula type with primitive bot

**Task**: #466
**Date**: 2026-07-02
**Focus**: Full review synthesis (no focus_prompt provided)

## Sources Fetched

| Source | Type | Status |
|--------|------|--------|
| https://github.com/leanprover/cslib/pull/648 | GitHub PR | Fetched (1 review, 3 conversation comments, 0 inline comments) |
| https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic | Zulip Thread | Fetched (35 messages, 2026-06-12 to 2026-06-29) |
| (description) | User Context | Included — read-only research constraints, delta between GitHub head and local head, prior draft locations |

## PR Overview

- **Title**: feat(Logics/Propositional): five-primitive formula type with primitive bot
- **Author**: benbrastmckie
- **State**: open (merged: false)
- **Branch**: `feat/propositional-v2` -> `main`
- **URL**: https://github.com/leanprover/cslib/pull/648
- **Created**: 2026-06-14T23:56:52Z
- **Current GitHub head SHA**: `c9364b65391b1cc2bfd211102a3deb86f3844d48`
- **Last GitHub activity (comment)**: 2026-06-30T18:20:24Z

### PR Description Summary

Revises PR #648 based on reviewer feedback (thomaskwaring, Zulip msg 606970606). Makes `bot` a primitive constructor of `Proposition` (no more `[Bot Atom]` constraints) and takes ex falso quodlibet (`efq`) as a **primitive natural-deduction rule**, so **IPL is the base logic**; minimal logic (MPL) is deliberately deferred to a separate PR/discussion per the agreed compromise. Rebased on upstream/main post-#536 (merged). Semantics removed (deferred to follow-up, per thomaskwaring). Connective typeclasses removed (deferred to PR #607). References updated to Avigad (2022), Gentzen (1935, English gloss), Prawitz (1965), Troelstra & van Dalen (1988), with a link to the Zulip design thread. Scope now four files: `Defs.lean`, two `NaturalDeduction/` files, `references.bib`.

## Review Feedback Summary

### Review by ctchou — CHANGES_REQUESTED

**Submitted**: 2026-06-15T23:41:08Z

- Likes the idea of `⊥` as a primitive.
- Doesn't understand why both `Semantics/Basic.lean` and `Semantics/Bool.lean` are needed — thinks the latter alone suffices.
- Objects to citing 1930s papers (some in German); recommends Avigad's *Mathematical Logic and Computation* (chs. 2–3) as a modern reference instead.
- Wants coordination with #607 and #587; notes #536 was not yet merged at review time and should be waited on.

**No re-review since this CHANGES_REQUESTED.** This is the sole review currently on the PR — ctchou has not looked again since the 2026-06-15 review, despite two rounds of rework (2026-06-16 and 2026-06-29/30 conversation comments) that address every point raised.

## Inline Code Comments

No inline code comments.

## Conversation Comments

**thomaskwaring** (2026-06-16T07:01:11Z):
> Raises substantive concerns about primitive `⊥` vs. `[Bot Atom]` (conservativity via non-bottom-preserving substitutions, e.g. `WithBot.some`), argues an extra constructor makes proofs/definitions more verbose (duplicated Kripke fields for atoms vs. `⊥`), defends `⊤ := a → a` as intentional. Agrees with ctchou on avoiding German-language references and prefers a `GeneralizedHeytingAlgebra`-based semantics unifying `Bool`/`Prop`. Asks for semantics to be split into its own PR. Flags that "CSLib's existing formula types" (an unmerged PR) isn't a strong precedent for the `imp`/`impl` rename — notes `Modal` uses `impl`.

**benbrastmckie** (2026-06-16T20:34:53Z):
> First rework reply. Rebased on upstream/main post-#536 merge; removed semantics files per Thomas's request (deferred to follow-up, floats the `GeneralizedHeytingAlgebra` idea as promising); replaced German references with Avigad (2022); added `Connectives.lean` aligned with fmontesi's #607; open to reverting `imp` back to `impl`; explains the primitive-`bot` substitution-invariance rationale (`subst f .bot = .bot` vs. side-conditions under `[Bot Atom]`).

**benbrastmckie** (2026-06-30T18:44:41Z — note: GitHub API reports 2026-06-30T18:20:24Z):
> Second rework reply, addressed to ctchou specifically, summarizing the narrowed scope following the Zulip design discussion with Thomas Waring: PR is now just the IPL-base foundation (`⊥` primitive + `efq` primitive rule), minimal logic and fragment design deferred, semantics files removed, four files remain in the PR. References: Avigad now cited first/lead; Gentzen kept but de-emphasized (last) with its German title replaced by an English gloss (this is essentially the content of `specs/tmp/comment.md`, which reads as already posted verbatim as this comment). Notes #536 merged and branch rebased; #587/#607 overlap resolved by removing semantics/connectives from #648, with a promise to review those PRs. Explicitly says: "Happy to wait for other maintainers' input on the `⊥`/`efq` design before a full re-review."

**This existing comment already references "the CSLib Zulip thread" in prose but does not include a specific `/near/` permalink to the settlement message** — that is the gap task 466 is meant to close.

## Zulip Discussion

Fetched 35 messages in stream **CSLib**, topic **Propositional Logic**, spanning 2026-06-12 to 2026-06-29.

### Thread arc (summarized; full text available in the raw fetch if needed)

1. **2026-06-12**: benbrastmckie announces Hilbert-system work for propositional logic (min/int/classical) with soundness/completeness and ND equivalence.
2. **2026-06-14 to 06-15**: Matthew Doty asks about a smaller semantics-only PR; Thomas Waring suggests `GeneralizedHeytingAlgebra`-based semantics unifying `Bool`/`Prop`, mentions his own Hilbert-style sketch (`cslib_SKI` branch); benbrastmckie opens PR #648 to make `⊥` a primitive constructor (message id 603163993).
3. **2026-06-15 to 06-17**: Extended debate on `Prop`- vs `Bool`-valued semantics (Doty wants `Bool` for DPLL/SAT portability; benbrastmckie explains `Prop`-valued `Evaluate` is needed for MCS-based canonical models and uniformity with Kripke semantics for modal/temporal logics; proposes adding `BoolEvaluate` as a bridge). ctchou's review (2026-06-15) arrives during this exchange (referenced in-thread by benbrastmckie at message 603572691, "@ctchou also suggested that Bool.lean alone would suffice").
4. **2026-06-16 to 06-17**: Core primitive-`bot`-vs-atom debate. Doty raises Dedekind–MacNeille completion to strengthen completeness to `HeytingAlgebra`; Waring counters that the polymorphic-algebra `Evaluate` breaks completeness for minimal logic unless valuations of `⊥` are allowed to diverge from the algebra's bottom (motivating `bot_val`/`botForces`); Doty argues for explicit falsum in the base syntax for fragment ergonomics (`IPL⟨∧,→,⊤⟩`, `IPL⟨→,⊤⟩`, etc.) and flags DPLL/CNF complications from `⊥ : Atom`. benbrastmckie (message 604219492, 2026-06-17) gives the detailed substitution-invariance argument for primitive `⊥` (nullary operation vs. atom; universal-algebra framing) — **this is the message some earlier drafts mistakenly link to as "the settlement"; it predates the actual compromise by 11 days and is Benjamin's own position statement, not an agreed resolution.**
5. **2026-06-21**: Thomas Waring (message 605341190) clarifies he formalized *minimal* natural deduction and that `IPL`/`CPL` should be seen as encodings; lays out a potential compromise in a branch (`cslib_SKI/intuitionistic`) adding `⊥` + `efq` together; still "not exactly convinced" on the cost argument; defers final call to the community.
6. **2026-06-22**: Matthew Doty says fragment design deserves its own thread/issue; leans toward a class-based approach with caveats. Chris Henson flags AI-content-policy concern on a message (06-22, message 605827029) — relevant to house style for any drafted comment (plain, first-person, not obviously LLM-generated).
7. **2026-06-23 to 06-26**: Further discussion of fragments (`CPL⟨→,⊤⟩` conservativity, message 606508446 from Doty); benbrastmckie replies "Definitely worth proving. I'll attend to that shortly." (message 606621686, 2026-06-26) — **note per task 474's Zulip drafts file, this promise has since been fulfilled locally (`cpl_conservative_over_imp` in `ClassicalImpCompleteness.lean`, sorry-free) but is not yet upstreamed; not directly relevant to #648 but worth being aware of if Doty is pinged in the same reply.**

### The settlement message (the actual compromise)

**Thomas Waring, 2026-06-28T07:22:12Z, message id 606970606:**
Permalink: **https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/606970606**

> "My sense is that, if we are going to have `⊥` as a primitive, we should also have efq — then minimal logic becomes `IPL⟨→,∧,∨,⊤⟩` as Matthew suggested above. It seems very unnatural to me to have a constructor with no semantics... It also makes the way Benjamin has stated the conservativity result, using the 'IsBotFree' predicate, more natural."
>
> "...I think we should be careful with the design to ensure that manipulations on derivations can be carried out for those fragments — ideally this should also be ensured by the way a fragment is specified, rather than being reproved for each. Given that work to get the fragment design right, I think it should be postponed to later work, in which case we would forget about minimal logic for the moment. Does this sound like a reasonable compromise? I'd like also to get some input from other reviewers / maintainers if & when they have capacity. I'll review the PR properly once we've settled on the design..."

He also flags two loose ends in that same message:
- Connective typeclasses should be a separate development (points at #607, suggests leaving a review there instead).
- References + Zulip-thread link were mentioned as added but weren't in the PR yet at that point.

**benbrastmckie's acceptance, 2026-06-29T18:44:41Z, message id 607217129:**
Permalink: **https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/607217129**

> "Thanks Thomas — that compromise sounds right to me, and I've implemented it in #648: `⊥` is a primitive constructor and `efq` is now a primitive rule, so IPL is the base logic... I've set minimal logic aside for now so that the fragment design gets done properly rather than rushed here... So 648 is now just the IPL-base foundation... MPL and the fragment machinery, plus semantics, are deferred to follow-ups."
>
> Also confirms: connective typeclasses removed from #648 (deferred to #607, promises a review there); references (Gentzen 1935, Prawitz 1965, Troelstra & van Dalen 1988, Avigad 2022) and the Zulip thread link are now in the PR "as of the latest push."

This exchange (606970606 -> 607217129) **is** the settlement referenced in the task description ("Waring, 2026-06-28"), and it is what the 2026-06-30 GitHub PR comment (already posted) paraphrases in prose without a direct permalink. The draft comment for task 466 should cite the `/near/606970606` permalink (Waring's compromise) directly, and may optionally also cite `/near/607217129` (Benjamin's acceptance) since it documents implementation status against the compromise.

No further Zulip messages after 2026-06-29T18:44:41Z were found in this topic (35 messages total, none after that date in the fetch window).

## Additional Context

Per the delegation's description field (task 466 constraints and prior-context pointers):

- This is a **read-only research dispatch** — no comments, pushes, or write operations were performed; only `gh api` GET calls, local read-only `git` inspection, and a Zulip GET fetch were run.
- **specs/tmp/comment.md** (dated 2026-06-30, 11:16) contains a draft reply to ctchou. Cross-checking its text against the actual GitHub conversation comments above shows this draft **has already been posted** — it is essentially verbatim identical to the 2026-06-30T18:20:24Z conversation comment from benbrastmckie. It is *not* a pending draft; it documents what's already live on GitHub. It does **not** contain a specific Zulip `/near/` permalink to the settlement message — it only says "the CSLib Zulip thread" generically (linking to the topic URL, not a message anchor). This confirms the precise gap task 466 must fill.
- **Task 440** ("review_pr_leanprover_cslib_648") exists in state.json (project_number 440) but its status is `not_started` — it was created (commit `bbd9c139 task 440: create review_pr_leanprover_cslib_648`) but per state.json has not been researched/planned/implemented under that task number. Its description closely tracks the same ctchou CHANGES_REQUESTED items (references, semantics restructuring, reviewer reply, coordination with #587/#607) — in practice this work appears to have been carried out directly against PR #648 (via the conversation comments above and task 56's polish commits) rather than through task 440's own lifecycle. Nothing further to extract from task 440's directory since no artifacts exist there.
- **Task 56** ("polish_pr_648_bib_and_binder_cleanup", completed) is the source of the two unpushed local commits on `feat/propositional-v2`. Its `completion_summary` confirms: "Polished PR #648 branch (commits bbcbef85, c98c4348 (amended: English-only Gentzen note) on feat/propositional-v2): English Gentzen citation, implicit-Gamma binders restored, subscript names restored, contra/efqRule re-added with simplified pierce, explicit Atom on CPL/LEM/Pierce, set-builder CPL, standard copyright headers. Adversarially verified: all six items confirmed, no scope creep, full CI green including lake test. Not pushed."
- **specs/474_draft_zulip_replies_meeting_fragments/zulip-drafts.md** references the same settlement in a different draft (Draft A, reply to Fabrizio Montesi): "#648 is the propositional base: five primitives with a primitive `⊥` and efq as a rule, so IPL is the base logic. That follows the compromise Thomas Waring proposed in the Propositional Logic thread, which I've implemented there." This is consistent framing but is a *different* draft aimed at a *different* recipient (Montesi, re: PR #607/meeting), not the ctchou re-review request task 466 needs. It also carries the same house-style note: rewrite in your own voice before posting, given the Zulip AI-content policy flagged by Chris Henson on 2026-06-22.

## Local Git State (branch delta)

- Current repo `HEAD` is on `main`; `feat/propositional-v2` exists both locally and as `remotes/origin/feat/propositional-v2`.
- Local `feat/propositional-v2` log (most recent first):
  ```
  c98c4348 chore(references): English citation for Gentzen 1935
  bbcbef85 fix(Logics/Propositional): revert binder and naming churn, restore derived rules
  c9364b65 feat(Logics/Propositional): make IPL the base logic with primitive ex falso
  cc44c14d doc: fix docstrings for primitive bot perspective
  1a2e2e7e feat(Logics/Propositional): five-primitive formula type with primitive bot
  ```
- **GitHub's current PR head SHA is `c9364b65391b1cc2bfd211102a3deb86f3844d48`** — i.e., GitHub has NOT yet seen `bbcbef85` or `c98c4348`. `git log origin/feat/propositional-v2..feat/propositional-v2` confirms exactly these two commits as unpushed.
- **Practical implication for the draft comment**: the comment must not claim the polish items (English-only Gentzen citation, restored implicit-`Γ` binders, restored subscript names, restored `contra`/`efqRule`, explicit `Atom` on `CPL`/`LEM`/`Pierce`, set-builder `CPL`, standard copyright headers) are visible on the PR yet — they exist only on the local branch. Either (a) the branch must be pushed before/alongside posting the comment so GitHub's head matches what the comment describes, or (b) the comment should be phrased to say these commits are queued to be pushed. Since this research dispatch is read-only, the implementation stage must decide/execute the push (out of scope for research).
- Note the small discrepancy: the already-posted 2026-06-30 comment describes the PR as "now four files" (`Defs.lean`, two `NaturalDeduction/` files, `references.bib`) — this matches the GitHub head (`c9364b65`) but does not yet reflect the two pending polish commits' content changes (e.g., Gentzen citation is already English-glossed per that comment's own text, "replaced its German title with an English gloss" — but per task 56's completion_summary, a *further* English-only citation commit (`c98c4348`) exists locally on top of that, suggesting either a follow-up refinement of the same citation or a second unrelated Gentzen-citation cleanup pass. The implementation stage should visually diff `references.bib`/`NaturalDeduction/Basic.lean` between `c9364b65` and `c98c4348` if precise wording is needed for the new comment.)

## Open Questions

1. Should the new comment link **only** the settlement message (606970606) or also benbrastmckie's acceptance (607217129)? Both are useful; the acceptance message directly states implementation status against the compromise, which is what ctchou needs to re-review.
2. Has "other maintainers' input" (which Waring explicitly requested in the settlement message before doing his own full review) actually arrived? Nothing in the fetched Zulip thread after 2026-06-29 shows further maintainer input — this may itself be worth flagging to ctchou/Waring in the new comment, or at least should not be presented as resolved.
3. Should the branch be pushed before posting the comment (so the GitHub head matches the described state), or should the comment explicitly say "pending push"? The description implies the comment must "accurately describe what the pushed branch will contain," which suggests push-then-comment is the intended order, but pushing is a write operation out of scope for this research task.
4. Is a re-review specifically from ctchou sufficient, or should Thomas Waring also be pinged given his "I'll review the PR properly once we've settled on the design" commitment in the settlement message itself? ctchou is the CHANGES_REQUESTED reviewer of record, but Waring is the other party to the actual compromise.
5. What is the precise content delta in `c98c4348`'s "English-only Gentzen citation" commit relative to the Gentzen gloss already described in the 2026-06-30 GitHub comment? Not resolved by this research pass (would require a local diff, which is implementation-stage work, not review-comment-drafting research, though a `git show c98c4348` read is harmless if needed).

## Requested Changes

From ctchou's CHANGES_REQUESTED review (2026-06-15), cross-referenced against what has been addressed:

| Item | Status |
|------|--------|
| Don't cite 1930s German-language papers; use Avigad (2022) chs. 2–3 | Addressed on GitHub (Avigad added, cited first) plus further local-only English-only Gentzen citation polish (commit `c98c4348`, unpushed) |
| Unclear why both `Semantics/Basic.lean` and `Semantics/Bool.lean` are needed | Addressed by removing both from the PR entirely (semantics deferred to a follow-up PR) |
| Coordinate with #607 and #587; wait for #536 | #536 merged and branch rebased on top of it; semantics/connectives removed from #648 resolves the #587/#607 overlap; benbrastmckie has committed (in the Zulip settlement reply) to reviewing #607 separately |

No further explicit change requests exist from ctchou beyond these three bullets — but ctchou has not re-reviewed since 2026-06-15, so there is no confirmation these resolutions are satisfactory, and no sign-off on the `⊥`/`efq` design pivot itself (which postdates ctchou's review).

## Next Steps

For the implementation stage (composing the draft PR comment, per the task's read-only constraint):

1. Draft a first-person, plain-English GitHub PR comment (in benbrastmckie's own voice, per the Zulip AI-content-policy sensitivity noted by Chris Henson) that:
   - Links the settlement permalink: `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/606970606` (Thomas Waring's compromise, 2026-06-28).
   - Optionally also links `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/607217129` (benbrastmckie's acceptance/implementation confirmation, 2026-06-29).
   - Summarizes, for ctchou specifically, how all three of his CHANGES_REQUESTED items were addressed (see table above), distinguishing what's already on GitHub (head `c9364b65`) from what's pending push (`bbcbef85`, `c98c4348` — polish only, no design changes).
   - Explicitly requests re-review from ctchou, noting no re-review has occurred since 2026-06-15 despite two rounds of rework.
2. Decide (with the user, since this is a write operation) whether to push `feat/propositional-v2` (bringing `bbcbef85`/`c98c4348` to GitHub) before or alongside posting the comment, so the PR's visible state matches what the comment describes.
3. Consider whether to also tag/ping Thomas Waring, given his stated intent to do a full review once the design settled.
4. This report and its permalinks are the complete input needed to compose the draft comment; no further Zulip or GitHub fetches should be necessary unless the exact `c98c4348` diff content is needed for precision (see Open Question 5).
