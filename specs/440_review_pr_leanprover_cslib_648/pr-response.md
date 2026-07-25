# PR Review Response

**PR**: [leanprover/cslib#648](https://github.com/leanprover/cslib/pull/648)
**Date**: 2026-07-25

---

## Changes Made

No code changes were required based on this review — the requests below were already
satisfied by the rework already on the branch (verified against commit `4834be23` on
`origin/feat/propositional-v2`, 2026-07-25).

---

## Response to Reviewers

### ctchou

> Some general comments:
> * I like the idea of adding \bot as a primitive.
> * I don't understand why we need both Semantics/Basic.lean and Semantics/Bool.lean.  I think the latter alone is enough.  Later we can add (for example) Kripke semantics for intuitionistic propositional logic.
> * It is not helpful to the readers to refer to old papers from the 1930s, some of which are in German.  A good modern reference is Jeremy Avigad's textbook:
> https://www.cambridge.org/core/books/mathematical-logic-and-computation/300504EAD8410522CE0C27595D2825A2
> whose chapters 2 and 3 covers everything in this PR.
> * You should definitely coordinate this PR with #607 abd #587.  #536 is ready to merge, so you should wait for it.

Thanks again for the original feedback, and sorry this reply is overdue. Taking each point in
turn, checked against the current branch head:

**`⊥` as primitive.** Glad this direction landed well — it's now the foundation of the PR:
`⊥` is a primitive constructor of `Proposition`, and `efq` (ex falso quodlibet) is a primitive
`Derivation` rule, so IPL is the base logic.

**Addressed — Semantics redundancy.** Both `Semantics/Basic.lean` and `Semantics/Bool.lean`
have been removed entirely, not reduced to one. `Cslib/Logics/Propositional/` now contains
only `Defs.lean` and `NaturalDeduction/`. Semantics is deferred to a follow-up PR — thomaskwaring
independently asked for the same split, so this also has his sign-off.

**Addressed — references.** `Avigad2022` (Avigad, *Mathematical Logic and Computation*, 2022) is
now in `references.bib` and cited first in `NaturalDeduction/Basic.lean`, both in the
implementation-notes list and the reference list. The `Gentzen1935` entry's title was changed to
its English-translation title, "Investigations into Logical Deduction" — no German text appears
anywhere in the citation now. I kept the Gentzen citation itself (moved to last position) rather
than dropping it outright; happy to remove it entirely if you'd still prefer that.

**Coordination.** `#536` is merged and this branch is rebased on top of it. On `#607` and `#587`:
removing the semantics files and the connective typeclasses from this PR removed the direct
file-level overlap with both. I've also left substantive comments on each, flagging the overlap
and proposing how to reconcile the remaining design questions (primitive `⊥`, `Has*` naming,
file organization). That's engaged discussion, not a formal review on either — both PRs are
still open, so I'd rather describe it accurately than as "coordinated" outright.

### Since that exchange

thomaskwaring approved the PR: "this looks pretty good to me! i'd like opinions from other
logic contributors, but on the whole i'd be happy for this to be merged." I also addressed 5
further inline comments from him since — docstring trims and simplifying a couple of
explicit-argument patterns — 4 of which are resolved directly. The fifth, `imp` vs. `impl`
naming (`Modal` currently uses `impl`), is intentionally left open: we agreed to reconcile it
once `#607` lands, since it's a naming question rather than a semantic one, and not something
either of you raised as blocking.

---

## One thing to flag before a re-review

This branch currently has a merge conflict against `main` — in `references.bib` only, and it
looks mechanical (both sides added entries near the same spot, not a design conflict). I'll
rebase and resolve it before merge. Flagging it now so a re-review isn't immediately
invalidated by that rebase.

---

## Remaining Questions / Clarifications

- Should the `Gentzen1935` citation be dropped entirely, or does citing it via the
  English-translation title resolve the original objection? I've left it in (last position,
  translated title) for now — happy to remove it if you'd still prefer that.

---

## Summary

Semantics redundancy is resolved by removing both files outright (semantics itself deferred to
a follow-up PR), and the German-title objection is fixed via an English-translation citation,
with an open offer to drop the Gentzen reference entirely if still unwanted. `#536` is merged
and the branch is rebased on it; the `#607`/`#587` file-level overlap is resolved, with ongoing
design discussion continuing via comments on both rather than a completed cross-review. The one
remaining blocker before merge is a mechanical `references.bib` conflict against `main`, which
I'll rebase and resolve. Would appreciate a re-review when convenient.
