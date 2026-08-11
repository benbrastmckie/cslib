# Zulip reply — "Propositional Logic" thread — draft

**Task**: 400 — reconcile_connectives_pr607
**Target**: CSLib Zulip "Propositional Logic" thread (reply to Waring, msg 606970606)
**Status**: draft (rewrite in your own words before posting — CSLib Zulip AI policy)

---

Thanks Thomas — that compromise sounds right to me, and I've implemented it in #648: `⊥` is a primitive constructor and `efq` is now a primitive rule, so IPL is the base logic. Making `efq` primitive makes the `IsBotFree` conservativity statement read more naturally. I've set minimal logic aside for now — the efq-free fragment — precisely so the fragment design gets done properly rather than rushed here: I share your concern that derivation manipulations should carry over instead of being reproved for each, and that deserves its own PR. So #648 is now just the IPL-base foundation, rebased on upstream/main, four files (`Defs`, the two `NaturalDeduction` files, `references.bib`); MPL and the fragment machinery, plus semantics, are deferred to follow-ups.

On your two flags: I've taken the connective typeclasses out of #648 — agreed they're a separate development — and I'll leave a review on [#607](https://github.com/leanprover/cslib/pull/607) to help it land, since the designs are very close. And the references (Gentzen 1935, Prawitz 1965, Troelstra & van Dalen 1988, Avigad 2022) and the link to this thread are now in the PR as of the latest push — sorry they weren't there when you looked. Happy to wait for other maintainers' input on the efq/fragment compromise before you do a full review.
