# Zulip reply — "Propositional Logic" thread — draft

**Task**: 400 — reconcile_connectives_pr607
**Target**: CSLib Zulip "Propositional Logic" thread (reply to Waring, msg 606970606)
**Status**: draft (rewrite in your own words before posting — CSLib Zulip AI policy)

---

Quick update on #648 first: it's rebased on current upstream/main and down to four files (`Defs`, the two `NaturalDeduction` files, `references.bib`). The substantive change is that ex falso is now a primitive rule (`efq`), so IPL is the base logic; minimal logic and semantics are deferred to separate PRs per the earlier discussion, and the connective typeclasses are out of #648 entirely. On those, I'll review [#607](https://github.com/leanprover/cslib/pull/607) to help it land — the designs are very close.
