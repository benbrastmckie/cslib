# Zulip reply — "Propositional Logic" thread — draft

**Task**: 400 — reconcile_connectives_pr607
**Target**: CSLib Zulip "Propositional Logic" thread (reply to Waring, msg 606970606)
**Status**: draft (rewrite in your own words before posting — CSLib Zulip AI policy)

---

Quick update on #648 first: it's rebased on current upstream/main, CI green and mergeable, down to four files (`Defs`, the two `NaturalDeduction` files, `references.bib`). The substantive change is that ex falso is now a primitive rule (`efq`), so IPL is the base logic; minimal logic and semantics are deferred to separate PRs per the earlier discussion, and the connective typeclasses are out of #648 entirely. On those, I'll review [#607](https://github.com/leanprover/cslib/pull/607) to help it land — the designs are very close. One correction to something I said earlier: having read #607's actual diff, I don't think it needs a `HasBot` class. A formula type with a primitive `⊥` (where `¬φ := φ → ⊥` and `⊤ := ⊥ → ⊥`) registers faithfully by reusing Mathlib's `Bot`/`Top` plus a derived `HasNot` (`not := neg`) and a `(φ → ⊥) = ¬φ` grind bridge — essentially what #607 already does for the upstream `Proposition`. Beyond falsum it's mostly naming (the `Has` prefix, and `imp` vs `impl` — we've gone with `imp`/`impI`/`impE` in #648, so I'll suggest #607 match), chenson's point about the `_def` lemma direction, and recording the precedence ladder in `NOTATION.md`. Once #607 lands I'll rebase our five-primitive `Proposition` onto the atomic classes and add the convenience bundles as a follow-up PR.
