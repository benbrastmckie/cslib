# Zulip reply — "Propositional Logic" thread — draft

**Task**: 400 — reconcile_connectives_pr607
**Target**: CSLib Zulip "Propositional Logic" thread (reply to Waring, msg 606970606)
**Status**: draft (rewrite in your own words before posting — CSLib Zulip AI policy)

---

Thanks, that makes sense — I've pulled the connective typeclasses out of #648 so there's no competing module, and I'll leave a review on [#607](https://github.com/leanprover/cslib/pull/607) to help it along; the designs really are close. The main substantive thing I want to raise there is falsum: for minimal/intuitionistic propositional logic with a primitive `⊥` (where `¬φ := φ → ⊥` and `⊤ := ⊥ → ⊥`), I think a formula type can register faithfully by reusing Mathlib's `Bot`/`Top` together with a derived `HasNot` (`not := neg`) and a `(φ → ⊥) = ¬φ` grind bridge, rather than adding a `HasBot` class. Beyond that it's mostly naming (the `Has` prefix, and `imp` vs `impl`), the direction of the `_def` lemmas that chenson flagged, and writing the precedence ladder into `NOTATION.md`. Once #607 lands I'll rebase our five-primitive `Proposition` onto the atomic classes and add the convenience bundles as a separate follow-up PR.
