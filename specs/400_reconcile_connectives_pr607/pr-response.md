# PR #607 review comment — draft

**Target**: https://github.com/leanprover/cslib/pull/607 · **Post as**: @benbrastmckie (author of the 2026-06-17 comment and of #648)
**Status**: draft — human review required before posting (CSLib Zulip AI policy)

**Grounding** (verified vs #607 head `c2ec296` + #648 + local main):
- #607 head rewrites `Propositional/Defs.lean`: `Proposition := {atom, and, or, impl}` (no primitive bot); `⊥ = atom ⊥` via `instBotProposition [Bot Atom]`; `neg`/`top` derived (gated `[Bot Atom]`/`[Inhabited Atom]`); `@[grind =] not_eq [Bot Atom] : (A → ⊥) = ¬ A := rfl`; plus its own `MPL`/`IPL`/`CPL`/`IsIntuitionistic`/`IsClassical` and `HasAnd/HasOr/HasImpl/HasNot` instances. 8 operator classes in `Cslib.Logic`; precedences `→`25 `∧`36 `∨`30 `⊗`35 `↔`20 `¬`40.
- #648 = `Propositional/Defs.lean` (five-primitive `Proposition`, primitive `⊥`) + `NaturalDeduction/{Basic,Theory}.lean` + `references.bib`; no connective classes (dropped, commit `85db79a6`). Local main also defines `MPL`/`IPL`/`CPL`/`IsIntuitionistic`/`IsClassical` (no `[Bot Atom]`), `neg := (·.imp .bot)`. CSLib uses `HasSubstitution`/`HasFresh` (no `HasContext`). NOTATION.md silent on connectives.

---

Following up on my comment above: the overlap I flagged is now resolved on #648's side — I've removed the connective typeclasses from #648, so it no longer duplicates the classes in this PR. #648 now contributes the five-primitive `Proposition` (primitive `⊥`), its natural deduction, and an `MPL`/`IPL`/`CPL`/`IsIntuitionistic` theory layer.

That leaves one spot where the two PRs still meet: your head has since its own `Proposition` and a near-identical `MPL`/`IPL`/`CPL`/`IsIntuitionistic` development in the same file, `Propositional/Defs.lean`. To stay coordinated we'd need a single `Proposition` and one copy of that theory layer. The one substantive decision is how `⊥` is represented — here it's `Proposition = {atom, and, or, impl}` with `⊥ = atom ⊥` gated on `[Bot Atom]`; in #648 `⊥` is a primitive constructor.

I'd favor the primitive `⊥`, mainly for substitution-invariance ([Zulip](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/604219492)): when `⊥ = atom ⊥`, falsum lies in the image of `atom`, so a substitution `Atom → Proposition` can rewrite it and the type is no longer the free algebra over the signature. A primitive `bot` keeps `⊥` fixed under substitution, drops the `[Bot Atom]`/`[Inhabited Atom]` side-conditions (`not_eq : (A → ⊥) = ¬A` becomes an unconditional `rfl`, and minimal logic works over any atom type), and gives `⊥` its own case in every recursion rather than folding it into `atom`. The gap is narrow either way — #607 already reuses Mathlib `Bot`/`Top` and has `not_eq := rfl` — so whichever we pick, that theory layer should live in one place; happy to do the merge, or to adapt #648 to whatever you settle on.

Two smaller notes: I'd keep the `Has*` prefix (bare `And`/`Or`/`Iff` clash with core, and CSLib already uses `HasSubstitution`/`HasFresh`), and the connective precedences are worth recording in `NOTATION.md`. The file consolidation and the grind-into-notation point already look covered.
