**Thread**: CSLib > Modal Logic
**Reply to**: [@fmontesi](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603)
**Status**: DRAFT — not posted. Requires EXPLICIT user approval before sending. Must only be sent
once the claims below are actually true at post time (task-475 accuracy discipline) — in
particular, re-verify the current PR/CI state of #607, #648, #649, #662 and the layer-ownership
split described below before sending, since any of these may have moved by the time approval is
given (fmontesi returns 23 July).

---

Hi Fabrizio — following up on the modal-logic thread, and picking up your "one at a time" ask: I've
split the modal/propositional work so each PR now owns one clean layer, and wanted to check in on
two things before you're back.

**1. Clean division across the four open PRs.** The layers now look like this:
- **#607 (yours)** — the operator-typeclass layer (`Foundations/Logic/Operators/*`): `HasAnd`,
  `HasOr`, `HasNot`, `HasImpl`/`HasImp`, `HasBox`, `HasDiamond`, etc. This is the foundation
  everything else imports.
- **#648** — the propositional formula type (primitive `⊥`, five-primitive `Proposition`) and its
  natural deduction.
- **#662** — the modal semantics (`Modal/Basic.lean`'s `Proposition` type, `Satisfies`, the K/T/B/4/5
  cube).
- **#649** — LTL, downstream of both #648 and #607/#662; it'll rebase onto whichever of those lands
  first.

Checked the overlaps: #607 and #648/#649 only share a few `HasAnd`/`HasOr` instance lines in
`Propositional/Defs.lean`, which reconcile trivially once your operator classes are the single
source of truth. The one place two designs can't coexist is `Modal/Basic.lean` between #607's
current basis and #662 — see below.

**2. The box-vs-diamond primitive question — your call.** #607's current modal edits assume
diamond-inclusive primitives (`{atom, not, and, diamond}`, with `box := ¬◇¬`). #662 instead uses
box-primitive (`{atom, bot, imp, box}`, with `diamond := ¬□¬`, necessitation and K stated purely on
`box`). These aren't reconcilable as-is — they define different constructors for the same
`Proposition` type — so this needs a decision from you as maintainer, not something we should just
pick downstream. Quick tradeoff summary:
- **Box-primitive** gives a pure necessitation rule and K axiom on `box` alone, a genuine
  free-algebra formula type (substitution-invariant, no `⊥ = atom ⊥` side-condition), and cleaner
  forward-compatibility with intuitionistic/minimal modal logics (IK/CK) via a later primitive
  `HasDia`. Cost: #607's current `HasDiamond`/`HasNot` primitive instances would need to become
  derived defs, and the modal `Satisfies` characterisations move from `rfl` to `simp; intro`.
- **Diamond-inclusive** (#607's current basis) keeps the already-reviewed modal edits and `rfl`
  characterisations exactly as they are — minimal near-term churn. Cost: `⊥` riding on `atom`
  breaks the free-algebra property and reintroduces a `[Bot Atom]` side-condition, and a future
  IK/CK extension would be harder to add cleanly.

For what it's worth, #648 (primitive `⊥`) and #662 (box-primitive) are both already CI-green and
already point the box-primitive direction, so there's an argument for letting your operator layer
(#607) land independently of this choice and settling on box-primitive for the modal semantics —
but that's genuinely your decision to make, not ours to assert, and I don't want to presume it.

**3. Offering what #662 already built.** While building the modal semantics I ended up prototyping
a `HasBot` class plus bundled `PropositionalConnectives`/`ModalConnectives` classes — exactly the
two things #607 is currently missing per the chenson2018/ctchou "should these be bundled?" and
eric-wieser "maybe one file" threads. Happy to offer those to #607 (suggestion or small follow-up
PR) so the operator layer lands complete and everything downstream just imports it, rather than
each PR growing its own interim typeclass file.

No rush on any of this — happy to wait until you're back on the 23rd, and equally happy to sync at
a CSLib meeting if one gets scheduled around then to talk through the primitive choice and the
naming question (`imp` vs `impl` — again, your call, we'll conform). Let me know what works.

Thanks for bearing with the PR-splitting — hopefully this makes each piece easier to review on its
own.
