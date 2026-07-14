**Thread**: CSLib > Modal Logic
**Reply to**: [@fmontesi](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603)
**Status**: DRAFT — not posted. Requires explicit user approval (Phase 6 gate) before sending,
and must only be sent after PR #662 has actually been retargeted/updated (Phase 5), so the claims
below are accurate at post time.

---

Hi Fabrizio — thanks for taking the time to look at this, and sorry for landing such a large PR
on you at once. I've gone back and split it up rather than asking you to review it all together.
Taking your points one at a time:

**1. Size/scope.** You're right that mixing the propositional-logic rework (#648) with the
modal-logic contribution made this hard to review productively. I've now rebased #648
(`feat/propositional-v2`) onto current `upstream/main` and rebuilt this PR as a single commit
**stacked on top of #648**, containing only the six files that are genuinely new: `Modal/Basic.lean`,
`Modal/Cube.lean`, `Modal/Denotation.lean`, `Modal/LogicalEquivalence.lean`,
`Foundations/Logic/Connectives.lean`, plus the `Cslib.lean` registration line. No propositional
files are touched — everything there is inherited unchanged from #648. The base of this PR is now
`feat/propositional-v2`, not `main`.

**2. Design questions on the primitive set.** I kept box as primitive rather than diamond, for the
same reason you'd expect: necessitation and the K axiom are pure proof rules on a single primitive
when box is primitive, whereas with diamond primitive you'd need the interaction law `¬◇¬` instead.
I've written this up as a doc comment in `Basic.lean` with the Blackburn–de Rijke–Venema vs.
Chagrov–Zakharyaschev references for both conventions, so the choice (and its tradeoffs) is
explicit rather than assumed. Diamond is derived classically as `¬□¬φ`, which I've flagged
explicitly depends on excluded middle and won't carry over once we do intuitionistic/minimal modal
logic — at that point we'd need a primitive `HasDia` typeclass alongside `HasBox`. I've deliberately
*not* attempted that generalization here; it's future work, noted as a TODO rather than solved
half-way.

**3. The `HasBox`/`ModalConnectives` typeclasses vs. your #607.** I went with the "one class per
operator" direction from your #607 (`HasBot`, `HasImp`, `HasBox`, bundled into
`PropositionalConnectives`/`ModalConnectives`), but self-owned it in `Connectives.lean` in this PR
rather than depending on #607 directly, since #607 isn't merged yet and doesn't currently have
`HasBot`/the bundled classes I needed. This is a known, temporary duplication — once #607 lands
I'd like to coordinate on folding this into it rather than maintaining two typeclass hierarchies.
Happy to sync on that whenever suits you.

**4. Logical equivalence.** Separately (task 472, already on `main`), I made `Proposition.Equiv`
parametric in the model class `S` rather than fixed to "all models" — this lets equivalence be
stated relative to any of the modal-cube classes (T/B/4/5/S4/S5, etc.), not just K. That fix is
folded into this PR's `LogicalEquivalence.lean` as well, so the stacked #662 and the version on
`main` agree.

I know you're away until 23 July — no rush on any of this. Whenever's convenient after you're
back, I'd also be glad to join a CSLib online meeting if one's being scheduled, to talk through
the #607/Connectives coordination and anything else that'd help review go more smoothly. Let me
know what works.

Thanks again for the detailed look — happy to split this further or adjust the design if any of
the above doesn't sit right.
