**Thread**: CSLib > Modal Logic
**Reply to**: [@fmontesi](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603)
**Status**: DRAFT — not posted. Requires EXPLICIT user approval before sending. Only send once the
claims below are actually true at post time (task-475 accuracy discipline) — re-verify the current
PR/CI state of #607, #648, #649, #662 and the layer split before sending, since any of these may
have moved by approval time (fmontesi returns 23 July).

---

Hi Fabrizio — following up on the modal-logic thread, and picking up your "one at a time" ask: I've
split the modal/propositional work so each PR owns one clean layer. The one thing I'd love your call
on before you're back is the box-vs-diamond question.

**The split:**
- **#607 (yours)** — the operator-typeclass layer (`Foundations/Logic/Operators/*`); the foundation
  everything else imports.
- **#648** — the propositional formula type (primitive `⊥`) and its natural deduction.
- **#662** — the modal semantics (`Modal/Basic.lean`, `Satisfies`, the K/T/B/4/5 cube).
- **#649** — LTL, downstream; it rebases onto whichever of the above lands first.

The only place two designs can't coexist is `Modal/Basic.lean`, between #607's current basis and
#662:

**Box-vs-diamond — your call.** #607 currently assumes diamond-inclusive primitives
(`{atom, not, and, diamond}`, `box := ¬◇¬`); #662 uses box-primitive (`{atom, bot, imp, box}`,
`diamond := ¬□¬`). They define different constructors for the same `Proposition`, so only one can
stand — and that's a maintainer decision, not something to pick downstream. Short version:
- **Box-primitive**: pure necessitation/K on `box` alone, a genuine free-algebra formula type, and a
  cleaner path to intuitionistic/minimal modal logics (IK/CK) later. Cost: #607's `HasDiamond`/
  `HasNot` instances become derived defs, and some `rfl` characterisations turn into `simp; intro`.
- **Diamond-inclusive** (#607 as-is): keeps the already-reviewed modal edits and `rfl` proofs
  untouched. Cost: `⊥` riding on `atom` loses the free-algebra property, and a later IK/CK extension
  is harder.

For what it's worth, #648 and #662 are both already CI-green and point box-primitive, so one option
is to let your operator layer (#607) land independently and settle box-primitive for the modal
layer — but that's genuinely yours to decide, I don't want to presume.

No rush at all — happy to wait till you're back on the 23rd, or to talk it through at a CSLib meeting
if one lands around then. Thanks for bearing with the PR-split — hopefully it makes each piece easier
to review on its own.
