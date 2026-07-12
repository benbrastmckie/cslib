**Thread**: CSLib > Modal Logic
**Reply to**: [@fmontesi](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603) (his 2 July message — "overwhelmed… take these one at a time… back 23 July")
**Status**: DRAFT — not posted. Requires EXPLICIT user approval before sending. Only send once the claims below are actually true at post time (task-475 accuracy discipline) — re-verify the current PR/CI state of #607, #648, #649, #662 and the layer split before sending, since any of these may have moved by approval time (fmontesi returns 23 July). This draft endorses making **both □ and ◇ primitive** in `Modal/Basic.lean` — converging #607's diamond basis with #662's box basis rather than deriving either — and so supersedes the earlier box-first framing. It keeps the necessitation/K signature point (12 June message) to a single reassurance clause and does not re-run the full argument.

**Re-verify before posting** (as of 2026-07-11): #607 is CI-green and consolidated into `Foundations/Logic/Operators.lean` (adds `HasBox`/`HasDiamond`/dynamic-logic typeclasses; still ◇-primitive with `box := ¬◇¬φ`). #648 (box-primitive prop base), #662 (box-primitive modal), and #649 (LTL) were all rebased onto current upstream/main on 2026-07-11 and now report `mergeable=MERGEABLE`; CI was re-triggered on the new tips (`pending` at rebase time). Pre-rebase branch tips are preserved as `backup/{648,662,649}-pre-rebase-jul11`. Before posting, confirm all three CI runs went green.

**Discovered issue in #607 itself** (task 477, follow-up task 485): while reworking #662 onto a both-primitive basis stacked on #607, the whole-library build was found to fail on #607's own tip — `Cslib/Logics/HML/LogicalEquivalence.lean` still instantiates the **old 3-arg** `LogicalEquivalence` class, but #607's `Foundations/Logic/LogicalEquivalence.lean` already upgraded that class to a **4-arg** signature (adds the inference-system param `S`). HML appears to have been missed when Modal and CLL were migrated to the new `HasLogicalEquivalence` API. Confirmed pre-existing and independent of #662 via `git stash` isolation on a pristine `pr607` base. This blocks `checkInitImports`/`shake`/`test` for the entire library (all pull in the `Cslib.lean` aggregator). Verify this is still present before mentioning it (fmontesi may fix it upstream first). Task 485 tracks a narrow instance migration if a local fix is preferred.

---

Hi @fmontesi,

No worries at all, and sorry about the volume. I'd be glad to join a CSLib meeting once you're back on the 23rd, though I'm in SF so 3:30am meeting time might be tricky for me.

To shrink the pile a little before then, I've tried to arrange things so each PR is one self-contained layer you can look at on its own: #648 is just the propositional formula type, #662 is just the modal semantics stacked on it, and #607 (yours) provides the operator-typeclass layer they both build on. #649 (LTL) sits downstream and rebases onto whichever lands first. All three are now rebased onto current main and CI-green, so none of this has to move together.

I'm glad to see both □ and ◇ as primitive since we'll need both eventually for the intuitionistic and minimal systems (IK, CK). Necessitation and K still touch only □, so the proof theory doesn't get any heavier. I will refactor #662 onto a both-primitive basis so it lines up with #607.

One small heads-up from doing that refactor: `Cslib/Logics/HML/LogicalEquivalence.lean` still uses the old 3-arg `LogicalEquivalence`, which now clashes with the 4-arg class #607 introduces — it looks like HML was missed when Modal and CLL were migrated, and it currently breaks the whole-library build on #607's tip (independent of my modal work). A small instance migration mirroring the Modal/CLL ones should sort it; happy to push that as a tiny PR against #607 if that's easiest.

Everything else we can take one at a time, as you suggested — happy to walk through it whenever suits. Enjoy the time away, and talk on the 23rd.
