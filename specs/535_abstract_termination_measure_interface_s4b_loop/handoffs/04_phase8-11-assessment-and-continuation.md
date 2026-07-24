# Continuation Handoff: Phase 8-11 Assessment + Phase 8 Technical Map

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `plans/02_keyed-s4-driver-restructured.md`
- **Written**: 2026-07-24
- **Session**: sess_1784905751_756cda_535

## What Was Completed This Dispatch

Recovered and landed **Phase 7** (single-step invariant preservation), commit `1ce152b6` on
`main`. This dispatch was a resume after a session-limit kill mid-Phase-7; the killed agent had
left ~376 uncommitted lines in `Cslib/Logics/Modal/Tableau/LoopChecking.lean` containing the
`modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` case-split skeleton, which did not build.
Three build-blocking bugs were found and fixed (all in the uncommitted material, none in
previously-landed code):

1. A redundant `clear hnbd` in a (now-deleted) helper lemma, after an `obtain ⟨hnb, hnd⟩ := hnbd`
   had already consumed `hnbd` from context.
2. The helper lemma itself, `keysMatch_eq_keys_of_not_mint`, took `hnbd` (a hypothesis whose type
   mentions the same `s`/`φ` being pattern-matched) as an explicit argument alongside a `match s,
   φ with ...` in its conclusion. Lean's equation compiler auto-reverted `hnbd` into the compiled
   matcher's motive, making the lemma's own matcher permanently non-defeq to the *different*,
   `hnbd`-free matcher compiled for the call sites' inline `keys'`-match (unfolded from
   `modalStepBranchS4Keyed`'s original, hnbd-unaware definition) -- an "Application type mismatch"
   at all 4 call sites. Deleted the lemma as dead code; replaced each call site with the SAME
   working idiom already used at `modalStepBranchS4_preserves_keyLowerBd`
   (`LoopChecking.lean:1491`, pre-existing/frozen): `rcases hs : sf.sign with _ | _ <;> rcases hf :
   sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]` followed by two
   `absurd ⟨hs, ψ, hf⟩ hnbd.{1,2}` closers for the two surviving (impossible) box/diamond
   branches. **Gotcha for future work in this file**: `Sign`'s constructor order is `pos, neg`
   (`Cslib/Foundations/Logic/Tableau/Sign.lean:47-50`), so after `rcases hs : sf.sign with _ | _`
   the FIRST branch is `pos`, not `neg` -- the surviving-goal order after the 14-way case split is
   `(pos, diamond)` then `(neg, box)`, the reverse of what a naive top-to-bottom reading of the
   `match`'s own `.neg, .box` / `.pos, .diamond` arms would suggest. Also: `dsimp only [hs, hf]`
   (not `simp only`) avoids an "unused simp argument" lint warning that `simp only` would trigger
   on the ~12 of 14 branches where only one of the two rewrites is load-bearing for the match to
   iota-reduce to `keys`.
3. Two `have hinveq : ... := by ...` blocks stated their LHS using bare `sf` (e.g.
   `(modalApplyOneS4Keyed φ₀ keys sf (lf ++ b) newAcc0).1 = RuleResult.linear lf`) instead of the
   exposed structure literal `⟨sf.sign, sf.formula, sf.label⟩`. Structure eta makes the two forms
   definitionally equal, so the ORIGINAL proof of `hinveq` still typechecked against either
   statement -- but a LATER `rw [hff] at hinveq` (where `hff : sf.formula = ...`, from a
   `rcases hff : sf.formula with ...` a few lines down) needs a literal `sf.formula` subterm to
   rewrite, which the bare-`sf` form does not expose. Fixed by restating both `hinveq`s with the
   explicit tuple; the existing proof bodies needed no other change.

Verification: `lean_verify` on `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` confirms
`propext`/`Classical.choice`/`Quot.sound` only. Full CSLib CI pipeline run: `lake build
Cslib.Logics.Modal.Tableau.LoopChecking` green (847 jobs), `lake exe checkInitImports` clean,
`lake lint` no new warnings on this file, `lake exe lint-style` clean, `lake shake` no new
findings, `lake exe mk_all --module` reports no update necessary. Zero `sorry` in the file (one
pre-existing docstring-prose mention only, `LoopChecking.lean:4619`). Zero new axioms.

## Required Assessment: Phase 9's `[BLOCKED]` Status and Phases 10-11 Viability

Per the plan's own contingency and the prior dispatch's own note in commit `a2d9d836` ("Phases
7-8 do not depend on 9 and retain full value; proceeding to them"), this dispatch explicitly
re-confirms that assessment rather than silently deferring it:

- **Phase 9's blocker is real and not resolved by anything landed this dispatch.** The blocked
  redirect's soundness obligation (`m.r (f lbl) (f wBlock)` for an arbitrary model witnessing
  `branchSatisfiableIn s4FC`) has no supporting reachability fact anywhere in `S4LoopInv`'s ten
  frozen fields, and S4's `s4FC` (reflexive + transitive, NOT symmetric) does not admit the
  common-origin-reachability argument S5's analogous witness-reuse rule relies on. This is a
  genuine mathematical gap, not a tactic-engineering one; nothing in Phase 6-7's syntactic
  Hintikka-tracking work touches it (Phase 7's own blocked-case argument, via
  `modalStepBranchS4Keyed_blocked_witness_mem`, is a *syntactic* witness-membership fact, entirely
  independent of the *semantic* soundness fact Phase 9 needs).
- **Phase 8 remains independently valuable and should be attempted next.** Its dependency list is
  `3, 4, 5, 7` (all landed) -- it does NOT depend on 9. Completing Phase 8 establishes that the
  keyed driver's output is a genuine syntactic Hintikka set (needed for Phase 11's completeness
  direction), independent of whether soundness (Phase 9-10) is ever resolved.
- **Phases 10-11 are transitively blocked and should NOT be attempted until Phase 9 is
  resolved or re-planned.** Phase 10 (`modalTableauS4Keyed_sound`) depends directly on 9; Phase 11
  (`s4Valid_decides`/`instDecidableS4Valid`, the task's closing deliverable) depends on 10. Absent
  a resolution, `instDecidableS4Valid` -- the definition-of-done target -- cannot be reached by this
  plan as written.
- **Recommendation for unblocking Phase 9** (from `a2d9d836`, still the best concrete option):
  revise the frozen `blockingWorldS4Keyed` guard (task 511) to restrict redirect candidates to
  worlds `acc`-reachable from the current label, giving the missing reachability fact directly at
  the point of redirect selection, rather than trying to recover it after the fact from
  `S4LoopInv`'s existing fields. This would require touching frozen task-511 code (a scope
  expansion beyond this plan's stated non-goals) and should go through `/revise` or a dedicated
  spawned research task before being attempted, NOT as an ad-hoc in-flight change during a Phase
  9 dispatch.
- **This dispatch's own honest terminal**: Phase 7 complete and verified; Phase 8 attempted-and-
  deferred (see below, not started this dispatch -- time/context budget after Phase 7's recovery
  work did not leave enough runway to safely attempt Phase 8's ~250-400 lines of genuinely new
  top-loop induction without risking another incomplete/broken hand-off). Recorded as `partial`
  (7 of 11 phases complete), NOT `implemented`.

## Phase 8 Technical Map (unchanged from the prior handoff, re-verified against current line
numbers)

**Goal**: `modalExpandBranchesS4Keyed_hintikka` -- assemble the termination top-loop so an open
branch produced by the keyed driver is a Hintikka set for the keyed rule, then bridge to the
concrete `modalHintikkaSetS4` form.

**Template**: `modalExpandBranchesHintikka`, `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:
1430-1660+` (re-read in full this dispatch; see excerpt below). Structure:
1. Outer induction on `fuel` (`zero`/`succ` cases).
2. A `suffices key : ...` restating the goal in terms of a `pending`/`done` split (mirrors the
   `modalExpandBranchesGen.processNext` worklist shape).
3. Inner induction on `pending` (`nil`/`cons`).
4. Within `cons`: `by_cases hcl : isModalClosed bh` (closed branches skip via `ih_inner`); else
   `cases hstep : modalStepBranchGen apply bh e a with | none => ... | some step => ...`.
5. The `none` (saturated/open) case is where the actual Hintikka-clause verification happens,
   per-shape (`atom`/`bot`/`imp`/`and`/`or`/`box`/`diamond`, each split on `sign`), consuming
   `modalStepBranchGen_none_saturated` + the `ModalLoopInvHintikka` bundle's own fields
   (`hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/`eDiamondOnlyPos`/`eDiamondPosWitness`) plus
   `hs.boxNegWitness'`/`hs.diaPosWitness'` (from `RuleApplicationSpecCore`) to rule out the
   "matched but not applicable" sub-case.
6. The `some step` case recurses via the OUTER `ih` (fuel induction), consuming
   `modalStepHintikka_preserves_inv` (the generic step-preservation, analogue of what THIS TASK's
   Phase 7 just built bespoke for the keyed driver) and `modalExpMeasure_step_lt_gen` (the generic
   measure-decrease, analogue of Phase 3-4's re-derived combinatorial primitives) to justify the
   fuel decrease.

**What Phase 8 must substitute, concretely**:
- `modalExpandBranchesGen` → `modalExpandBranchesS4Keyed` (landed, Phase 1).
- `modalStepBranchGen apply bh e a` → `modalStepBranchS4Keyed φ₀ bh e a keys` (landed; note the
  EXTRA `keys`/`keys'` threading absent from the generic template -- every recursive call and
  worklist tuple needs an extra `keys` component alongside `(branches, expandedSets, accs)`,
  unlike anything in the generic file).
- `ModalLoopInvHintikka apply φ0 Aux bi ei ai` → the CONJUNCTION of `S4LoopInv φ₀ bi ei ai keysi`
  (frozen, task 511) and `S4KeyedHintikkaInv φ₀ bi ei ai keysi` (Phase 6, landed) -- there is no
  single bundled structure playing `ModalLoopInvHintikka`'s exact role for the keyed driver (by
  Phase 6's OWN documented design decision: `S4KeyedHintikkaInv` deliberately does NOT bundle
  `S4LoopInv`'s fields). Phase 8's per-index invariant hypothesis will need to be a PAIR/conjunction
  of both, threaded through the worklist exactly as Phase 7's own three-hypothesis pattern
  (`S4LoopInv`, `S4KeyedHintikkaInv`, plus the two proof-internal `keysWorldsKnown`/
  `worldsContiguousS4` auxiliaries) already establishes as the call-site convention.
- `modalStepBranchGen_none_saturated` → needs an S4Keyed-specific analogue (does not yet exist;
  check `LoopChecking.lean` for anything named `modalStepBranchS4Keyed_none_saturated` or similar
  before writing one from scratch -- Phase 7's own case-split over
  `modalStepBranchS4Keyed`'s `findSome?`/`split_ifs` structure is the template to mirror, NOT the
  generic file's version, since the keyed driver's `sf`-selection mechanics were already fully
  worked out fixing Phase 7 this dispatch).
- `hs.boxNegWitness'`/`hs.diaPosWitness'` (from `RuleApplicationSpecCore`, generic-only) → the
  keyed driver has no `RuleApplicationSpecCore` instance (it never had one; Phase 1-2's
  restructure bypassed the generic `RuleApply`/`spec` machinery entirely per the v2 plan's own
  overview). The "matched but redirected-to-blocked, so no NEW witness formula emitted" sub-case
  needs Phase 7's OWN blocked-case argument instead:
  `modalStepBranchS4Keyed_blocked_witness_mem` (`LoopChecking.lean:5750` as of Phase 6's dispatch,
  RE-GREP -- Phase 7 added further lines above it) plus the `S4KeyedHintikkaInv.eBoxNegWitness`/
  `eDiamondPosWitness` fields Phase 6-7 already established survive the blocked case.
- `modalExpMeasure_step_lt_gen` → the Phase 3-4 keyed measure-decrease obligations (landed;
  locate via `grep -n "modalExpMeasure.*S4Keyed\|S4Keyed.*measure" LoopChecking.lean` and re-read
  their exact statements before assembling the fuel-decrease argument -- this dispatch did not
  re-verify their exact names/signatures, only confirmed they exist per the Phase 3-4 landed
  commits).
- `hintikka_congr_S4` (Phase 2, landed) + `modalHintikkaSetS4_eq` (re-grep exact line, was
  `LoopChecking.lean:3874` as of Phase 6 but has shifted with Phase 7's insertions) close the
  final bridge to the concrete `modalHintikkaSetS4 φ₀ b acc` target, exactly as the prior handoff
  already noted.

**Estimated size**: 250-400 lines (per plan; unchanged assessment, and the single largest
remaining phase). Given Phase 7's own experience this dispatch -- where even a MOSTLY-COMPLETE,
carefully-designed skeleton needed three distinct non-trivial defeq/matcher-compilation bug fixes
before it built -- Phase 8 should be dispatched with real runway (a fresh session/dispatch, ideally
`--hard` for H8 phase-sizing discipline) rather than appended to an already-long recovery dispatch.

## Recommended Next Steps

1. Dispatch Phase 8 fresh, using this handoff's technical map. Re-grep every cited line number
   first (Phase 7 added ~90 net lines to `LoopChecking.lean`).
2. In parallel or immediately after, either (a) spawn a research task to investigate the
   `blockingWorldS4Keyed` reachability-restriction fix for Phase 9 (touches frozen task-511 code,
   needs its own scoping/`/revise` pass), or (b) accept Phase 9-11 as out of THIS plan's reach and
   formally re-plan the task's remaining scope once Phase 8 lands, whichever the task owner
   prefers -- this dispatch does not have standing to make that call unilaterally since it changes
   the plan's own non-goals (frozen-code modification).
3. `S4KeyedHintikkaInv_weaken`, `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`, and the
   three bug-fix idioms documented above are now the load-bearing per-step API Phase 8 assembles
   against -- treat them as stable/frozen inputs, not subject to re-derivation.

## Verification Baseline (for regression checking after Phase 8)

- `lean_verify Cslib.Logic.Modal.Tableau.modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`:
  `propext`/`Classical.choice`/`Quot.sound`.
- `grep -n "\bsorry\b" Cslib/Logics/Modal/Tableau/LoopChecking.lean`: exactly one hit, a
  docstring prose mention (currently line 4619, re-grep after Phase 8's insertions).
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: green, 847 jobs, zero new warnings versus
  this dispatch's baseline (8 pre-existing `unusedSimpArgs` warnings at lines 2533/3054/3058/
  3120/3124/3145/3152, none in Phase 6-7's own additions).
