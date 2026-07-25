# Continuation Handoff: Phases 6-11 (Invariant Bundle Through Decidability)

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `plans/02_keyed-s4-driver-restructured.md`
- **Written**: 2026-07-24
- **Session**: sess_1784905751_756cda_535

## What Was Completed This Dispatch

Phases 3, 4, 5 of plan v02 (Phases 1-2 were already landed in a prior dispatch). All commits are
on `main`:

- `91629da0` — task 535 phase 3: re-derive generic combinatorial measure primitives
- `40d2a9c5` — task 535 phase 4: per-call measure obligations for modalApplyOneS4Keyed
- `808f0af5` — task 535 phase 5: modalFuelS4 + entry-measure sufficiency + fuel repoint

**Phase 3** landed four `private` combinatorial primitives in `LoopChecking.lean`
(`modalCount_notMem_append_drop_S4`, `modalCount_notMem_mono_S4`, `modalWork_drop_linear_S4`,
`modalWork_drop_persistent_S4`), verbatim transcriptions of `FmpMeasure.lean`'s file-private
originals.

**Phase 4** landed the three per-call measure obligations for `modalApplyOneS4Keyed φ₀ keys`
(∀ `keys`): `modalApplyOneS4Keyed_persistentFresh_S4`, `modalApplyOneS4Keyed_branchingLength_S4`,
`modalApplyOneS4Keyed_outputsSubsetUniverse_S4`. These required NEW supporting lemmas not
anticipated in the plan's risk table at this granularity: the T-rule/4-rule propagation helpers
(`modalTBoxSelf`, `modalTDiaNegSelf`, `modalFourBoxProp`, `modalFourDiaNegProp` in
`FrameRules.lean`) needed their own freshness facts (`modalTBoxSelf_fresh`,
`modalTDiaNegSelf_fresh`, `modalFourBoxProp_fresh`, `modalFourDiaNegProp_fresh`), and two
intermediate per-call lemmas (`modalApplyOneT_persistentFresh`/`_branchingLength`,
`modalApplyOneS4Rules_persistentFresh`/`_branchingLength`) had to be built layer-by-layer
(K → T → S4Rules → S4Keyed) since `modalApplyOneS4Keyed`'s non-mint case reduces through THREE
wrapper layers, not directly to K.

**Phase 5** landed `modalFuelS4` (placed early in the file, right after
`modalUniverseS4_length_le`, so it is in scope for `modalTableauS4Keyed`'s definition — NOT at
the tail where the plan's phase ordering might suggest) and
`modalExpMeasure_entry_le_fuelS4`, then repointed `modalTableauS4Keyed`'s fuel argument from
`modalFuel φ` to `modalFuelS4 φ`.

All three phases are `lean_verify`-confirmed `propext`/`Classical.choice`/`Quot.sound` only (Phase
5's entry-measure lemma is even cleaner: `propext`/`Quot.sound`, no `Classical.choice`). Zero
`sorry`. `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green throughout, zero new lint
warnings introduced by any of the three phases (checked via full-project `lake build` grep after
each phase — all warnings present are pre-existing, at line numbers below the new additions).

## Hard-Won Lesson: `split_ifs at h` Goal Ordering Is Not `if`-Source-Order

Repeatedly, in this dispatch, `split_ifs at hca with hemp` on a hypothesis
`hca : (if C then A else B) = target` did NOT produce goals in `[C-true, C-false]` order as
naively expected. Empirically (verified via `lean_goal` at each bullet, not by convention):
- The FIRST bullet after `split_ifs at hca with hemp` corresponds to the ELSE/negative case
  (`hemp : ¬C`), not the THEN/positive case.
- When the target and one branch's constructor SHARE the same head (e.g. both `.branching`),
  `split_ifs` auto-discharges the OTHER branch (contradiction via constructor mismatch) and
  produces only ONE live goal — attempting a second bullet then fails with "no goals to be
  solved". This happened for every `notApplicable`/`persistent`-vs-`persistent` split in this
  file.
- When neither branch shares the target's head constructor at all (both mismatch, e.g. target is
  `.branching` but branches are `persistent`/`notApplicable`), BOTH auto-discharge and
  `split_ifs at hca` alone closes the goal with zero bullets needed.
- Always verify goal state empirically per-bullet via `lean_goal` (or just write one bullet,
  build, and let "no goals"/"unsolved goals" errors tell you the true shape) rather than
  reasoning from the `if`'s source-code left-to-right order. This cost significant iteration in
  Phase 4 — budget for it in Phases 6-11, which will hit the same `RuleResult`/`Option`
  case-splitting pattern repeatedly.

## IMPORTANT: Git Commit Contamination Detected

The Phase 5 commit (`808f0af5`) accidentally includes ~190 lines from a DIFFERENT, concurrent
task's work: `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean`,
`Cslib/Logics/Temporal/Semantics/Validity.lean`, and
`specs/451_bxplus_completeness_over_group_flows/plans/01_bxplus-completeness-uniform-class.md`.
This happened because another concurrent agent process staged those files (`git add`) in the
shared working tree between this agent's `git add <task-535-files>` and `git commit` calls —
`git commit` with no pathspec commits the FULL index at commit time, not what `git diff --staged`
showed moments earlier. The content itself appears complete and well-formed (not a
half-edit), so no data was corrupted, but the commit message/attribution is wrong for those
files. **Recommendation for the next dispatch and for `/orchestrate`**: use
`git commit -- <exact task file list>` (pathspec-scoped commit form) instead of plain
`git commit` after `git add`, since pathspec-scoped commits are immune to concurrent
index mutations from other processes. This was adopted for the remainder of this dispatch
(there were no further phases attempted) but should be standard practice for any future dispatch
in this multi-agent session.

## What Is NOT Done: Phases 6-11

None of Phases 6-11 were started (no Lean code written for them). Per the plan's dependency
table, Phase 6 (Wave 3) depends on nothing new, but Phase 7 depends on 6, and Phases 8/10 depend
on 3+4+5 (done) plus 7/9 respectively. Phase 9 (Wave 2) is independent and could be tackled in
parallel with Phase 6 by a `--team` dispatch if desired.

**Phase 6** (handoff 3d-i): Keys-threaded Hintikka-tracking invariant bundle. Define the
keys-threaded analogue of `ModalLoopInvHintikka` (`CompletenessLoop.lean:262-337`), exploiting
`modalHintikkaClauseGen` (`Completeness.lean:652`) carving ALL box/diamond shapes as vacuous
`True` (so the real tracking burden is only propositional shapes + box-negative/diamond-positive
witness existence). Estimated 250-400 lines.

**Phase 7** (handoff 3d-ii): Single-step invariant preservation for `modalStepBranchS4Keyed`
against Phase 6's bundle, mirroring `modalStepBranchS4_preserves_S4LoopInv`
(`LoopChecking.lean:4614+`, now shifted further down by ~280 lines from Phases 3-5's additions —
re-grep the name rather than trust any line number in this handoff or the plan). Estimated
200-350 lines.

**Phase 8** (handoff 3e): Top-loop induction `modalExpandBranchesS4Keyed_hintikka`, assembling
Phase 3's measure primitives + Phase 4's per-call obligations + Phase 5's fuel + Phase 6-7's
invariant, mirroring `modalExpandBranchesHintikka` (`CompletenessLoop.lean:1430-1650+`).
Estimated 250-400 lines. This is the biggest remaining single phase.

**Phase 9** (handoff 4-i): S4 blocked-mint-redirect soundness lemma — genuinely NEW semantic
content (no such lemma exists anywhere; confirmed via `grep` in the prior research). Built from
`S4LoopInv.keyLowerBd`/`keysDistinct` + the reflexive-transitive frame condition. Highest-variance
phase per the plan's risk table. Estimated 150-300 lines. Independent of Phases 6-8 (depends only
on Phase 2, already landed) — a good candidate to dispatch in parallel or first, since a `[BLOCKED]`
result here would be the most consequential discovery for the task's overall viability.

**Phase 10** (handoff 4-ii): Keys-threaded soundness top-loop `modalTableauS4Keyed_sound`, in
`FrameCompleteness.lean`, reusing Phase 3-5 measure/fuel infrastructure and Phase 9's redirect
lemma. Estimated 150-250 lines.

**Phase 11** (handoff 5): `modalTableauS4Keyed_complete`, `s4Valid_decides`,
`instDecidableS4Valid`, in `FrameCompleteness.lean`. Closes the task. Estimated 150-250 lines.

## Recommended Next Steps

1. Re-run `lake exe cache get` if this is a fresh session (Mathlib cache).
2. Dispatch Phase 6 next (blocks Phase 7, which blocks Phase 8). Consider `--hard` mode given the
   ~1500-line remaining scope and the plan's own recommendation (Rollback/Contingency section).
3. Phase 9 can be dispatched independently/in parallel — it only needs Phase 2 (landed) and is
   flagged as the highest-uncertainty phase; surfacing a `[BLOCKED]` there early is more valuable
   than discovering it after Phases 6-8's ~850 lines are sunk.
4. Grep for exact current line numbers before editing — this handoff and the plan file's cited
   line numbers for `LoopChecking.lean` are now stale by ~280 lines (Phases 3-5 added ~280 lines
   total) and will keep drifting with Phases 6-8's additions.
5. Adopt `git commit -- <file list>` (pathspec form) for every phase commit to avoid repeating
   the cross-task contamination noted above.

## Verification Baseline (for regression checking after each future phase)

- `lean_verify hintikka_congr_S4`: `propext`/`Classical.choice`/`Quot.sound`.
- `lean_verify modalExpMeasure_entry_le_fuelS4`: `propext`/`Quot.sound`.
- `lean_verify` on all four Phase 3 primitives and all Phase 4 per-call obligations: same
  three-axiom set, confirmed in this dispatch.
- `grep -n "\bsorry\b" Cslib/Logics/Modal/Tableau/LoopChecking.lean`: exactly one hit, a docstring
  prose mention at (currently) line 4619, NOT code.
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: green.
