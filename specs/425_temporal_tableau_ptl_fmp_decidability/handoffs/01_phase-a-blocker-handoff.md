# Continuation Handoff: Task 425 (PTL FMP / Temporal Tableau Decidability)

- **Dispatch outcome**: Phase A blocked during pre-implementation analysis. No `.lean` files were
  edited (territory `Cslib/Logics/Temporal/Tableau/` untouched). No phases completed.
- **Status**: `partial`, `requires_user_review: true`.

## What Happened

Before writing any Lean code, I traced the exact semantics of every predicate
`eventualityDefect_unsat` would need to consume (`findEventualityDefect`, `isSubsetBlocked`,
`allEventualitiesFulfilledOrDuplicated`, `ancestorTimes`, `EventualityTracker`) against
`branchSat`'s definition and `untl_iff`/`snce_iff`, to make sure the "pumping" argument sketched
in the research report (§3) would actually go through before committing to a Lean proof attempt.
It does not, for three compounding reasons (full detail in the plan file's Phase A `[BLOCKED]`
annotation — `specs/425_temporal_tableau_ptl_fmp_decidability/plans/01_ptl-fmp-decidability-plan.md`):

1. **Hypothesis gap**: the lemma's bare hypotheses (`findEventualityDefect ... = some t`) do not
   tie `tracker`'s pending entries back to actual branch members. That link only holds by
   construction during a real `temporalStepBranch` run (via `registerEventualities` /
   `fulfillEventualities`), not from the static predicate alone.
2. **Two-point insufficiency**: even granting branch-faithfulness, a single subset-blocked
   ancestor/descendant pair `(t_anc, t)` only yields two independent Until-witness existentials
   via `branchSat`, which are mutually consistent (I constructed an explicit non-contradictory
   witness assignment). No contradiction follows without either an infinite-regress/pigeonhole
   argument over the branch's finite time-type space, or negative information the bare predicate
   doesn't supply.
3. **Validity-quantifier mismatch (the deeper finding)**: `branchSat` quantifies over *arbitrary*
   `LinearOrder`/`Nontrivial` D (no seriality/discreteness), but the `untlPos` rule
   (`Rules.lean:264-272`) is only sound if the freshly-created `t'` is the model's immediate
   successor of `t` (its `branch1` case asserts `T(event)@t'` with no guard-on-`(t,t')` clause,
   which is only valid if that open interval is empty). Cross-checked against
   `Metalogic/Soundness.lean:74` / `Metalogic/Completeness.lean:101`, which both target
   `Temporal.validSerial` (`NoMaxOrder`/`NoMinOrder`), and `TimeOrdering`'s `+1`/`-1` successor
   design, which matches `Temporal.validDiscrete` instead. `valid`/`validSerial`/`validDiscrete`
   form a documented *incomparable* hierarchy (`Semantics/Validity.lean:19-39`) — so this plan's
   Phase F target (`Decidable (Temporal.valid φ)`) and `branchSat`'s current signature are very
   likely the wrong validity notion for what this tableau's rules actually decide.

## Recommended Next Action

Before further implementation on task 425, run a dedicated research pass (recommend `--lit` with
the [Reynolds1994] source already cited in `Soundness.lean`/`Completeness.lean`) to settle:

1. Which validity notion (`Temporal.valid`, `validSerial`, or `validDiscrete`) this tableau
   actually decides, given its successor-based `TimeOrdering`.
2. Whether `branchSat` (`Soundness.lean:79-87`) needs a domain hypothesis correction (e.g.
   `SuccOrder`/`PredOrder`/`IsSuccArchimedean`) to make the `untlPos`/`snceNeg` rules sound.
3. What run-level invariant (tracker/branch faithfulness, mirroring the existing
   `WorklistInv`/`OrdFreshWRT` machinery in `Saturation.lean`/`Rules.lean`) is needed to make
   `eventualityDefect_unsat` provable, and whether it should be threaded through a
   `run_level_P1`-style induction like `temporalTableau_instantStrict`.
4. The corresponding correction to Phase F's target — likely `Temporal.validDiscrete`, not
   `Temporal.valid`.

This is likely a plan-revision-scale finding (new/updated report, then a revised plan), not a
same-dispatch implementation fix. Recommend `/research 425 --lit --hard` (H3 reference grounding
against Reynolds 1994) followed by `/revise 425` before the next `/implement 425`.

## Files Touched This Dispatch

- `specs/425_temporal_tableau_ptl_fmp_decidability/plans/01_ptl-fmp-decidability-plan.md` — Phase A
  marked `[BLOCKED]` with full blocker writeup; Phase B annotated with a cross-reference note;
  plan-level `Status` field set to `[BLOCKED]`.
- `specs/425_temporal_tableau_ptl_fmp_decidability/handoffs/01_phase-a-blocker-handoff.md` — this
  file.
- `specs/425_temporal_tableau_ptl_fmp_decidability/summaries/01_ptl-fmp-summary.md` — dispatch
  summary.
- No `Cslib/**/*.lean` files were read-write touched; `Cslib/Logics/Temporal/Tableau/` remains
  exactly as it was before this dispatch (verified clean via `git status`).

## Coordination Note

Task 425's territory (`Cslib/Logics/Temporal/Tableau/`) was not touched, so no conflict with the
concurrently-running tasks 393 (Foundations/GenericMCS), 535 (Modal/Tableau), or 449
(Temporal/ProofSystem + Metalogic soundness files).
