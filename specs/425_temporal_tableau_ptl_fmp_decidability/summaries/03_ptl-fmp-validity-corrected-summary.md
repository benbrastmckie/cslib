# Implementation Summary: PTL Finite Model Property and Temporal Tableau Decidability (validDiscrete-corrected)

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Plan**: plans/03_validity-corrected-fmp-plan.md
- **Status**: [PARTIAL] — Phases 1-2 complete and verified; Phase 3 blocked (documented finding);
  Phase 4 partial (spike complete, tractability confirmed); Phases 5-8 not started.

## What Was Done

### Phase 1: Semantics and domain foundation [COMPLETED]

- Added `Temporal.satisfiableDiscrete` and `Temporal.Validity.validDiscrete_iff_not_satisfiableDiscrete_neg`
  to `Cslib/Logics/Temporal/Semantics/Validity.lean`, mirroring `satisfiable`/`satisfiable_not_valid_neg`
  over the discrete-serial frame class (`NoMaxOrder`, `NoMinOrder`, `SuccOrder`, `PredOrder`,
  `IsSuccArchimedean`).
- Restricted `branchSat`'s existential domain in `Cslib/Logics/Temporal/Tableau/Soundness.lean` to the
  same discrete-serial frame class (previously bare `[LinearOrder D] [Nontrivial D]`, which admitted a
  dense countermodel — the root cause of the prior plan-01 Phase-A block). `classicallyClosed_unsat`
  updated (five extra `_` discards) and still builds.
- Added three missing BibKeys to `references.bib` (`HodkinsonReynolds2006`, `CaleiroViganoVolpe2013`,
  `Gabbay1993`) and updated the `## References` sections of `Soundness.lean`/`Completeness.lean` to
  canonical format.
- Verified: `lake build` green on both targets; `lean_verify` reports only `propext`/`Classical.choice`/
  `Quot.sound`.

### Phase 2: Run-level faithfulness invariant [COMPLETED]

- Added `TrackerBranchFaithful` to `Cslib/Logics/Temporal/Tableau/Saturation.lean`: every pending
  eventuality in an `EventualityTracker` is backed by an actual positive occurrence on the branch.
- Proved the full run-level threading: `fulfillEventualities_pending_subset`,
  `registerEventualities_new_or_old`, `temporalStepBranch_preserves_faithful` (single-step
  preservation), and a parallel `WorklistInvFaithful`/`P1Faithful`/`P2Faithful`/`run_level_faithful`
  induction (three-list variant of the existing `WorklistInv`/`P1`/`P2`/`run_level_P1` induction that
  proves `temporalTableau_instantStrict`), without modifying the already-landed `InstantStrict`
  machinery. Entry-point corollary: `temporalTableau_trackerBranchFaithful`.
- Verified: `lake build` green; `lean_verify` on the entry corollary reports only `propext`/`Quot.sound`.

### Phase 3: Soundness half [BLOCKED — see plan file for full writeup]

Careful analysis of `eventualityDefect_unsat`'s target statement (`branchSat b ord → False` given
`findEventualityDefect b ord tracker = some t` and `TrackerBranchFaithful b ord tracker`) found that
report 02 Finding 3(b)'s "local two-point pigeonhole under `IsSuccArchimedean`" sketch does not close:
`branchSat`'s existential model is not constrained by the tableau's own procedural "still pending"
bookkeeping — a duplicated pending Until/Since formula at two branch labels gives two *independent*
existential witnesses in any model, with no forced relationship between them. The standard soundness
argument for this style of tableau (Wolper-style rule-soundness induction, guided by an assumed model
across the *entire* construction history) is a materially larger undertaking than the local invariant
sketched in report 02, and corresponds to the *original* pre-task "Blocked Obligation" #2 in
`Soundness.lean`'s docstring (`temporalStepBranch_preserves_sat`), not something Phase 2's
`TrackerBranchFaithful` alone resolves. Full write-up, including the exact semantic argument for why
the local statement appears false as specified, is in the plan file under Phase 3's `[BLOCKED]`
heading. No `sorry`/vacuous placeholder was introduced; `eventualityDefect_unsat` and
`temporalTableau_sound` remain undefined pending a research/planning revision.

**Per the plan's own Wave dependency table, Phase 3 gates only Phase 8** (the final decidability
instance) — Phases 4-7 (the FMP/completeness construction, the task's core novel contribution) depend
only on Phase 1 and each other, not on Phase 3, so work continued there.

### Phase 4: Countermodel redesign — bi-lasso extractModelℤ [PARTIAL]

Following the plan's explicit spike-first discipline, spiked the periodic-reduction core of the
bi-lasso `extractModelℤ` redesign in `Completeness.lean`:

- `periodicReduce (instAnc instNew : ℤ) (hL : instAnc < instNew) (z : ℤ) : ℤ` — folds any integer
  beyond `instNew` back into the loop window `[instAnc, instNew)`, using Mathlib's `toIcoMod`
  (`Mathlib.Algebra.Order.ToIntervalMod`).
- `extractModelℤPeriodic` — the periodic model, parameterized by an explicit loop witness
  `(instAnc instNew : ℤ) (hL : instAnc < instNew)` rather than one derived from `isSubsetBlocked`
  (that derivation is unstarted; see below).
- Three property lemmas confirming tractability: `extractModelℤPeriodic_atom_sat_iff_of_le` (identity
  below `instNew` — the spike's literal ask), `extractModelℤPeriodic_atomPos_sat_of_le`, and
  `periodicReduce_mem_Ico_of_gt` (the genuinely load-bearing fact: wraparound always lands back in
  `[instAnc, instNew)`, via Mathlib's `toIcoMod_mem_Ico`).

**Spike outcome: tractable.** `noncomputable` is required throughout (`toIcoMod` is noncomputable),
matching the accepted `Decidable`-instance precedent elsewhere in the library.

**Not yet done** (substantial remaining work, each comparable in scope to Phases 1-2 combined):
1. The loop-extraction helper deriving an actual `(t_anc, t_new : TimeIndex)` pair and
   `hL : ord.instant t_anc < ord.instant t_new` from a genuine `isSubsetBlocked b t_new t_anc = true`
   witness (currently `instAnc`/`instNew`/`hL` are free parameters to the spike).
2. The symmetric backward-loop periodic reduction for the past tail (the spike only does the forward
   tail; the full bi-lasso is periodic-past + finite-middle + periodic-future).
3. Wiring `extractModelℤPeriodic` in to replace `extractModelℤ` at real call sites.
4. The "every instant carries a complete Hintikka time-type" helper (report 01 §8.3).
5. Re-proving all `extractModelℤ_*` atom/bot property lemmas against the new definition.

### Phases 5-8: Not started

Blocked transitively on Phase 4's remaining work (5, 6, 7) and Phase 3 (8).

## Plan Deviations

- Phase 1: `validDiscrete_iff_not_satisfiableDiscrete_neg` was proved as a genuine biconditional
  (both directions) rather than a verbatim one-direction mirror of `satisfiable_not_valid_neg`, since
  the plan's own Goals section states the target as an `↔`.
- Phase 2: `TrackerBranchFaithful`'s landed conjunct omits the `e.isUntil = true → e.formula.isUntl`
  shape clause from the plan's sketch; branch-membership alone is what every consumer needs (the shape
  fact is separately available via `registerEventualities_new_or_old`).
- Phase 3: escalated as `[BLOCKED]` rather than implemented — see above and the plan file for the full
  reasoning.
- Phase 4: partial — spike only, per the plan's own explicit "confirm tractability before building the
  rest of the phase" instruction; the remaining four sub-tasks are unstarted, not deviated-from.

## Verification

- `lake build` green on all touched modules (`Semantics.Validity`, `Tableau.Soundness`,
  `Tableau.Saturation`, `Tableau.Completeness`) both individually and together with their known
  downstream consumers (`Metalogic.DenseCompleteness`, `LTL.EmbeddingSemantics`).
- `lake exe lint-style` clean on all touched files.
- No `sorry`, no vacuous definitions, no new axioms anywhere in the diff (`lean_verify` on every new
  public declaration reports only `propext`/`Classical.choice`/`Quot.sound`).
- **Known external blocker (not in scope)**: `lake lint` (project-wide) and a bare `lake build`
  currently fail on `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (unsolved goals), which is
  unrelated in-progress work from a concurrent session, not touched by this task. `checkInitImports`
  could not run project-wide for the same reason; all files touched here import `Cslib.Init`
  transitively (they did before this dispatch too — no new files were created).

## Cross-Task Note

Task-301 registration of `instDecidableValid` (Phase 8) also depends on sibling tasks 423/424 landing,
per the plan's Non-Goals section — moot for now since Phase 8 is additionally blocked on Phase 3.

## Files Modified

- `Cslib/Logics/Temporal/Semantics/Validity.lean`
- `Cslib/Logics/Temporal/Tableau/Soundness.lean`
- `Cslib/Logics/Temporal/Tableau/Saturation.lean`
- `Cslib/Logics/Temporal/Tableau/Completeness.lean`
- `references.bib`
- `specs/425_temporal_tableau_ptl_fmp_decidability/plans/03_validity-corrected-fmp-plan.md`

## Commits

1. `task 425 phase 1: satisfiableDiscrete, branchSat discrete restriction, references`
2. `task 425 phase 2: TrackerBranchFaithful run-level invariant`
3. `task 425: block phase 3 (eventualityDefect_unsat likely unprovable as specified)`
4. `task 425 phase 4 (partial): spike bi-lasso periodic countermodel core`

## Recommended Next Steps

1. **Research/replan Phase 3**: either find the missing semantic ingredient (if the local statement
   is in fact provable by some argument not surfaced here), or redesign `eventualityDefect_unsat`/
   `temporalTableau_sound` as a run-level, model-guided induction over `temporalStepBranch`/
   `processNext` (materially larger than the current ~4h estimate).
2. **Continue Phase 4**: the loop-extraction helper is the natural next step (it also informs how
   Phase 3's redesign, if any, would obtain its own loop witness).
3. Phases 5-7 can then proceed once Phase 4 is complete; Phase 8 needs both 3 and 7.
