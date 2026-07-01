# Implementation Summary: Audit and Reduce maxHeartbeats Inflation (Task 453)

- **Task**: 453 - Audit and reduce `maxHeartbeats` inflation across Bimodal/Temporal metalogic;
  normalize scoping to `in`-scoped
- **Plan**: plans/01_reduce-maxheartbeats-inflation.md
- **Status**: All 4 phases COMPLETED
- **Result**: Zero-debt reduction. All 64 `set_option maxHeartbeats` sites in
  `Cslib/Logics/{Bimodal,Temporal}/Metalogic/**` were eliminated (not lowered, eliminated) --
  every single one was pure defensive inflation, confirmed by an actual `lake build` on the
  option-removed file for each site. No declaration in the entire inventory required any extra
  heartbeat budget above the 200000 default.

## Before/After Value Distribution

| Value | Before (count) | After (count) |
|-------|-----------------|-----------------|
| 6400000 (32x) | 1 | 0 |
| 3200000 (16x) | 33 | 0 |
| 1600000 (8x) | 12 | 0 |
| 1200000 (6x) | 3 | 0 |
| 800000 (4x) | 11 | 0 |
| 400000 (2x) | 4 | 0 |
| **Total** | **64** | **0** |

| Scoping | Before | After |
|---------|--------|-------|
| Unscoped (file-wide) | 15 | 0 |
| Scoped (`... in`) | 49 | 0 |

Zero `maxHeartbeats` sites remain anywhere in `Cslib/Logics/Bimodal/Metalogic/**` or
`Cslib/Logics/Temporal/Metalogic/**` (grep-verified).

## Per-Phase Outcome

- **Phase 1** (15 unscoped file-wide sites): build-probed each (delete option, `lake build`,
  check for failing declarations). All 15 files' declarations built clean at the default with
  the option deleted entirely -- zero needed a scoped replacement of any value.
- **Phase 2** (49 scoped sites, targeting the 33x 3.2M cluster + opportunistic lower sites):
  same probe procedure applied to every scoped site across `CompletenessHelpers.lean`,
  `DedekindZ/Cases.lean`, `CountermodelExtraction.lean`, `Saturation.lean`, `QLemma.lean`,
  `Eliminations.lean`, `HierarchyCaseSep.lean`, `RecursiveWalks.lean`, `DenseCompleteness.lean`,
  and (opportunistically) `GeneralizedNecessitation.lean`. All 48 sites removed entirely; bisection
  to a nonzero value was never needed anywhere.
- **Phase 3** (planned: lemma-extract the worst offender, `eliminatePotentialCounterexample` at
  6.4M): the build-probe showed this declaration also builds clean at the 200000 default (~7s),
  so the planned 4-arm lemma extraction was unnecessary and was **not performed** -- the proof
  statement and structure are completely unchanged. This is a documented deviation from the plan
  (see plan file Phase 3 task annotations).
- **Phase 4** (planned: document remaining >=1.6M sites with justification comments): zero sites
  survived to Phase 4, so there is nothing to document. The final CI gate was run instead.

## Plan Deviations

1. **Phase 3 lemma-extraction skipped**: the plan anticipated `eliminatePotentialCounterexample`
   (6.4M, the worst offender) would need restructuring into 4 separate lemmas to lower its
   ceiling. The build-probe disproved this -- the declaration builds clean at the 200000 default
   with no proof changes. Extraction would have been a substantial, risky, and now-unjustified
   change to a 1686-line proof; skipping it is the correct zero-debt outcome.
2. **Phase 3 residual-offender profiling skipped**: the plan reserved `lean_profile_proof` for
   any 3.2M sites surviving Phase 2's bisection. None survived -- every scoped site removed
   cleanly in Phase 2 -- so there was nothing left to profile.
3. **Phase 4 documentation skipped**: the plan's Phase 4 task was to add one-line justification
   comments above every surviving >=1.6M option. Zero options survived, so this task is vacuous
   by construction rather than skipped for cause.
4. **Stale comments removed alongside options**: many removed `set_option maxHeartbeats` sites
   had an adjacent comment claiming heartbeats were "required" (e.g. "Extended heartbeats: ...",
   "requires extended heartbeats due to..."). These claims were disproven by the build-probe, so
   the comments were removed or updated alongside the option to avoid leaving misleading text in
   the codebase. This is a natural extension of the zero-debt code-hygiene goal, not a scope
   violation (no proof statements or logic were touched).

None of these deviations weaken any proof, add any `sorry`, or change any theorem/def statement.
Every reduction was verified by an actual `lake build` on the affected module, per the task's
hard constraint.

## Out-of-Scope Follow-Up

5 further `maxHeartbeats` sites exist elsewhere under `Cslib/Logics/`, outside the two Metalogic
trees this task covers (confirmed untouched):
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean:541` (400000)
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean:581` (210000)
- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean:53` (1600000)
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean:55` (800000)
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean:780` (2000000)

Given how uniformly the Bimodal/Temporal Metalogic inventory turned out to be defensive
inflation, these 5 sites are plausible candidates for the same build-probe treatment in a future
follow-up task, but they were not touched here (out of this task's declared scope).

## Concurrency Note

Task 453 was run without task 414 (Modal/Temporal/Bimodal `simp only` list normalization) running
concurrently -- 414's status remained `not_started` throughout this implementation, so there was
no risk of merge churn on shared files, per the plan's dependency note.

A genuinely unrelated, pre-existing build failure was observed mid-task in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (outside this task's scope,
traced via `git stash` to a concurrent task-317 commit `619acd3a`, not caused by any task 453
change). It self-resolved during the session (the concurrent process evidently fixed it); the
final full-project `lake build`/`lake test`/`checkInitImports`/`lint-style` all pass green.

## Final Verification

- `lake build` (full project) -- green (3188 jobs)
- `lake test` -- green (exit 0)
- `lake exe checkInitImports` -- passes (exit 0)
- `lake exe lint-style` -- passes (exit 0)
- `lake lint` -- no new warnings in any of the 25 modified files (checked against the 7
  prevention categories: docBlame, defLemma, defsWithUnderscore, simpNF, unusedSectionVars,
  topNamespace, dupNamespace)
- `lake shake --add-public --keep-implied --keep-prefix` -- no suggestions touch any of the 25
  modified files (no imports were changed by this task)
- `lake exe mk_all --module` -- no update necessary
- 0 `sorry` in any modified file
- 0 vacuous definitions introduced
- 0 new axioms introduced
- 0 `maxHeartbeats` sites remain in `Cslib/Logics/Bimodal/Metalogic/**` or
  `Cslib/Logics/Temporal/Metalogic/**` (down from 64)

## Files Modified (25)

- `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean`
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Saturation.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/RecursiveWalks.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Burgess.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Seeds.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Splitting.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean`
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean`
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean`
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean`
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`
- `Cslib/Logics/Temporal/Metalogic/MCS.lean`
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean`
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean`

## Commits

17 incremental green-gated commits (`task 453 phase N: ...`), one per file or small batch, plus
plan-status-update commits per phase. All commits pass `lake build` on the affected module at
minimum; the final state passes the full CI pipeline.
