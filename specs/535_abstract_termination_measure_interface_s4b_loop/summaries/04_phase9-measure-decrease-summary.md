# Phase 9 Dispatch Summary: Keyed Per-Step Measure Decrease

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `plans/03_completeness-line-rescope.md`, Phase 9
- **Scope of this dispatch**: Phase 9 only (`modalExpMeasure_step_lt_S4Keyed`)
- **Commit**: `31557bf1` — "task 535 phase 9: keyed per-step measure decrease over modalUniverseS4"

## What landed

`modalExpMeasure_step_lt_S4Keyed` (`Cslib/Logics/Modal/Tableau/LoopChecking.lean`): one step of
the keyed 4-tuple stepper `modalStepBranchS4Keyed` strictly decreases the base-3 damped worklist
measure `modalExpMeasure (modalUniverseS4 φ₀) …` by at least one. This is the fuel-decrease fact
Phase 10's top-loop induction needs.

The lemma is a line-by-line transcription of the public `modalExpMeasure_step_lt_gen`
(`FmpMeasure.lean:3227`), which is hardwired to K's `modalUniverse φ0`/`modalWorldBound φ0` and so
cannot be called directly against the S4-keyed line (confirmed by the plan's "Measure-Decrease
Lead" section; direct instantiation does not typecheck). The transcription consumes:

- Phase 3's four universe-generic combinatorial primitives (`modalCount_notMem_append_drop_S4`,
  `modalCount_notMem_mono_S4`, `modalWork_drop_linear_S4`, `modalWork_drop_persistent_S4`).
- Phase 4's three landed per-call obligations (`modalApplyOneS4Keyed_branchingLength_S4`,
  `_persistentFresh_S4`, `_outputsSubsetUniverse_S4`) at the three hypothesis positions the
  generic engine's `hBranchingLength`/`hPersistentFresh`/`hOutputsSubsetUniverse` parameters
  expect.
- Phase 8's projection bridge `modalStepBranchS4Keyed_proj_stepBranchGen` (converts the keyed
  4-tuple `hstep` into the generic 3-tuple `modalStepBranchGen` form the transcribed proof body
  needs) and its local `modalExpMeasure_split_S4`/`_append_S4` re-derivations.

`modalExpMeasure_step_lt_S4Keyed`'s hypothesis list replaces the generic template's
`accFreshInv bh acc` + `modalMaxWorld bh < modalWorldBound φ0` pair with `hknown : accTargetsKnown
bh acc`, `hWC : worldsContiguousS4 bh`, `hKT`, `hKD`, `hKI` — the exact extra hypotheses
`modalApplyOneS4Keyed_outputsSubsetUniverse_S4` needs (it derives the strict world bound
internally via `modalStepBranchS4_worldBound`, so no separate raw bound hypothesis is required).
Phase 10 will supply these five from the ambient `S4LoopInv` at each call site, per the plan's
own note that they are "not free."

## Plan Deviations

- **Third private helper re-derived, not enumerated in the plan.** The plan's Phase 8 task list
  named only `modalExpMeasure_split`/`modalExpMeasure_append` (`FmpMeasure.lean:3174`/`3191`) as
  the private upstream helpers needing local re-derivation. The generic engine
  (`modalExpMeasure_step_lt_gen`) also calls a third private helper, `modalExpMeasure_const_exp`
  (`FmpMeasure.lean:3204`), overlooked in that enumeration. Added
  `modalExpMeasure_const_exp_S4` alongside the Phase 9 lemma, by the identical mechanical
  re-derivation pattern Phase 3/8 already established (universe-generic, `simp only` unfold).
  This is a small, low-risk addition, not a design change, and is documented inline in the plan
  and the source docstring.

No other deviations. The lemma's statement, hypothesis shape, and proof structure otherwise match
the plan's Phase 9 task list exactly.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: 847 jobs, exit 0.
- `grep -rn '\bsorry\b' Cslib/`: only pre-existing sorries in unrelated files (Bimodal
  Metalogic, Propositional tableau completeness lines, etc. — none new, none in
  `LoopChecking.lean` beyond the pre-existing docstring-prose mention at `:4619`, which is text,
  not a `sorry` keyword).
- `lean_verify` on both new declarations:
  - `modalExpMeasure_step_lt_S4Keyed`: `propext`, `Classical.choice`, `Quot.sound` only.
  - `modalExpMeasure_const_exp_S4`: `propext`, `Quot.sound` only.
  - Both scans' only `opaque`-pattern hits are at pre-existing lines 897/4667, unrelated to the
    new code.
- `lake exe checkInitImports`: clean (no output, exit 0).
- `lake lint`: 2 errors, both in unrelated files (`CS5Completeness.lean`, `Saturation.lean` under
  `Temporal/Tableau`) touched by other concurrent out-of-scope work; zero hits attributable to
  `LoopChecking.lean`.
- `lake exe lint-style`: zero hits in `LoopChecking.lean`.
- `FmpMeasure.lean` byte-unchanged (read-only per the plan's Non-Goals).
- Frozen `blockingWorldS4Keyed` guard (`LoopChecking.lean:469`) and loop-check guard untouched —
  no need arose to touch it; Phase 9 is guard-independent per the plan's R1 blast-radius item 5.

## Status

Phase 9 `[COMPLETED]`. Phase 10 (`modalExpandBranchesS4Keyed_hintikka`, the top-loop induction)
and Phase 11 (`modalTableauS4Keyed_complete`) remain, per plan `03_completeness-line-rescope.md`.
Not blocked; this dispatch's scope was Phase 9 only and stops here per the per-phase dispatch
contract.
