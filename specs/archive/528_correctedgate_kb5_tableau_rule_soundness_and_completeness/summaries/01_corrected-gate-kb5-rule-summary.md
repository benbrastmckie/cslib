# Implementation Summary: Corrected-Gate KB5 Tableau Rule Soundness and Completeness

- **Task**: 528 - correctedgate_kb5_tableau_rule_soundness_and_completeness
- **Status**: [COMPLETED]
- **Started**: 2026-07-18T00:00:00Z
- **Completed**: 2026-07-18T18:36:00Z
- **Effort**: ~8 sessions across the full 8-phase plan; this session covered Phases 6-8
- **Dependencies**: None outstanding
- **Artifacts**: plans/01_corrected-gate-kb5-rule.md, handoffs/01_*.md, handoffs/02_*.md

## Overview

Delivers full soundness and completeness for KB5 (symmetric right-Euclidean) modal logic via a
corrected-gate full-cluster tableau rule (`modalApplyOneKb5''`), fixing a mathematically genuine
gap in the earlier frozen rule (`modalApplyOneKb5'`, task 524): the self-target propagation arm
fired only when the trigger world was literally the root, when it needed to fire whenever the
known cluster had any non-root member, regardless of trigger identity. This session (continuing a
prior session's Phases 1-5) completed Phase 6 (the Hintikka lift), Phase 7 (completeness +
decidability assembly), and Phase 8 (documentation reconciliation, regression tests, full CI).

## What Changed

- **Phase 6** (`FiveSimplification.lean`, `FrameCompleteness.lean`): `modalApplyOneKb5''_worldGrowth`
  and `modalStepBranchKb5''_preserves_worldInv` (ports `modalApplyOneFive_worldGrowth`/
  `modalStepBranchFive_preserves_worldInv`'s mint-shape cases verbatim; propagation-shape case is
  fresh, resting on `modalApplyOneKb5''Prop_boxPos_diaNeg_eq`). `ModalLoopAuxKb5''` (three-conjunct
  Hintikka-lift `Aux` instantiation: universe-closure + `FiveWorldInvE` + root-known-ness, the
  extra conjunct the corrected gate needs beyond Five's own two), `ModalLoopAuxKb5''_bounds`,
  `ModalLoopAuxKb5''_stepPreserved`, `modalLoopInvHintikkaKb5''_initial`.
- **Phase 7** (`FrameCompleteness.lean`): `modalOpenBranchKb5''_countermodel`,
  `modalTableauKb5''_complete`, `kb5Valid_decides`, `instDecidableKb5Valid` -- mirrors
  `modalTableauFive_complete`'s own assembly.
- **Phase 8**: reconciled three stale docstrings that framed KB5 completeness as
  blocked/open/deferred (`FrameCompleteness.lean`'s "5/KB5 Coverage via the S5 Route" section and
  its frozen-rule blocker note -- kept as documentation, with a new "Resolved" paragraph;
  `FiveSimplification.lean`'s KB5-instantiation update note; `S5Simplification.lean`'s Pure-K5/
  Pure-5 scope note), replacing task-number citations with durable anchors. Extended
  `CslibTests/ModalFrameSeparation.lean` with three regression examples (`inferInstance` on
  `instDecidableKb5Valid`, a trivial `kb5Valid` witness, `modalTableauKb5''_complete` closing the
  tableau concretely) and diagnosed the pre-existing kernel `decide`-reduction stall.

## Decisions

- `FiveWorldInvE`/`expandedRootTagsFive`/`usedTagsFiveNonRoot`/`mintTags` are reused directly (no
  `Kb5''`-named fork) since they are already rule-independent -- minimizes new surface area.
- `modalApplyOneKb5''_worldGrowth`/`modalStepBranchKb5''_preserves_worldInv` live in
  `FiveSimplification.lean` (not `FrameCompleteness.lean`), matching where the analogous private
  helper `modalApplyOneKb5''_outputsSubsetUniverse` they consume is file-scoped.
- `ModalLoopAuxKb5''` bundles root-known-ness as a genuine third conjunct beyond Five's two,
  because `AuxStepPreserved`'s ambient hypotheses (`accFreshInv`/`accTargetsKnown`) do not supply
  it but the corrected propagation gate's Hintikka-step lemma needs it.
- The kernel `decide`-reduction stall (confirmed to persist for `instDecidableKb5Valid`, identical
  to the pre-existing `instDecidableS5Valid`/`instDecidableFiveValid` limitation) is documented,
  not fixed -- out of this task's scope per the plan.

## Impacts

- KB5 (symmetric right-Euclidean) modal logic now has a complete, decidable, sorry-free,
  axiom-free tableau decision procedure (`instDecidableKb5Valid`), matching Five's own delivery.
- The frozen `modalApplyOneKb5'` rule and its own soundness proof are untouched (verified via
  `git diff` at every commit: only additions to pre-existing declarations, never edits).
- `LoopChecking.lean` was not touched (out of scope, separate task).

## Follow-ups

- The pre-existing `unusedArguments` lint findings on `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`
  (landed at an earlier Phase 1 commit, not part of the 7 tracked lint-prevention categories) are
  out of this task's scope; a future lint-fix task could address them.
- The pre-existing `lake shake` import-minimization suggestions across the wider codebase
  (`Propositional/`, `Temporal/`, etc.) are unrelated to this task's touched files and out of scope.
- The kernel `decide`-reduction stall on `modalExpandBranchesGen`'s fuel loop (shared by
  `instDecidableS5Valid`/`instDecidableFiveValid`/`instDecidableKb5Valid`) remains a driver-level
  limitation; a future task could pursue a keyed-stepper or alternate reduction strategy.

## References

- specs/528_correctedgate_kb5_tableau_rule_soundness_and_completeness/plans/01_corrected-gate-kb5-rule.md
- specs/528_correctedgate_kb5_tableau_rule_soundness_and_completeness/handoffs/01_phases-1-4-complete-phase5-continuation.md
- specs/528_correctedgate_kb5_tableau_rule_soundness_and_completeness/handoffs/02_phase5-complete-phase6-continuation.md
- Cslib/Logics/Modal/Tableau/FiveSimplification.lean
- Cslib/Logics/Modal/Tableau/FrameCompleteness.lean
- Cslib/Logics/Modal/Tableau/S5Simplification.lean
- CslibTests/ModalFrameSeparation.lean
