# Implementation Summary: Task #564

- **Task**: 564 - Migrate the S4 Keyed drivers onto the St ladder and retire the duplicated
  `keys'` derivation
- **Status**: Implemented (all 6 phases completed)
- **Plan**: `specs/564_tableau_s4keyed_migration_st_ladder/plans/01_migrate-s4keyed-st-ladder.md`
- **Research**: `specs/564_tableau_s4keyed_migration_st_ladder/reports/01_s4keyed-st-ladder-migration.md`

## Overview

Two structurally independent halves landed sequentially, exactly as planned:

- **Half 1 (Phases 2-3)**: removed `S4LoopInv.outDegEq` and its three orphaned preservation
  lemmas — a pure deletion of already-proved material.
- **Half 2 (Phases 4-5)**: landed the state-threaded S4 Keyed bridge additively onto the
  `RuleApplySt` ladder, giving it its first real consumer, and closed the entry-point story with
  a corollary tying `modalTableauS4Keyed` to `modalExpandBranchesGenSt`.

## Phase-by-Phase Results

| Phase | Description | Result |
|-------|-------------|--------|
| 1 | Re-verify and record the gate baseline | All figures matched the plan's Scope Hypothesis exactly (build green, sorry census 1, shake 9 findings, `LoopChecking.lean` 11761 / `FrameCompleteness.lean` 8266 / `Saturation.lean` 755 lines). |
| 2 | Remove `S4LoopInv.outDegEq` and orphaned lemmas | 438 lines removed (`LoopChecking.lean` -436, `FrameCompleteness.lean` -2). Committed atomic-batch after `lake build Cslib` green. |
| 3 | Update the four field-list docstrings | All 4 stale `outDegEq` prose mentions removed/corrected; field counts fixed (six->five rule-independent fields, ten->nine total). |
| 4 | Land the state-threaded S4 Keyed bridge additively | 5 declarations transcribed from the verified asset (`modalApplyOneS4KeyedSt` + 4 bridge theorems), 157 lines added, strictly additive (no existing declaration modified), EXPERIMENT labels replaced with real prose. |
| 5 | Entry-point corollary and `Saturation.lean` note retirement | Added `modalTableauS4Keyed_eq_modalExpandBranchesGenSt`; retired the stale "separate, later task" note in `Saturation.lean`. |
| 6 | Full CI gate and scope-exclusion record | Full pipeline green; net -256 lines across the three in-scope files. |

## Verification Gate Table (Phase 6, against the Phase 1 baseline)

| Gate | Baseline (Phase 1) | Final (Phase 6) | Status |
|------|--------------------|-------------------|--------|
| `lake build Cslib` | exit 0, 3313 jobs | exit 0, 3313 jobs | green |
| Modal/Tableau sorry census | 1 (`FrameSoundness.lean:1251`) | 1 (`FrameSoundness.lean:1251`) | unchanged |
| `lake exe checkInitImports` | exit 0 | exit 0 | unchanged |
| `lake exe lint-style` | exit 0 | exit 0 | unchanged |
| `lake lint` | not captured (only `lint-style`/`shake` in Phase 1) | 145 findings repo-wide, **zero** in the three touched files | no regression in scope |
| `lake shake --add-public --keep-implied --keep-prefix` | exit 1, 9 findings, none in Modal/Tableau | exit 1, 9 findings (identical file set), none in Modal/Tableau | unchanged |
| `lake test` | not run in Phase 1 | pass, 9378 jobs | green |
| Vacuous definitions | n/a | zero in diff | clean |
| New axioms | n/a | zero | clean |

## Net Line-Count Delta

| File | Baseline | Final | Delta |
|------|----------|-------|-------|
| `Cslib/Logics/Modal/Tableau/LoopChecking.lean` | 11761 | 11500 | -261 |
| `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` | 8266 | 8264 | -2 |
| `Cslib/Logics/Modal/Tableau/Saturation.lean` | 755 | 762 | +7 |
| **Total** | 20782 | 20526 | **-256** |

This is a materially different figure from the plan's ~330-line hypothesis (~437 removed in
Phases 2-3, ~105 added in Phases 4-5). The `outDegEq` removal (Phase 2) still delivered the bulk
of the reduction (438 lines), exactly as the research predicted. Phase 4's bridge transcription
cost more than the terse ~100-line estimate (actual: 157 lines) because real, verbose CSLib-style
prose docstrings replaced the asset's terse `EXPERIMENT 1/1b/2/3` labels — a documentation-quality
cost, not extra code. Reported honestly here rather than restated as the hypothesis, per the
plan's own Scope Hypothesis instruction.

## Plan Deviations

- **Phase 2 lemma boundaries re-located, not blind-trusted**: the plan's line-number estimates for
  the three orphaned lemmas (`modalStepBranchS4_preserves_outDegEq`,
  `modalStepBranchS4KeyedOrdered_preserves_outDegEq`, `modalApplyOneS4KeyedMint_outDeg_step`) were
  pre-Phase-2 estimates and had already shifted by the time of deletion (after the field/obtain
  edits landed first within the same atomic batch). Each was re-located via fresh `grep -n` per
  the plan's own instruction ("the line numbers above are pre-deletion and will have shifted")
  rather than trusted blindly.
- **Phase 4 insertion-point and line-count deviate from the stale pre-Phase-2 estimates**: the
  plan's `:8281`/`:8346` insertion-point line numbers were pre-Phase-2 and had shifted to
  `:7845`/`:7896` by Phase 4 (expected and explicitly anticipated by the plan's own phrasing
  "currently opening at ..., pre-Phase-2 numbering"). The +100-line estimate for the transcribed
  bridge undershot the actual +157 lines, attributable to real-prose docstrings replacing terse
  EXPERIMENT labels (see Net Line-Count Delta above) — not extra code.
- **No other deviations.** All six phases were executed in the plan's exact sequence, with no
  step skipped, altered in substance, or deferred.

## Scope Exclusions (recorded per Phase 6, task 6/6)

1. **KeyedOrdered migration excluded.** Structurally impossible against the current `RuleApplySt`
   ladder: `modalStepBranchGenSt` abstracts over the *rule* passed to it, not over the
   *traversal* it performs, while `modalStepBranchS4KeyedOrdered` is a two-stage traversal whose
   minting gate depends on a global property of the branch `b` that no choice of
   `apply : RuleApplySt Atom σ` can express. **Recommended follow-up**: a new
   stepper-parameterised rung in `Saturation.lean` (research estimate: a ~55-line rung plus two
   ~50-line bridge proofs) would be required to enable this migration.
2. **Destructive redefinition of the bespoke drivers excluded.** Redefining
   `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed` as instantiations of the generic
   `RuleApplySt` machinery was measured (research report) as net **+80 lines** across **40**
   proof sites requiring re-verification, because those sites depend on the definitional *shape*
   of the steppers, not merely their behavior. The plan's Non-Goals explicitly excluded this and
   noted it would require explicit user sign-off not obtainable under autonomous orchestration.

## Artifacts

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — `S4LoopInv.outDegEq` and three orphaned
  lemmas removed; five bridge declarations plus one entry-point corollary added; four docstrings
  updated.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — positional constructor arity reduced by
  one, matching bullet deleted.
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — stale "separate, later task" note retired.
- `specs/564_tableau_s4keyed_migration_st_ladder/plans/01_migrate-s4keyed-st-ladder.md` — all six
  phases marked `[COMPLETED]` with inline verification results.
- This summary.

## Commits

- `a7e7893e` — task 564 phase 1: re-verify and record gate baseline
- `18f1b47d` — task 564 phase 2: remove S4LoopInv.outDegEq and orphaned preservation lemmas
- `7588be95` — task 564 phase 3: update the four field-list docstrings
- `302bf15b` — task 564 phase 4: land the state-threaded S4 Keyed bridge additively
- `6c380e5e` — task 564 phase 5: entry-point corollary and Saturation.lean note retirement
