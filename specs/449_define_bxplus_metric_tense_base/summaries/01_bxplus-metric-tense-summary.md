# Implementation Summary: BX⁺ metric tense base

- **Task**: 449 - define_bxplus_metric_tense_base
- **Status**: [COMPLETED]
- **Started**: 2026-07-24T10:38:37Z
- **Completed**: 2026-07-24T11:15:00Z
- **Effort**: ~35 minutes (4 phases)
- **Dependencies**: None
- **Artifacts**: plans/01_bxplus-metric-tense-plan.md, this summary
- **Standards**: status-markers.md, artifact-management.md, tasks.md, summary-format.md

## Overview

Implemented `BX⁺`, the metric tense logic sound over ordered-abelian-group time, as a new
`FrameClass.Metric` Temporal frame class layered above `Base` (`Base < Metric`, incomparable to
`Dense`/`Discrete`), following the plan's four sequential phases exactly. All four phases
completed green with zero deviations to the core design; two import-only deviations were needed
beyond what the research report anticipated (documented inline in the plan and below). Full
CSLib CI pipeline (cache, build, checkInitImports, lint, lint-style, test) passed clean with
zero sorry, zero vacuous defs, and no new axioms.

## What Changed

- **`Cslib/Logics/Temporal/ProofSystem/Axioms.lean`**: added `FrameClass.Metric` (`Base < Metric`,
  incomparable to `Dense`/`Discrete`) via the `LE` instance; added four axiom constructors
  (`discrete_symm_fwd`, `discrete_symm_bwd`, `discrete_propagate_fwd`, `discrete_propagate_bwd`)
  as a new "Layer: Metric Uniformity" block with house-style docstrings; gated all four in
  `Axiom.minFrameClass` to `.Metric`; updated the module and `FrameClass`/`Axiom` docstrings.
- **`Cslib/Logics/Temporal/Metalogic/Soundness.lean`**: repaired the exhaustive `cases h_ax with`
  in `axiom_sound` with four absurd cases (`.Metric ≰ .Base`).
- **`Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean`**: repaired the exhaustive
  `cases h_ax with` in `axiom_sound_dense` with four absurd cases (`.Metric ≰ .Dense`).
- **`Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean`** (new): four `*_sound` theorems
  proving the metric uniformity axioms valid over ordered-abelian-group time (ported from the
  bimodal `discrete_symm_fwd_valid` … `discrete_propagate_bwd_valid` arithmetic, adapted to
  Temporal's native `Formula.top` and primitive `allFuture`/`allPast`); `axiom_sound_metric`
  assembling all 32 axioms; `swap_valid_of_valid_metric` (via `OrderDual`); `soundness_metric`;
  `soundness_thderivable_metric`; and `Temporal.BXPlusDerivable`, the `BX⁺` derivability
  abbreviation (`@[nolint dupNamespace]`, genuine `Prop` abbreviation, not vacuous).
- **`Cslib/Logics/Temporal/Metalogic.lean`**: added the barrel import for `MetricSoundness`.
- **`Cslib.lean`**: regenerated via `lake exe mk_all --module` (one new import line).

## Decisions

- Followed the plan's exact phase sequence and lemma decomposition with no substitutions; the
  four `*_sound` proofs use the settled `calc`-based arithmetic spine (`sub_lt_self`, `sub_pos`,
  `add_lt_add_left`, `sub_add_cancel`, `add_sub_sub_cancel`, `sub_sub_cancel`,
  `sub_lt_sub_right`) exactly as specified — no `omega`/`aesop` substitution.
- `discrete_propagate_bwd_sound`'s proof body is provably identical in structure to
  `discrete_propagate_fwd_sound` (the immediate-successor witness `u + (s - t)` is independent of
  whether `u` precedes or follows `t`); this is simpler than the bimodal source because
  Temporal's `allPast`/`allFuture` are primitive constructors rather than negation-derived, so no
  double-negation contradiction scaffolding was needed.
- Kept `BXPlusDerivable` in `MetricSoundness.lean` importing `DenseMCS` only for `ThDerivableFc`,
  per the plan's stated preference (not the inline `Nonempty (DerivationTree …)` fallback).
- Added `MetricSoundness` to the `Metalogic.lean` barrel exactly as the plan specifies, even
  though `DenseSoundness` (the structural template) is not itself in that barrel — followed the
  plan literally rather than re-deriving the import topology.

### Plan Deviations

Two deviations, both import-only additions beyond what the research report's verified snippets
implied, annotated inline in the plan:

- **Phase 2** *(altered)*: required an additional `public import Mathlib.Algebra.Order.Group.Defs`
  for the `NoMaxOrder`/`NoMinOrder` auto-synthesis instances (`LinearOrderedAddCommGroup.to_noMaxOrder`
  and its `to_noMinOrder` dual) to resolve under `[AddCommGroup D] [LinearOrder D]
  [IsOrderedAddMonoid D] [Nontrivial D]`. The two imports implied by the research report
  (`Mathlib.Algebra.Order.Group.Unbundled.Basic`, `Mathlib.Algebra.Order.Monoid.Defs`) did not
  carry these instances.
- **Phase 3** *(altered)*: required an additional `public import Mathlib.Algebra.Order.Monoid.OrderDual`
  for the `OrderDual`-transfer instances (`AddCommGroup Dᵒᵈ`, `IsOrderedAddMonoid Dᵒᵈ`) used by
  `swap_valid_of_valid_metric`.

No task step was skipped, altered in substance, or deferred — both deviations are additive import
fixes discovered by the compiler, not changes to the proof design.

## Impacts

- `BX⁺` (`Temporal.BXPlusDerivable`) is now available as a genuine derivability notion sound over
  ordered-abelian-group time, ready for the follow-up conservativity task (`TM` over `BX⁺`,
  explicitly out of scope here per the plan's Non-Goals).
- No existing behavior changed: the work is purely additive (new frame-class constructor, four
  new axioms gated to `.Metric`, one new module); all pre-existing Temporal, Modal, and
  Propositional proofs are unaffected (confirmed by the full green CI run).
- `discrete_box_necessity` (`χ → □χ`) remains explicitly deferred (no pure-temporal form) per the
  plan's Non-Goals.

## Verification

- `lake exe cache get`: cache already warm, no-op.
- `lake build` (full project): green, 3251/3251 jobs.
- `lake exe checkInitImports`: clean (no output, exit 0).
- `lake lint`: `-- Linting passed for Cslib.` (zero warnings).
- `lake exe lint-style`: clean (no output, exit 0).
- `lake test`: exit 0, 9243+ jobs (pre-existing `sorry`s in
  `Cslib/Logics/Propositional/Tableau/{Intuitionistic,Minimal}/*.lean` are unrelated baseline
  debt, not introduced by this task).
- `grep -rn "\bsorry\b" Cslib/Logics/Temporal`: zero actual `sorry` tactic uses (only docstring
  mentions of "sorry-free" in `Tableau/Completeness.lean`, outside this task's territory).
- No new `axiom` declarations; no vacuous `def X := True`-style placeholders.
- `lake shake` (informational, not gated by this plan's Testing & Validation section): the four
  touched files surface only the same pre-existing repo-wide `Cslib.Init`/public-import
  normalization backlog present throughout the codebase — not new debt introduced by this task.

## Follow-ups

- The conservativity theorem (`TM` over `BX⁺`) — deferred to the follow-up task per the plan's
  Non-Goals.
- `discrete_box_necessity` handling — deferred (no pure-temporal form).
- Relocating `DerivFc`/`ThDerivableFc` out of `DenseMCS.lean` to a neutral module — nice-to-have,
  explicitly out of scope.

## References

- specs/449_define_bxplus_metric_tense_base/plans/01_bxplus-metric-tense-plan.md
- specs/449_define_bxplus_metric_tense_base/reports/01_bxplus-metric-tense-survey.md
- Cslib/Logics/Temporal/ProofSystem/Axioms.lean
- Cslib/Logics/Temporal/Metalogic/Soundness.lean
- Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean
- Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean
- Cslib/Logics/Temporal/Metalogic.lean
- Cslib.lean
