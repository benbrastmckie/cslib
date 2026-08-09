# Implementation Summary: S4 loop-checking machinery, termination bound, and decidability

- **Task**: 506 - s4_loopchecking_machinery_termination_bound_and_decidability
- **Status**: [PARTIAL] (Phases 1-7 [COMPLETED]; Phase 8 [BLOCKED] with mechanical portion
  landed; Phase 9 [BLOCKED], unreachable this run)
- **Started**: 2026-07-14T21:37:15Z
- **Completed**: 2026-07-14T23:23:24Z
- **Effort**: ~19 hours budgeted; full session spent through Phase 8's blocker
- **Dependencies**: None hard for Phases 1-8; Phase 9 additionally gated on task 510
  (which completed all 9 of its own phases during this run, commit `817a5b45`)
- **Artifacts**: plans/01_s4-loopchecking-termination-decidability.md

## Overview

Delivered the S4 (reflexive-transitive) modal tableau system: the 4-rule, equality-blocking
loop-checking machinery, `ReflTransGen` countermodel extraction, S4 soundness, and the
box-positive/diamond-negative truth-lemma bridge (Phases 1-7, the plan's mandatory
"Definition of Done"). Phase 8 (the `2^|Sf|` termination bound) is the acknowledged
high-risk crux; its mechanical scaffolding landed but the core preservation lemma hit a
genuine, well-documented blocker, exercised per the plan's standing `[BLOCKED]` permission
rather than forced with `sorry`. Phase 9 (decidability) is consequently unreachable this run.

## What Changed

- **`Cslib/Logics/Modal/Tableau/FrameRules.lean`** (Phase 1): `modalFourBoxProp`/
  `modalFourDiaNegProp` (box/diamond-itself propagation across a recorded successor edge)
  and `modalApplyOneS4Rules` (wraps `modalApplyOneT`, adding the 4-rule arms), plus the
  `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg` agreement lemma.
- **`Cslib/Logics/Modal/Tableau/LoopChecking.lean`** (new file, Phases 2/5/6/8):
  `formulasAtWorld`, `sameRelevantSet` (the decidable equality-blocking test, with
  reflexivity/symmetry/transitivity and a membership characterization); `blockingWorld`
  (the concrete minting guard); `modalApplyOneS4` (the φ₀-parameterized S4 rule-application
  function -- deviates from a literal plan reading by using `RuleResult.linear []` rather
  than `.persistent []`/`.notApplicable` for the blocked case, since `.notApplicable`
  silently drops the driver's accessibility update and `.persistent []` causes unbounded
  re-selection of the same formula); the S4 driver (`modalStepBranchS4`/
  `modalExpandBranchesS4`/`modalTableauS4`, definitional reuse only, no
  `RuleApplicationSpec` instance); `modalHintikkaSetS4`; the S4 Hintikka bridges
  (`hintikkaS4_box_pos_step`/`_self`, `hintikkaS4_dia_neg_step`/`_self`,
  `hintikkaS4_box_neg`, `hintikkaS4_diamond_pos`) and the crux `ReflTransGen` path bridges
  (`hintikkaS4_box_pos_reflTransGen`/`hintikkaS4_dia_neg_reflTransGen`); and (Phase 8)
  `modalWorldBoundS4`, `modalUniverseS4` + `modalUniverseS4_length_le`, and the
  `S4LoopInv` structure.
- **`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`** (Phases 3/7): `extractModelS4`
  (instantiated at `Relation.ReflTransGen`) with free `Std.Refl`/`IsTrans` instances and
  `extractModelS4_hasEdge_imp_r`; `modalTruthLemmaS4` (a new induction, not a reuse of
  `modalTruthLemma`, since the model's relation differs) and
  `modalOpenBranchS4_countermodel`. Required a new private lemma
  `modalApplyOneS4_eq_of_not_modal_shaped` and two additional imports
  (`LoopChecking.lean`, `FrameSoundness.lean`).
- **`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`** (Phase 4): `s4FC`, `s4Valid`, and
  4-rule semantic soundness (`branchSatisfiableIn_s4FC_boxPos_trans_mem`/
  `_diaNeg_trans_mem`, `modalFourBoxProp_sound`/`modalFourDiaNegProp_sound`), proved
  directly from `IsTrans.trans` per Correction 2 (not via `Satisfies.four`).
- **`Cslib.lean`**: barrel entry for `LoopChecking` (auto-placed alphabetically between
  `GenericDriver` and `LoopInduction`).

## Decisions

- Followed all three "Corrections to the Task Description" from the plan: sibling
  `S4LoopInv` (not an extension of `ModalPotentialInv`); 4-rule soundness from
  `IsTrans.trans` directly (not `Satisfies.four`); no `RuleApplicationSpec` instance for S4.
- Sanity-checked `modalTableauS4` interactively (`lean_run_code`/`#eval`): `□p → p` closes
  (T), `□p → □□p` closes (4, confirming the entire point of this task), bare `p` stays
  open. Not embedded as permanent `#eval`/`#guard`/`native_decide` declarations -- all three
  forms fail to compile in this file's `module`/`public import` configuration (verified;
  no precedent file in `Cslib/Logics/Modal/Tableau/` uses any of them either).
- Verified via careful re-derivation (per the orchestrator's mid-run correction) that
  `hintikka_box_neg`/`hintikka_diamond_pos` are pure structural projections but
  `hintikka_box_pos`/`hintikka_diamond_neg` require genuinely new proofs unfolding
  `modalApplyOne` concretely; the S4 analogues needed one additional unfolding layer
  (`modalApplyOneS4` → `modalApplyOneS4Rules` → `modalApplyOneT` → `modalApplyOne`),
  resolved via chained equation lemmas and a generic "append-then-filter" membership
  helper that avoids needing to know the K/T layers' exact list contents.
- Phase 8 blocker: exercised the plan's standing permission to mark `[BLOCKED]` rather than
  force a `sorry`-backed or scope-reduced proof. Full detail in the plan file's Phase 8
  "BLOCKER" note; short version: `worldSetsDistinct` is not, as currently designed, an
  actual per-step loop invariant of `modalStepBranchS4` -- persistent rule firings can
  change an existing world's relevant set without re-checking distinctness (the plan's own
  anticipated hard sub-goal, confirmed real), and the minting guard checks the *source*
  world's uniqueness rather than the *freshly-minted world's own prospective content*, so a
  new world is not guaranteed distinct from existing ones at birth either.

## Impacts

- Phases 1-7 are independently valuable and are the plan's mandatory "Definition of Done" --
  they are complete, green, and committed. No existing K, T, or (per task 510's concurrent
  work) generalized-chain declaration was modified.
- `FmpMeasure.lean` diff is empty across the whole task, as required.
- No `RuleApplicationSpec` instance exists for any S4 `apply`, as required.
- Task 510 (`generalize_completeness_loop_hintikka_chain_over_spec`) completed all 9 of its
  own phases during this run (commit `817a5b45`). This does not by itself unblock Phase 9,
  which is gated on Phase 8's bound closing first, and its own generalized-predicate
  requirement (`modalHintikkaSetGen`, not `modalHintikkaSet`) was not verified this run.

## Follow-ups

- Create task **`s4-loop-checking-termination`**, scoped to: redesign the minting guard
  (check the prospective new world's content, not just the source's) and/or restate
  `S4LoopInv` over a saturation-stable notion; then `worldSetsDistinct` preservation, the
  pigeonhole bound (`Finset.card_powerset`/`Finset.card_le_card_of_injOn` are the likely
  Mathlib anchors), and `modalStepBranchS4_worldBound`. Should start from
  `modalApplyOneS4`'s definition (`LoopChecking.lean`) and the Phase 8 BLOCKER note.
- Once Phase 8 closes, re-attempt Phase 9, first verifying task 510's generalized loop
  lemma concludes in `modalHintikkaSetGen apply bR aR` (not `modalHintikkaSet bR aR`) before
  attempting `modalExpandBranchesS4_hintikka`.

## References

- specs/506_s4_loopchecking_machinery_termination_bound_and_decidability/plans/01_s4-loopchecking-termination-decidability.md
- Cslib/Logics/Modal/Tableau/FrameRules.lean
- Cslib/Logics/Modal/Tableau/LoopChecking.lean
- Cslib/Logics/Modal/Tableau/FrameCompleteness.lean
- Cslib/Logics/Modal/Tableau/FrameSoundness.lean
