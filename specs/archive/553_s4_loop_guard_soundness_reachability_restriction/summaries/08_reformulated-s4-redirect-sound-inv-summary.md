# Implementation Summary: Reformulated S4 Redirect Soundness Invariant

- **Task**: 553 - S4 loop-guard soundness / reachability restriction
- **Status**: [COMPLETED]
- **Started**: 2026-08-05 (this plan version; the task overall spans multiple prior plan
  versions and dispatches)
- **Completed**: 2026-08-05T21:57:00-07:00
- **Effort**: This dispatch: ~3 hours (Phase 9.1 outer induction design + implementation, Phase
  9.2 capstone, Phase 10 CI gate). Whole plan: multiple dispatches across Phases 1-10.
- **Dependencies**: Phases 1-8 (landed in prior dispatches), Phase 9 Scope Decision (recorded in
  the plan file)
- **Artifacts**: `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/08_reformulated-s4-redirect-sound-inv.md`
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The keyed S4 tableau driver's original loop guard (`blockingWorldS4Keyed`) has a genuine
soundness defect: it can redirect an edge to a world whose recorded birth key has gone stale,
asserting semantic accessibility that is not guaranteed by the underlying model. This plan
closes the soundness question for the *ordered* successor driver
(`modalStepBranchS4KeyedOrdered`/`modalExpandBranchesS4KeyedOrdered`/
`modalTableauS4KeyedOrdered`) via a reformulated conserved predicate, `S4RedirectSoundInv`, that
quarantines redirect-created edges from the semantic edge-realization obligation rather than
discharging that obligation directly. This dispatch completed the plan's two remaining
substantive phases (9.1's outer fuel induction and 9.2's end-to-end soundness capstone) plus
Phase 10's regression corpus and full CI gate, landing `modalTableauS4KeyedOrdered_sound`: if the
ordered keyed driver closes on `F(φ₀)@0`, then `φ₀` is genuinely, unweakenedly `s4Valid`.

## What Changed

- **`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`** (+~285 lines for Phase 9.1's
  infrastructure and outer induction, +~35 lines for Phase 9.2's capstone):
  - `S4KOFullInv`: bundles `S4OrderedFuelInv` with an existential `S4RedirectSoundInv` witness at
    one `(b, e, acc, keys)` quadruple.
  - `modalStepBranchS4KeyedOrdered_newExps_eq_map`: structural fact that a stepper output's
    `newExps` column (and, via `List.map_const'`, the replicated `newAcc`/`keys'` columns) is
    constant across `newBs` in every `RuleResult` arm.
  - `zip4`, `Ex4Inv`: a 4-column EXISTENTIAL threading relation ("some one position across the
    four parallel worklists carries an `S4KOFullInv` witness"), built from nested `List.zip`,
    used instead of a universal `List.Forall₂`-style relation. This is the key design pivot from
    the prior dispatch's stalled attempt (see Decisions below).
  - `mem_zip_of_mem_map_const`, `Ex4Inv_of_mem_const`, `zip4_append`, `Ex4Inv_embedLeft`,
    `Ex4Inv_embedRight`, `mem_zip4_proj13`, `zip4_cons_mem_cases`: the small mechanical lemmas
    needed to transport an `Ex4Inv` witness across a step and across list appends.
  - `modalExpandBranchesS4KeyedOrdered_closed_False`: the outer fuel induction. Concludes `False`
    directly (not a per-branch `¬branchSatisfiableIn` fact, unlike the generic
    `modalExpandBranchesGen_closed_unsatIn` it mirrors), since `Ex4Inv` already carries a
    satisfiability witness and a closed branch bearing that witness is an immediate contradiction
    via Phase 8's terminal payoff.
  - `modalTableauS4KeyedOrdered_sound`: the end-to-end capstone. Builds the seed-state
    `S4KOFullInv` witness from an assumed countermodel (`S4RedirectSoundInv_initial` for the
    redirect-sound half, the private `modalTableauS4Keyed_initial` plus `keysOriginS4_entry` for
    the structural half) and feeds the outer induction. Compiled on the first attempt.
  - A `## Scope of modalExpandBranchesS4KeyedOrdered_closed_False` module comment naming what the
    result does and does not say (it does not discharge the standing `sorry`).
- **`CslibTests/S4LoopGuardRegression.lean`** (+17 lines, additive only): imports
  `FrameCompleteness`; adds a permanent type-level regression row (an `example` applying
  `modalTableauS4KeyedOrdered_sound` to the T-axiom control) confirming the capstone's statement
  shape compiles against this file's vocabulary. Every pre-existing `#guard_msgs` row is
  byte-identical.
- **Plan file** (`plans/08_reformulated-s4-redirect-sound-inv.md`): Phase 9.1, 9.2, and 10 marked
  `[COMPLETED]` with per-task deviation/landing annotations.

## Decisions

- **Ex4Inv (existential, 4-column) over a Forall₂-style universal relation**: the prior dispatch's
  Progress Record drafted a zip-triple design bundling `(e, acc, keys)` into one `List.Forall₂`
  relation and stalled on a base-case membership-transport argument. This dispatch instead
  observed that `S4RedirectSoundInv_step`'s own conclusion is already existential (only ONE child
  branch is guaranteed to inherit the invariant across a step, never all of them), so tracking a
  single witness position via an existential relation is both sufficient and strictly easier to
  establish than a universal one. `Ex4Inv` is built from a plain nested `List.zip` (`zip4`)
  rather than a custom inductive relation, reusing Lean/Mathlib's own `List.zip_append`/
  `List.zip_map'` lemmas for the append/transport lemmas.
- **The outer induction concludes `False` directly**, not a per-branch fact. Since the witness
  IS a satisfiability certificate (via `S4RedirectSoundInv`'s conjunct (b)), there is no need to
  carry a preserved conclusion outward through the recursion the way the generic K/S5 proofs do
  (which need a per-branch fact because their conclusion is derived by contradiction from an
  ASSUMED satisfiability, not a held witness).
- **The structural helper fact `modalStepBranchS4KeyedOrdered_newExps_eq_map` avoids needing to
  case-split on which `RuleResult` arm fired** when transporting a witness across a step --
  every arm's `newExps` (and the replicated `newAcc`/`keys'`) is provably a constant map over
  `newBs`.
- **The T-axiom regression row is a type-level, not computational, witness.** `decide`/
  `native_decide`/`rfl` all stall on the fuel driver's `WellFounded.fix` (a pre-existing,
  documented blocker), so the row's hypothesis `h` is an unproved parameter. This is a
  legitimate, cheap regression: it would fail to compile if the capstone's statement shape ever
  drifted, and the adjacent `#eval` control independently confirms the hypothesis is
  non-vacuously satisfiable.
- **A second full-project `lake lint` run, attempted between Phases 9.1 and 9.2, did not
  complete** -- apparently starved by unrelated concurrent `lean`/`lake` processes from another
  project observed running on the same host. This was recorded honestly in the plan rather than
  silently assumed clean; a third attempt after system load settled completed and confirmed zero
  warnings in every file this task touched.

## Impacts

- `modalTableauS4KeyedOrdered_sound` is a new, real, machine-checked soundness result for the
  ordered keyed S4 driver -- the successor driver named in `modalTableauS4KeyedOrdered`'s own
  docstring as needing "a proved soundness/completeness pair of its own" before the old
  `modalTableauS4Keyed`/`modalExpandBranchesS4Keyed` driver can be retired (a future phase, out
  of this plan's scope).
- The standing `sorry` at `FrameSoundness.lean:1251` is untouched: it documents the *unweakened*
  per-step soundness statement this task established is not provable for the keyed guard in
  general (Phase 7.4's verdict). This plan's result is a genuine, different, and complete
  theorem via a reformulated (but at the seed state, undiluted) predicate -- not a discharge of
  the old sorry.
- No axioms beyond `propext, Classical.choice, Quot.sound` were introduced by any new
  declaration (`#print axioms` confirmed for both the outer induction and the capstone).
- Full whole-project CI (build, checkInitImports, lint, lint-style, test, mk_all, shake) is
  green with this task's changes included.

## Follow-ups

- Retiring `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` (the old,
  unordered, known-unsound driver) in favor of the ordered successor now that it has both a
  completeness (`modalTableauS4Keyed_complete`, pre-existing) and soundness
  (`modalTableauS4KeyedOrdered_sound`, this plan) result -- explicitly named as future work in
  `modalTableauS4KeyedOrdered`'s own docstring, out of scope for this plan.
- `instDecidableS4Valid` (wiring `s4Valid`'s `Decidable` instance to the ordered driver) remains
  out of scope until the retirement above happens.
- The report §7 fallback (driver-level provenance / separate redirect-edge accumulator) was never
  needed -- the Terminal Condition's kill gate did not fire at any phase of this plan.

## References

- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/08_reformulated-s4-redirect-sound-inv.md`
  (full phase-by-phase record, including the Phase 9 Scope Decision and Phase 9.1 Progress
  Record documenting the design pivot this dispatch made)
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (all new declarations)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`S4OrderedFuelInv`,
  `modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv`/`_preserves_S4OrderedFuelInv`,
  landed in the prior dispatch)
- `CslibTests/S4LoopGuardRegression.lean` (regression corpus, including the new capstone
  witness row)
