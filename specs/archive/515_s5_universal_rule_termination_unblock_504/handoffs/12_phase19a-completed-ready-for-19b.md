# Handoff 12: Phase 19a COMPLETED; Phase 19b ready to begin

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 19a (`Guarded mint arm + termination bound re-derivation`) -- now `[COMPLETED]`
**Commits landed this dispatch**: `2c7abe73` (`task 515 phase 19a.2: land source-split
termination-bound re-derivation`), `c3d6c608` (plan marker update)

## What landed this dispatch

Resumed from `handoffs/11_phase19a-mint-arm-guard-landed-termination-open.md`. The mint-arm guard
(`56a84d07`) was already landed and was NOT re-touched. This dispatch closed Phase 19a's second
(previously unattempted) task: the source-split termination-bound re-derivation.

See `summaries/12_phase19a-termination-bound-landed.md` for the full declaration-by-declaration
account. In brief, all additive in `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`:

- `usedTagsFiveNonRoot`/`usedTagsFiveRoot` (+ monotonicity lemmas): source-split `usedTags`
  analogues, Finset filters of the reused-verbatim `mintTags φ₀`.
- `witnessWorldFive_none_not_mem_usedTagsFiveNonRoot`: non-root reuse-miss case.
- `diamondPos_root_mem_usedTagsFiveRoot`/`boxNeg_root_mem_usedTagsFiveRoot`: root-trigger-always-
  fresh case (unconditional, witnessed by the trigger's own branch presence).
- `FiveWorldInv`: source-split `S5wWorldInv` (sum of both source-class tag counts).
- `two_mul_modalOps_lt_worldBound` + `modalMaxWorld_lt_worldBound_of_FiveWorldInv`: the final
  arithmetic chain, `modalMaxWorld b < modalWorldBound φ₀` at the larger-but-linear `2·modalOps φ₀`
  constant, matching `outputsSubsetUniverse`'s `hW` hypothesis shape.

`mintTags`/`S5wTagInv` (and their tag-membership corollaries) are reused **verbatim** from
`S5Simplification.lean` (now `public import`ed) -- genuinely rule-independent, so no Five-local
redefinition was needed or performed. `S5Simplification.lean` itself was NOT edited.

Full CI green (scoped + full `lake build` 3240/3240, `checkInitImports`, `lint-style`, full-repo
`lake lint`/`lake shake` with zero new warnings/suggestions attributable to this file, `lake test`,
zero `sorry`, axioms confirmed via `lake env lean` + `#print axioms` as `[propext,
Classical.choice, Quot.sound]` only on every new declaration).

## Scope note carried forward (not a blocker -- intentional deferral)

This dispatch lands the *static* source-split structures and the final arithmetic bound only,
mirroring how `S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w` themselves work (taking the
world-bound invariant as a hypothesis, not proving it holds at every reachable branch inline).
**Not yet done, and NOT required by this dispatch's scope**: the inductive step-preservation proof
that `FiveWorldInv` actually holds across the whole fuel-driven expansion (the source-split
analogue of `S5wTagInv_S5wWorldInv_step`, `S5Simplification.lean`). This is explicitly Phase
19b-scale work per the plan's own sizing and the continuation handoff's task breakdown (which
listed exactly the three tasks this dispatch completed, not a fourth step-induction task).

For whoever picks up Phase 19b: `modalApplyOneFive_specCore`'s `outputsSubsetUniverse` field takes
`hW : modalMaxWorld b < modalWorldBound φ0` as a raw hypothesis parameter -- it does not derive it
from `FiveWorldInv`, and no site in `FiveSimplification.lean` currently discharges `hW` via this
chain (same situation as handoff 11 described before this dispatch, now with the source-split
bound available to actually supply that `hW` once the step-induction is built). Building that
step-induction will need to case-split `modalApplyOneFive`'s four shapes (via
`modalApplyOneFive_agree_or_reuse`/`modalApplyOneFive_diaPos_eq_or_reuse`/
`_boxNeg_eq_or_reuse`, all already landed) and track how `usedTagsFiveNonRoot`/`usedTagsFiveRoot`
grow across each step -- likely also needing to thread the driver's `expanded` list (from
`modalStepBranchGen`, `Saturation.lean`) for the root-mint case, since (per this dispatch's own
design-time analysis) the root-trigger-always-fresh case's "fires at most once per trigger
occurrence" guarantee comes from the driver's `.linear`-result `expanded` memoization
(`modalStepBranchGen`'s `if expanded.any (· == sf) then none else ...` guard), not from any
branch-content-only argument -- this is a genuinely new piece of infrastructure the S5 chain never
needed (since `modalApplyOneS5w`'s mint arms always consult `witnessWorldS5` before minting, so
its argument never needed `expanded` at all).

## Resume point for Phase 19b

1. Read `plans/07_s5-termination-machinery.md`'s Phase 19b section (`modalTableauFive_sound`
   bespoke assembly, "Depends on: 19a" -- now satisfied) before writing any code.
2. The soundness assembly can proceed using the landed Route-1 propagation fix, the five
   soundness/structural building-block lemmas (`modalApplyOneFiveProp_knownWorlds_step`,
   `modalApplyOneFive_agree_or_reuse`, `modalStepBranchFive_preserves_accReachableInv`,
   `FiveSoundInv`, `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`), and the mint-arm guard
   -- all landed and green, per handoff 10/11's own accounting, unaffected by this dispatch.
3. If/when the fuel-induction assembly needs `modalMaxWorld b < modalWorldBound φ0`, the new
   `FiveWorldInv`/`modalMaxWorld_lt_worldBound_of_FiveWorldInv` (this dispatch) supply the target
   type; establishing `FiveWorldInv` itself as an inductive invariant across the induction is the
   work noted above.
4. Resolve every declaration by name (`lean_local_search`/`lean_declaration_file`/grep), not by
   plan line-number citations.
5. Do not touch `S5Simplification.lean`'s shared `S5w*` declarations; if truly unavoidable, stop
   and escalate.

## Files touched this dispatch

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/summaries/12_phase19a-termination-bound-landed.md`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/handoffs/12_phase19a-completed-ready-for-19b.md` (this file)
