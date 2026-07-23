# Summary 15: Phase 21 partial -- `accTargetsNeRoot` top-loop pair landed; `modalTableauFive_complete` blocked on `FiveWorldInv` step-preservation

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 21 (`modalTableauFive_complete` + `Decidable (fiveValid φ)`) -- now `[PARTIAL]`
**Commit landed this dispatch**: `720088c9` (`task 515 phase 21.1: land accTargetsNeRoot
top-loop preservation pair`)

## What landed this dispatch

Resumed from `handoffs/14_phase20-completed-ready-for-21.md` (Phase 20 -- `extractModelFive` +
the Euclidean truth lemma -- fully `[COMPLETED]`; not re-touched). This dispatch's explicit new
scope item was the `accTargetsNeRoot` top-loop preservation pair, mirroring
`modalStepBranch_preserves_accTargetsKnown_gen` + `modalExpandBranchesGen_openBranch_accTargetsKnown`
(`BDriver.lean`/`FmpMeasure.lean`).

### `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (additive)

- `hasEdge_addEdge_cases_Five` (private, local re-derivation of `Soundness.lean`'s
  `hasEdge_addEdge_cases`, unavailable across files).
- `modalNextWorld_ne_zero_Five` (private): a fresh world is never the root, since
  `WorldIndex := Nat` makes `modalNextWorld b = modalMaxWorld b + 1 ≥ 1` unconditionally
  (`Nat.succ_ne_zero`).
- `modalApplyOneFive_edge_target_ne_root`: the per-call root-isolation fact -- whenever
  `modalApplyOneFive` records a new accessibility edge, its target is non-root. Combines Phase
  19b's `modalApplyOneFive_agree_or_reuse_ne_root` (a reuse edge's target is already known
  non-root) with `FiveSimplification.lean`'s existing `modalApplyOneFiveProp_knownWorlds_step`
  (a genuine mint edge's target is `modalNextWorld b`, non-root per the helper above).
- `modalStepBranchFive_preserves_accTargetsNeRoot`: single-step preservation, given
  `accTargetsKnown b acc` as an ambient hypothesis (needed by
  `modalApplyOneFiveProp_knownWorlds_step`'s own signature).
- `modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot` +
  `modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot`: the joint single-step/top-loop
  pair, bundling `accTargetsKnown` and `accTargetsNeRoot` together as one invariant threaded
  through `modalExpandBranchesGen_openBranch_gen`'s generic induction (`BDriver.lean`), since
  `accTargetsNeRoot`'s own single-step preservation needs `accTargetsKnown` as an ambient
  invariant maintained *across the same induction*, not just at the final branch -- the identical
  "necessary THIRD hypothesis beyond the plan's literal signature" pattern
  `S5Simplification.lean`'s `modalStepBranchS5w_preserves_worldInv` documents for `S5wWorldInv`.

This fully discharges Phase 20's `accTargetsNeRoot` abstract hypothesis for a real
`modalTableauFive`/`modalExpandBranchesFive` run, alongside the existing
`accSourcesKnown`/`accTargetsKnown` top-loop lemmas already available at `modalApplyOneFive`
(via the generic `modalApplyOneFive_fresh_local`).

**Verification**: scoped build (`Cslib.Logics.Modal.Tableau.FrameCompleteness`) green; full
`lake build` 3240/3240 green; `lake exe checkInitImports` exit 0; `lake lint` zero hits in the
touched file; `lake exe lint-style` clean; zero `sorry` in the touched file; axioms confirmed via
`lake env lean` + `#print axioms` on all new public declarations:
`[propext, Classical.choice, Quot.sound]` only -- no `sorryAx`, no new custom axiom (repo-wide
axiom count unchanged at 28, all pre-existing baseline).

## Investigation finding: the `hintikka_congr` task item is moot

The plan's second Phase 21 task bullet asks whether a `hintikka_congr` analogue is needed for
Five, mirroring S5's bridge between `modalApplyOneS5w`'s Hintikka set and `modalApplyOneS5`'s.
Investigation this dispatch confirms **no bridging is needed at all**: unlike S5 (whose tableau
runs the terminating `modalApplyOneS5w` but whose countermodel needs a
`modalHintikkaSetGen modalApplyOneS5` witness), `modalTableauFive` already runs
`modalApplyOneFive` directly -- Five ships only the one rule -- and
`modalOpenBranchFive_countermodel` already takes `modalHintikkaSetGen modalApplyOneFive b acc`
directly as its `hH` hypothesis (landed Phase 20). This task item is marked moot in the plan.

## Blocker: `modalTableauFive_complete` / `instDecidableFiveValid` remain unimplemented

The plan's remaining three Phase 21 task bullets (`modalTableauFive_complete`,
`instDecidableFiveValid`, and the `s5Valid`-non-derivability probe) are blocked on a **separate,
larger, previously-deferred gap**: `modalTableauFive_complete`'s fourth ingredient -- the Hintikka
"wall" `modalHintikkaSetGen modalApplyOneFive b a` at a real open branch -- needs
`modalExpandBranchesHintikka` (`CompletenessLoop.lean`) instantiated at a bespoke
`Aux := ModalLoopAuxFive φ0` (Five's analogue of S5's `ModalLoopAuxS5w`). Building this Aux
requires the **inductive step-preservation proof for `FiveWorldInv`** across the fuel-driven
expansion, which `FiveSimplification.lean`'s own docstring (lines 1424-1431, written when
`FiveWorldInv` was landed) explicitly flags as NOT YET BUILT: *"the inductive step-preservation
proof establishing `FiveWorldInv` holds across the whole fuel-driven expansion ... is Phase
19b-scale work, for whatever call site eventually maintains it."* This dispatch confirms `grep`
still finds zero consumers of `FiveWorldInv`/`modalMaxWorld_lt_worldBound_of_FiveWorldInv` before
this investigation -- a real, pre-existing gap, not a regression introduced here.

Investigation ruled out a shortcut: the K-rank route (`ModalLoopAuxK`, generic over any
`RuleApplicationSpec`-satisfying rule) is unavailable, since Five's box-positive/diamond-negative
propagation shapes share S5's universal rule's `rankStep`-defeating shape (the documented,
mechanized `RuleApplicationSpec.rankStep` counterexample in `S5Simplification.lean`'s "Phase 2
Obstruction" section) -- precisely why the witness-counting `FiveWorldInv` route was built in the
first place.

A faithful Five analogue of S5w's own machinery (`modalApplyOneS5w_step`, ~230 lines, plus
`modalStepBranchS5w_preserves_worldInv`, ~100 lines, plus supporting private lemmas -- all read
in full this dispatch) would need the same case-work, doubled by `FiveWorldInv`'s root/non-root
source-class split (`usedTagsFiveNonRoot` vs. `usedTagsFiveRoot`). This is comparable in scale to
Phase 19b itself and beyond what could be responsibly attempted without risking a rushed,
under-verified proof in this dispatch's remaining budget. The plan file records the full
diagnosis and a concrete four-step recipe for the follow-up phase under Phase 21's "BLOCKER"
note.

## Plan Deviations

- Task 1 (the `accTargetsNeRoot` pair) is an **added** item, not one of the plan's original four
  Phase 21 bullets -- this dispatch's orchestrator-level instruction flagged it as real, budgeted
  new scope. Marked `[x]` with a `(deviation: added ...)` annotation.
- Tasks 2-4 (the original `modalTableauFive_complete`, `hintikka_congr` check,
  `instDecidableFiveValid`, and the non-derivability probe) are marked `(deviation: blocked --
  see note below)`, with the full diagnosis in the plan's new "BLOCKER" section. Task 2 (the
  `hintikka_congr` check) is additionally noted as investigated-and-moot, not merely deferred.
- Phase 21's heading is `[PARTIAL]`, not `[COMPLETED]` or `[BLOCKED]` outright: real, additive,
  verified progress landed (the `accTargetsNeRoot` pair), but the phase's primary deliverable
  (`modalTableauFive_complete`/decidability) remains unimplemented pending the follow-up phase.

## Files touched this dispatch

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`
  (Phase 21 heading + checklist + new BLOCKER note only, hunk-scoped)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/summaries/15_phase21-accTargetsNeRoot-landed-wall-blocked.md`
  (this file)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/handoffs/15_phase21-partial-fiveworldinv-wall-blocked.md`
  (handoff)

## Procedural note

The plan file's Phase 22/23 headings still show a pre-existing, uncommitted `[NOT STARTED]` ->
`[IN PROGRESS]` marker-only edit in the working tree (present before this dispatch started,
unrelated to any work performed here -- same stray edit `handoffs/14` already documented). This
dispatch again used `git add -p` (hunk-scoped) to stage only its own two Phase 21 hunks, leaving
the Phase 22/23 markers unstaged and untouched. No Phase 22/23 work was performed or claimed.
