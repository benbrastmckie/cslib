# Handoff 15: Phase 21 PARTIAL -- `accTargetsNeRoot` pair landed; `FiveWorldInv` wall blocks the rest

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 21 (`modalTableauFive_complete` + `Decidable (fiveValid φ)`) -- now `[PARTIAL]`
**Commit landed this dispatch**: `720088c9` (`task 515 phase 21.1: land accTargetsNeRoot
top-loop preservation pair`)

## What landed this dispatch

Resumed from `handoffs/14_phase20-completed-ready-for-21.md`. Landed the `accTargetsNeRoot`
top-loop preservation pair this dispatch's orchestrator instruction flagged as real new scope --
see `summaries/15_phase21-accTargetsNeRoot-landed-wall-blocked.md` for the full
declaration-by-declaration account. In brief, `FrameCompleteness.lean` gained:
`hasEdge_addEdge_cases_Five`, `modalNextWorld_ne_zero_Five` (private helpers),
`modalApplyOneFive_edge_target_ne_root`, `modalStepBranchFive_preserves_accTargetsNeRoot`,
`modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot`,
`modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot`. Full CI-relevant checks green:
scoped + full `lake build` (3240/3240), `checkInitImports` exit 0, `lint`/`lint-style` clean for
the touched file, zero `sorry`, axioms `[propext, Classical.choice, Quot.sound]` only on every new
public declaration (confirmed via `lake env lean` + `#print axioms`, not `lean_verify` alone).

## Blocker discovered this dispatch (beyond the orchestrator's stated new-scope item)

The orchestrator's dispatch instruction described only the `accTargetsNeRoot` pair as new scope.
Investigation this dispatch surfaced a **second, larger, pre-existing gap** blocking the
remaining three Phase 21 task bullets (`modalTableauFive_complete`, `instDecidableFiveValid`, the
non-derivability probe): `modalTableauFive_complete` needs a `ModalLoopAuxFive` (Five's analogue
of S5's `ModalLoopAuxS5w`) to supply the Hintikka "wall" via `modalExpandBranchesHintikka`
(`CompletenessLoop.lean`). Building `ModalLoopAuxFive_stepPreserved` requires the **inductive
step-preservation proof for `FiveWorldInv`** across the fuel-driven expansion --
`FiveSimplification.lean`'s own docstring (lines 1424-1431) already flags this as NOT YET BUILT,
explicitly deferred as "Phase 19b-scale work." `grep` confirms `FiveWorldInv` and
`modalMaxWorld_lt_worldBound_of_FiveWorldInv` have zero consumers before this dispatch.

A faithful port of S5w's own analogous machinery (`modalApplyOneS5w_step`, ~230 lines;
`modalStepBranchS5w_preserves_worldInv`, ~100 lines; several supporting private lemmas -- all
read in full this dispatch) would need the same case analysis, doubled by `FiveWorldInv`'s
root/non-root source-class split. The K-rank shortcut (`ModalLoopAuxK`) is confirmed unavailable:
Five's propagation shapes share S5's `rankStep`-defeating structure (the mechanized counterexample
in `S5Simplification.lean`'s "Phase 2 Obstruction" section), which is why the witness-counting
`FiveWorldInv` route was built at all.

This is comparable in scale to Phase 19b itself and was judged beyond what could be responsibly
attempted -- without risking an under-verified, rushed multi-hundred-line proof -- within this
dispatch's remaining budget, per the KILL BUDGET instruction. The plan file's Phase 21 section now
records the full diagnosis and a concrete four-step recipe for the follow-up phase (see "BLOCKER"
note there).

## Resume point for the next dispatch

1. **Do NOT re-derive** any of: `accSourcesKnown`/`accTargetsKnown`/`accTargetsNeRoot`'s top-loop
   lemmas (all landed, this dispatch + Phase 20), `modalTruthLemmaFive`/
   `modalOpenBranchFive_countermodel` (Phase 20), `modalTableauFive_sound` (Phase 19b), or
   `FiveWorldInv`/`usedTagsFiveNonRoot`/`usedTagsFiveRoot`/
   `modalMaxWorld_lt_worldBound_of_FiveWorldInv` (landed earlier, still unconsumed).
2. **The real remaining work** is building, in `FrameCompleteness.lean` or `FiveSimplification.lean`
   (matching where `FiveWorldInv` already lives):
   - `modalApplyOneFive_step` (mirrors `modalApplyOneS5w_step`, `S5Simplification.lean:1307`,
     doubled for root/non-root at the two mint shapes against `usedTagsFiveNonRoot`/
     `usedTagsFiveRoot` instead of a single `usedTags`).
   - `modalStepBranchFive_preserves_worldInv` (mirrors
     `modalStepBranchS5w_preserves_worldInv`, `S5Simplification.lean:1697`), assembling the above
     into single-step preservation of `S5wTagInv φ₀ b ∧ FiveWorldInv φ₀ b`.
   - `ModalLoopAuxFive`, `ModalLoopAuxFive_bounds` (trivial via the already-landed
     `modalMaxWorld_lt_worldBound_of_FiveWorldInv`), `ModalLoopAuxFive_stepPreserved`,
     `modalLoopInvHintikkaFive_initial` (mirrors `modalLoopInvHintikkaS5w_initial`,
     `CompletenessLoop.lean:412`).
   - Then `modalTableauFive_complete` and `instDecidableFiveValid`, assembled exactly as
     `modalTableauS5_complete`/`instDecidableS5Valid` are (`FrameCompleteness.lean:2330`/`2412`),
     now with all four ingredients available.
3. **Budget this generously** -- re-cost at Phase 19b's own historical scale (multiple dispatches
   across several commits), not the plan's stated "3 hours."
4. The `hintikka_congr` plan task item is **moot** (investigated this dispatch): `modalTableauFive`
   already runs `modalApplyOneFive` directly, no bridging needed. Do not re-investigate.
5. Resolve every declaration by name (`lean_local_search`/`lean_declaration_file`/grep), not by
   plan line-number citations.
6. Do NOT touch `S5Simplification.lean`'s shared `S5w*` declarations (this dispatch did not;
   `S5wTagInv` itself is reused verbatim by Five's own route, consistent with the existing
   design, but its *lemmas about it* stay untouched).
7. When staging the plan file, `git diff` it first and use `git add -p` (hunk-scoped) -- the
   Phase 22/23 headings still carry a stray, pre-existing, uncommitted `[IN PROGRESS]` marker
   from an unrelated/concurrent source, left untouched again this dispatch.
8. Do NOT start Phases 22-23 before Phase 21 fully completes.

## Files touched this dispatch

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`
  (Phase 21 heading + checklist + BLOCKER note, hunk-scoped)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/summaries/15_phase21-accTargetsNeRoot-landed-wall-blocked.md`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/handoffs/15_phase21-partial-fiveworldinv-wall-blocked.md`
  (this file)
