# Task 511 Phase 5+6 — Dispatch 7 Handoff: `S4LoopInv` Fully Sorry-Free, Phase 6 Closed

## Summary

Landed Phase 6's pigeonhole world-bound lemmas and used them to discharge both of Phase 5's
remaining strategic sorries (`bClosure`, `eClosure`), fully closing
`modalStepBranchS4_preserves_S4LoopInv` — **all 10 `S4LoopInv` fields are now proven, zero
sorry, zero new axiom**.

## Key Correction: `eClosure` vs `bClosure` Analysis

The prior dispatch's continuation note mis-attributed the T-self/4-propagation formula-subset
composite to `eClosure`. Re-reading `modalStepBranchS4Keyed`'s definition shows `newExps` is
`e ++ [sf]` (or `e` unchanged for `.persistent`) — it only ever gains the *selected* formula
`sf` (already `∈ b`, hence covered directly by `hb`), never the rule's output content. The
output content (`newForms`) goes to `newBs`, which is `bClosure`'s concern.

This means:
- **`eClosure`** closed immediately, via the same case-split shape as the already-landed
  `modalStepBranchS4_preserves_eNodup`.
- **`bClosure`** needed the substantial T-self/4-propagation formula-subset composite (the one
  originally mis-assigned to `eClosure`) for its 12 non-minting shapes, plus Phase 6's own
  pigeonhole world-bound as a genuine prerequisite for its 2 minting shapes.

## What's Closed This Dispatch

**Universe-membership groundwork** (mirrors `FmpMeasure.lean`'s K-level facts, retargeted to
`modalUniverseS4`/`modalWorldBoundS4`):
- `mem_modalUniverseS4_of`/`mem_modalUniverseS4_of'`, `modalUniverseS4_mem_label`.
- `mem_boxPositivesOf_S4`, `boxProps_outputs_subset_S4`, `diaNegProps_outputs_subset_S4`.
- `modalApplyOne_boxNeg_outputs_subset_S4`/`modalApplyOne_diamondPos_outputs_subset_S4` (mint
  content lands in `modalUniverseS4 φ₀`, given the STRICT `modalMaxWorld b < modalWorldBoundS4
  φ₀` bound).

**Non-minting universe-membership composite** (mirrors the existing "known-worlds" composite's
exact case-split shape, concluding full `modalUniverseS4 φ₀` membership instead of only
`modalKnownWorlds b`):
- `modalApplyOne_boxPos_fst_S4`/`_snd_S4`, `modalApplyOne_diamondNeg_fst_S4`/`_snd_S4` (direct
  unfoldings, bypassing the abstract `modalApplyOne_boxPos_eq`/`modalApplyOne_knownWorlds_step`
  whose persistent payload is deliberately existentially-quantified and carries no formula
  content).
- `modalApplyOneT_boxPos_diaNeg_universe_S4`, `modalApplyOneS4Rules_boxPos_diaNeg_universe_S4`,
  `modalApplyOne_nonModal_universe_S4`, `modalApplyOneS4Keyed_nonMint_universe_S4`.

**`modalStepBranchS4_preserves_eClosure`** — CLOSED, zero sorry.

**Phase 6 pigeonhole lemmas**:
- `worldsContiguousS4` — a **new proof-internal auxiliary invariant**
  (`∀ w ≤ modalMaxWorld b, w ∈ modalKnownWorlds b`; deliberately NOT an `S4LoopInv` field,
  mirrors the `keysWorldsKnown` precedent from the prior dispatch, threaded as an extra
  hypothesis/conclusion) plus its preservation lemma
  `modalStepBranchS4_preserves_worldsContiguousS4`. Needed because density of world labels does
  not otherwise follow from `S4LoopInv`'s existing fields — this was not fully anticipated in
  the plan's original Phase 6 task wording ("a small dense-labels fact from consecutive
  minting") but turned out to require this genuine extension of the threading pattern.
- `modalKnownWorlds_nodup_S4`, `modalKnownWorlds_length_le_worldBoundS4` (the pigeonhole
  cardinality bound, via `Classical.choice` to extract a canonical key per known world,
  `Finset.card_le_card_of_injOn`).
- `modalStepBranchS4_worldBound : modalMaxWorld b < modalWorldBoundS4 φ₀` — the deliverable that
  closes the original task 506 Phase 8.

**`modalStepBranchS4_preserves_bClosure`** — CLOSED, zero sorry, using the composite +
`modalStepBranchS4_worldBound`.

**`modalStepBranchS4_preserves_S4LoopInv`** — now threads `worldsContiguousS4` alongside
`keysWorldsKnown` (extra hypothesis in, extra conclusion out as a third conjunct) so a Phase 7
continuation dispatch can re-supply both across repeated steps.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green throughout, 5 incremental commits.
- Zero `sorry` in the file (confirmed via grep on non-comment lines and the build log's absence
  of any `declaration uses 'sorry'` warning).
- `lean_verify` on `modalStepBranchS4_preserves_S4LoopInv`, `modalStepBranchS4_preserves_bClosure`,
  `modalStepBranchS4_preserves_eClosure`, `modalStepBranchS4_worldBound`,
  `modalKnownWorlds_length_le_worldBoundS4`, `modalStepBranchS4_preserves_worldsContiguousS4`:
  all report `propext`/`Classical.choice`/`Quot.sound` only, no `sorryAx`.
- `lake exe checkInitImports` and `lake exe lint-style` clean.
- Full-project `lake build`/`lake test` NOT run this dispatch (dispatch instructions explicitly
  scoped verification to `Cslib.Logics.Modal.Tableau.LoopChecking`; concurrent task 517/530/531
  sessions have uncommitted edits to unrelated files that would surface as unrelated
  full-project failures).

## Files Modified

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md` (Phase
  5/6 marked `[COMPLETED]`, stale continuation narrative trimmed to closure summaries)

## Next Steps (Phase 7, not started this dispatch)

Phase 7 (Phase 9 decidability): the Hintikka-alignment bridge `modalHintikkaSetS4_eq` is already
landed (independent, prior dispatch). Remaining tasks:
1. Record Planner Decision 2 (recommend spawning the abstract termination-measure interface,
   9-A, as a separate task rather than inlining it in `CompletenessLoop.lean`, shared with tasks
   505/513).
2. Wire fuel sufficiency from `modalStepBranchS4_worldBound` (now available) plus the 9-A/9-B
   decision to derive `Decidable (s4Valid φ)` against `Cube.S4`.
3. Otherwise mark `[BLOCKED]` with the exact open goal state and the spawned task number.

`modalStepBranchS4_preserves_S4LoopInv` is now the fully-closed loop invariant a Phase 7
induction over repeated `modalStepBranchS4Keyed` calls can consume directly, re-supplying
`worldsContiguousS4`/`keysWorldsKnown` at each step from the assembly theorem's own
third/second conjuncts.
