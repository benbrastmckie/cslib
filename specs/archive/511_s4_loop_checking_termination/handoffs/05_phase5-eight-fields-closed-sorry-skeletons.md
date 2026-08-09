# Task 511 Phase 5 — Dispatch 6 Handoff: 8/10 `S4LoopInv` Fields Closed, 2 Documented Strategic Sorries

## Summary

Continued Phase 5 (`S4LoopInv` preservation lemmas — "the crux") from the prior dispatch's
handoff, which had closed all four "key" fields (`keysDistinct`/`keyLowerBd`/`keysInUniverse`/
`keysTotal`) but not yet built the six "rule-independent" fields or the final assembly.

This dispatch closed **four more fields** (`eNodup`, `outDegEq`, `accFresh`, `accKnown`) and
landed the assembly theorem `modalStepBranchS4_preserves_S4LoopInv`, with **8 of 10 fields fully
closed, zero sorry, zero new axiom**. The remaining two fields (`bClosure`, `eClosure`) are
landed as **documented strategic-sorry skeletons** — complete, non-vacuous theorem statements
carrying every hypothesis their eventual proof will need, not placeholders.

## Key Discovery: the "Generic Bridge" Plan Does Not Work As Stated

The prior dispatch's continuation note proposed bridging `modalStepBranchS4Keyed` to
`modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys)` so six existing generic `_gen` preservation
lemmas could be reused "mechanically". Attempting this revealed two structural obstacles:

1. **`hFreshLocal`-shaped hypotheses don't fit the guard's blocked case.** The generic
   `accFreshInv_gen`/`accTargetsKnown_gen` lemmas need `(apply sf b acc).fst = .linear
   (wsf::rest)` (a *nonempty* linear result) whenever `acc` changes. `modalApplyOneS4Keyed`'s
   guard-BLOCKED minting sub-case returns `.linear []` (genuinely empty) while still adding an
   edge — this never satisfies the dichotomy.
2. **The generic `eClosure`/`bClosure` facts are keyed to K's own `modalUniverse`/
   `modalWorldBound`**, not `modalUniverseS4`/`modalWorldBoundS4`. Even with a working bridge,
   these lemmas' conclusions target the wrong universe/bound pair.

The actual fix for (1): a new proof-internal auxiliary invariant `keysWorldsKnown` (every
recorded key's world is a known branch world) — deliberately *not* a new `S4LoopInv` struct
field (would reopen the completed Phase 4 design), threaded as an extra hypothesis/conclusion
alongside the struct instead. Every field closed this dispatch used a direct case split on
`modalStepBranchS4Keyed`'s own definition (same style as the four key fields), never the
generic bridge.

## What's Closed This Dispatch

- `modalStepBranchS4_preserves_keysDistinct` — driver-level wrapper around the already-closed
  `keysUpdate_preserves_keysDistinct` combinator (not previously wired to
  `modalStepBranchS4Keyed`).
- `modalApplyOneS4Keyed_nonMint_snd_eq_acc` — composite: `acc` is unchanged at all 12
  non-minting shapes.
- `modalStepBranchS4_preserves_eNodup` — fully rule/keys-agnostic.
- `outDeg_addEdge_self_S4`/`_ne_S4`, `modalApplyOne_boxNeg_mint_snd_S4`/
  `_diamondPos_mint_snd_S4`, and `modalStepBranchS4_preserves_outDegEq`.
- `keysWorldsKnown` (new auxiliary invariant) + `modalStepBranchS4_preserves_keysWorldsKnown`.
- `accFreshInv_append_S4`/`hasEdge_addEdge_cases_S4` and `modalStepBranchS4_preserves_accFresh`/
  `_accKnown`.
- `modalStepBranchS4_preserves_S4LoopInv` — the assembly (8/10 fields closed).

## What Remains — `bClosure`/`eClosure` (Documented Strategic Sorries)

- **`eClosure`** needs a formula-subset composite for T-self (`modalTBoxSelf`/
  `modalTDiaNegSelf`) and 4-propagation (`modalFourBoxProp`/`modalFourDiaNegProp`) outputs,
  mirroring the existing known-worlds composite's case-split shape but concluding subformula
  membership. K's own public `modalApplyOne_boxPos_outputs_subset`/
  `modalApplyOne_diamondNeg_outputs_subset` ARE directly reusable for the K piece.
- **`bClosure`** needs Phase 6's own pigeonhole world-bound argument (`modalMaxWorld b <
  modalWorldBoundS4 φ₀`) as a genuine *prerequisite* — needed on the pre-step branch before any
  mint, not merely as Phase 6's later corollary.

See the plan file's Phase 5 continuation note and `specs/511_s4_loop_checking_termination/
.orchestrator-handoff.json`'s `sorry_inventory` for the precise remaining obligations.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green (scoped), throughout all 9
  incremental commits.
- Exactly 2 `sorry` occurrences in the file, both in the documented skeletons.
- `lean_verify` on every closed lemma: `propext`/`Classical.choice`/`Quot.sound` only.
  `modalStepBranchS4_preserves_S4LoopInv` correctly reports `sorryAx` (expected).
- `lake exe lint-style` clean on the modified file.
- Full-project `lake build` fails entirely in `Cslib/Logics/Bimodal/Metalogic/BXCanonical/
  Chronicle/CounterexampleElimination/*.lean` — confirmed via `git status` to be uncommitted,
  in-progress edits from the concurrent task 517 session; not this task's file scope, not a
  regression.

## Files Modified

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`
