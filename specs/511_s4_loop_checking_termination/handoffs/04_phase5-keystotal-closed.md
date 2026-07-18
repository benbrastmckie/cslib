# Phase 5 Continuation Handoff — `keysTotal` Closed (the Crux)

## Immediate Next Action

Build the `modalStepBranchS4Keyed`-to-`modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys)` bridge
lemma (mechanical: same `apply`, same `b.findSome?` selection, same 4-way `RuleResult` dispatch,
`keys'` just dropped), then reuse the six existing generic preservation lemmas
(`modalStepBranch_preserves_accFreshInv_gen`, `modalStepBranch_preserves_outDegEq_gen`,
`modalStepBranch_preserves_accTargetsKnown_gen`, `modalStepBranch_eClosure_gen`,
`modalStepBranch_preserves_expandedNodup_gen`, plus a `bClosure` generic fact still to be located
by name) to assemble `modalStepBranchS4_preserves_S4LoopInv`.

## Current State

- **All 4 of `S4LoopInv`'s key fields are CLOSED**: `keysDistinct`, `keyLowerBd`,
  `keysInUniverse`, and (this dispatch) `keysTotal` — the field explicitly flagged across three
  prior dispatches as "the crux" and "genuinely harder than mechanical casework".
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` builds green (scoped:
  `lake build Cslib.Logics.Modal.Tableau.LoopChecking`). `lake exe checkInitImports`,
  `lake exe lint-style`, and `lake lint` (full project) all pass with zero new issues (the two
  `lake lint` errors present are both in `FiveSimplification.lean`, unrelated to this task).
  Zero sorry anywhere in the file. `lean_verify` on `modalStepBranchS4_preserves_keysTotal`:
  `propext`/`Classical.choice`/`Quot.sound` only.
- The plan file's Phase 5 section (`specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`)
  has been updated: `keysTotal`'s checklist item is now `[x]` with a full account of what was
  built; the continuation note has been rewritten to describe the current (much narrower) gap.
- Phase 5's heading status remains `[PARTIAL]` — the six-field bridge and final `S4LoopInv`
  assembly are NOT done, so Phase 5 is not fully complete. This is an honest partial, not a
  stuck/abandoned state: the mathematically hard part is finished.

## Key Decisions Made

- Built a brand-new known-worlds dichotomy for `modalApplyOneS4Rules` (composing K+T+4 rule
  layers) from scratch, since no such lemma existed anywhere in the codebase for S4 (S5/Five have
  flatter analogues that don't compose three layers). This required:
  - Local re-derivations of several `FmpMeasure.lean` `private` lemmas that are unavailable
    cross-file: `mem_successorsOf_hasEdge_S4`, `modalKnownWorlds_fold_spec_S4` /
    `mem_modalKnownWorlds_S4` / `modalKnownWorlds_mono_append_S4` (all mirror
    `S5Simplification.lean`'s equivalent local re-derivations), `mintGroup_label_eq_freshWorld_S4`
    (mirrors `FmpMeasure.lean`'s private `mintGroup_label_eq_freshWorld`, parametrized over the
    minting shape's sign/formula so both `boxNeg`/`diamondPos` share one proof).
  - `modalApplyOneT_boxPos_diaNeg_known_S4`: the K+T layer's own dichotomy at the two
    T-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`) — never mints, self-propagation stays at `sf.label`
    (known since `sf ∈ b`), K's own `boxPos`/`diamondNeg` outputs known via `accTargetsKnown`
    (reusing K's own `modalApplyOne_knownWorlds_step`, public).
  - `modalApplyOneS4Rules_boxPos_diaNeg_known_S4`: composes the 4-rule layer
    (`modalFourBoxProp`/`modalFourDiaNegProp`) on top, whose propagation targets are recorded
    successors — known via `accTargetsKnown` + `mem_successorsOf_hasEdge_S4`.
  - `modalApplyOne_nonModal_known_S4`: the 10 "plain" propositional shapes (atom/bot/imp/and/or
    × pos/neg), via K's own `modalApplyOne_prop_outputs_subset` (all tryAllPropRules outputs
    stay at `sf.label`) plus the observation that non-modal `sf.formula` never hits any of
    `modalApplyOne`'s four modal-rule match arms.
  - `modalApplyOneS4Keyed_nonMint_known_S4`: the composite fact for all 12 non-minting leaves at
    once, combining the two lemmas above via a `by_cases` on the T/4-relevant-shape condition
    (NOT a full 14-way case split — this is a cleaner structure than `keyLowerBd`'s own
    12-goals-uniform-plus-2-explicit assembly, since the dichotomy is proven once generically
    rather than per-concrete-shape).
  - `modalStepBranchS4Keyed_keys_subset`: `keys ⊆ keys'` always (trivial once the outer
    `keys'` computation's 3-way shape — `keys`, or `keys ++ [newEntry]` at either minting
    shape's unblocked case — is exposed via `modalStepBranchS4Keyed_result_keys_eq`, the same
    extraction helper `keyLowerBd`/`keysInUniverse` already used).
  - `modalStepBranchS4_preserves_keysTotal` itself: assembled by a **top-level** `by_cases` split
    on whether `sf` is one of the two minting shapes (NOT the full 14-way split `keyLowerBd`
    used) — at the 2 minting shapes, explicit handling mirrors `keyLowerBd`'s own explicit
    minting-case blocks (pin `newForms` via the `mint_fst_S4` lemmas, show every emitted label
    equals `modalNextWorld b` via `mintGroup_label_eq_freshWorld_S4`, and `keys'`'s new entry is
    exactly the witness); at the 12 non-minting shapes, `modalApplyOneS4Keyed_nonMint_known_S4`
    collapses the "new known world" case back into the "old known world" case (no genuinely new
    label is ever introduced there), so `keys ⊆ keys'` suffices via `hold`.

## What NOT to Try

- Do not attempt to reuse `TDriver.lean`'s `modalApplyOneT_boxPos_fst`/`_snd` or
  `modalApplyOneT_knownWorldsStep` directly — `LoopChecking.lean` does not import `TDriver.lean`
  (only `FmpMeasure.lean` and `FrameRules.lean`), and those names are unavailable. This was
  discovered the hard way (unknown-identifier build errors); the fix was to unfold
  `modalApplyOneT` directly via `unfold modalApplyOneT; simp only [hkeq]` after extracting the
  raw `modalApplyOne` pair via `rcases hkeq : modalApplyOne (...) b acc with ⟨kResult, kAcc⟩`.
- Do not use `dsimp only` to reduce a goal of the shape `(if c then (a,x) else (b,x)).snd = y` —
  it makes no progress on `ite`-over-pairs. Use
  `simp only [apply_ite Prod.snd, apply_ite Prod.fst, ite_self]` instead (pushes the projections
  into the branches, then `ite_self` collapses the `.snd` since both branches agree there).
- Do not assume `List.subset_append_left`/`List.Subset.refl` apply directly via `exact` against
  a goal still containing an unreduced `match some wBlock with | some val => ... | none => ...`
  — Lean's `exact` elaboration did not push through the literal-constructor match reduction
  reliably here. The robust fix was `intro p hp` (turning `keys ⊆ X` into `∀ p ∈ keys, p ∈ X`)
  and using `List.mem_append_left _ hp` / `exact hp` directly, which DO see through the match's
  defeq reduction on a literal `some wBlock`/`none` scrutinee.

## Remaining Goals (verbatim from plan checklist)

- [ ] Assemble `modalStepBranchS4_preserves_S4LoopInv` (needs the six-field generic bridge, see
  "What is needed" in the plan file's Phase 5 continuation note).

Phase 6 and Phase 7's remaining items are unchanged and still blocked on the above (Phase 6
directly consumes `keysTotal`'s pigeonhole map, so it is now mathematically unblocked but still
requires the full `S4LoopInv` instance to exist before its own proofs can consume it).

## References

- Plan: `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`
  (Phase 5 section, lines ~255-435)
- File modified: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (new section inserted after
  `keysInUniverse`'s proof, before `/-! ## S4 Hintikka Set -/`)
- Prior handoffs: `02_phase5-keylowerbd-fact-closed.md`, `03_phase5-keylowerbd-keysinuniverse-closed.md`
- Generic preservation lemmas to reuse (once the bridge exists):
  `modalStepBranch_preserves_accFreshInv_gen` (`Soundness.lean`),
  `modalStepBranch_preserves_outDegEq_gen`, `modalStepBranch_preserves_accTargetsKnown_gen`,
  `modalStepBranch_eClosure_gen`, `modalStepBranch_preserves_expandedNodup_gen` (all
  `FmpMeasure.lean`)
