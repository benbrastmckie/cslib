# Phase 5 Continuation Handoff — `keyLowerBd`'s minting-case fact closed

## What this dispatch closed

The specific gap the prior dispatch's blocker named as unresolved is now CLOSED, verified,
zero sorry, zero new axiom:

- `successorBirthContent_boxNeg_subset_relevantSetFinset`
- `successorBirthContent_diamondPos_subset_relevantSetFinset`

Both state: `successorBirthContent φ₀ b s φ w ⊆ relevantSetFinset φ₀ (newForms ++ b)
(modalNextWorld b)`, taking `newForms` via a hypothesis phrased in terms of `modalApplyOne`'s
actual output (`(modalApplyOne ⟨s,formula,w⟩ b acc).fst = RuleResult.linear newForms`), so the
caller only needs `modalApplyOne`'s real output, not a hand-reconstructed list literal.

**Key insight that unblocked this**: `S4LoopInv.keyLowerBd` is stated as `k ⊆
relevantSetFinset φ₀ b w` (a subset), not an equality. The prior dispatch's `Finset.ext`
attempt chased a stronger equality (both directions) and got stuck bridging `Bool`-valued
`List.any`/`==` against the `Prop`-valued `Finset`/`∨`/`∃` target. This dispatch only proves
the forward/subset direction, and converts every `Bool`-valued `List.any` fact to a plain
`List.mem` fact IMMEDIATELY (via `any_beq_of_mem_S4`/`mem_of_any_beq_S4`), then reasons
entirely with `List.mem_cons`/`List.mem_append`/`List.mem_filterMap` — never touching the
`Bool`/`Prop` boundary again after that initial conversion.

## Additional groundwork landed this dispatch

- `modalApplyOneS4Keyed_boxNeg_blocked_eq` / `_unblocked_eq` / `_diaPos_blocked_eq` /
  `_unblocked_eq` — guard-spec lemmas for the keyed rule application, mirroring the existing
  `modalApplyOneS4_boxNeg_blocked_eq` family (which covers the OLD, live-set-guarded
  `modalApplyOneS4`, task 506/511 Phase 3 — untouched).
- `modalStepBranchS4Keyed_branch_superset` — every branch `modalStepBranchS4Keyed` produces is
  a superset of the pre-step branch, UNCONDITIONALLY (regardless of which rule fired or which
  `RuleResult` shape resulted). This is the fact that lets OLD keys' `keyLowerBd` obligation
  survive any step via `relevantSetFinset_mono`, and is reusable for `keysTotal`/
  `keysInUniverse` preservation too.

## What remains open

`modalStepBranchS4_preserves_keyLowerBd` — the driver-level lemma quantifying over an actual
`modalStepBranchS4Keyed` step (not just the minting-content fact in isolation). Every
mathematical ingredient is proved and green; what's missing is the case-analysis GLUE:

1. Extract `sf` via `List.exists_of_findSome?_eq_some hstep0` (after `unfold
   modalStepBranchS4Keyed at hstep0`), exactly as `modalStepBranchS4Keyed_branch_superset`'s
   own proof does (see that lemma's body for the working skeleton — `split_ifs at hsf with
   hexp` produces exactly ONE live goal here, not two, since the `then` branch is `none`
   which cannot unify with `some (...)`; do NOT write two bullets under `split_ifs`).
2. Case-split on `sf.sign, sf.formula`. Nine relevant leaves:
   - `atom`, `bot`, `imp`, `and`, `or` (5 leaves, both signs): non-minting regardless of sign.
     `keys'` reduces to `keys` via the catch-all `| x, x_1 => keys` match arm inside
     `modalStepBranchS4Keyed`'s definition. Argument: `have hold := fun b' hb' w k hwk =>
     relevantSetFinset_mono φ₀ b b' w (hsuper b' hb') (hLB w k hwk)` where `hsuper` comes from
     `modalStepBranchS4Keyed_branch_superset`; extract `keys' = keys` from `hsf` (4-way split
     on `result`'s `RuleResult` constructor, same `rcases hres : result with nf | brs | nf |
     -; rw [hres] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf` pattern already
     proven in `modalStepBranchS4Keyed_branch_superset`), then `rw [← hkeq] at hwk; exact hold
     b' hb' w k hwk`.
   - `box φ` with `sign = .pos`: non-minting (same argument as above).
   - `box φ` with `sign = .neg`: MINTING. Split on `blockingWorldS4Keyed φ₀ b keys .neg φ
     sf.label`:
     - `some wBlock`: use `modalApplyOneS4Keyed_boxNeg_blocked_eq` to pin `result = .linear
       []`, hence the new branch is `[] ++ b = b` and `keys' = keys` (same "old keys"
       argument).
     - `none`: use `modalApplyOneS4Keyed_boxNeg_unblocked_eq` to get `result = (modalApplyOne
       sf b acc).fst`, then `modalApplyOne_boxNeg_mint_fst_S4` pins `newForms` exactly, and
       `keys' = keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]`.
       Apply `successorBirthContent_boxNeg_subset_relevantSetFinset` directly for the new key;
       `hold` for the old keys.
   - `diamond φ` with `sign = .neg`: non-minting (same argument as the 5-leaf group).
   - `diamond φ` with `sign = .pos`: MINTING, dual of the box-neg case, using
     `modalApplyOneS4Keyed_diaPos_blocked_eq`/`_unblocked_eq`,
     `modalApplyOne_diamondPos_mint_fst_S4`, and
     `successorBirthContent_diamondPos_subset_relevantSetFinset`.

This is volume, not difficulty — every sub-argument above has already been proven in isolation
this dispatch. A continuation dispatch should budget for the mechanical casework (likely
150-250 lines, matching the ORIGINAL research report's estimate for "this piece" — which turned
out to be the assembly, not the minting-content fact itself).

## After `keyLowerBd` assembles

- `modalStepBranchS4_preserves_keysTotal` / `_preserves_keysInUniverse`: expected
  straightforward. `keysInUniverse`'s minting case reuses the SAME `hwit`
  (`mem_signedSubfmls_of_formula_S4`-derived witness-membership) argument already proved
  inside the two closed subset lemmas.
- Assemble `modalStepBranchS4_preserves_S4LoopInv` from the four field-preservation lemmas
  (`keysTotal`, `keyLowerBd`, `keysDistinct` — already closed as `keysUpdate_preserves_
  keysDistinct` — and `keysInUniverse`) plus the six rule-independent fields inherited from
  `S4LoopInv`'s sibling relationship to `ModalPotentialInv`.
- Phase 6 (pigeonhole world bound) and Phase 7 (decidability) become attemptable once Phase 5
  fully assembles.

## Unrelated observation

`lake test` currently fails on `CslibTests/ModalFrameSeparation.lean` (`decide` stuck reducing
`instDecidableFiveValid`). Confirmed via `git log`/`git status` to be entirely task 515's S5/Five
decidability work (committed by that task, clean working tree), unrelated to any file this task
touches. Not a regression from this dispatch; out of scope.
