# Handoff: Task 553, Phase 10 BLOCKED

## Immediate Next Action

Do not re-attempt Phase 10's `blockedRedirect_boxctx_mem` with the hypotheses as currently
scoped (`blockingWorldS4Keyed_eq_birthContent` + `S4LoopInv.keyLowerBd` only) -- it is not
provable; the exact stuck goal is reproduced below and was confirmed via `lean_goal` +
`lean_multi_attempt` (`aesop` exhausts without closing). The recommended next action is
`/revise 553` to insert a new phase (between 9 and 10) that adds a "key origin edge" invariant
to `S4LoopInv`, described under "What Would Close It" below, before re-attempting this phase's
tasks.

## Current State

- Phases 1-9 remain complete, committed, and verified green (see
  `handoffs/phase-10-handoff-20260726.md`, written by the Phase 9 dispatch, for their full
  state -- unchanged by this dispatch).
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` is byte-for-byte identical to its Phase-9
  committed state (`git diff --stat` empty) -- this dispatch's scratch lemma (with a trailing
  `sorry`) was written only to obtain the exact `lean_goal` state, then fully reverted. No
  `sorry`, no partial declaration, no import addition was left in place.
- The plan file (`plans/01_s4-settled-context-scheduling.md`) Phase 10 heading is now
  `[BLOCKED]`, with a blocker note prepended documenting the exact stuck goal, root cause, and
  the "what would close it" analysis (see that section for the full citations).
- No axiom count change, no new sorries anywhere in the repo (unchanged at 0 outside documented
  strategic ones -- there are none from this dispatch).

## Key Decisions Made

- Confirmed empirically (not just by inspection) that `modalApplyOne_boxNeg_mint_fst_S4` /
  `_diamondPos_mint_fst_S4` (`LoopChecking.lean:1329`/`1362`) transmit only the *unwrapped* `ψ`
  for each box-positive at a minting source -- never the boxed form `□ψ` -- contradicting the
  plan's "Named difficulty" assumption that "S4 sends both `ψ` and `□ψ` forward" at mint time.
  The boxed form is added only later, by a separate 4-rule step (`modalFourBoxProp`, landed in
  Phase 9), which requires an edge to already exist.
- Decided this is a genuine mathematical gap, not a tactic-automation gap: `aesop` and
  `simp_all [successorBirthContent, relevantSetFinset]` both exhaust on the literal goal without
  closing it (see plan file for the full transcript-derived analysis).
- Decided NOT to leave a `sorry`-based "skeleton" placeholder: this does not meet the
  anti-analysis strategic-sorry five-condition test (it is not a deliberate, pre-planned
  division boundary -- it is a discovery that the plan's obligation, as stated, needs
  additional invariant machinery the plan did not anticipate).

## What NOT to Try

- Do not retry `aesop`/`simp`-family automation directly on `blockedRedirect_boxctx_mem`'s bare
  goal (`{ sign := Sign.pos, formula := □ψ, label := wBlock } ∈ b` from
  `hsub : successorBirthContent φ₀ b s φ v ⊆ relevantSetFinset φ₀ b wBlock`) -- already
  exhausted.
- Do not assume `modalApplyOne`'s K-level minting payload carries the boxed form `□ψ` at mint
  time for either minting shape -- empirically false in this codebase (see citations above).
- Do not weaken `blockedRedirect_boxctx_mem`'s conclusion to the unwrapped form (`T(ψ)@wBlock`)
  to make it "provable" -- this is NOT what `branchPropAdequateIn_s4FC_boxPos_trans_mem`'s
  `hready` hypothesis needs (it needs the boxed form specifically); a weakened restatement would
  be a vacuous/misleading discharge, prohibited by both `lean4.md` and the plan's own explicit
  instruction.

## What Would Close It (recommended follow-up phase)

Add a new `S4LoopInv` field tracking each key's **origin edge**: every non-root
`(w, k) ∈ keys` arose from some recorded mint edge `(u, w) ∈ acc` with `k =
successorBirthContent φ₀ b_birth s' φ' u` for the historical pre-mint branch `b_birth ⊆ b`
(current). Composed with branch-monotonicity (formulas never leave `b`), this gives `T(□ψ)@u
∈ b` for wBlock's *real* mint source `u` whenever `(pos, ψ) ∈ key(wBlock)` (since `ψ` was
recorded as box-positive at `u`, the actual mint source -- not merely coincidentally at `v`,
the current blocked attempt's source). Mint-readiness (`modalStepBranchS4KeyedOrdered_
mintReady`) applied to the *existing* edge `(u, wBlock)` then forces `T(□ψ)@wBlock ∈ b`: if it
were absent, `modalFourBoxProp`'s candidate at `(u, T(□ψ)@u, edge u→wBlock)` would still be an
unsettled non-mint candidate, contradicting mint-readiness at the current (later) mint-shaped
step.

This requires:
1. A new `S4LoopInv` field, e.g. `keysOrigin : ∀ w k, (w, k) ∈ keys → w = 0 (root case) ∨ ∃ u s'
   φ' b_birth, acc.hasEdge u w = true ∧ k = successorBirthContent φ₀ b_birth s' φ' u ∧ (∀ x ∈
   b_birth, x ∈ b)` (exact shape to be worked out; needs enough to recover `T(□ψ)@u ∈ b`
   without re-deriving the whole historical branch).
2. Proving this field is preserved across all ~12 step shapes of `modalStepBranchS4KeyedOrdered`
   -- the same scale of work as `keyLowerBd`/`keysDistinct`'s own preservation lemmas (Phases
   1-8 of this plan).
3. Re-deriving `blockedRedirect_boxctx_mem` using this new field plus mint-readiness, per the
   argument above.

This is materially larger than Phase 10's stated 3.5-hour budget and reshapes Phase 11's
induction (which will need to thread the new field too). Recommend `/revise 553` to insert this
as its own phase (a "Phase 9.5" or renumbered slot between 9 and 10) rather than silently
expanding Phase 10's scope.

## Remaining Goals (verbatim from plan, Phase 10)

- [ ] Prove `blockedRedirect_boxctx_mem`: under mint-readiness (Phase 4's `_mintReady`), the
  guard's `some` case, and `S4LoopInv`, every `T(□ψ)@v ∈ b` has `T(□ψ)@wBlock ∈ b`.
- [ ] Prove the dual `blockedRedirect_diaNeg_mem` for `F(◇ψ)@v ∈ b`.
- [ ] Assemble `blockedRedirect_propAdequate`: the added edge `v → wBlock` satisfies the
  `branchPropAdequateIn` edge conjunct, given the two membership facts and the branch-formula
  conjunct already in the invariant.
- [ ] State explicitly in the docstring why mint-readiness is load-bearing: without it, `v`'s box
  context can grow after the decision and the two membership facts fail -- this is exactly the
  counterexample's mechanism.

## References

- Plan: `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/01_s4-settled-context-scheduling.md`
  (Phase 10 section, now `[BLOCKED]`, contains the full blocker writeup)
- Prior handoff (Phase 9 -> 10 briefing, still valid background): `handoffs/phase-10-handoff-20260726.md`
- Key files: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`blockingWorldS4Keyed`,
  `successorBirthContent`, `S4LoopInv`, `modalStepBranchS4KeyedOrdered_mintReady`),
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (`branchPropAdequateIn` and Phase 9's
  consumer lemmas, unchanged)
