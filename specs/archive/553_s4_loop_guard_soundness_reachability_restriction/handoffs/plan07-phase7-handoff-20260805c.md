# Handoff: Plan v6 (`plans/07_canonical-witness-truth-lemma.md`), Phase 7 continuation (c)

- **Date**: 2026-08-05
- **Session**: sess_1785947077_74defa (third continuation dispatch)
- **Plan**: `plans/07_canonical-witness-truth-lemma.md` (v6, latest; plans 01-05 superseded)
- **Status at handoff**: Phases 1-6 `[COMPLETED]`, Phase 7 `[IN PROGRESS]` (three of the bespoke
  step lemma's case-split arms now landed sorry-free; see the plan's `#### Phase 7 Progress
  Record` (third dispatch, at the top of that subsection) for the authoritative, up-to-date
  state -- this handoff summarizes it and adds narrative context).

## What landed this dispatch (sorry-free, `{propext, Classical.choice, Quot.sound}` only)

All three in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, each a standalone case-scoped
lemma (not yet wired into one dispatcher theorem):

1. `modalApplyOneS4Keyed_notBoxDia_sat` -- propositional/non-modal case. Reduces
   `modalApplyOneS4Keyed` to plain K's `modalApplyOne` off box/diamond shapes (the bridge lemma
   `modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box` was un-privatized in `LoopChecking.lean` to
   make it visible from `FrameCompleteness.lean`, per the layering note), then closes via
   `tryAllPropRules_sat` in one call -- far cheaper than the ~350-line inline duplication the
   plain-K generic wrapper (`modalStepBranchGen_preserves_satIn`) uses for the analogous arm.
2. `modalApplyOneS4Keyed_boxNeg_mint_sat` -- mint-unblocked, box-negative (`F(□ψ)@w`,
   `blockingWorldS4Keyed = none`). Mirrors the plain-K box-negative mint arm's fresh-witness
   pointwise extension `f' := fun n => if n = w' then ww else f n` verbatim
   (`FrameSoundness.lean`'s `neg`/`box φ` case, ~lines 606-720), consuming the already-landed
   closed form `modalApplyOneS4KeyedMint_boxNeg_eq_S4` for the exact payload, with
   `boxPlusExtraS4_sat` (landed prior dispatch) closing the one extra chunk S4-keyed adds beyond
   plain K's own witness group.
3. `modalApplyOneS4Keyed_diaPos_mint_sat` -- direct dual, mint-unblocked diamond-positive.

Verification per lemma: scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` clean;
`lake exe lint-style` clean; sorry-free confirmed via direct `#print axioms` (NOT `lean_verify`,
which reports a known spurious `sorryAx` on these declarations -- see the caution note this
handoff inherits from the prior one). Bare-tactic sorry census over
`Cslib/Logics/Modal/Tableau/` stayed at exactly 1 (`FrameSoundness.lean:1251`, standing, retained)
after each commit. A whole-project `lake build` was also run this dispatch and is clean (not run
at the end of the prior two dispatches -- worth doing again before Phase 7 closes).

Three separate green commits, one per lemma, per the phase-substep commit convention.

## The mint-blocked correction -- read this before attempting that case again

The prior handoff (`...-20260805b.md`) catalogued mint-blocked (redirect) as the **cheapest**
remaining case, via `branchSatisfiableIn_s4FC_addEdge_of_blocked` (the Phase 6 capstone)
"directly". This dispatch found that claim does not hold up: that capstone requires
`hH : modalHintikkaSetS4 φ₀ b acc`, which demands **every** box-negative/diamond-positive-shaped
formula on the WHOLE branch `b` already have a witness successor (conjuncts 3/4 of
`modalHintikkaSetS4`), not just the one formula the current step is processing. It is a
terminal/fully-saturated-branch construction (matching an open-branch countermodel step at the
end of a completeness argument, rebuilding the model from scratch via `extractModelS4`), not a
per-step invariant. At an arbitrary settled ordered-stepper state -- the precondition under which
mint-blocked can fire (`modalStepBranchS4KeyedOrdered_mintReady`: settledness means every
*non-minting* rule has already fired, nothing about sibling mint-shaped formulas) --
`modalHintikkaSetS4 φ₀ b acc` is not available from `S4LoopInv`/`S4KeyedHintikkaInv` alone.

The alternative -- extend the SAME ambient `(W, m, f)` the way the three landed cases above do --
needs `m.r (f w) (f wBlock)` in an ARBITRARY model satisfying `b`. But `wBlock` is chosen by
`blockingWorldS4Keyed` via a purely syntactic key-subset comparison
(`S4LoopInv.keyLowerBd`), with no a priori semantic tie to whatever model happens to satisfy `b`
at this point. Neither route closes with what's currently available.

This looks like a genuine open architectural question -- either the induction needs a stronger
invariant than plain `branchSatisfiableIn s4FC b acc` threaded through every step (carrying
enough saturation, or an incrementally-maintained "redirect edges already realized" witness), or
mint-blocked is not provable as a literal per-step lemma and the soundness architecture needs
rethinking at the phase-design level. **This should be flagged to the user / raised at planning
level before the next dispatch burns more tool calls re-deriving the same dead end.** Full
technical detail (conjunct-by-conjunct) is in the plan's Progress Record.

## What remains

- **Mint-blocked (redirect)**: blocked on the architectural question above.
- **4-rule box-positive** (`T(□φ)@w`): unchanged from the prior catalogue, not attempted this
  dispatch. Needs a three-layer merge lemma (K + T-self + 4-propagation, all pre-existing sound
  pieces) plus a Keyed→S4 `.fst`-equality bridge. Still the single largest remaining piece of new
  content. Exact ingredients and line references are in the plan's Progress Record.
- **4-rule diamond-negative** (`F(◇φ)@w`): dual of the above, not attempted.
- Once (if) all cases close: assemble the single dispatcher theorem (case-split exactly mirroring
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`'s shape), extend the regression corpus,
  run the full 8-step gate.
- Still open (per the prior handoff, unresolved): whether Phase 7's task list is bounded to the
  step-level lemma alone, or also needs a fuel-induction wrapper /
  `modalTableauS4KeyedOrdered_sound`-shaped capstone. Not decided this dispatch either.

## Constraints that still apply, unchanged

- File scope: `Cslib/Logics/Modal/Tableau/{FrameCompleteness,FrameSoundness,LoopChecking}.lean`,
  `CslibTests/S4LoopGuardRegression.lean`. Everything else in the subsystem stays read-only.
- The standing sorry at `FrameSoundness.lean:1251` is retained by explicit user decision --
  untouched this dispatch, census confirmed still exactly 1.
- Never commit a `sorry`. Land only what genuinely closes; hand off the rest with an honest
  correction if a catalogued route turns out not to work (as this dispatch did for mint-blocked)
  rather than forcing a proof through with a placeholder.
- Un-privatizing a `LoopChecking.lean` lemma to consume it from `FrameCompleteness.lean` is
  in-scope (both files are in `file_scope`) -- this dispatch did it once
  (`modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box`) and the 4-rule cases will likely need it
  again for `modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding` /
  `modalApplyOneS4Rules_boxPos_diaNeg_known_S4`.
- Re-verify every line number by grep before trusting it (including this handoff's) -- edits
  shift line numbers.

## Continuation entry point

Read the plan's `#### Phase 7 Progress Record` (third-dispatch version, at the top) first, then:
1. Raise the mint-blocked architectural question (this handoff's main finding) rather than
   re-attempting the catalogued-but-broken route.
2. In parallel, the 4-rule box-positive case is well-scoped enough to attempt directly if the
   architectural question needs external input -- it does not depend on resolving mint-blocked.
