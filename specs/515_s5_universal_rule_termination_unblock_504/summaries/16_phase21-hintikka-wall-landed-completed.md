# Summary 16: Phase 21 fully COMPLETED -- the `FiveWorldInv` Hintikka wall landed

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 21 (`modalTableauFive_complete` + `Decidable (fiveValid φ)`) -- now `[COMPLETED]`

## What landed this dispatch

Resumed from `handoffs/15_phase21-partial-fiveworldinv-wall-blocked.md`, which recorded the
`accTargetsNeRoot` top-loop pair as landed (commit `720088c9`) but the primary Phase 21
deliverable (`modalTableauFive_complete`/`instDecidableFiveValid`) as blocked on a missing
inductive step-preservation proof for `FiveWorldInv` -- the "Hintikka wall" -- explicitly flagged
by `FiveSimplification.lean`'s own docstring as deferred, "Phase 19b-scale work."

This dispatch built and landed the full four-step recipe the blocker's note specified, with one
necessary technical refinement discovered and documented as a deviation. Six green sub-milestone
commits:

1. **`69d5f657`** -- `expandedRootTagsFive`/`FiveWorldInvE` infrastructure
   (`FiveSimplification.lean`): the `e`-aware refinement of `FiveWorldInv` needed for a
   step-local induction (see "The `e`-aware refinement" below).
2. **`6eefff80`** -- `modalApplyOneFive_worldGrowth` (`FiveSimplification.lean`): the per-call
   world-growth dichotomy mirroring `modalApplyOneS5w_step`, doubled for the root/non-root mint
   split (known-only / non-root-fresh-mint / root-triggered-mint).
3. **`ee112b41`** -- `modalStepBranchFive_preserves_worldInv` (`FiveSimplification.lean`): the
   combined step-preservation theorem mirroring `modalStepBranchS5w_preserves_worldInv`, three-way
   case split instead of S5w's two, assembling `modalApplyOneFive_outputsSubsetUniverse` (F2,
   already landed) with the growth lemma.
4. **`f1fa2965`** -- `ModalLoopAuxFive` + `_bounds` + `_stepPreserved` +
   `modalLoopInvHintikkaFive_initial` (`FrameCompleteness.lean`): the `Aux` instantiation
   `modalExpandBranchesHintikka` needs.
5. **`245e2157`** -- `modalTableauFive_complete` + `fiveValid_decides` +
   `instDecidableFiveValid` (`FrameCompleteness.lean`): the payoff, assembled exactly as
   `modalTableauS5_complete`/`instDecidableS5Valid` do.
6. **`31398911`** -- plan file: Phase 21 marked `[COMPLETED]`, checklist updated, BLOCKER note
   replaced with a RESOLVED note (staged via `git hash-object`/`update-index` against HEAD's blob
   to avoid pulling in stray, pre-existing, uncommitted Phase 22/23 `[IN PROGRESS]` markers from a
   concurrent session).

## The `e`-aware refinement (deviation from the recipe's literal step 3)

The blocker's recorded recipe suggested `ModalLoopAuxFive φ₀ b _e _acc := S5wTagInv φ₀ b ∧
FiveWorldInv φ₀ b` (mirroring `ModalLoopAuxS5w`, ignoring `e` entirely). A careful per-step
analysis showed this literal shape is **not** step-preservable: a root-triggered mint
(`sf.label = 0`) consumes a root tag that was already counted in the presence-based
`usedTagsFiveRoot` the moment its trigger *appeared* on the branch -- chronologically *before*
the mint itself fires (unlike a non-root fresh mint, where the tag-set membership and the world
growth flip in the same step). A bare, `e`-independent invariant therefore cannot show the
required per-step growth at a root-triggered mint step (concrete trace: if a non-root mint for a
tag fires first, establishing a non-root witness, then later the *same* tag's root trigger fires
too -- Five's guard permits this "double mint per tag, once per source class" by design -- the
root side of the accounting shows no growth at the second mint, even though the world count grows
by one).

The fix threads the expanded-set `e` (already present in `AuxStepPreserved`'s signature for
exactly this kind of need, per its own docstring) into `expandedRootTagsFive`, an `e`-aware root
tag counter that counts a root tag only once its unique trigger occurrence has been *dequeued*
(is a member of `e`), not merely present on `b`. This strictly grows at the exact step a
root-triggered mint fires (the trigger moves from not-expanded to expanded), restoring the
"count grows in lockstep with `modalMaxWorld`" argument. `FiveWorldInvE` (using
`expandedRootTagsFive`) still implies the plain, already-landed `FiveWorldInv`
(`FiveWorldInvE_imp_FiveWorldInv`, since `expandedRootTagsFive ⊆ usedTagsFiveRoot` unconditionally
by a strictly-stronger filter predicate), so `ModalLoopAuxFive_bounds` still routes through
`modalMaxWorld_lt_worldBound_of_FiveWorldInv` (Phase 19a) unchanged.

## Verification

- **Sorry-free** throughout: `grep -rn '\bsorry\b'` on both touched files returns zero hits
  (outside doc comments referencing the word).
- **Axioms**: `#print axioms` on every new public declaration
  (`modalApplyOneFive_worldGrowth`, `modalStepBranchFive_preserves_worldInv`,
  `ModalLoopAuxFive_bounds`, `ModalLoopAuxFive_stepPreserved`,
  `modalLoopInvHintikkaFive_initial`, `modalTableauFive_complete`, `fiveValid_decides`,
  `instDecidableFiveValid`) confirms `[propext, Classical.choice, Quot.sound]` only -- no
  `sorryAx`, no new custom axiom.
- **Full CI green**: `lake build` (3240/3240), `lake exe checkInitImports` (exit 0), `lake lint`
  (only the pre-existing `PrimeExclusion.lean` baseline remains, after adding
  `@[nolint unusedArguments]` to `ModalLoopAuxFive`, caught during this dispatch's own lint run),
  `lake exe lint-style` (exit 0), `lake shake --add-public --keep-implied --keep-prefix` (no
  import changes suggested for either touched file), `lake test` (green, 9230/9231 targets --
  the pre-existing Intuitionistic/Minimal `sorry` warnings are an unrelated baseline).
- **Live regression probe** (the plan's own Verification requirement): `decide (fiveValid
  (□(atom 0) → atom 0)) = false` while `decide (s5Valid (□(atom 0) → atom 0)) = true` -- `□p → p`
  is S5-valid via reflexivity but not Euclidean-valid, confirming `instDecidableFiveValid`
  genuinely routes through `fiveFC`/`modalApplyOneFive` and is not silently equal to
  `instDecidableS5Valid`.

## Plan Deviations

- **Root-mint `Aux` refinement** (documented above): `e`-aware `expandedRootTagsFive`/
  `FiveWorldInvE` in place of the recipe's literal `e`-ignoring `S5wTagInv ∧ FiveWorldInv`
  suggestion -- a mathematical necessity, not a stylistic choice (the literal shape is not
  step-preservable, per the trace above).
- **`hintikka_congr` item**: confirmed moot (already investigated and recorded moot in the prior
  dispatch; re-confirmed here since `modalTableauFive_complete`'s proof consumes `hH :
  modalHintikkaSetGen modalApplyOneFive b a` directly, no bridging step).
- **Non-derivability probe**: discharged via a live `decide`/`#eval` regression check rather than
  a standalone `fiveValid_ssubset_s5Valid` lemma (which does not exist under that name in the
  codebase and was not required by the plan's own Verification section for this phase, which asks
  specifically for the live check).
- **`bClosure` tracking inside `Aux`**: `ModalLoopAuxFive` bundles a `modalUniverse`-closure
  conjunct alongside `FiveWorldInvE` (rather than only `S5wTagInv`-style formula closure), since
  `AuxStepPreserved`'s signature does not thread `ModalLoopInvHintikka.bClosure` as an ambient
  hypothesis the way it threads `accFreshInv`/`accTargetsKnown`. This let the closure half reuse
  the already-landed `modalApplyOneFive_outputsSubsetUniverse` (F2) wholesale instead of
  re-deriving a parallel `signedSubfmls`-based closure argument from scratch, at the cost of a
  slightly heavier `Aux` (redundant with `ModalLoopInvHintikka`'s own `bClosure` field, which is
  harmless).

## Files touched

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`

## What this unblocks

Task 504 (S5/KB5 decidability): the task's re-scoped deliverable's first half (`fiveValid`
decidability) is now fully delivered and shipped. Phase 22 (KB5 rule + soundness) and Phase 23
(KB5 completeness + `Decidable (kb5Valid φ)` + final docstring reconciliation) remain queued,
not started this dispatch, per the hard constraint. Both phases are expected to reuse the Five
pattern (including this dispatch's `expandedRootTagsFive`-style `e`-aware refinement, if KB5's own
mint-arm guard shares the same root/non-root double-mint structure).
