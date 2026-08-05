# Handoff: Plan v6 (`plans/07_canonical-witness-truth-lemma.md`), Phase 7 continuation (b)

- **Date**: 2026-08-05
- **Session**: sess_1785947077_74defa (second continuation dispatch)
- **Plan**: `plans/07_canonical-witness-truth-lemma.md` (v6, latest; plans 01-05 superseded)
- **Status at handoff**: Phases 1-6 `[COMPLETED]`, Phase 7 `[IN PROGRESS]` (genuine partial
  progress landed; see the plan's `#### Phase 7 Progress Record` for the authoritative,
  up-to-date table of what's landed and what remains -- this handoff summarizes it and adds
  narrative context, but the Progress Record is the source of truth if the two ever diverge).

## What landed this dispatch (sorry-free, standard axioms only)

1. **`boxPlusExtraS4_sat`** (`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`) -- the one
   piece of genuinely new SEMANTIC content the mint-unblocked step case needs.
   `modalApplyOneS4KeyedMint` (`LoopChecking.lean`) appends `boxPlusExtraS4 b w` -- a BOXED
   re-transmission of every `T(□ψ)@w`/`F(◇ψ)@w` already on the branch, retargeted to the fresh
   witness `w'` -- on top of `modalApplyOne`'s own K witness group. This lemma proves every
   `boxPlusExtraS4` element is satisfied at the pointwise-extended world-assignment, via a
   single hop of `s4FC`'s `IsTrans` off the mint edge: a `T(□ψ)@w` fact is `∀ v, m.r (f w) v →
   Satisfies m v ψ`; any `m.r`-successor of the fresh witness value `ww` is ALSO an
   `m.r`-successor of `f w` by transitivity, so the identical universal fact reinstates at `w'`
   literally boxed, not just unwrapped. Diamond-negative is the contrapositive dual.
2. A "Re-scoped Phase 7" module-comment section header in `FrameCompleteness.lean`, recording
   the layering note (soundness content for the keyed ordered driver must live here, since this
   is the only file importing both `LoopChecking.lean` and `FrameSoundness.lean`) and why the
   generic `modalStepBranchGen_preserves_satIn` is not reusable (its `hAgree` hypothesis
   requires `apply` to agree with `modalApplyOne` off the T/4-rule shapes, but the keyed guard's
   BLOCKED arm departs from `modalApplyOne` precisely at the two MINTING shapes, which
   `hAgree`'s domain does not exclude).

Verification: scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` clean;
`lake exe lint-style` clean on the file; `lean_verify` reports `{propext, Quot.sound}` only, no
`sorryAx`; bare-tactic sorry census over `Cslib/Logics/Modal/Tableau/` returns exactly one line
(`FrameSoundness.lean:1251`, the standing, explicitly-retained sorry -- untouched).

## Why Phase 7 is larger than the plan estimated

Confirmed by direct inspection (not anticipated at v6 planning time): `modalStepBranchS4Keyed`/
`modalStepBranchS4KeyedOrdered` have **no existing soundness theory whatsoever** to extend --
not even for the *plain, unkeyed* S4 driver. `FrameSoundness.lean`'s S4 section (`## S4
(Reflexive-Transitive Frame)`) contains only rule-level building blocks (the 4-rule propagation
soundness lemmas, the T-rule self-propagation lemmas), never a step-preservation theorem
comparable to `modalStepBranchS5Gen_preserves_satIn` (`FrameSoundness.lean:2491`),
`modalStepBranchFive_preserves_satIn` (`:3745`), or `modalStepBranchKb5''_preserves_satIn`
(`:4488`) -- each several hundred lines. The bespoke step lemma Phase 7 needs is genuinely new
content on that same order, not a small wiring shim.

## What remains: the bespoke step-preservation lemma's case-split

Mirror `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`'s case-split shape exactly
(`LoopChecking.lean:10189`): `unfold modalStepBranchS4Keyed at hstep0; obtain ⟨sf, hsfmem, hsf⟩
:= List.exists_of_findSome?_eq_some hstep0; split_ifs at hsf with hexp; rcases hpair :
modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩; by_cases hmint : (sf.sign = .neg
∧ ∃ φ, sf.formula = .box φ) ∨ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)`, then within the
mint case, `rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg/.pos ψ sf.label with _ | wBlock`.

The plan's `#### Phase 7 Progress Record` (read this first, it is the authoritative version --
this handoff is a narrative summary of the same table) catalogues, per case, exactly which
pre-existing lemma supplies the ingredient:

- **Mint, blocked (redirect)** -- cheapest: `branchSatisfiableIn_s4FC_addEdge_of_blocked`
  (this file's own Phase 6 capstone) directly, `hUniv := hLoopInv.bClosure`, `hkL :=
  hLoopInv.keyLowerBd` (confirmed field names on `S4LoopInv`, `LoopChecking.lean:7672`).
- **Mint, unblocked**: `modalApplyOneS4Keyed_boxNeg_unblocked_eq`/`_diaPos_unblocked_eq` +
  `modalApplyOneS4KeyedMint_boxNeg_witness`/`_diaPos_witness` (`LoopChecking.lean`) give the
  exact output shape. Mirror the K mint construction in `FrameSoundness.lean` lines 412-472
  (`T(◇φ)@w` mint) / 606-691 (`F(□φ)@w` mint) for the `f' := fun n => if n = w' then ww else
  f n` extension and base witness satisfiability, then append `boxPlusExtraS4_sat` (landed this
  dispatch) for the extra chunk.
- **4-rule, box-positive `T(□φ)@w`**: `modalApplyOneS4_boxPos_fst_eq`
  (`LoopChecking.lean:9587`) gives the exact three-layer closed form (K's `boxPropagation`, THEN
  `modalTBoxSelf` dedup-appended, THEN `modalFourBoxProp` dedup-appended). **The single largest
  remaining piece**: a merge lemma showing this dedup-append-of-three-sound-layers preserves
  satisfiability, composing `modalApplyOne_boxPos_sound` (`SoundnessStep.lean:447`) +
  `modalTBoxSelf_sound` (`FrameSoundness.lean:1019`) + `modalFourBoxProp_sound`
  (`FrameSoundness.lean:1123`). Also needs a Keyed→S4 `.fst`-equality bridge at this shape via
  `modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding` + `modalApplyOneS4Rules_boxPos_diaNeg_
  known_S4` (both landed, `LoopChecking.lean`) -- confirm these compose to reach
  `modalApplyOneS4` exactly (one more small bridging fact may be needed).
- **4-rule, diamond-negative `F(◇φ)@w`**: dual, via `modalApplyOneS4_diaNeg_fst_eq`
  (`LoopChecking.lean:9658`), `modalTDiaNegSelf_sound` (`FrameSoundness.lean:1037`),
  `modalFourDiaNegProp_sound` (`FrameSoundness.lean:1143`).
- **Propositional/non-modal** -- second-cheapest: `modalApplyOneS4Keyed_eq_modalApplyOne_of_
  not_box` (landed) reduces to plain `modalApplyOne`; `tryAllPropRules_sat`
  (`SoundnessStep.lean:369`) gives `RuleResultSat m f (tryAllPropRules ... sf)` from `sfSat m f
  sf` in ONE call covering all five propositional shapes -- far cheaper than the ~350-line
  inline duplication `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:197`) uses (that
  duplication apparently predates `tryAllPropRules_sat`'s extraction). Only needs a small,
  not-yet-built generic "`RuleResultSat` result appended to the branch preserves
  `branchSatisfiableIn FC`" wrapper on top.

**Suggested order for the next dispatch** (cheapest first, bank incremental green commits):
propositional -> mint-blocked -> mint-unblocked -> 4-rule box-positive -> 4-rule
diamond-negative (dual, faster once box-positive's pattern lands) -> assemble the full step
lemma -> extend `CslibTests/S4LoopGuardRegression.lean` -> run the full gate set (`lake build`
whole library, `lake exe lint-style`, `lake lint`, `lake test`, `lake shake --add-public
--keep-implied --keep-prefix` -- not yet run any dispatch this task).

## Open scope question, not yet resolved

Whether Phase 7's task list (four bullets: wire the step argument, layering note, regression,
full gate) is bounded to the STEP-level preservation lemma alone, or also requires the
fuel-induction wrapper and a `modalTableauS4KeyedOrdered_sound`-shaped end-to-end capstone
(mirroring `modalTableauS5_sound` etc., `FrameSoundness.lean:3317`). Reading the task list
literally, it looks bounded to the step lemma. If a future dispatch judges otherwise, that is
substantial additional work (comparable to the S5 Bespoke Fuel-Induction Assembly,
`FrameSoundness.lean:2453-3320`) and should be split into its own phase, not absorbed silently.

## Constraints that still apply, unchanged

- File scope: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`,
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, `Cslib/Logics/Modal/Tableau/LoopChecking.lean`,
  `CslibTests/S4LoopGuardRegression.lean`. `Rules.lean`, `Saturation.lean`, `Branch.lean`,
  `SoundnessStep.lean`, `Support/Accessibility.lean`, and everything under `Metalogic/**` stay
  read-only (consumed for their existing lemmas only).
- The standing sorry at `FrameSoundness.lean:1251` is retained by explicit user decision -- do
  not touch it. Sorry census must stay exactly 1 at every phase boundary.
- Never commit a `sorry`. If a sub-case cannot be closed within one dispatch, land what DOES
  close as a genuine, fully-proved lemma (the `boxPlusExtraS4_sat` pattern this dispatch
  followed) and hand off the rest -- do not sorry a placeholder.
- Re-locate every declaration by `grep -n '^def\|^lemma\|^theorem\|^structure\|^abbrev'`; no
  line number from any prior plan version or handoff (including this one) should be trusted
  without re-verifying via grep, since edits shift line numbers.
- The `lean_verify` MCP tool's `axioms` field can report a spurious `sorryAx` for a declaration
  that does NOT actually depend on `sorry` (a false positive from its source-scan heuristic). If
  it ever reports `sorryAx` on a newly-landed declaration, cross-check with a direct `lake env
  lean` script (`import <module>; #print axioms <fully.qualified.name>`) before treating it as a
  real blocker.

## Continuation entry point

Read the plan's `#### Phase 7 Progress Record` first (the authoritative, most current version of
everything in this handoff), then resume with the propositional case (cheapest, using
`tryAllPropRules_sat`), building the bespoke step lemma incrementally, case by case, committing
each green sub-case per the git-workflow phase-substep convention (`task 553 phase 7.N: {case
name}`) before moving to the next.
