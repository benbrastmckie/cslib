# Handoff: Plan v6 (`plans/07_canonical-witness-truth-lemma.md`), Phase 3 continuation

- **Date**: 2026-08-05
- **Session**: sess_1785947077_74defa
- **Plan**: `plans/07_canonical-witness-truth-lemma.md` (v6, latest; plans 01-05 superseded)
- **Status at handoff**: Phases 1-2 `[COMPLETED]`, Phase 3 `[PARTIAL]`, Phases 4-7 `[NOT STARTED]`

## What landed this dispatch (all sorry-free, verified)

1. **Phase 1 (Gate 0)**: `reflTransGen_addEdge_iff` (`FrameCompleteness.lean`) -- the
   `addEdge`/`ReflTransGen` decomposition identity. Closed on the first attempt. **Outcome (i)**:
   Gate 0 passes on the cheap branch, collapsing the entire agreement-lemma/canonical-witness
   workstream. See `#### Phase 1 Verdict` in the plan for the full re-scope of Phases 3-6.
2. **Phase 2 (Gate B)**: `hintikkaS4_box_pos_reflTransGen_wrapped`,
   `hintikkaS4_dia_neg_reflTransGen_wrapped`, and `modalS4Saturated_of_ordered_settled`
   (`LoopChecking.lean`). **Outcome (i)**: Gate B passes at its cheapest, no additional invariant
   field needed. See `#### Phase 2 Verdict`.
3. **Phase 3 (partial)**: `modalHintikkaSetS4_addEdge_of_saturated` (`FrameCompleteness.lean`) --
   discharges 3 of 4 `modalHintikkaSetS4` conjuncts unconditionally, takes the 4th
   (`modalS4Saturated` at the extended accessibility) as an explicit hypothesis rather than
   sorrying it. See the plan's `#### Phase 3 Progress Record`.

Sorry census over `Cslib/Logics/Modal/Tableau/` is exactly 1 (`FrameSoundness.lean:1251`,
the standing, explicitly-retained sorry) at every commit. `lean_verify` on every new declaration
reports axioms exactly `{propext, Classical.choice, Quot.sound}`. Scoped builds, `lake exe
checkInitImports`, and `lake exe lint-style` are all clean.

## What remains (re-scoped Phases 3-7, per the Phase 1 Verdict)

**Phase 3's remaining piece** (the actual hard content): prove

```lean
modalS4Saturated φ₀ b (acc.addEdge src wBlock)
```

given `modalS4Saturated φ₀ b acc`, `blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock`, and
`S4LoopInv`'s ambient invariants (`keyLowerBd`/`bClosure` at minimum). The plan's Phase 3
Progress Record lays out the concrete route:

1. **`sf.label ≠ src`**: a "local shape invariance" lemma showing
   `modalApplyOneS4 φ₀ sf b (acc.addEdge src wBlock) = modalApplyOneS4 φ₀ sf b acc`, keyed off
   `(acc.addEdge src wBlock).successorsOf w = acc.successorsOf w` for `w ≠ src` (true by
   unfolding `Accessibility.successorsOf`/`addEdge`, not yet written as a named lemma). This
   should mirror `modalApplyOneS4Keyed_fst_eq_of_not_box`'s proof style
   (`LoopChecking.lean:9042`), but keyed off `acc`-invariance rather than `b`-invariance.
2. **`sf.label = src`, box-positive/diamond-negative shape**: consume
   `blockedRedirect_boxed_boxPos_mem`/`blockedRedirect_boxed_diaNeg_mem`
   (`LoopChecking.lean:9419`/`9451`, already landed, sorry-free) to get `T(□χ)@wBlock ∈ b` /
   `F(◇χ)@wBlock ∈ b` from the corresponding fact at `src`. These need
   `hkL : ∀ w k, (w,k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w` (= `S4LoopInv.keyLowerBd`) and
   `(Sign.pos, .box χ) ∈ signedSubfmls φ₀` (from `S4LoopInv.bClosure` via a not-yet-located
   `modalUniverseS4`-to-`signedSubfmls` membership bridge -- search `mem_modalUniverseS4` first,
   or derive directly from `modalUniverseS4`'s definition, `LoopChecking.lean:366`).
3. **Assembly**: the per-`χ` transfer needs to be lifted into the FULL `.persistent`-result
   membership goal (`∀ sf' ∈ newForms, sf' ∈ b` for `modalFourBoxProp`'s extended output),
   likely via a case split on whether a given new-forms element targets an "old" successor
   (covered by `hH`'s saturation at `acc`) or the "new" successor `wBlock` (covered by the boxed
   free-transfer lemma), mirroring `hasEdge_addEdge_cases`'s shape.

**Phases 4-5** (re-scoped): were "canonical truth lemma, box-positive/diamond-negative
directions" -- now these directions are not proved as a standalone truth lemma at all. Instead,
once Phase 3's saturation-preservation lemma lands, `modalHintikkaSetS4_addEdge_of_saturated`
composes with it to give the FULL `modalHintikkaSetS4 φ₀ b (acc.addEdge src wBlock)`. Consider
merging what remains of Phase 3 with Phases 4-5 into a single phase, since the case split above
is inherently one connected argument, not two independent directions -- record any such merge in
the plan per its own "Scope Hypothesis" self-correction mechanism.

**Phase 6** (re-scoped): apply `modalTruthLemmaS4` at `acc.addEdge src wBlock` (consuming the
assembled `modalHintikkaSetS4`) to conclude branch-satisfiability at the extended accessibility
directly -- this is the actual redirect-preservation capstone. Then remove
`canonicalWitnessRestrictionProbe_agreementConditional` and its section header
(`FrameSoundness.lean`), since the re-scoped route never consumes it. Enumerate dependents by
`grep -rn 'canonicalWitnessRestrictionProbe' Cslib/ CslibTests/` before removing (expect zero).

**Phase 7**: wire the capstone into the keyed ordered driver's per-step soundness argument
(bespoke step lemma, NOT an instance of the generic `modalStepBranchGen_preserves_satIn` -- this
was verified at v5 planning time), extend `CslibTests/S4LoopGuardRegression.lean` with a
permanent witness row, record the layering note (soundness content for the keyed driver now
lives in `FrameCompleteness.lean`, not `FrameSoundness.lean`, forced by the import graph -- see
the plan's Overview), and run the full gate set.

## Constraints that still apply, unchanged

- File scope: `FrameCompleteness.lean`, `FrameSoundness.lean`, `LoopChecking.lean`,
  `CslibTests/S4LoopGuardRegression.lean`. `Rules.lean`, `Saturation.lean`, `Branch.lean`,
  `SoundnessStep.lean`, and everything under `Metalogic/**` stay read-only.
- The standing sorry at `FrameSoundness.lean:1251` (`branchSatisfiableIn_s4FC_ancestor_redirect`)
  is retained by explicit user decision -- do not touch it. Sorry census must stay exactly 1 at
  every phase boundary.
- `accPinnedBy`, `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical` are
  preserved verbatim (not used by the re-scoped route, but not removed either).
- Never commit a `sorry`. `modalHintikkaSetS4_addEdge_of_saturated`'s pattern (a genuine,
  fully-proved lemma taking the hard fact as an explicit hypothesis) is the sanctioned way to
  make forward progress without sorrying -- reuse this pattern for any further phase splits.
- Re-locate every declaration by `grep -n '^def\|^lemma\|^theorem\|^structure\|^abbrev'`; no line
  number from any prior plan version (including this handoff) should be trusted without
  re-verifying via grep, since edits shift line numbers.

## Continuation entry point

Read the plan's `#### Phase 3 Progress Record` (in `plans/07_canonical-witness-truth-lemma.md`)
first, then resume at re-scoped Phase 3's remaining saturation-preservation proof as laid out
above.
