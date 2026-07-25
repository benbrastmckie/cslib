# Phase 10 Dispatch Summary: Top-Loop Induction

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `plans/03_completeness-line-rescope.md`, Phase 10
- **Scope of this dispatch**: Phase 10 only (`modalExpandBranchesS4Keyed_hintikka`)
- **Commits**:
  - `de2ff6b3` — "task 535 phase 10.1: top-loop helper lemmas (newExps_const, none_saturated,
    box-neg/dia-pos not-notApplicable)"
  - `3400f426` — "task 535 phase 10.2: top-loop induction modalExpandBranchesS4Keyed_hintikka"

## What landed

`modalExpandBranchesS4Keyed_hintikka` (`Cslib/Logics/Modal/Tableau/LoopChecking.lean`): the
termination top-loop theorem — an open branch produced by `modalExpandBranchesS4Keyed` is a
Hintikka set for the live S4 rule `modalApplyOneS4 φ₀`. This is the core of the completeness
line and the plan's single largest genuinely-new phase.

Structural port of `modalExpandBranchesHintikka` (`CompletenessLoop.lean:1430-1740`): outer
induction on `fuel`, a `suffices key : …` restatement over the `pending`/`done` worklist split,
inner induction on `pending`, and a three-way per-branch dispatch (closed / saturated-open /
stepped). The per-index hypothesis is the literal 4-way conjunction `S4LoopInv φ₀ bi ei ai keysi
∧ S4KeyedHintikkaInv φ₀ bi ei ai keysi ∧ keysWorldsKnown ∧ worldsContiguousS4 bi` — there is no
single bundled structure playing `ModalLoopInvHintikka`'s role for the keyed driver (Phase 6
deliberately did not bundle `S4LoopInv`'s fields), so the four are threaded and destructured
together at every call site. An extra `keyss`/`pendingKeys`/`doneKeys` worklist column is
threaded throughout, parallel to `accs`/`pendingAccs`/`doneAccs`.

Four new territory-local helper lemmas support the induction:

- `modalStepBranchS4Keyed_newExps_const` — re-derivation of `CompletenessLoop.lean`'s `private
  modalStepBranchGen_newExps_const`, specialized to the keyed 4-tuple stepper, needed to put a
  raw step outcome into the constant-`newExp` form `modalExpMeasure_step_lt_S4Keyed`'s hypothesis
  requires.
- `modalStepBranchS4Keyed_none_saturated` — the saturated-leaf characterisation
  (`sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable`) derived directly
  against the keyed stepper via `List.findSome?_eq_none_iff` + case-split, mirroring Phase 7's own
  idiom rather than routing through the public but 3-tuple-only `modalStepBranchGen_none_saturated`
  (`Completeness.lean:809`).
- `modalApplyOneS4Keyed_boxNeg_ne_notApplicable` / `_diaPos_ne_notApplicable` — the keyed rule's
  result at the two minting shapes is always `.linear _` (never `.notApplicable`), in both the
  blocked (`.linear []`) and unblocked (K's `modalApplyOne_boxNeg_witness`/
  `_diamondPos_witness`, always nonempty) sub-cases. Guard-independent: holds for any
  `blockingWorldS4Keyed` outcome.

The `some step` case consumes Phase 7's `modalStepBranchS4_preserves_S4LoopInv`
(`LoopChecking.lean:4624`, giving the combined `S4LoopInv`/`keysWorldsKnown`/`worldsContiguousS4`
preservation in one call) and `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`
(`LoopChecking.lean:5949`) for invariant preservation, and Phase 9's
`modalExpMeasure_step_lt_S4Keyed` for the fuel decrease, feeding it `hLoopInv.bClosure`,
`hLoopInv.accKnown`, the ambient `worldsContiguousS4`, and `hLoopInv.{keysTotal,keysDistinct,
keysInUniverse}` directly (no separate raw hypotheses needed, since these are already
`S4LoopInv` fields under the same names/shapes the measure lemma's `hKT`/`hKD`/`hKI` expect).

The `none` (saturated) case dispatches the four Hintikka conjuncts per-shape
(`atom`/`bot`/`imp`/`and`/`or`/`box`/`diamond`, each split on `sign`), closing with
`rw [modalHintikkaSetS4_eq, ← hintikka_congr_S4 φ₀ k]` immediately after obtaining the
saturated-leaf invariant, then dispatching the four conjuncts against the keyed-rule
`modalHintikkaSetGen` form.

## Plan Deviations

- **The R1-sensitive blocked-redirect witness sub-case did not need its own call in this phase.**
  The plan flagged that box-negative/diamond-positive witness discharge in the `none` case would
  need `modalStepBranchS4Keyed_blocked_witness_mem` plus `S4KeyedHintikkaInv.eBoxNegWitness`/
  `eDiamondPosWitness` to handle "matched but redirected to a blocked world" formulas. On
  inspection, that mechanism is already fully internal to Phase 7's landed
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` — by induction, every box-neg/dia-pos
  formula reaching the saturated leaf is already `∈ e` with its witness recorded (proved here via
  the two new `_ne_notApplicable` lemmas, which rule out the "not yet expanded" branch of the
  saturated-leaf dichotomy at these two shapes, in both blocked and unblocked sub-cases). This
  phase's own code never calls `modalStepBranchS4Keyed_blocked_witness_mem` directly; the
  R1-sensitive argument stays isolated entirely inside Phase 7's already-committed, unmodified
  code — narrowing R1's future blast radius further than the plan anticipated, not widening it.
- **`none`-direction driver projection not available, so a direct local re-derivation was added
  instead.** Phase 8's contingency note flagged that the converse/`none` direction of
  `modalStepBranchS4Keyed_proj_stepBranchGen` "might be wanted" by Phase 10; it was not landed.
  Rather than adding it retroactively to Phase 8's territory, this phase adds a self-contained
  `modalStepBranchS4Keyed_none_saturated` derived directly against the keyed 4-tuple stepper
  (mirroring Phase 7's `findSome?` idiom), which is simpler than projecting through the generic
  3-tuple driver's own saturated-leaf lemma would have been.

No other deviations. The theorem's statement, per-index invariant shape, and induction structure
otherwise match the plan's Phase 10 task list exactly.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: 847 jobs, exit 0.
- `grep -n '\bsorry\b' Cslib/Logics/Modal/Tableau/LoopChecking.lean`: only the pre-existing
  docstring-prose mention at `:4619`.
- `lean_verify modalExpandBranchesS4Keyed_hintikka`: `propext`, `Classical.choice`, `Quot.sound`
  only (scan's only `opaque`-pattern hits are pre-existing lines 897/4667, unrelated text).
- `lean_verify modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` (regression): unchanged,
  same three axioms only.
- `lean_verify instDecidableS5Valid` (`FrameCompleteness.lean`, regression): empty extra-axiom
  set, unaffected.
- `lake exe checkInitImports`: clean.
- `lake lint`: zero hits in `LoopChecking.lean`.
- `lake exe lint-style`: zero hits in `LoopChecking.lean`.
- `lake shake`: zero unused-import/unused-hypothesis findings attributable to this phase's
  additions in `LoopChecking.lean` (the same pre-existing `modalUniverseS4_length_le`
  unused-hypothesis note as baseline); unrelated pre-existing `sorry`s surfaced in
  `Propositional/Tableau/{Intuitionistic,Minimal}` files, outside this task's territory.
- Warning count in `LoopChecking.lean`: 10 before and after this dispatch (8 `unusedSimpArgs` +
  1 hypothesis-unused note + 1 `longLine`, all pre-existing) — zero new warnings.
- `FmpMeasure.lean`, `Saturation.lean`, `CompletenessLoop.lean` byte-unchanged (read-only per the
  plan's Non-Goals); frozen `blockingWorldS4Keyed` guard (`LoopChecking.lean:469`) untouched.

## Status

Phase 10 `[COMPLETED]`. Phase 11 (`modalTableauS4Keyed_complete`) remains, per plan
`03_completeness-line-rescope.md`. Not blocked; this dispatch's scope was Phase 10 only and stops
here per the per-phase dispatch contract.
