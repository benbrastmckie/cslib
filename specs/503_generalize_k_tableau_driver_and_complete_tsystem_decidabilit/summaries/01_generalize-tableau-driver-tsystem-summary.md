# Implementation Summary: Task #503 -- Generalize K Tableau Driver + Complete T-System Decidability

- **Task**: 503
- **Plan**: `specs/503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/plans/01_generalize-tableau-driver-tsystem.md`
- **Status**: PARTIAL (Phases 1-4 COMPLETED and committed, zero-debt; Phase 5 BLOCKED with a
  documented handoff; Phases 6-7 NOT STARTED, sequentially dependent on Phase 5)

This summary supersedes the prior draft written when Phase 3 was still blocked. Task 507
(`generalize_k_fmp_termination_measure_over_ruleapplicationspec`) subsequently delivered Phase 3
(all three K termination lemmas generalized over `RuleApplicationSpec`, extending it from three
to seven fields), unblocking this task's continuation through Phase 4. This session executed
Phase 4 to completion and then hit a new, distinct blocker in the prerequisite for Phase 5.

## What Was Delivered (Phases 1-4, zero-debt, full CI green)

### Phase 1 -- Generic driver definitions (`Saturation.lean`)

`RuleApply Atom`, `modalStepBranchGen`, `modalExpandBranchesGen`, `modalTableauGen`: a generic
tableau driver parametrized over an abstract rule-application function matching
`modalApplyOne`'s signature. K's existing `modalStepBranch`/`modalExpandBranches`/`modalTableau`
kept byte-identical; three bridge theorems relate K to the trivial instantiation.

### Phase 2 -- Structural-hypothesis interface bundle (`GenericDriver.lean`, new file)

`RuleApplicationSpec (apply)`, initially three fields (`freshLocal`, `outputsSubsetUniverse`,
`persistentFresh`), `modalApplyOne_spec : RuleApplicationSpec modalApplyOne` (trivial witness).

### Phase 3 -- Generic FMP termination measure (delivered by task 507, not this session)

All three K termination lemmas (`modalStepBranch_potential_step`, `modalStepBranch_worldBound`,
`modalExpMeasure_step_lt`) generalized over `(apply, spec : RuleApplicationSpec apply)`.
`RuleApplicationSpec` extended from three to seven fields (`rankStep`, `outDegStep`,
`knownWorldsStep`, `branchingLength` added). See task 507's own summary for full detail.

### Phase 4 -- T tableau driver instantiation + `modalApplyOneT_spec` (`TDriver.lean`, new file)

Built `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` as the generic driver
(`Saturation.lean`) instantiated at `apply := modalApplyOneT` (`FrameRules.lean`), and proved
`modalApplyOneT_spec : RuleApplicationSpec modalApplyOneT`, discharging all seven fields.

Strategy: `modalApplyOneT` agrees with `modalApplyOne` exactly outside the two T-relevant
signed-formula shapes (box-positive `T(□φ)@w`, diamond-negative `F(◇φ)@w`,
`modalApplyOneT_eq_of_not_boxPos_diaNeg`), so every field's "not shaped" case reduces directly to
the corresponding K witness from `GenericDriver.lean`'s `modalApplyOne_spec`. At the two
T-relevant shapes, `modalApplyOneT` never mints a world (its own dispatch, composed with K's
already-established "box-positive/diamond-negative are always persistent/notApplicable, never
linear/branching" restriction, forces the same restriction to hold for T, hence the
accessibility output is provably unchanged via `modalApplyOne_fresh_local`) and only ever
*appends* a single self-propagated formula (`modalTBoxSelf`/`modalTDiaNegSelf`) at the source's
own world, drawn from `modalSubfmls` of the source formula. Each field's "shaped" case combines
the corresponding K witness (applied to the same signed formula) with a small direct argument
for the appended self-conjunct.

Two small public downstream-reuse helpers were added to `FmpMeasure.lean`
(`modalUniverse_mem_of_sameWorld_subfml`, `label_mem_modalKnownWorlds`) rather than enlarging
`modalUniverse`, since T's self-propagated formula is already a subformula at an *existing*
world, already inside the unchanged universe.

**Deviation**: the plan's Phase 4 also asked to "generalize the loop-invariant plumbing in
`CompletenessLoop.lean` ... over `apply`/`spec`". This was **not** attempted: `ModalLoopInv`'s
box-negative/diamond-positive witness invariants are tied to concrete rule-shape facts the
current seven-field `RuleApplicationSpec` does not capture, and generalizing them would be a
crux-sized undertaking (extending the spec further, mirroring task 507's own scope) that is not
needed for T specifically -- `modalApplyOneT` agrees with `modalApplyOne` *exactly* on the
box-negative/diamond-positive shapes, so T's own completeness development was expected to reuse
`CompletenessLoop.lean`'s K-specific witness lemmas directly via that agreement rather than
through a generic abstraction. This expectation is what surfaced as Phase 5's blocker (see
below): those K-specific lemmas are `private` and would need T-specific re-derivation, a
several-hundred-line undertaking in its own right.

## What Was Not Delivered (Phases 5-7)

### Phase 5 -- BLOCKED (documented in the plan file)

Producing a `modalHintikkaSetT` witness from an open `modalExpandBranchesT` result (the
prerequisite the T truth lemma needs as its hypothesis) requires a T-analog of the top-loop
lemma `modalExpandBranches_hintikka` (`CompletenessLoop.lean:746`). Its full dependency chain
(`ModalLoopInv`, `modalStep_preserves_invariant`, six further private helper lemmas in
`CompletenessLoop.lean` about box-negative/diamond-positive witness invariants, and
`Completeness.lean`'s parallel saturation-characterisation section --
`modalHintikkaClause`/`modalApplyOne_fst_eq_of_not_box`/`modalHintikkaClause_lift`/
`modalStepBranch_none_saturated`/`modalStepBranch_hintikka_inv`, ~300 more lines) is entirely
`private` and stated directly against the concrete `modalApplyOne` symbol, not against an opaque
`apply` and not against `modalApplyOneT`. This is a several-hundred-line, multi-lemma
development -- fully comparable in size to Phase 4's own 770-line `TDriver.lean` delivery -- not
a one-case fix. The plan's own `[BLOCKED]` fallback anticipated risk only in the truth lemma's
genuinely-new box-positive reflexive-self-edge case (which **is** tractable and remains fully
scoped in the plan for the follow-up task to execute directly); the actual obstruction surfaced
one layer earlier, at the Hintikka-set-production prerequisite. See the plan file's Phase 5
section for the full documented blocker (what was tried, why it's stuck, exactly what four-part
follow-up is needed) and the recommendation to scope it as its own multi-phase task (4-6+ hours
estimated).

### Phases 6-7 -- NOT STARTED (sequentially blocked by Phase 5)

- Phase 6: `tValid_decides`, `instDecidableTValid`.
- Phase 7: Interface documentation, downstream contract, final CI sweep.

Neither was attempted, since both require Phase 5's T truth lemma / `tValid` completeness as a
precondition. No `sorry`/`axiom`/vacuous placeholder was introduced anywhere.

## Plan Deviations

1. **Phase 4**: Did not generalize `CompletenessLoop.lean`'s `ModalLoopInv` over abstract
   `apply`/`spec` (documented above and in the plan file's Phase 4 task-level annotation).
2. **Phase 4**: `FmpMeasure.lean` gained two new public downstream-reuse helper lemmas instead of
   a `modalUniverse` enlargement (T's self-propagated formula needs no enlargement; it is already
   a subformula at an existing world).
3. **Phase 5**: Marked `[BLOCKED]` with a documented four-part follow-up plan, per the escalation
   protocol, rather than attempted with `sorry`. Phases 1-4 preserved green.
4. **Phases 6-7**: Left `[NOT STARTED]` (not attempted out of dependency order).

## Verification

Full CSLib CI run at the end of this session (after Phase 4):
- `lake build` (full project, 3232 jobs) -- green.
- `lake exe checkInitImports` -- clean.
- `lake lint` -- zero new warnings on touched files (`TDriver.lean`, `FmpMeasure.lean`,
  `GenericDriver.lean`); pre-existing unrelated warnings elsewhere in the repo untouched.
- `lake exe lint-style` -- clean.
- `lake test` -- exit 0, full `CslibTests/` suite green.
- `lake exe mk_all --module` -- "No update necessary" (confirms `Cslib.lean`'s manual
  registration of `TDriver.lean` was already correctly placed).
- `lake shake --add-public --keep-implied --keep-prefix` -- zero suggestions on touched files
  (pre-existing, unrelated suggestions on Temporal-logic files elsewhere in the repo untouched).
- `grep -rn "\bsorry\b\|^axiom "` on `TDriver.lean`/`FmpMeasure.lean`/`GenericDriver.lean` --
  zero sorry, zero axiom.
- Zero-regression gate: K's public theorems (`modalTableau_decides`/`instDecidableKValid`)
  unchanged in statement, still green (K-touching files were not modified this session apart
  from the two additive `FmpMeasure.lean` helpers).

## Files Changed (This Session, Phase 4)

- `Cslib/Logics/Modal/Tableau/TDriver.lean` (new, 770 lines) -- `modalStepBranchT`/
  `modalExpandBranchesT`/`modalTableauT`; shape lemmas for the two T-relevant signed-formula
  shapes; unfold lemmas for `modalApplyOneT`'s `.fst`/`.snd` at each shape; the seven
  `RuleApplicationSpec` field proofs; `modalApplyOneT_spec`.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` -- two new public downstream-reuse helper lemmas
  (`modalUniverse_mem_of_sameWorld_subfml`, `label_mem_modalKnownWorlds`).
- `Cslib.lean` -- registers `TDriver.lean`.
- This plan file and summary.

**Note**: the `FmpMeasure.lean` helper addition was made in this session's working tree but its
commit landed under a concurrent session's commit message (task 508's session, no worktree
isolation between concurrent sessions in this environment) rather than this task's own commit --
the content itself is intact and correctly present at `HEAD` (verified via `git show`), mirroring
a precedent already noted in task 507's own summary. `Cslib.lean`, `TDriver.lean`, and this
plan/summary were committed cleanly under `task 503 phase 4: ...` (commit `305356e2`).

## Recommendation

Spawn a dedicated follow-up task scoped specifically to Phase 5's blocker: producing
`modalHintikkaSetT` from an open `modalExpandBranchesT` result via T-specific re-derivations of
`Completeness.lean`'s saturation-characterisation section and `CompletenessLoop.lean`'s
`ModalLoopInv`/fuel-induction machinery (see the plan file's Phase 5 section for the precise
four-part scope). Once that lands, the remainder of Phase 5 (the T truth lemma's genuinely-new
box-positive reflexive-self-edge case, and `tValid` completeness) plus Phases 6-7 can proceed
using the already-committed Phase 1-4 foundation (in particular `modalApplyOneT_spec` and the
`(apply, spec)`-bundled termination wrappers) without re-doing any of this session's work.
