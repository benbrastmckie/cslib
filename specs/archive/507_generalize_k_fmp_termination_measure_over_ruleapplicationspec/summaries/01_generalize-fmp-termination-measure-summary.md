# Implementation Summary: Task #507 — Generalize K FMP Termination Measure over RuleApplicationSpec

- **Task**: 507 - Generalize the K FMP termination measure over `RuleApplicationSpec`
- **Status**: [COMPLETED]
- **Plan**: `plans/01_generalize-fmp-termination-measure.md` (all 8 phases)

## Outcome

All three K termination lemmas (`modalStepBranch_potential_step`, `modalStepBranch_worldBound`,
`modalExpMeasure_step_lt`) are now proven for an abstract `(apply : RuleApply Atom)` given a
`RuleApplicationSpec apply` witness, via a chain of `_gen` lemmas in `FmpMeasure.lean` and
`(apply, spec)`-bundled wrapper theorems in `GenericDriver.lean`. K's own concrete lemma
statements are byte-unchanged (confirmed by diff against pre-507 commit `d5b24e67`), now proven
as one-line corollaries via the `modalStepBranch_eq` bridge. Zero `sorry`, zero new `axiom`,
full CSLib CI green at every phase, and no net new lint/shake debt across the two files (81
warnings, at or below the pre-507 baseline throughout).

This unblocks task 503's Phase 3 (and thus its Phases 4-7: T driver instantiation, T truth
lemma, `Decidable (tValid φ)`) and is a prerequisite for tasks 504 (S5/KB5) and 505 (B).

## What Was Delivered, By Phase

- **Phase 1**: Extended `RuleApplicationSpec` with three new per-single-call step obligations
  (`rankStep`, `outDegStep`, `knownWorldsStep`), each discharged for `modalApplyOne` by
  extracting the K-specific proof body formerly inlined inside
  `modalStepBranch_exists_rank'`/`modalStepBranch_preserves_outDegEq`/`modalStepBranch_knownWorlds`
  into standalone lemmas (`modalApplyOne_rank_step`/`_outDeg_step`/`_knownWorlds_step`,
  `FmpMeasure.lean`). Pure refactor-and-generalize; zero proof-content change.
- **Phase 2**: Generalized `modalStepBranch_preserves_outDegEq` to
  `modalStepBranch_preserves_outDegEq_gen`. Found `outDeg_le_of_expandedNodup` and its
  supporting private helpers already fully rule-agnostic (no change needed).
- **Phase 3**: Generalized `modalStepBranch_exists_rank'` to `modalStepBranch_exists_rank'_gen`.
  Found its own body needs no field beyond `rankStep` (no separate mint-point field).
- **Phase 4**: Generalized `modalStepBranch_preserves_accTargetsKnown` (needs only `freshLocal`),
  `modalStepBranch_knownWorlds` (needs `knownWorldsStep`), and `modalStepBranch_eClosure` (fully
  rule-agnostic, no field needed) to their `_gen` forms.
- **Phase 5 (the crux)**: Generalized `modalStepBranch_potential_step` to
  `modalStepBranch_potential_step_gen`, closing sorry-free on the **first attempt**. Confirmed
  the Phase 1 finding: the crux's own body, once its five callee lemmas are generalized, is pure
  arithmetic (`geomCap_zero`/`geomCap_succ`/`Nat`/`ring`) independent of `apply` — no additional
  spec field was needed beyond the six established by Phases 1-4. Also generalized
  `modalStepBranch_preserves_expandedNodup` (a residual dependency, fully rule-agnostic).
- **Phase 6**: Generalized `modalStepBranch_worldBound` to `modalStepBranch_worldBound_gen`,
  reusing the Phase 5 crux; the remainder is pure arithmetic (`geomCap_le_pow` + pow monotonicity).
- **Phase 7**: Generalized `modalExpMeasure_step_lt` to `modalExpMeasure_step_lt_gen`. Discovered
  and added a **seventh** `RuleApplicationSpec` field, `branchingLength` (every `.branching`
  result has exactly two sub-branches — a fixed-arity catalog fact, not an aggregate-behaviour
  fact like the other six), discharged for `modalApplyOne` via the pre-existing
  `modalApplyOne_branching_length`.
- **Phase 8**: Confirmed all three K corollaries byte-identical to pre-507 statements; confirmed
  `CompletenessLoop.lean` (read-only) still typechecks against the whole Tableau tree; rewrote
  `GenericDriver.lean`'s module docstring into a single "Sufficiency" section documenting the
  final seven-field set and the downstream-reuse contract (T/S5/B discharge pattern, S4
  exclusion, unchanged); ran the full CI pipeline end-to-end; swept all 29 new/changed
  declarations for axiom safety.

## Architectural Discovery (documented in the plan's "Architectural Note")

`GenericDriver.lean` imports `FmpMeasure.lean` to state `RuleApplicationSpec`'s fields (which
reference `FmpMeasure.lean`-defined predicates: `accFreshInv`, `accTargetsKnown`,
`modalKnownWorlds`, `isMintingShaped`, `modalUniverse`, etc.). This means `FmpMeasure.lean`
cannot import `GenericDriver.lean` back, so a `_gen` lemma physically located in
`FmpMeasure.lean` cannot take a bundled `spec : RuleApplicationSpec apply` parameter directly.

**Resolution**: every `_gen` lemma in `FmpMeasure.lean` takes the *raw, unbundled* hypothesis
it needs (textually identical to the corresponding `RuleApplicationSpec` field's type) as an
explicit parameter. `GenericDriver.lean` then supplies a thin corollary wrapper
(`modalStepBranchGen_preserves_outDegEq`, `_exists_rank'`, `_preserves_accTargetsKnown`,
`_knownWorlds`, `_eClosure`, `_potential_step`, `_worldBound`, `_expMeasure_step_lt`) unpacking
`spec.field` into each raw parameter — giving downstream instances (T/S5/B) the ergonomic
`(apply, spec)` calling convention the plan originally specified, without an import cycle.

## Final `RuleApplicationSpec` Field Set (Seven Fields)

| Field | Provenance | Discharge for `modalApplyOne` |
|---|---|---|
| `freshLocal` | Task 503 Phase 2 | `modalApplyOne_fresh_local` |
| `outputsSubsetUniverse` | Task 503 Phase 2 | `modalApplyOne_outputs_subset` |
| `persistentFresh` | Task 503 Phase 2 | `modalApplyOne_persistent_props` |
| `rankStep` | Task 507 Phase 1 | `modalApplyOne_rank_step` |
| `outDegStep` | Task 507 Phase 1 | `modalApplyOne_outDeg_step` |
| `knownWorldsStep` | Task 507 Phase 1 | `modalApplyOne_knownWorlds_step` |
| `branchingLength` | Task 507 Phase 7 | `modalApplyOne_branching_length` |

## Verification

Every phase ended at a green `lake build`. Final sweep (Phase 8):
- `lake build` (full project): green (3231 jobs).
- `lake exe checkInitImports`: green.
- `lake lint`: one pre-existing, unrelated failure (`PrimeExclusion.lean`); zero new warnings on
  either changed file.
- `lake exe lint-style`: green.
- `lake test`: green (`CslibTests` suite).
- `lake exe mk_all --module`: wants to reorder unrelated concurrent-session imports in
  `Cslib.lean` — reverted (out of scope for this task).
- `lake shake --add-public --keep-implied --keep-prefix`: 81 warnings on the two touched files,
  at or below the pre-507 baseline (82) throughout every phase.
- `#print axioms` on all 29 new/changed top-level declarations: every one is
  `{propext, Classical.choice, Quot.sound}` (a subset of the standard trio) — zero sorry, zero
  new axiom.
- K's three public corollary statements (`modalStepBranch_potential_step`,
  `modalStepBranch_worldBound`, `modalExpMeasure_step_lt`): byte-identical to their pre-507
  forms (`git show d5b24e67`), confirmed by direct diff.
- `CompletenessLoop.lean`: read-only, untouched, still typechecks against the whole Tableau tree.

## Plan Deviations

- **Architectural**: `_gen` lemmas in `FmpMeasure.lean` take raw unbundled hypotheses instead of
  a bundled `spec : RuleApplicationSpec apply` parameter, to avoid an import cycle (see above).
  Fully documented in the plan's "Architectural Note" (added after Phase 1, before Phase 2).
- **Field-set growth**: the plan anticipated the field set might grow during Phases 2-5; it grew
  by three fields in Phase 1 (`rankStep`/`outDegStep`/`knownWorldsStep`, anticipated) and by one
  further field in Phase 7 (`branchingLength`, a fixed-arity catalog fact the plan's Phase 7 text
  did not specifically anticipate but whose "Non-Goals"/"Risks" section allowed for).
  Both additions are documented inline in the plan's Phase 1/7 task annotations and in
  `GenericDriver.lean`'s module docstring.
- **No `[BLOCKED]` needed**: the Phase 5 crux — explicitly flagged in the plan as the
  make-or-break phase most likely to require a `[BLOCKED]` fallback — closed sorry-free on the
  first attempt, using exactly the fields Phases 1-4 already established.
- **Git note**: several commits during this session's phase-by-phase work were incidentally
  swept into a concurrently-running, unrelated session's commits (task 508) due to that session's
  broader `git add` scope while this session's working tree held uncommitted Phase 2 changes.
  The Lean content itself is intact and correctly committed (verified via `git show`); only the
  commit *message* attribution for that one increment differs from this task's convention. All
  other phases (1, 3-7) committed cleanly under proper `task 507 phase N: ...` messages.

## Artifacts

- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — `RuleApplicationSpec` extended with four new
  fields (`rankStep`, `outDegStep`, `knownWorldsStep`, `branchingLength`); `modalApplyOne_spec`
  re-discharged; eight `(apply, spec)`-bundled wrapper theorems; finalized "Sufficiency"
  module docstring.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — twelve new `_gen` lemmas (generic
  re-derivations of the full rule-dependent dependency chain and the three top-level step
  lemmas over an abstract `apply`); three new standalone per-call witness lemmas
  (`modalApplyOne_rank_step`/`_outDeg_step`/`_knownWorlds_step`); nine existing K lemmas
  re-proved as byte-identical-statement corollaries; world-agnostic size bounds
  (`modalUniverse`/`modalWork`/`modalExpMeasure`/`modalFuel`/`modalWorldBound`) left unchanged.
- This summary.
