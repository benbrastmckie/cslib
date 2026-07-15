# Handoff: Task 515 -- Phase 4 COMPLETE, Phase 5 2/4 Birth-Key Fields Landed, Two Remain

**Date**: 2026-07-15
**Session**: sess_1784130637_a36e2a (cycle 4)
**Status**: Phase 4 (generic-field preservation) now **COMPLETE**. Phase 5 (birth-key
preservation) 2/4 fields landed (`keysDistinct`, `keysInUniverse` -- the latter added in a
follow-up pass within the same cycle-4 dispatch, after this handoff's original draft; its
"Recommended next dispatch order" below is superseded by the plan file's own updated task list,
which should be treated as authoritative). Phase 6 (pigeonhole) remains `[COMPLETED]` from
cycle 2, unchanged.

**UPDATE (same dispatch, after initial write)**: `keysInUniverse` also landed sorry-free,
confirming this handoff's own prediction that it was "likely the easiest of the three
remaining fields" -- see the plan file's Phase 5 task list for the final per-field status.
Only `keyLowerBd` and `keysTotal` remain `[NOT STARTED]`. The `keysInUniverse` section below is
retained for its (still-accurate, now-historical) reasoning, but its status line is stale --
consult the plan file, not this paragraph, for current status.

## What landed this dispatch (cycle 4)

1. **Unblocked Phase 4 in full**, closing the gap documented in handoff
   `02_phase4-bclosure-contiguity-gap.md`:
   - Added the 12th `S5LoopInv` field `worldsContiguous : modalMaxWorld b + 1 =
     (modalKnownWorlds b).length` (exactly the recommendation from handoff 02), plus its
     preservation lemma `modalStepBranchS5g_preserves_worldsContiguous`.
   - Built a substantial new "`bClosure` support" layer of local re-derivations mirroring
     `FmpMeasure.lean`'s private `modalApplyOne_outputs_subset` family (all unavailable
     cross-file), swapped to `modalUniverseS5`/`modalWorldBoundS5`:
     `modalSubfmls_trans_S5`, `mem_modalUniverseS5_of`/`_of'`, `modalUniverseS5_mem_formula`/
     `_mem_label`, `mem_boxPositivesOf_S5`, `boxProps_outputs_subset_S5`,
     `diaNegProps_outputs_subset_S5`, `modalApplyOne_diamondPos_outputs_subset_S5`,
     `modalApplyOne_boxNeg_outputs_subset_S5`, `modalApplyOne_outputs_subset_S5` (K-level top
     dispatch), `modalApplyOneS5_outputs_subset` (S5-merge-aware top dispatch).
   - Also added `modalApplyOneS5_knownWorlds_step` (S5 analogue of K's
     `modalApplyOne_knownWorlds_step`) and `modalApplyOneS5_boxPos_diaNeg_eq` as byproducts.
   - Landed `modalStepBranchS5g_preserves_bClosure` and `_preserves_eClosure` sorry-free.
   - `eClosure` turned out MUCH simpler than `bClosure` once treated as consuming `bClosure` as
     an ambient hypothesis: the only formula ever appended to `e` is the trigger `sf` itself,
     already known to be in `modalUniverseS5 φ₀` via `hbClosure sf hsfmem` directly -- no
     mint-case/contiguity reasoning needed at all.
2. **Phase 5's crux, `keysDistinct`, landed sorry-free** on the first real attempt after
   authoring one new helper, `modalStepBranchS5gKeyed_keys_shape` (mirroring the file's
   established `_expanded_shape`/`_acc_shape` pattern), which characterizes `newKeys`'s shape:
   either `keys` unchanged, or `keys` grown by exactly one fresh
   `(modalNextWorld b, successorBirthContentS5 φ₀ b s φ sf.label)` entry at one of the two
   K-minting shapes when the keyed guard is unblocked. Given this, `keysDistinct`'s
   preservation is a direct 4-way case split (old/old, old/fresh, fresh/old, fresh/fresh) using
   `blockingWorldS5Keyed_none_fresh` (Phase 3) for the two mixed cases -- confirming the
   keys-aware guard design works exactly as Phase 3 intended, with zero live-set reasoning.

Commits: `caaea293` (Phase 4 complete: worldsContiguous + bClosure/eClosure), plus this
dispatch's uncommitted-at-write-time `keysDistinct` addition (commit hash TBD by the time this
handoff is read -- check `git log --oneline -- Cslib/Logics/Modal/Tableau/S5Simplification.lean`
for the latest).

Full CI green at both commits: `lake build` (3239/3239), `lake exe checkInitImports`,
`lake exe lint-style`, `lake lint` (0 new warnings; the 1 pre-existing `PrimeExclusion.lean`
error is untouched/unrelated), `lake test` (exit 0), `lake shake` (0 new import-minimization
suggestions for `S5Simplification.lean`). Zero `sorry`, zero new axioms in
`S5Simplification.lean` (`lean_verify` on the new lemmas: only `propext`/`Classical.choice`/
`Quot.sound`).

## What remains: three birth-key fields (`keyLowerBd`, `keysTotal`, `keysInUniverse`)

These were **not attempted** this dispatch (budget was spent on Phase 4 + `keysDistinct`).
None are `[BLOCKED]` -- they are `[NOT STARTED]`, genuinely open work with a concrete plan
below, not a discovered obstruction.

### `keyLowerBd` (likely the hardest of the three)

**Statement**: `∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w`.

**Preservation obligation**: `∀ w k, (w, k) ∈ newKeys → ∀ b' ∈ newBs, k ⊆ relevantSetFinset φ₀ b' w`.

- **Old-key case** ((w,k) ∈ keys unchanged): straightforward via `relevantSetFinset_mono`
  (`LoopChecking.lean:344`, public) once you know `b ⊆ b'` (i.e. `∃ xs, b' = xs ++ b`, already
  established generically via the `hbb'`-style helper pattern used throughout Phase 4's
  lemmas). Combine: old `keyLowerBd` gives `k ⊆ relevantSetFinset φ₀ b w`; `relevantSetFinset_mono`
  gives `relevantSetFinset φ₀ b w ⊆ relevantSetFinset φ₀ b' w`; transitivity closes it.
- **Fresh-key case** (mint step, `w = modalNextWorld b`, `k = successorBirthContentS5 φ₀ b s φ
  sf.label`): this is the genuinely new work. Need `k ⊆ relevantSetFinset φ₀ b' (modalNextWorld
  b)` where `b'` is the SPECIFIC minted branch (`newForms ++ b`, containing the witness formula
  and box/diamond-context copies, all at label `modalNextWorld b`). `successorBirthContentS5`'s
  membership unfolds to three cases (`Finset.mem_insert`/`Finset.mem_filter`):
  1. The witness `(s, φ)` itself -- need `⟨s, φ, modalNextWorld b⟩ ∈ b'`. This should be the
     easiest: `b'`'s `newForms` always HEADS with the witness formula (see `Rules.lean`'s
     `diamondPos`/`boxNeg` definitions, `witness :: boxProps ++ diaNegProps`), so
     `List.mem_cons_self`-style reasoning plus `List.mem_append_left` should close it directly
     -- but this requires literally unfolding `modalApplyOne`'s `diamondPos`/`boxNeg` arms (or
     finding/authoring a witness-membership lemma; check if one already exists, e.g. search
     `mem.*witness` or similar in `FmpMeasure.lean`/`Rules.lean`).
  2. A box-positive pair `(pos, ψ)` with `T(□ψ)@w ∈ b`: need `⟨pos, ψ, modalNextWorld b⟩ ∈ b'`.
     This is the CONVERSE direction of `modalApplyOne_boxPos_outputs_subset`/
     `boxProps_outputs_subset_S5` (which prove membership-implies-subformula, not
     subformula-implies-membership). You need an "introduction" lemma: given
     `T(□ψ)@w ∈ b`, EITHER `T(ψ)@w' ∈ b` already (then it is in `b'` via `b ⊆ b'`) OR
     `T(ψ)@w' ∉ b` and it was freshly added by the `boxProps` `filterMap` (then it is in
     `newForms` directly). This dichotomy is exactly what the `if b.any (· == sf') then none
     else some sf'` guard inside `boxProps`'s construction encodes -- a short case split on
     that `if`, not a deep new lemma.
  3. A diamond-negative pair `(neg, ψ)` with `F(◇ψ)@w ∈ b`: symmetric to (2) via `diaNegProps`.

  **Concrete next step**: author two small "introduction" lemmas mirroring (2)/(3)'s dichotomy
  (`boxProps_mem_of`/`diaNegProps_mem_of`-style, analogous to how `modalS5BoxAll_mem_of` was
  authored in Phase 2 for the S5 arms) directly against K's `Rules.lean`
  `diamondPos`/`boxNeg` raw expressions (the same raw `filterMap` terms already unfolded inside
  `modalApplyOne_diamondPos_outputs_subset_S5`/`modalApplyOne_boxNeg_outputs_subset_S5`'s own
  proofs -- you have the exact expressions already, just need the introduction direction
  instead of elimination).

### `keysTotal`

**Statement**: `∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys`.

**Preservation obligation**: `∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ newKeys`, for each
`b' ∈ newBs`.

Plan (per the original plan's own framing): case on whether `w` was ALREADY known on `b` (then
reuse the old `keysTotal` witness, `keys ⊆ newKeys` always since `newKeys` only ever appends)
or is the FRESHLY minted world (`w = modalNextWorld b`, only possible in the mint case, use the
fresh key `keys'`'s own new entry as witness, trivially `(modalNextWorld b, successorBirthContentS5
...) ∈ newKeys` by construction). The dichotomy "which known worlds of `b'` are new vs old" is
EXACTLY what `modalApplyOneS5_knownWorlds_step` (landed this dispatch, Phase 4) already gives
you combined with `accKnown` (a Phase 4-landed hypothesis) -- this should compose fairly
directly from already-landed infrastructure, likely the most tractable of the three remaining
fields alongside `keysInUniverse`.

### `keysInUniverse`

**Statement**: `∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀`.

**Preservation obligation**: `∀ w k, (w, k) ∈ newKeys → k ⊆ signedSubfmls φ₀`.

- Old-key case: direct from the unchanged `keysInUniverse` hypothesis.
- Fresh-key case: `successorBirthContentS5 φ₀ b s φ w` is, BY CONSTRUCTION, `insert (s, φ)
  (Finset.filter (fun p => ...) (signedSubfmls φ₀))` -- the filtered part is trivially `⊆
  signedSubfmls φ₀` (`Finset.filter_subset`), and the witness `(s, φ)` needs `φ ∈ modalSubfmls
  φ₀` (NOTE: `signedSubfmls φ₀` vs `modalSubfmls φ₀` -- check the exact relationship/definition
  of `signedSubfmls`, likely `(Sign.pos, ·) :: (Sign.neg, ·) ::` mapped over `modalSubfmls φ₀`
  or similar; grep `def signedSubfmls` in `LoopChecking.lean`), which follows from `bClosure`
  (already a Phase-4-landed hypothesis) + `hsf ∈ b` + `modalSubfmls_trans_S5` (already built
  this dispatch), IDENTICAL reasoning to what `bClosure`'s own mint case already used for the
  witness's formula-closure. **This is likely the easiest of the three remaining fields** --
  almost a direct restatement of work already done for `bClosure`.

## Recommended next dispatch order

1. `keysInUniverse` first (easiest, reuses `bClosure`'s already-built witness-closure
   reasoning almost verbatim).
2. `keysTotal` second (reuses `modalApplyOneS5_knownWorlds_step` + `accKnown`, both landed).
3. `keyLowerBd` last (needs the two new "introduction" lemmas for `boxProps`/`diaNegProps`
   membership -- genuinely new work, but bounded in scope, mirroring the existing
   elimination-direction lemmas' raw expressions).
4. Once all four Phase 5 fields land, the full termination chain (Phases 3-6) is closed, since
   Phase 6 (pigeonhole) is already `[COMPLETED]`.
5. Phase 7 (soundness bridge, `FrameSoundness.lean`) is independent of Phases 3-6 (forks after
   the landed Phase 1) and was NOT attempted this dispatch either -- still a good candidate to
   attempt in parallel with, or instead of, the remaining Phase 5 work, since it does not depend
   on it.

## Reusable infrastructure inventory (as of end of cycle 4)

- **Phase 3**: `blockingWorldS5Keyed`, `blockingWorldS5Keyed_eq_birthContent`,
  `blockingWorldS5Keyed_none_fresh`, `S5LoopInv` (now **twelve** fields, including
  `keysKnown` and `worldsContiguous`), `modalStepBranchS5gKeyed`,
  `modalStepBranchS5gKeyed_expanded_shape`, `modalStepBranchS5gKeyed_acc_shape`,
  `modalStepBranchS5gKeyed_keys_shape` (new this dispatch).
- **Phase 4 (complete)**: all six generic-field preservation lemmas
  (`modalStepBranchS5g_preserves_{bClosure,eNodup,eClosure,accFresh,accKnown,outDegEq}`) plus
  `modalStepBranchS5g_preserves_worldsContiguous`.
- **`bClosure`-support layer** (new this dispatch, reusable for `keysInUniverse`'s witness
  reasoning): `modalSubfmls_trans_S5`, `mem_modalUniverseS5_of`/`_of'`,
  `modalUniverseS5_mem_formula`/`_mem_label`, `mem_boxPositivesOf_S5`,
  `boxProps_outputs_subset_S5`, `diaNegProps_outputs_subset_S5`,
  `modalApplyOne_diamondPos_outputs_subset_S5`, `modalApplyOne_boxNeg_outputs_subset_S5`,
  `modalApplyOne_outputs_subset_S5`, `modalApplyOneS5_outputs_subset`,
  `modalApplyOneS5_knownWorlds_step`, `modalApplyOneS5_boxPos_diaNeg_eq`.
- **Phase 6 (complete)**: `modalKnownWorlds_length_le_worldBoundS5`,
  `modalKnownWorlds_nodup_S5`, `modalKnownWorlds_fold_nodup_S5` (all relocated earlier in the
  file this dispatch so Phase 4's `worldsContiguous` preservation could consume them).
- **Phase 5 (1/4 landed)**: `modalStepBranchS5g_preserves_keysDistinct`.
- **Contiguity bookkeeping** (new this dispatch): `modalMaxWorld_append_eq_of_forall_le_S5`,
  `modalMaxWorld_append_single_S5`, `modalKnownWorlds_length_append_of_known_S5`,
  `modalKnownWorlds_length_append_single_S5`, `modalNextWorld_not_mem_modalKnownWorlds_S5`,
  `mem_successorsOf_hasEdge_S5`.
