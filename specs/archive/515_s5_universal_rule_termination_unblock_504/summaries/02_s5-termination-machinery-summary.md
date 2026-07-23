# Implementation Summary: S5 Universal-Rule Termination Machinery (v2 plan, round 2, cycles 2-9)

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Plan**: `plans/02_s5-termination-machinery.md`
- **Status**: PARTIAL -- **Phases 1-7 are now COMPLETED** (termination chain P1-P6 closed across
  cycles 2, 4, 5, 6; see commits `d4e7ed73`/`49ed521b` for the final Phase 5 fields and
  `bfbe032f` for the Phase 5-complete handoff. **Phase 7 (soundness bridge) is now fully
  `[COMPLETED]`** as of cycle 8: `modalTableauS5_sound` lands sorry-free via a bespoke
  S5-specialized fuel induction (`modalStepBranchS5_preserves_satIn` +
  `modalExpandBranchesS5_closed_unsatIn`), reusing the cycle-7 semantic core
  (`accReachableInv`, `modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn`) as black boxes. Phases
  **Phase 8 is `[BLOCKED]` and Phase 9 transitively `[BLOCKED]`** as of cycle 9 -- see the
  "Cycle 9" section appended at the end of this summary for what landed, the exact open goal, and
  two structural findings that re-scope Phase 8.
- **Commits cycle 2**: `db5b837a` (Phase 4: accFresh/accKnown/outDegEq), `8e4a17ba` (Phase 6:
  pigeonhole world bound)
- **Commits cycle 4**: `caaea293` (Phase 4 COMPLETE: 12th field `worldsContiguous` +
  `bClosure`/`eClosure`), `fa816254` (Phase 5: `keysDistinct`), `f04817cf` (Phase 5:
  `keysInUniverse`)
- **Commits cycles 5-6** (Phase 5 completion, termination chain closed): `d4e7ed73` (`keysTotal`),
  `49ed521b` (`keyLowerBd` -- Phase 5 COMPLETE, Phases 3-6 all closed)
- **Commits cycle 7** (Phase 7 partial): `e2430463` (`modalApplyOneS5_fresh_local`
  + `accReachableInv` scaffolding), `a1018c6b`
  (`modalStepBranchS5_preserves_accReachableInv`), `4dd7d0e7` (`modalS5BoxAll_soundIn` /
  `modalS5DiaNegAll_soundIn`)
- **Commits cycle 8** (this dispatch, Phase 7 COMPLETE): `modalTableauS5_sound` assembly --
  `S5SoundInv`, `modalStepBranchS5_preserves_satIn`, `modalExpandBranchesS5_closed_unsatIn`,
  `modalTableauS5_sound` (see the final commit hash in this cycle's handoff `07_*.md`)
- **Handoffs**:
  - `handoffs/01_phase4-generic-field-preservation.md` (cycle-2-prior dispatch: proof template,
    gotchas)
  - `handoffs/02_phase4-bclosure-contiguity-gap.md` (cycle 2: exact `bClosure`/`eClosure` blocker
    and recommended 12th-invariant-field fix -- **fully resolved this cycle 4 dispatch**)
  - `handoffs/03_phase5-keysdistinct-landed-keylowerbd-scope.md` (cycle 4: `keysDistinct`/
    `keysInUniverse` landed; concrete next-step plan for `keyLowerBd`/`keysTotal`)
  - `handoffs/05_phase5-complete-termination-chain-closed.md` (cycle 6: Phase 5 complete,
    termination chain P3-P6 closed)
  - `handoffs/06_phase7-reachability-soundIn-landed-assembly-remains.md` (cycle 7: Phase 7's
    semantic core landed; exact assembly gap and two viable strategies)
  - `handoffs/07_phase7-complete-modalTableauS5-sound-landed.md` (cycle 8, **this dispatch**:
    Phase 7 fully complete; Phase 8 entry point for the next dispatch)

## Cycle 2 Context

This dispatch resumed from a quota-halted prior session. Step 0 recovered ~364 lines of
UNVERIFIED mid-edit WIP from git stash (`task515-cycle2-WIP`) via `git stash pop` (clean, no
conflicts), covering draft `accFresh`/`accKnown`/`outDegEq` preservation lemmas. The stash
restored cleanly but did not build; one outstanding `rw` failure in `outDegEq`'s proof was
diagnosed and fixed (see "Central finding" below). All three stashed lemmas then built,
verified, and were committed. Phase 6's pigeonhole bound was then authored fresh (not present in
the stash) and landed in full. Phase 4's `bClosure`/`eClosure` were then investigated and found
to require additional infrastructure not achievable safely within this dispatch's remaining
budget (documented as a precise, actionable blocker rather than rushed with `sorry` or a
vacuous placeholder).

## Per-Phase Status Ledger (as of cycle 8, current)

| Phase | Status | Notes |
|-------|--------|-------|
| 1. Frame surface + S5 world bound + universe | COMPLETED | commit `66021669` |
| 2. Live-set guard + guarded rule (preserved scaffold) | COMPLETED | commit `aa9015d6` |
| 3. Keys-aware guard redesign + extended `S5LoopInv` | COMPLETED | commit `4f41f3a4`; extended to 12 fields cycle 4 (`caaea293`) |
| 4. Generic-field preservation lemmas | COMPLETED | all six generic fields plus the 12th field land sorry-free |
| 5. Birth-key preservation lemmas | COMPLETED | all four birth-key fields land sorry-free (cycles 4-6) |
| 6. Pigeonhole world bound | COMPLETED | `modalKnownWorlds_length_le_worldBoundS5`, commit `8e4a17ba` |
| 7. Soundness bridge `modalTableauS5_sound` | **COMPLETED (cycle 8)** | `modalTableauS5_sound` lands sorry-free via bespoke `S5SoundInv`/`modalStepBranchS5_preserves_satIn`/`modalExpandBranchesS5_closed_unsatIn`, reusing cycle-7's semantic core |
| 8. Spec-free Hintikka lift + fuel + completeness + decidability | NOT STARTED | highest-risk frontier per plan; does NOT depend on Phase 7 (depends on 6 and 3, both landed) -- ready for the next dispatch |
| 9. 5/KB5 validity + completeness | NOT STARTED | gated on Phase 8 |

## Per-Phase Status Ledger (as of cycle 4, historical)

| Phase | Status | Notes |
|-------|--------|-------|
| 1. Frame surface + S5 world bound + universe | COMPLETED (prior dispatch) | commit `66021669` |
| 2. Live-set guard + guarded rule (preserved scaffold) | COMPLETED (prior dispatch) | commit `aa9015d6` |
| 3. Keys-aware guard redesign + extended `S5LoopInv` | COMPLETED (prior dispatch) | commit `4f41f3a4`; extended to 12 fields cycle 4 (`caaea293`) |
| 4. Generic-field preservation lemmas | **COMPLETED** | `eNodup` (cycle 2, `12f32499`); `accFresh`/`accKnown`/`outDegEq` (cycle 2, `db5b837a`); `bClosure`/`eClosure`/`worldsContiguous` (cycle 4, `caaea293`) -- all six generic fields plus the new 12th field now land sorry-free |
| 5. Birth-key preservation lemmas | **COMPLETED** (cycles 5-6) | `keysDistinct`/`keysInUniverse` (cycle 4); `keysTotal` (cycle 5, `d4e7ed73`); `keyLowerBd` (cycle 6, `49ed521b`) -- all four birth-key fields land sorry-free |
| 6. Pigeonhole world bound | **COMPLETED** | `modalKnownWorlds_length_le_worldBoundS5`, cycle 2, commit `8e4a17ba` |
| 7. Soundness bridge `modalTableauS5_sound` | **PARTIAL** (cycle 7, this dispatch) | `modalApplyOneS5_fresh_local`, `accReachableInv` (+base case, single-step preservation), `reachable_imp_related_s5`, `accReachableInv_related_s5`, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn` all landed sorry-free; final fuel-induction assembly (`modalTableauS5_sound`) not attempted -- see handoff 06 for the precise structural gap and two viable completion strategies |
| 8. Spec-free Hintikka lift + fuel + completeness + decidability | NOT STARTED | highest-risk frontier per plan; does NOT depend on Phase 7 (depends on 6 and 3, both landed) -- available for parallel/independent attempt |
| 9. 5/KB5 validity + completeness | NOT STARTED | gated on Phase 8 |

## What Was Delivered This Dispatch (Cycle 2)

### Phase 4: `accFresh`/`accKnown`/`outDegEq` (commit `db5b837a`)

Both `modalStepBranchS5g_preserves_accFresh` and `_preserves_accKnown` built cleanly from the
recovered stash with no changes needed. `modalStepBranchS5g_preserves_outDegEq`'s stashed proof
had one outstanding build error, fixed as follows:

**Central finding (reusable pattern)**: the stashed proof's final step,
`rw [modalApplyOne_outDeg_step ..., ← modalApplyOneS5_eshape_eq ...]`, failed with "did not find
occurrence of the pattern" even though the pattern was visibly present in the goal's pretty-print.
Root cause: Lean compiles each `match ... with` expression to its own auto-generated matcher
auxiliary constant, PER OCCURRENCE in the source -- so two syntactically-identical `match`
expressions written in two different lemmas' statements (`modalApplyOne_outDeg_step` and
`modalApplyOneS5_eshape_eq`) are backed by two DIFFERENT matcher constants, which `rw`'s
`kabstract` cannot unify (it requires the same head symbol), even though `exact`/term-mode
elaboration succeeds via `isDefEq` (which unfolds matcher auxiliaries during whnf and finds them
defeq). **Fix**: bridge the two lemmas via a term-mode composition instead of `rw`:
```lean
have hfull := (modalApplyOne_outDeg_step ...).trans
  (congrArg (fun l => (List.filter ... l).length) (modalApplyOneS5_eshape_eq ...).symm)
```
then `rw [hfull]` (a plain, single-instance substitution, safe) and case-split cleanly. Also
required one `omit [Hashable Atom] in` annotation to clear a new `unusedSectionVars` warning
introduced by the lemma (caught by `lake shake`, not `lake lint`, but fixed per the lint
prevention rules regardless).

### Phase 6: Pigeonhole world bound (commit `8e4a17ba`)

`modalKnownWorlds_length_le_worldBoundS5 φ₀ b keys hTotal hDistinct hInUniv` -- a **static**
lemma (per the resume task's explicit directive) requiring only `S5LoopInv`'s three birth-key
structural fields on a fixed `(b, keys)` pair, no step-preservation reasoning. Proof: inject each
known world into `(signedSubfmls φ₀).powerset` via a classical choice of its birth key
(`keysTotal`); `keysDistinct` gives injectivity; `keysInUniverse` gives codomain membership; then
`Finset.card_le_card_of_injOn` + `List.toFinset_card_of_nodup` + the pre-existing
`signedSubfmls_powerset_card_le` (`LoopChecking.lean`, reused as-is since `modalWorldBoundS5 φ₀`
is definitionally `modalWorldBoundS4 φ₀`, both `2 ^ (2 * (modalSubfmls φ₀).length)`). Added two
supporting local re-derivations (`modalKnownWorlds_nodup_S5`, `modalKnownWorlds_fold_nodup_S5`)
mirroring the file's existing pattern of re-deriving `FmpMeasure.lean`'s private lemmas locally.

### Phase 4: `bClosure`/`eClosure` -- BLOCKED at cycle 2, RESOLVED at cycle 4

Cycle 2 found a **genuine gap** consuming Phase 6's pigeonhole bound to close `bClosure`/
`eClosure`'s mint-case obligation: Phase 6 bounds the *count* of known worlds, but placing a
freshly-minted formula (at label `modalNextWorld b`) into `modalUniverseS5 φ₀` needs a bound on
the *numeric value* `modalNextWorld b`. This was scoped in full detail (with a concrete
recommended field statement and per-case proof sketch) in
`handoffs/02_phase4-bclosure-contiguity-gap.md`, and left `[ ]`/`[BLOCKED]` rather than rushed.

**Cycle 4 resolved this in full**, following handoff 02's recommendation almost verbatim:

1. Added the 12th `S5LoopInv` field `worldsContiguous : modalMaxWorld b + 1 =
   (modalKnownWorlds b).length` and its preservation lemma
   `modalStepBranchS5g_preserves_worldsContiguous` (case analysis via
   `modalStepBranchS5gKeyed_acc_shape`: non-mint case appends at already-known labels, both
   sides unchanged; mint case appends at exactly `modalNextWorld b`, both sides increment by
   1). Needed six new local re-derivations for the append-invariance facts
   (`modalMaxWorld_append_eq_of_forall_le_S5`, `modalMaxWorld_append_single_S5`,
   `modalKnownWorlds_length_append_of_known_S5`, `modalKnownWorlds_length_append_single_S5`,
   `modalNextWorld_not_mem_modalKnownWorlds_S5`, plus relocating the pre-existing
   `modalKnownWorlds_nodup_S5` earlier in the file so Phase 4 could consume it before Phase 6's
   own definition site).
2. This alone was NOT sufficient for `bClosure` -- also needed a substantial new "`bClosure`
   support" layer mirroring `FmpMeasure.lean`'s private `modalApplyOne_outputs_subset` /
   `boxProps_outputs_subset` / `diaNegProps_outputs_subset` /
   `modalApplyOne_diamondPos_outputs_subset` / `modalApplyOne_boxNeg_outputs_subset` machinery
   (all `private`, hence unavailable cross-file), re-derived locally against
   `modalUniverseS5`/`modalWorldBoundS5`: `modalSubfmls_trans_S5`, `mem_modalUniverseS5_of`/
   `_of'`, `modalUniverseS5_mem_formula`/`_mem_label`, `mem_boxPositivesOf_S5`,
   `boxProps_outputs_subset_S5`, `diaNegProps_outputs_subset_S5`,
   `modalApplyOne_diamondPos_outputs_subset_S5`, `modalApplyOne_boxNeg_outputs_subset_S5`, the
   K-level top dispatch `modalApplyOne_outputs_subset_S5`, and finally the S5-merge-aware top
   dispatch `modalApplyOneS5_outputs_subset` that `bClosure`'s own preservation consumes
   directly. Also produced `modalApplyOneS5_knownWorlds_step` (an S5 analogue of K's
   `modalApplyOne_knownWorlds_step`) and `modalApplyOneS5_boxPos_diaNeg_eq` as byproducts, used
   by `worldsContiguous`'s own preservation proof.
3. `eClosure` turned out to be MUCH simpler once stated as consuming `bClosure` as an ambient
   hypothesis: the only formula ever appended to `e` is the trigger `sf` itself, and `sf ∈ b`
   with `bClosure` gives `sf ∈ modalUniverseS5 φ₀` directly -- no mint-case/contiguity reasoning
   needed at all for `eClosure`.

All landed sorry-free, zero new axioms, full CI green (commit `caaea293`).

## Phase 5: `keysDistinct` and `keysInUniverse` (cycle 4, commits `fa816254`/`f04817cf`)

With Phase 4 unblocked, cycle 4 continued into Phase 5. **`keysDistinct`** (the phase's namesake
crux, and the fix for the v1 design gap this whole v2 plan exists to close) landed sorry-free on
the first real attempt, after authoring one new private helper,
`modalStepBranchS5gKeyed_keys_shape` (mirroring the file's established `_expanded_shape`/
`_acc_shape` pattern), characterizing `newKeys`'s shape: either `keys` unchanged, or `keys` grown
by exactly one fresh `(modalNextWorld b, successorBirthContentS5 φ₀ b s φ sf.label)` entry at one
of the two K-minting shapes when the keyed guard is unblocked. Given this, a direct 4-way case
split (old/old, old/fresh, fresh/old, fresh/fresh) using `blockingWorldS5Keyed_none_fresh`
(Phase 3) for the two mixed cases closes it -- confirming the Phase 3 keys-aware guard design
works exactly as intended, with zero live-set reasoning.

**`keysInUniverse`** also landed sorry-free on the first attempt, reusing `bClosure` +
`modalSubfmls_trans_S5` (both from Phase 4's new support layer) for the witness pair's
formula-closure, plus `Finset.filter_subset` for the `successorBirthContentS5`-filtered
remainder -- essentially a restatement of reasoning `bClosure`'s own mint case already used.

`keyLowerBd` and `keysTotal` remain `[NOT STARTED]` (not attempted this dispatch; budget
constraints). See `handoffs/03_phase5-keysdistinct-landed-keylowerbd-scope.md` for a concrete
per-field next-step plan -- `keyLowerBd` is flagged as the hardest of the two, needing a new
"introduction-direction" correspondence lemma for `boxProps`/`diaNegProps` membership not yet
built anywhere in the codebase (K or S5); `keysTotal` should compose fairly directly from
`modalApplyOneS5_knownWorlds_step` (landed Phase 4) + `accKnown`.

## Plan Deviations

1. **`S5LoopInv.keysKnown` (Phase 3, cycle-2-prior dispatch)**: unchanged from before, see round
   2 plan history.
2. **`S5LoopInv.worldsContiguous` (Phase 3/4, cycle 4)**: added as the 12th field, per handoff
   02's recommendation, to bridge Phase 6's pigeonhole COUNT bound to the VALUE bound
   `bClosure`'s mint-case obligation needs.
3. **Phase 4 fully unblocked cycle 4**: all six generic fields plus `worldsContiguous` now land
   sorry-free and CI-green.
4. **Phase 6 landed ahead of Phase 5** (cycle 2), ahead of the plan's stated dependency order --
   justified because the resume task explicitly directed establishing the pigeonhole bound as a
   static fact (no step-preservation reasoning needed), independent of Phase 5's birth-key
   preservation proofs.
5. **Phase 5 partially landed cycle 4** (`keysDistinct`, `keysInUniverse`); `keyLowerBd`/
   `keysTotal` deferred, not blocked -- see handoff 03.
6. **Phase 7 not attempted** in either cycle 2 or cycle 4 (budget consumed by Phases 4-5); remains
   independent and available for a future dispatch per the plan's own framing.
7. **Phase 7 completed cycle 8, via Strategy 2 (bespoke copy)**, not Strategy 1 (extraction), per
   handoff 06's two offered options. Chosen to keep zero blast-radius on the frozen K/T/B/S4
   soundness chain (`modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`
   are entirely untouched -- confirmed by the full `lake build`/`lake test` re-run showing all
   3239 jobs green with no regressions). The cost is ~700 lines of near-duplicate proof in the
   "not box/dia shape" branch, matching the plan's own risk assessment for Strategy 2.
8. **`accFreshInv` retained** (not dropped) in the Phase 7 assembly's threaded invariant
   (`S5SoundInv`), contrary to handoff 06's speculative "drop `accFreshInv` entirely if unneeded"
   suggestion: `accFreshInv` (`hInv` in `modalStepBranchS5_preserves_satIn`) IS needed by the two
   K-minting shapes (`F(□φ)`/`T(◇φ)`) inside the ported "not shape" branch, for the
   freshness-confinement argument establishing the new witness world `w'` is disjoint from every
   existing edge endpoint. Kept as a third `S5SoundInv` conjunct alongside `accReachableInv`/
   `accTargetsKnown`.

## Verification (at final commit `f04817cf`, cycle 4)

- `lake build` (full project): 3239/3239 jobs green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint`: 0 new warnings on touched files (1 pre-existing unrelated `unusedArguments` error
  in `PrimeExclusion.lean`, predates this task, confirmed untouched).
- `lake test`: `CslibTests` suite exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: 0 new import-minimization suggestions
  for `S5Simplification.lean` (verified via explicit grep against the file's own suggestion
  block; all listed suggestions elsewhere in the codebase are pre-existing).
- `grep -n sorry Cslib/Logics/Modal/Tableau/S5Simplification.lean`: 0 matches outside a prose
  reference inside an existing doc comment ("sorry-free").
- `grep -n '^axiom ' Cslib/Logics/Modal/Tableau/S5Simplification.lean`: 0 matches.
- `lean_verify` on `modalStepBranchS5g_preserves_bClosure`/`_worldsContiguous`/`_keysDistinct`/
  `_keysInUniverse`: only `propext`/`Classical.choice`/`Quot.sound` (standard Mathlib axioms, no
  new axioms).

## Continuation Guidance (historical, cycle 4; superseded by cycle 8 below for Phase 7)

See `handoffs/03_phase5-keysdistinct-landed-keylowerbd-scope.md` for full technical detail on the
remaining Phase 5 fields. In brief, the next dispatch should:

1. Prove `modalStepBranchS5g_preserves_keysTotal` next (most tractable of the two remaining
   fields) -- reuse `modalApplyOneS5_knownWorlds_step` (landed Phase 4) + `accKnown` for the
   known-vs-fresh-world dichotomy; the fresh world's own key entry is immediate from
   `modalStepBranchS5gKeyed_keys_shape`.
2. Prove `modalStepBranchS5g_preserves_keyLowerBd` last -- needs two new small "introduction"
   lemmas (`boxProps_mem_of_S5`/`diaNegProps_mem_of_S5`-style, converse direction of the
   existing elimination lemmas built this cycle) plus `relevantSetFinset_mono`
   (`LoopChecking.lean:344`, already public) for the old-key case.

(Both items above were completed in cycles 5-6; Phase 5 and the whole termination chain P3-P6
are now `[COMPLETED]` -- see the Per-Phase Status Ledger above.)

## Cycle 8: Phase 7 Completion (`modalTableauS5_sound`)

**What landed**: three new declarations in `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`,
appended immediately after the cycle-7 semantic core (`## Task 515 Phase 7` section):

1. `S5SoundInv b acc := accFreshInv b acc ∧ accReachableInv b acc ∧ accTargetsKnown b acc` --
   the combined per-step invariant threaded via a single `List.Forall₂` through the outer fuel
   induction (mirroring how the K/T generic chain threads `accFreshInv` alone).
2. `modalStepBranchS5_preserves_satIn` -- a bespoke S5 specialization of the generic
   `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:193`), fixed to
   `apply := modalApplyOneS5`/`FC := s5FC` with an added `hreach : accReachableInv b acc`
   hypothesis. The box-positive/diamond-negative branch swaps in the landed
   `modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn` in place of the generic theorem's
   `hBoxPos`/`hDiaNeg` parameters (which cannot receive `hreach` -- confirmed structurally per
   handoff 06). Every other shape is a byte-for-byte copy of the generic crux's own "not shape"
   branch (`FrameSoundness.lean:318-718` in the pre-cycle-8 file), the only substantive edits
   being the `hAgree`-call replaced by `modalApplyOneS5_eq_of_not_boxPos_diaNeg` and the single
   `negImp_alpha_preserved_gen FC ...` call's `FC` replaced by `s5FC` -- confirmed via `grep` that
   these are the ONLY two places in that ~400-line branch referencing the generic `apply`/`FC`
   parameters (besides the tactic keyword `apply`, which is unrelated and left untouched).
3. `modalExpandBranchesS5_closed_unsatIn` -- a bespoke S5 specialization of the generic
   `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:729`), fixed similarly, threading
   `S5SoundInv` instead of bare `accFreshInv`. At each step, the three components are produced by:
   `modalStepBranch_preserves_accFreshInv_gen` and `modalStepBranch_preserves_accTargetsKnown_gen`
   (both ALREADY GENERIC in `apply`, reused directly at `modalApplyOneS5` via the landed
   `modalApplyOneS5_fresh_local` witness -- zero new proof content for these two), plus the landed
   `modalStepBranchS5_preserves_accReachableInv` for the third.
4. `modalTableauS5_sound` -- the capstone, mirroring `modalTableauT_sound`
   (`FrameCompleteness.lean:1182`) exactly: `by_contra` on a falsifying model, build the initial
   `branchSatisfiableIn s5FC` witness and the initial `S5SoundInv` witness (`accFreshInv_empty`,
   the landed `accReachableInv_initial`, and an inline vacuous `accTargetsKnown` proof for the
   edgeless empty accessibility relation), feed both into
   `modalExpandBranchesS5_closed_unsatIn (modalFuel φ)` at the initial tableau configuration, and
   close by contradiction.

**Strategy decision**: chose Strategy 2 (bespoke copy) from handoff 06's two options, not
Strategy 1 (extraction), specifically to keep the frozen K/T/B/S4 chain's own declarations
(`modalStepBranchGen_preserves_satIn`, `modalExpandBranchesGen_closed_unsatIn`,
`modalTableau_sound_frame_gen`, `modalTableauT_sound`, etc.) completely untouched -- verified via
`git diff` showing the only changes to `FrameSoundness.lean` are pure additions (no lines removed
or modified in the pre-existing K/T/generic machinery), and via a full `lake build`/`lake test`
re-run confirming 3239/3239 jobs green with the same pre-existing (out-of-scope) sorries in
`Cslib/Logics/Propositional/Tableau/{Intuitionistic,Minimal}/*.lean` as before.

**Verification (cycle 8, this dispatch)**:
- `lake build` (full project): 3239/3239 jobs green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint`: 0 new errors (only the 1 pre-existing unrelated `PrimeExclusion.lean`
  `unusedArguments` error, untouched).
- `lake test`: `CslibTests` suite exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: the only suggestion touching
  `FrameSoundness.lean` is `remove import Mathlib.Data.List.Forall2` -- confirmed pre-existing
  and unrelated to this dispatch's additions (`Soundness.lean`, already `public import`ed by this
  file, also directly imports `Mathlib.Data.List.Forall2`, and `List.Forall₂` was already used
  extensively by the pre-existing K/T generic fuel induction before this dispatch touched the
  file; the redundant-transitive-import fact predates cycle 8).
- `grep -c sorry Cslib/Logics/Modal/Tableau/FrameSoundness.lean`: 0 matches.
- `grep -c '^axiom ' Cslib/Logics/Modal/Tableau/FrameSoundness.lean`: 0 matches.
- `lean_verify` on `modalTableauS5_sound`, `modalStepBranchS5_preserves_satIn`,
  `modalExpandBranchesS5_closed_unsatIn`: only `propext`/`Classical.choice`/`Quot.sound`.

**Continuation guidance for Phase 8** (the next dispatch's entry point): Phase 8 (spec-free
Hintikka lift + fuel bridge + `Decidable (s5Valid φ)`) does NOT depend on Phase 7 (plan's own
"Depends on: 6 and 3" line) and can start fresh. Per the plan's pre-authorized fallback: attempt
`modalExpandBranchesS5_hintikka` (the `S5LoopInv`-parametrized analogue of
`modalExpandBranchesGen_hintikka`, `CompletenessLoop.lean:876`) first; if it resists within
budget, mark `[BLOCKED]` with the exact open goal and pivot to Strategy 2 (semantic bounded-model
FMP via the landed `extractModelS5`, Massacci Fact 9.1 single-cluster models) as the sorry-free
fallback for `instDecidableS5Valid`. See handoff `07_*.md` (this cycle) for the fully detailed
recipe.
3. Once all four Phase 5 fields land, the full termination chain (Phases 3-6) closes, since
   Phase 6 is already `[COMPLETED]`.
4. Phase 7 (soundness bridge) can be attempted independently/in parallel at any point, per the
   plan's own framing ("forks after P1, runs parallel to P3-P6").

No `sorry`, no vacuous definitions, and no re-added rank axiom were introduced at any point
across cycles 2 or 4.


---

## Cycle 9 (2026-07-15): Phase 8 partial -- S5 truth lemma landed, lift `[BLOCKED]`

- **Status**: Phase 8 `[BLOCKED]`, Phase 9 transitively `[BLOCKED]`. **7 of 9 phases COMPLETED.**
- **Commits**: `6d04e74e` (truth lemma + world-bound capstone), `07c79505` (spec generalization
  + S5 `accSourcesKnown` instance).
- **Sorry inventory**: EMPTY. Zero `sorry`, zero new axioms, zero vacuous definitions, zero
  weakened statements.

### Plan-marker reconciliation (dispatch instruction)

The dispatch flagged that the plan records `keyLowerBd`/`keysTotal` as `[NOT STARTED]` inside an
otherwise-`[COMPLETED]` Phase 5. **Verified against disk: this discrepancy no longer exists.**
Both tasks are checked `[x]` with cycle-6 landing notes, and the on-disk state agrees --
`grep` for `sorry` across `Cslib/Logics/Modal/Tableau/` returns only prose mentions, and
`lake build` is green at 3239/3239. The stale text was already reconciled in cycle 6; only the
prose paragraph *below* the task list still narrates them as deferred, which is historical
narration of the cycle-4 state, not a live marker. No action needed.

### What Changed

- **`S5Simplification.lean`** -- `modalMaxWorld_lt_worldBoundS5_of_keys` and
  `S5LoopInv.worldBound`: the termination chain's **actual payload**, exposed as a named lemma.
  Phases 3-6 exist to establish the a-priori world bound via the birth-key pigeonhole (the rank
  route being *false* for S5), but that conclusion existed only as a `have hW` buried inside
  `_preserves_bClosure`. It is now the chain's public conclusion; `_preserves_bClosure` consumes
  the named lemma. This is the S5 counterpart of K's
  `modalMaxWorld_lt_worldBound_of_phiBound`.
- **`FrameCompleteness.lean`** -- the **S5 truth lemma over the universal relation** (the task
  description's explicit "Phase 4" deliverable): `eqvGen_mem_modalKnownWorlds_iff`,
  `hintikkaS5_box_pos`, `hintikkaS5_diamond_neg`, `modalTruthLemmaS5`,
  `modalOpenBranchS5_countermodel`. This is the **countermodel half of S5 completeness**, and it
  is independent of both the termination chain and the blocked lift: like
  `modalTruthLemmaT`/`modalTruthLemmaB` it consumes a `modalHintikkaSetGen modalApplyOneS5 b acc`
  witness as a *hypothesis*.
- **`BDriver.lean`** -- generalized `modalStepBranchGen_preserves_accSourcesKnown` and
  `modalExpandBranchesGen_openBranch_accSourcesKnown` from the bundled
  `spec : RuleApplicationSpec apply` to the raw `freshLocal` dichotomy they actually consumed
  (verified: the sole use site was one `rcases spec.freshLocal`). Zero regression to B, which now
  passes `modalApplyOneB_spec.freshLocal`.
- **`FrameCompleteness.lean`** -- `modalExpandBranchesS5_openBranch_accSourcesKnown`, the S5
  instantiation that generalization unlocks, plus an in-file **"Phase 8 scope note"** recording
  precisely what `modalTableauS5_complete` still needs.

### Decisions

- **The S5 universal rule trivialises the truth lemma.** `extractModelS5`'s relation is the
  *equivalence closure* `Relation.EqvGen acc.hasEdge` -- far more than the single raw edge K's/T's
  bridges consume, and more even than B's `SymmGen`. Rather than chase paths, the S5 bridges
  observe that `modalApplyOneS5`'s `T(□φ)@w` arm emits `T(φ)@w'` at **every** known world, so a
  saturated branch already carries the payload everywhere; the bridges take a bare
  `w' ∈ modalKnownWorlds b` where T's/B's take a path. The only residual obligation is that
  `EqvGen` cannot escape the known-world set (`eqvGen_mem_modalKnownWorlds_iff`).
- **`eqvGen_mem_modalKnownWorlds_iff` is stated as an `Iff`, not the `→` actually consumed.**
  Forced, not stylistic: `Relation.EqvGen`'s `symm` constructor is otherwise not dischargeable by
  induction (at `symm` the IH gives `x known → y known` while the goal needs the converse), so
  both directions must be carried together. This is also why it needs `accSourcesKnown` *and*
  `accTargetsKnown`, one per raw-edge endpoint.
- **Generalize rather than copy.** For `accSourcesKnown` the fix was to weaken an over-strong
  hypothesis in the shared generic lemma, not to author an S5 copy (contrast Phase 7's soundness
  bridge, where a bespoke copy was chosen to protect the frozen K crux). Justified because the
  change is a strict generalization with a single call site, and `#print axioms` on
  `modalTableauB_complete` confirms B is unregressed.
- **Strategy 2 (semantic FMP) deliberately NOT started.** It needs a filtration truth lemma
  *plus* an atom-locality argument to make valuation enumeration decidable for arbitrary `Atom`
  (no `Fintype Atom` is assumed by any decidability instance in the file). That is multi-dispatch
  work; starting and not finishing it would have produced no landable artifact. It remains
  pre-authorized and untouched.

### Impacts -- two structural findings that re-scope Phase 8

Both are new this cycle; **the plan did not account for either**, and they explain why Phase 8 is
larger than its 3-hour estimate:

1. **`S5LoopInv` is an invariant of a stepper no driver runs.** `S5LoopInv`/
   `modalStepBranchS5gKeyed` is the *keyed* stepper; `modalTableauS5 = modalTableauGen
   modalApplyOneS5` runs the *unguarded* `modalStepBranchGen modalApplyOneS5`, and no
   `modalExpandBranchesS5gKeyed` exists. Generalizing the lift over `S5LoopInv` does not by
   itself yield a lift for `modalTableauS5`: it needs either a keyed driver (with its OWN
   soundness bridge, since the landed `modalTableauS5_sound` is stated for the unguarded surface)
   or a fuel-domination proof for the unguarded expansion (plan risk R7).
2. **`S5LoopInv` carries no Hintikka-forcing fields** -- none of `ModalLoopInvGen`'s
   `hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/`eDiamondOnlyPos`/`eDiamondPosWitness`. Those
   five fields plus preservation lemmas are prerequisite work for any `S5LoopInv`-parametrized
   lift, on top of the twelve fields already landed.

Also worth recording: **fuel insufficiency is a completeness-only hazard, never a soundness one.**
`modalExpandBranchesGen` at `fuel = 0` returns `.openBranch` whenever any branch is open
(`Saturation.lean:206-212`), never a premature `.closed`. This is why `modalTableauS5_sound` holds
unconditionally at K's fuel while completeness does not -- and it means R7 must be settled before
`modalTableauS5_complete` can even be *stated* at the shipped surface.

### The exact blocker

`modalTableauS5_complete` needs four facts at the open branch `(b, a)`:

| # | Fact | Status |
|---|------|--------|
| 1 | `F(φ0)@0 ∈ b` | AVAILABLE (`modalExpandBranchesGen_openBranch_initial_mem`, generic) |
| 2 | `accSourcesKnown b a` | AVAILABLE (landed this cycle) |
| 3 | `accTargetsKnown b a` | NOT BUILT -- mechanical (see below) |
| 4 | `modalHintikkaSetGen modalApplyOneS5 b a` | **THE WALL** |

Item 4's open goal, verbatim:
```
⊢ modalHintikkaSetGen modalApplyOneS5 bR aR
```
from `modalExpandBranchesGen modalApplyOneS5 branches expandedSets accs fuel = .openBranch bR aR`.
`modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:876`) cannot serve: it demands
`spec : RuleApplicationSpec apply` (PROVEN FALSE for S5 at `rankStep`) and threads
`ModalLoopInvGen`, whose `potentialInv`/`phiBound` fields are rank-based by construction.

### Follow-ups (next dispatch, in order)

1. **Item 3 (cheap, mechanical)**: generalize `modalExpandBranchesGen_openBranch_accSourcesKnown`'s
   double induction over an arbitrary step-preserved per-`(branch, acc)` predicate `P` -- its body
   is already predicate-agnostic -- then instantiate at both `accSourcesKnown` and
   `accTargetsKnown` (step-level fact already exists and is S5-ready:
   `modalStepBranch_preserves_accTargetsKnown_gen`). This closes items 1-3 entirely.
2. **Settle R7 before building anything large**: decide whether K's `modalFuel` dominates the
   unguarded S5 expansion. If YES, the lift can target the shipped `modalTableauS5` surface
   directly and finding 1 dissolves. If NO, a keyed driver + its own soundness bridge is required,
   and that should be re-planned as its own phase rather than absorbed into Phase 8.
3. **Only then** attempt the lift, or pivot to Strategy 2.

### Verification (cycle 9)

- `lake build`: 3239/3239 green.
- `lake exe checkInitImports`: exit 0. `lake exe lint-style`: exit 0. `lake test`: exit 0.
- `lake lint`: only the 1 pre-existing unrelated `PrimeExclusion.lean` `unusedArguments` error.
- `lake shake --add-public --keep-implied --keep-prefix`: no new import suggestions for touched
  files.
- **`#print axioms` (run via `lake env lean`, independent of the LSP)** on
  `modalTruthLemmaS5`, `modalOpenBranchS5_countermodel`, `hintikkaS5_box_pos`,
  `hintikkaS5_diamond_neg`, `eqvGen_mem_modalKnownWorlds_iff`,
  `modalExpandBranchesS5_openBranch_accSourcesKnown`,
  `modalExpandBranchesGen_openBranch_accSourcesKnown`, `modalTableauB_complete`,
  `modalTableauS5_sound`: `propext`/`Classical.choice`/`Quot.sound` only -- **no `sorryAx`**.
  (`eqvGen_mem_modalKnownWorlds_iff` depends on no axioms at all.)
  Recorded because an interim `lean_verify` call returned a spurious `sorryAx` for a
  freshly-edited declaration; it was a stale-LSP artifact, disproved by both the independent
  `#print axioms` run and by `lake build` emitting no `declaration uses sorry` warning for the
  file. The only such warning in the project is the pre-existing task-317
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118`, outside this task's scope.
- Pre-existing unrelated issues left untouched: the task-317 `sorry` above, and the
  `PrimeExclusion.lean` lint error.

### Plan Deviations (cycle 9)

- **Landed the truth lemma, which plan v2 does not list under Phase 8.** Plan v2's Phase 8 task
  list assumes the lift comes first; the truth lemma is listed only implicitly (task description
  "the generic Hintikka lift + truth lemma over the universal relation (Phase 4)") and in the
  Artifacts ledger. Since the lift is blocked and the truth lemma is genuinely *independent* of
  it, the dispatch delivered the independent half rather than nothing. This is a scope
  re-ordering, not a scope reduction.
- **Edited `BDriver.lean`, not named in plan v2's Phase 8 "Files to modify".** The edit is a
  strict hypothesis generalization (`spec` -> `freshLocal`) with one call site, verified
  zero-regression by `#print axioms` on `modalTableauB_complete`. It does not touch
  `GenericDriver.lean`'s `RuleApplicationSpec` core, which the plan's Non-Goals protect.
- **`GenericDriver.lean` untouched**, as the plan's Non-Goals require. No
  `RuleApplicationSpec modalApplyOneS5` witness was reintroduced; no rank axiom.
