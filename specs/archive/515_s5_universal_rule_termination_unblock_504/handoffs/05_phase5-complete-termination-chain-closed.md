# Handoff: Cycle 6 -- Phase 5 COMPLETE (4/4), Termination Chain (Phases 3-6) Closed

**Date**: 2026-07-15
**Session**: sess_1784143744_a1ea21 (cycle 6, hard-mode dispatch, resume after pause at cycles 5/5)
**Status**: Phases 1, 2, 3, 4, **5**, 6 all `[COMPLETED]`. Phases 7, 8, 9 `[NOT STARTED]`.
**Commits**: `d4e7ed73` (`keysTotal` + combined shape helper), `49ed521b` (`keyLowerBd` +
mint-output infrastructure -- Phase 5 complete).

## What landed this cycle

Both remaining Phase 5 birth-key fields, sorry-free, exactly along handoff 04's recipe:

1. **Re-added verbatim** the two cycle-5 standalone lemmas right after `modalApplyOneS5_snd_eq`
   (~line 356): `modalApplyOne_snd_eq_acc_of_not_mint_shape_S5` (K leaves `acc` unchanged
   outside its two minting shapes) and `modalApplyOneS5_snd_eq_acc_of_not_mint_shape` (S5 lift).
   Both compiled first try, as handoff 04 promised.

2. **`modalStepBranchS5gKeyed_keys_full_shape`** (private): the combined helper giving the
   `newBs`-shape AND `newKeys`-shape from ONE case split on the SAME trigger `sf` -- 4-way
   disjunction (blocked / wildcard-with-`snd = acc` / neg-box mint / pos-diamond mint).
   **Compiled on the FIRST attempt.** Decisive deviation from handoff 04's bug-fix recipe: did
   NOT destructure `sf` up front. Instead mirrored the landed `_keys_shape` skeleton verbatim
   (`split at hsf <;> repeat' split at hsf; all_goals try injection hsf; all_goals (rename_i
   hsf; simp only [Prod.mk.injEq] at hsf); all_goals first | ...`). This sidesteps all three
   cycle-5 bugs at once: split-generated shape hypotheses + `by assumption`/`_` witnesses avoid
   the hygiene mismatch (bug 1) and the Sign-order trap (bug 2), and the uniform split-then-inject
   pipeline is bug 3's fix by construction. For the NEW wildcard disjunct
   (`(modalApplyOneS5 sf b acc).snd = acc`), the default match arm's auto-generated no-match
   hypotheses feed `modalApplyOneS5_snd_eq_acc_of_not_mint_shape`'s `hns` via
   `⟨by rintro ⟨hs, ψ, hf⟩; simp_all, by rintro ⟨hs, ψ, hf⟩; simp_all⟩`.

3. **`modalStepBranchS5g_preserves_keysTotal`**: blocked case direct; wildcard case selects
   `modalApplyOneS5_knownWorlds_step`'s non-mint disjunct via the helper's `snd = acc` fact plus
   the new micro-helper `addEdge_ne_self_S5` (cons strictly grows `edges`, so
   `acc.addEdge w w' ≠ acc` by length); mint case gives old worlds their old keys
   (`keys ⊆ newKeys` by append) and the fresh world `modalNextWorld b` the SAME-step appended key.
   NOTE: `modalApplyOneS5_knownWorlds_step` requires `[Hashable Atom]` -- do NOT put
   `omit [Hashable Atom] in` before lemmas that use it (first build error of the cycle).

4. **`modalStepBranchS5g_preserves_keyLowerBd`** (Phase 5 field 3/4, the "hard" field --
   landed in the same dispatch): old keys via `relevantSetFinset_mono` under branch prepend.
   Mint case infrastructure:
   - `mintBoxPropsS5`/`mintDiaNegPropsS5` (private defs): K's two mint-output groups NAMED, so
     every lemma shares ONE expression -- no cross-lemma matcher unification ever arises.
   - `boxPositivesOf_intro_S5`: introduction direction of the collector.
   - `mintBoxPropsS5_mem_intro`/`mintDiaNegPropsS5_mem_intro`: the freshly-emitted-or-already-
     on-`b` dichotomy encoded by the `if b.any (· == sf')` dedup guard.
   - `modalApplyOne_boxNeg_eq_S5`/`modalApplyOne_diamondPos_eq_S5`: FULL mint-arm
     characterizations (strengthen `modalApplyOne_boxNeg_witness`'s existential `rest` to the
     concrete `mintBoxPropsS5 b sf.label ++ mintDiaNegPropsS5 b sf.label` tail); proof = the
     `htry`-not-applicable step from `Rules.lean`'s witness lemmas + `rfl`.
   - `successorBirthContentS5_subset_relevantSetFinset_mint`: sign-generic (one lemma covers
     both mint shapes, witness `⟨s, φ, modalNextWorld b⟩` heads the list); places every
     birth-content pair on the minted branch at label `modalNextWorld b`. Witness-pair
     `signedSubfmls` membership from `bClosure`, identical to `keysInUniverse`'s derivation --
     keep the two-step `have hφmem : φ ∈ modalSubfmls (Proposition.box φ) := ...` form with the
     explicit type ascription (inlining it loses the unification anchor; second build error of
     the cycle).

## Verification (at `49ed521b`)

Full CSLib CI green: `lake build` 3239/3239; `lake exe checkInitImports` clean;
`lake exe lint-style` clean; `lake lint` only the 1 pre-existing unrelated
`PrimeExclusion.lean` `unusedArguments` error; `lake test` exit 0; `lake shake` 0 suggestions
for `S5Simplification.lean` (its Temporal/* suggestions belong to other tasks' committed
files). `lean_verify` on `_preserves_keysTotal` and `_preserves_keyLowerBd`:
`propext`/`Classical.choice`/`Quot.sound` only. Zero `sorry`, zero new axioms in
`S5Simplification.lean`. (A pre-existing `sorry` warning in
`Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118` was committed by task 317
at `19c68791` -- outside this task's files and scope.)

## State of the plan

- **Termination chain CLOSED**: Phases 3-6 all complete. All twelve `S5LoopInv` fields now have
  preservation lemmas over `modalStepBranchS5gKeyed`, and the pigeonhole bound
  (`modalKnownWorlds_length_le_worldBoundS5`) consumes them.
- **Phase 7 (soundness bridge, `FrameSoundness.lean`)**: NOT STARTED, fully independent (forks
  after Phase 1). This is the next dispatch's natural target -- see the plan's Phase 7 task list
  (reachability-threading bridge `modalExpandBranchesGen_closed_unsatIn_reachable`, single-step
  reachability preservation, `modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn` under `s5FC`,
  assembly of `modalTableauS5_sound` mirroring `modalTableauT_sound`,
  `FrameCompleteness.lean:1182`).
- **Phase 8 (spec-free Hintikka lift + decidability)**: gated on P6 (done) + P3 (done) -- now
  unblocked, but HIGH risk (R6); Strategy 2 semantic-FMP fallback pre-authorized. Blackburn
  2002 chunks (filtration/FMP) are indexed in the literature corpus if the Strategy-2 route is
  taken.
- **Phase 9**: gated on P8.

## Next dispatch recipe

1. Attempt Phase 7 in `FrameSoundness.lean` per the plan's task list. It touches a DIFFERENT
   file than Phases 3-6, so no interaction with the landed termination chain.
2. Read `FrameSoundness.lean:728` (`modalExpandBranchesGen_closed_unsatIn`) and
   `FrameSoundness.lean:193` (`modalStepBranchGen_preserves_satIn`, reuse as black box) first;
   mirror `modalTableauT_sound` for the assembly.
3. The landed P1 lemmas `modalS5BoxAll_mem`/`modalS5DiaNegAll_mem` give the non-mint universal
   arms' target labels ∈ `modalKnownWorlds b`; `modalApplyOne_fresh_local`
   (`FmpMeasure.lean:802`) covers the mint case for the reachability-preservation step.
4. After P7, Phase 8 (or its Strategy-2 fallback) is the only remaining hard frontier.
