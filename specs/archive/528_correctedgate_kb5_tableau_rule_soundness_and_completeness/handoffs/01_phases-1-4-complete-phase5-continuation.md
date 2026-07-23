# Handoff: Task 528, Phases 1-4 complete, continuing at Phase 5

## Status

Phases 1-4 (Wave 1, Wave 2, Wave 3's Phase 4 slice) are **landed, committed, and verified**:
zero `sorry`, zero new axioms (identical axiom profile to the frozen task-524 chain:
`propext`/`Classical.choice`/`Quot.sound`, several lemmas fully constructive with zero axioms),
`lake build` green on all three touched files both individually and together.

Phase 6 (open-branch supply lemmas) is also Wave-3 and unblocked (depends only on Phase 2), but
was **not started** — Phase 4/6 file-overlap serialization (both touch `FrameCompleteness.lean`)
means whoever picks this up next should do Phase 5 first (it's next in the dependency chain and
this handoff has full context for it), then Phase 6, per the plan's wave table.

Commits (all on `main`, in order):
1. `task 528 phase 1: corrected-gate rule definitions + membership dichotomy`
2. `task 528 phase 2: specCore instance + termination/world bound`
3. `task 528 phase 3.1` through `phase 3.4`, plus `task 528 phase 3: complete corrected-gate KB5 frame soundness capstone`
4. `task 528 phase 4.1` through `4.3`, plus `task 528: mark phase 4 complete in plan file`

Plan file: `specs/528_correctedgate_kb5_tableau_rule_soundness_and_completeness/plans/01_corrected-gate-kb5-rule.md` — Phases 1-4 marked `[COMPLETED]` with full deviation annotations inline.

## What was landed

### Phase 1+2 — `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv` — the corrected-gate propagation helpers (self-target
  arm fires on `clusterNonempty` alone, not `w == 0 && clusterNonempty`).
- `modalKb5BoxAllUniv_mem`/`modalKb5DiaNegAllUniv_mem` — trigger-free membership dichotomy.
- `modalKb5BoxAllUniv_mem_eq`/`modalKb5DiaNegAllUniv_mem_eq` — shape lemmas.
- `modalApplyOneKb5''Prop`/`modalApplyOneKb5''` — the dispatcher + full rule (mint shapes verbatim
  `modalApplyOneFive` witness-reuse, unchanged).
- `modalTableauKb5''`/`modalTableauKb5''_eq` — entry point.
- All the mint-shape case-split/bridge lemmas mirroring `modalApplyOneKb5'`'s own
  (`_diaPos_eq_or_reuse`, `_boxNeg_eq_or_reuse`, `_boxPos_eq`, `_diaNeg_eq`,
  `_eq_of_not_mint_shape`, `_diaPos_eq_or_reuse_ne_root`, `_boxNeg_eq_or_reuse_ne_root`,
  `_agree_or_reuse_ne_root`, `_agree_or_reuse`).
- `modalApplyOneKb5''Prop_boxPos_diaNeg_eq`/`modalApplyOneKb5''Prop_knownWorlds_step` — **take an
  explicit `(h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)` hypothesis** the frozen versions don't
  need (see "Key discovery" below).
- `modalApplyOneKb5''_specCore : RuleApplicationSpecCore modalApplyOneKb5''` — all 9 fields.
- `Kb5''WorldInv` (`:= FiveWorldInv`, `rfl`) + `modalMaxWorld_lt_worldBound_of_Kb5''WorldInv`.
- `modalKb5BoxAllUniv_mem_of`/`modalKb5DiaNegAllUniv_mem_of` — introduction-direction lemmas
  (Phase 4 work, placed here per plan instruction since this file is in this task's `file_scope`).

### Phase 3 — `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `reachable_imp_related_kb5_symm` — the one new one-liner the plan anticipated (symmetrized
  `reachable_imp_related_kb5`).
- `modalKb5BoxAllUniv_soundIn`/`modalKb5DiaNegAllUniv_soundIn` — rule-level semantic soundness.
- `modalStepBranchKb5''_preserves_accReachableInv` — **bundles** `accReachableInv b' newAcc ∧
  (0 : WorldIndex) ∈ modalKnownWorlds b'` in its conclusion (needs `h0` as a hypothesis too).
- `modalStepBranchKb5''_preserves_satIn` — semantic satisfiability preservation (does NOT need
  `h0` — see below).
- `Kb5''SoundInv := FiveSoundInv b acc ∧ (0 : WorldIndex) ∈ modalKnownWorlds b`.
- `modalExpandBranchesKb5''_closed_unsatIn` — the fuel induction, threading `Kb5''SoundInv`.
- `modalTableauKb5''_sound` — **the Phase 3 capstone**: `modalTableauKb5'' φ = .closed → kb5Valid φ`.

### Phase 4 — `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `extractModelKb5_clusterNonempty_of_reach_root` — the Risk 3 witness helper (simpler than
  anticipated, see below).
- `hintikkaKb5''_box_pos`/`hintikkaKb5''_diamond_neg` — trigger-free Hintikka insertion lemmas
  (the `w = 0` conjunct dropped from the self-target condition vs. the frozen
  `hintikkaKb5'_box_pos`/`_diamond_neg`).

## Key discovery: the "root always known" invariant

The frozen task-524 rule's self-target arm only fires when the *trigger* is the root (`w == 0`),
so every proof that needed "the self-target world `0` is a known world of `b`" got it for free
from "the trigger is known" (`sf ∈ b` combined with `w = 0`). The corrected rule's self-target arm
fires from **any** trigger, so that shortcut is gone. Two genuinely different situations arose:

1. **F2 (`outputsSubsetUniverse`) and the semantic soundness lemmas need NO new invariant.**
   `WorldIndex := Nat`, so `(0 : WorldIndex) ≤ modalWorldBound φ0` holds unconditionally via
   `Nat.zero_le` (this is even hinted at, unused, in the frozen `Full` rule's own docstring). And
   `accReachableInv_kb5_root_refl`/`reachable_imp_related_kb5_symm` (the semantic lemmas) never
   needed the trigger to be the root in the first place — they only need the `clusterNonempty`
   witness, which the mem-dichotomy already supplies.
2. **The SYNTACTIC `modalKnownWorlds`-membership bookkeeping (`knownWorlds_step`,
   `accReachableInv` preservation, the fuel induction) genuinely needs `(0 : WorldIndex) ∈
   modalKnownWorlds b`** as an explicit extra hypothesis, threaded exactly the way completeness
   proofs elsewhere in this codebase already thread `F(φ)@0 ∈ b` explicitly (grep for that phrase
   in `FrameCompleteness.lean` to see the existing idiom). It is trivial to establish (true at the
   singleton seed branch `[F(φ)@0]`) and trivial to preserve (`modalKnownWorlds_mono_append_FS`,
   since branches only ever grow — formulas are never removed).

**Watch for this pattern in Phase 5+6+7**: any new lemma that needs "a world is known" where that
world could be `0` reached via the *corrected* self-target arm should be checked against this
same distinction — is it a numeric-bound fact (free via `Nat.zero_le`) or a genuine
`modalKnownWorlds`/Hintikka-membership fact (needs `h0` threaded, or — better — reuse
`extractModelKb5_clusterNonempty_of_reach_root`/`hintikkaKb5''_box_pos`'s existing `hcond`
machinery, which already encapsulates the witness correctly).

## Next: Phase 5 — the truth lemma `modalTruthLemmaKb5`

**This is the lemma that was mathematically FALSE for the frozen rule** (witnessed by
`extractModelKb5_nonRoot_boxPos_gap`, still in `FrameCompleteness.lean`, kept as documentation —
do not delete it, Phase 8 reconciles its docstring framing) **and is now TRUE for the corrected
rule.** Mirror target: `modalTruthLemmaFive` (`FrameCompleteness.lean:2693`, ~190 lines), strong
induction on `modalComplexity`, proved against `extractModelKb5` instead of `extractModelFive`.

### Concrete next steps (from the plan, cross-checked against current line numbers)

1. **Propositional cases** (`imp`/`and`/`or`/`atom`/`bot`): port verbatim from
   `modalTruthLemmaFive`, substituting the prop-shape agreement lemma. The needed analogue of
   `modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg` for `Kb5''` is
   **`modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg`** — already landed in Phase 1
   (`FiveSimplification.lean`), no new work needed here.
2. **Box-positive case** (`.box ψ`, i.e. `T(□ψ)@w ∈ b`): for `w'` with
   `(extractModelKb5 b acc).r w w'`:
   - Use `symmEuclGen_mem_modalKnownWorlds_iff` (`FrameCompleteness.lean:3285`) and
     `extractModelKb5_root_reach_mem_modalKnownWorlds` (`:3310`) to place `w'` in the known
     cluster.
   - **The crux, `w' = 0` sub-case**: this is exactly where the frozen rule's gap dissolved. Use
     `extractModelKb5_clusterNonempty_of_reach_root` (Phase 4, landed) to get the
     `∃ u ∈ modalKnownWorlds b, u ≠ 0` witness `hintikkaKb5''_box_pos`'s `hcond` right disjunct
     needs — call it with `hwne := (the fact w ≠ 0)` and `hr := (the fact (extractModelKb5 b
     acc).r w 0)`. Watch the direction: the helper takes `hr : (extractModelKb5 b acc).r w 0`
     (trigger `w` relates TO `0`), matching exactly what the box-positive case has in hand
     (`(extractModelKb5 b acc).r w w'` with `w' = 0`).
   - `w' ≠ 0` sub-case: `hintikkaKb5''_box_pos`'s `hcond` left disjunct, trivial from `w' ∈
     modalKnownWorlds b`.
   - Then `hintikkaKb5''_box_pos` (Phase 4, landed) gives `T(ψ)@w' ∈ b`, then apply the IH
     (strong induction on `modalComplexity ψ < modalComplexity (.box ψ)`).
3. **Box-negative / diamond-positive cases**: reuse the *already-generic* `hintikka_box_neg_gen`/
   `hintikka_diamond_pos_gen` (`Completeness.lean:1007`/`:1019`) + `extractModelKb5_hasEdge_imp_r`
   (`FrameCompleteness.lean:3266`), mirroring the Five arms verbatim — no KB5-specific work
   needed here (these shapes are untouched, mint-only, by the gate fix).
4. **Diamond-negative case**: dual to box-positive, via `hintikkaKb5''_diamond_neg` (Phase 4,
   landed) — mirror step 2 with signs flipped.
5. `lean_verify` the lemma; confirm zero `sorry`, axiom profile unchanged.

### If it does not close

Per the plan's own contingency: mark Phase 5 `[BLOCKED]` in the plan file with the exact
`lean_goal` state and what's missing — **do not insert `sorry` or a placeholder**. Given how
cleanly Phases 1-4 closed (including the two harder-than-expected pieces — the root-known
invariant and the fuel-induction re-derivation — both resolved with local, principled fixes), the
truth lemma is likely tractable, but it is the single highest-complexity phase in this plan and
should get a full, unhurried pass.

## After Phase 5: Phases 6, 7, 8

- **Phase 6** (open-branch supply lemmas, `FrameCompleteness.lean`, different section from Phase
  4's Hintikka block — no edit conflict): Hintikka lift for `modalApplyOneKb5''`
  (`modalExpandBranchesHintikka` + `modalApplyOneKb5''_specCore` from Phase 2 + a
  `ModalLoopAuxKb5''` loop invariant), `accSourcesKnown` (generic bridge, should apply directly),
  `accTargetsKnown` open-branch preservation (`modalStepBranchKb5''_preserves_accTargetsKnown`
  step lemma). **Watch for the same root-known-invariant pattern** if any sub-lemma here needs
  `modalKnownWorlds`-membership of `0` specifically.
- **Phase 7** (completeness + decidability assembly): `modalOpenBranchKb5''_countermodel`,
  `modalTableauKb5''_complete`, `kb5Valid_decides`, `instDecidableKb5Valid`. Depends on 3 (done),
  5, 6.
- **Phase 8** (docs reconciliation + regression tests + full CI): reconcile stale
  blocker/scope docstrings (durable anchors only, no task-number citations per
  `no-task-references-in-deliverables.md`), extend `CslibTests/ModalFrameSeparation.lean`,
  diagnose (do not fix) the orthogonal `decide`-reduction kernel stall
  (`S5Simplification.lean:1959-1963`), run the full 7-step CSLib CI pipeline (`lake exe cache get`
  first — likely already warm from this session's builds).

## Hard constraints (unchanged, still binding)

- `modalApplyOneKb5'`/`modalTableauKb5'`/`modalKb5BoxAllFull`/`modalKb5DiaNegAllFull` (frozen
  task-524 deliverables) are **untouched** — verified via `git diff` showing only additions, never
  edits, to any pre-existing declaration in the three touched files.
- Zero `sorry`, zero new axioms (verified at every commit via `lean_verify` + `grep`).
- `LoopChecking.lean` is out of scope (owned by a separate task) — not touched, not built as part
  of this session's scoped builds (only `FiveSimplification.lean`/`FrameSoundness.lean`/
  `FrameCompleteness.lean` were built, individually and together).

## Verification commands to re-run at the start of the next session

```bash
cd ~/Projects/cslib
lake build Cslib.Logics.Modal.Tableau.FiveSimplification \
  Cslib.Logics.Modal.Tableau.FrameSoundness \
  Cslib.Logics.Modal.Tableau.FrameCompleteness
grep -n "sorry" Cslib/Logics/Modal/Tableau/{FiveSimplification,FrameSoundness,FrameCompleteness}.lean | grep -v '^\S*:.*--\|/--'
git log --oneline -20
```
All three should build green; the sorry grep should return only doc-comment mentions (as verified
throughout this session); `git log` should show the 12 commits listed above at the top.
