# Continuation Handoff: Phases 7-11 (Single-Step Preservation Through Decidability)

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `plans/02_keyed-s4-driver-restructured.md`
- **Written**: 2026-07-24
- **Session**: sess_1784905751_756cda_535

## What Was Completed This Dispatch

Phase 6 of plan v02 (Phases 1-5 were already landed in prior dispatches). Commit on `main`:

- `828aefd4` — task 535 phase 6: keys-threaded Hintikka-tracking invariant bundle (partial
  commit message says "(partial)" but all four Phase 6 checklist items are in fact closed —
  see the plan file's Phase 6 section, now `[COMPLETED]`)

**Phase 6** landed, all additive in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`:

- `modalApplyOneS4Keyed_fst_eq_of_not_box` (line ~5488): the F8 local-shape-invariance discharge
  for `modalApplyOneS4Keyed φ₀ keys` — outside the two minting shapes, it reduces to raw
  `modalApplyOne` regardless of `keys` (the dispatch chain `modalApplyOneS4Keyed →
  modalApplyOneS4 → modalApplyOneS4Rules → modalApplyOneT → modalApplyOne` fires its catch-all
  arm at every layer).
- `modalHintikkaClauseGen_lift_S4` (private, line ~5528): territory-local re-derivation of
  `Completeness.lean`'s `private modalHintikkaClauseGen_lift` (unavailable across files, same
  re-derivation precedent as Phase 3's combinatorial primitives). Kept generic in `apply`.
- `modalApplyOneT_snd_eq`/`modalApplyOneS4Rules_snd_eq` (private, lines ~5600/5614): the
  accessibility-output component of `modalApplyOneT`/`modalApplyOneS4Rules` is UNCONDITIONALLY
  identical to raw K's own `modalApplyOne sf b acc`.snd — the T/4-rule propagation arms only
  ever touch the `.fst` formula-output component. Proved by case-splitting `sf.sign`/
  `sf.formula` then (for the two T/4-relevant shapes only) the inner `RuleResult` match; every
  branch reduces via `dsimp only` + the case split, no `split_ifs`-on-empty-goal traps (see
  "Hard-Won Lesson" below for the exact tactic idiom that worked).
- `modalApplyOneS4Keyed_hasEdge_mono` (line ~5635): an existing `acc.hasEdge w w'` survives one
  `modalApplyOneS4Keyed φ₀ keys` application, for any `keys`. Built from `hasEdge_addEdge_mono`
  (blocked minting case) + K's own `modalApplyOne_fresh_local` dichotomy (unblocked/non-mint
  cases, via the two `_snd_eq` facts above).
- `S4KeyedHintikkaInv` (structure, line ~5691): the keys-threaded analogue of
  `ModalLoopInvHintikka`'s five Hintikka-specific conjuncts (`hintikkaInv`/`eBoxOnlyNeg`/
  `eBoxNegWitness`/`eDiamondOnlyPos`/`eDiamondPosWitness`), parametrized over
  `(φ₀, b, e, acc, keys)`. Deliberately does NOT duplicate `S4LoopInv`'s universe-closure/
  keys-bookkeeping fields — those are threaded as a SEPARATE ambient hypothesis at each call
  site (see "Design Decision" below).
- `S4KeyedHintikkaInv_weaken` (line ~5721): the bundle weakens across branch/accessibility
  growth at a FIXED expanded set `e` — `hintikkaInv` via the lift lemma, `eBoxOnlyNeg`/
  `eDiamondOnlyPos` unchanged (mention no `b`/`acc`), the two witness fields via raw
  `hbsub : b ⊆ b'` / `haccsub : ∀ w w', acc.hasEdge w w' = true → acc'.hasEdge w w' = true`
  hypotheses.

All `lean_verify`-confirmed `propext`/`Classical.choice`/`Quot.sound` only. Zero `sorry`.
`lake build Cslib.Logics.Modal.Tableau.LoopChecking` green, zero new lint warnings (confirmed by
diffing `lake build` output against the pre-Phase-6 baseline — the same pre-existing warnings at
the same line numbers, nothing new).

## Design Decision: `S4KeyedHintikkaInv` Does NOT Bundle `S4LoopInv`

Unlike K's `ModalLoopInvHintikka` (which bundles bClosure/eClosure/eNodup/accFresh/accKnown/aux
alongside the five Hintikka fields into ONE structure), `S4KeyedHintikkaInv` carries ONLY the
five Hintikka-specific fields. This is deliberate: `S4LoopInv` (task 511, frozen) already carries
the universe-closure/keys-bookkeeping conjuncts, and its own preservation theorem
(`modalStepBranchS4_preserves_S4LoopInv`, `LoopChecking.lean:4624` as of this dispatch — but see
the re-grep warning below) already threads `keysWorldsKnown`/`worldsContiguousS4` as separate
ambient hypotheses, not struct fields. Phase 7's preservation lemma should thread THREE
hypotheses at each call site: `S4LoopInv φ₀ b e acc keys`, `S4KeyedHintikkaInv φ₀ b e acc keys`,
and the two proof-internal auxiliaries (`keysWorldsKnown`/`worldsContiguousS4`) — mirroring
exactly the hypothesis bundle `modalStepBranchS4_preserves_S4LoopInv` already takes/returns.

## Hard-Won Lesson: Proving `.snd` Equality Through Nested `let`+`match`

`modalApplyOneT`/`modalApplyOneS4Rules` are defined as `let (kResult, kAcc) := modalApplyOne sf b
acc; match sf.sign, sf.formula with | ... => (X, kAcc) | ... => (Y, kAcc) | _, _ => (kResult,
kAcc)` — every arm returns `kAcc` as the snd component, so `.snd` is invariant, but Lean's `exact`/
`rfl` do NOT automatically reduce through the outer `match sf.sign, sf.formula` without `rcases`/
`cases` on the concrete discriminants first (even after that, a **second** `rcases`/`obtain` on
the *let-bound pair itself* — e.g. `rcases hk : (modalApplyOne sf b acc) with ⟨kResult, kAcc⟩` —
is needed, PLUS a `dsimp only` immediately after, to force the reduction through the pair-match
before the final `rcases kResult with ... <;> (try split_ifs) <;> rfl`). Two traps hit and fixed
this dispatch:

1. `rcases hk : (modalApplyOne sf b acc).fst with ...` (case-splitting the `.fst` PROJECTION)
   does NOT substitute into a goal whose outer match scrutinizes the LET-BOUND `kResult`
   variable, not the literal `.fst` term — the rcases succeeds (it can case-split any term) but
   leaves the goal's match un-reduced, and `rfl`/`split_ifs` then fail ("no goals to split" or
   defeq-mismatch) or fail. **Fix**: destructure the WHOLE pair via
   `rcases hk : (modalApplyOne sf b acc) with ⟨kResult, kAcc⟩`, matching the def's own `let
   (kResult, kAcc) := ...` shape.
2. Even after step 1, `exact <term of type ... = tAcc>` can fail with a "type mismatch" against
   the fully-unreduced nested-match expression, because `exact`'s defeq check does not always
   force iota-reduction through an intervening `have foo := ...; match ...` binder (the T/4-rule
   arms use `have selfNew := modalTBoxSelf ...; match kResult with ...`). **Fix**: insert
   `dsimp only` (bare, no lemma arguments — using `simp only [hk]`/`simp only [ht]` instead
   triggers an "unused simp argument" lint warning, since the rewrite it would perform already
   happened via the `rcases ... with ⟨_, _⟩` destructuring) immediately before the final
   `rcases kResult with ... <;> (try split_ifs) <;> rfl`/`exact hTA` line, to force the
   reduction. See `modalApplyOneT_snd_eq`/`modalApplyOneS4Rules_snd_eq`'s final proof text for
   the exact working tactic sequence — worth copying verbatim rather than re-deriving if a
   similar `.snd`/`.fst`-through-nested-match obligation arises in Phases 7-11.

## Groundwork for Phase 7's Blocked-Case Witness: the `keyLowerBd` Chain

While researching Phase 6, the exact argument for why `S4KeyedHintikkaInv`'s
`eBoxNegWitness`/`eDiamondPosWitness` fields survive the BLOCKED minting case (redirect to an
existing `wBlock`, `.linear []`, no new witness formula emitted) was worked out but NOT YET
formalized as a lemma — this is squarely Phase 7's job (the single-step preservation theorem
itself), so record the chain here to save re-discovery:

1. `blockingWorldS4Keyed φ₀ b keys s φ w = some wBlock` gives (via
   `blockingWorldS4Keyed_eq_birthContent`, `LoopChecking.lean:479`) that
   `(wBlock, successorBirthContent φ₀ b s φ w) ∈ keys`.
2. `successorBirthContent φ₀ b s φ w = insert (s, φ) (...)` (`LoopChecking.lean:384`) — so
   `(s, φ) ∈ wBlock`'s recorded key, literally by `insert`-membership.
3. `S4LoopInv.keyLowerBd` (a **pre-step** hypothesis on `(b, e, acc, keys)` — `wBlock`'s key was
   recorded when `wBlock` was born, strictly before this call) gives
   `wBlock`'s key `⊆ relevantSetFinset φ₀ b wBlock`, hence `(s, φ) ∈ relevantSetFinset φ₀ b
   wBlock`.
4. `relevantSetFinset φ₀ b wBlock = (signedSubfmls φ₀).filter (fun p => b.any (· ==
   ⟨p.1, p.2, wBlock⟩))` (`LoopChecking.lean:333`) — so `(s, φ) ∈ relevantSetFinset φ₀ b wBlock`
   unfolds to exactly `⟨s, φ, wBlock⟩ ∈ b` (plus the vacuous `(s,φ) ∈ signedSubfmls φ₀` side
   condition, itself immediate since `φ ∈ modalSubfmls φ₀` for a formula reached via the
   sub-formula-closed universe).

So: **the boxNeg/diaPos witness formula `⟨s, φ, wBlock⟩` is ALREADY on the branch `b` at the
moment of the blocked redirect**, by (1)-(4) chained through `S4LoopInv.keyLowerBd` — this is
what makes `S4KeyedHintikkaInv.eBoxNegWitness`/`eDiamondPosWitness` genuinely provable (not just
assumed) in the blocked case, and confirms the keyed driver really does produce a syntactic
Hintikka set (needed for Phase 8's top-loop, NOT just a semantically-sound one via Phase 9's
separate soundness argument). Phase 7 should state this as its own small lemma (something like
`modalStepBranchS4Keyed_blocked_witness_mem`, consuming `S4LoopInv.keyLowerBd` as a hypothesis)
before assembling the full single-step preservation theorem.

## What Is NOT Done: Phases 7-11

**Phase 7** (single-step invariant preservation, `modalStepBranchS4Keyed` against
`S4KeyedHintikkaInv` + `S4LoopInv` + `keysWorldsKnown`/`worldsContiguousS4`): mirror
`modalStepBranchS4_preserves_S4LoopInv`'s case-split shape (mint-unblocked/mint-blocked/non-mint,
`LoopChecking.lean:4624` as of this dispatch — RE-GREP, this line number will have shifted by
Phase 6's ~250 added lines already and will shift further). Use `S4KeyedHintikkaInv_weaken` to
lift the OLD `e`'s facts to the post-step `(b', acc')` (feed it `modalApplyOneS4Keyed_hasEdge_mono`
for `haccsub`), then separately establish `hintikkaInv`/witness facts for the NEWLY-selected
formula `sf_exp` itself (mirroring `modalStepBranchGen_hintikka_inv`'s per-shape composition,
`Completeness.lean:859-950+`) — the blocked-case witness argument above is the key new content
for the two minting shapes' blocked sub-case. Estimated 200-350 lines (per plan).

**Phase 8** (top-loop induction, `modalExpandBranchesS4Keyed_hintikka`): assemble the keyed
single-step measure-decrease (Phase 3+4 primitives/obligations) with Phase 5's fuel and Phase
6-7's invariant, mirroring `modalExpandBranchesHintikka` (`CompletenessLoop.lean:1430-1650+`).
Close with `hintikka_congr_S4` (Phase 2, landed) + `modalHintikkaSetS4_eq` (`LoopChecking.lean:
3874` as of this dispatch). Estimated 250-400 lines, biggest remaining single phase.

**Phase 9** (S4 blocked-mint-redirect SOUNDNESS lemma, genuinely new semantic content, NOT the
syntactic witness argument above): redirecting a blocked mint to `wBlock` preserves
`branchSatisfiableIn s4FC` — a model-theoretic argument (reflexive-transitive frame condition),
distinct from Phase 7's syntactic Hintikka-witness argument even though both consume
`S4LoopInv.keyLowerBd`. Independent of Phases 6-8 (only needs Phase 2). Flagged highest-variance
in the plan's risk table — a good candidate to attempt EARLY/in parallel with Phase 7 if a future
dispatch has team capacity, since a `[BLOCKED]` result here is the most consequential discovery
for the task's overall viability. Estimated 150-300 lines, in `FrameSoundness.lean` or
`FrameCompleteness.lean`.

**Phase 10** (keyed soundness top-loop `modalTableauS4Keyed_sound`, `FrameCompleteness.lean`):
depends on 3,4,5,9. Estimated 150-250 lines.

**Phase 11** (completeness + decidability, `modalTableauS4Keyed_complete`/`s4Valid_decides`/
`instDecidableS4Valid`, `FrameCompleteness.lean`): depends on 8,10,2. Estimated 150-250 lines.
Closes the task.

## Recommended Next Steps

1. Re-grep every cited line number before editing — Phase 6 added ~250 lines to
   `LoopChecking.lean`, shifting everything below its insertion point (before
   `end Cslib.Logic.Modal.Tableau`, i.e. everything AFTER `modalExpMeasure_entry_le_fuelS4`
   was NOT shifted, but the file's own internal cross-references in docstrings may be stale).
2. Dispatch Phase 7 next (blocks Phase 8). Given the ~1100-1350-line remaining scope across
   5 phases and Phase 9's flagged novelty, `--hard` mode (H8 phase-sizing, H9 wrap-up
   discipline) remains the plan's own recommendation.
3. Consider dispatching Phase 9 independently/in parallel with Phase 7 if `--team` capacity is
   available — it only needs Phase 2 (landed) and its `[BLOCKED]` risk is the single highest-value
   thing to discover early.
4. Use `git commit -- <exact task file list>` (pathspec form) for every phase commit — this
   session's own commit used pathspec scoping successfully and no contamination was observed,
   but the prior dispatch's contamination incident (task 425/451 files pulled into a task-535
   commit) means this remains essential practice in this multi-agent session.
5. When proving any further `.snd`/`.fst`-through-nested-`let`+`match` obligation (Phase 7's
   step-preservation will very likely need more of these), copy the exact tactic idiom from
   `modalApplyOneT_snd_eq`/`modalApplyOneS4Rules_snd_eq` (see "Hard-Won Lesson" above) rather
   than re-deriving from scratch.

## Verification Baseline (for regression checking after each future phase)

- `lean_verify Cslib.Logic.Modal.Tableau.modalApplyOneS4Keyed_fst_eq_of_not_box`:
  `propext`/`Classical.choice`/`Quot.sound`.
- `lean_verify Cslib.Logic.Modal.Tableau.modalApplyOneS4Keyed_hasEdge_mono`:
  `propext`/`Classical.choice`/`Quot.sound`.
- `lean_verify Cslib.Logic.Modal.Tableau.S4KeyedHintikkaInv_weaken`:
  `propext`/`Classical.choice`/`Quot.sound`.
- `grep -n "\bsorry\b" Cslib/Logics/Modal/Tableau/LoopChecking.lean`: exactly one hit, a
  docstring prose mention (currently line 4619, NOT code — re-grep, may have shifted).
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: green, zero new warnings versus the
  pre-Phase-6 baseline.
