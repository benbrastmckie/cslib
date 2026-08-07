# Phase 10 Handoff — Tier-3 triage and residue accounting

**Status**: [COMPLETED WITH EXCLUSIONS]

## What happened

Traced the full transitive import graph for every Tier-3 residue family before acting, rather
than trusting the plan's origin-file groupings (which turned out to be partially wrong).

**Resolved as genuine class (a)** (6 families, all deleted-and-consolidated):
- `modalHintikkaClauseGen_lift` — `Completeness.lean` origin de-privatized, `LoopChecking.lean`'s
  `_S4` copy deleted (`LoopChecking` reaches `Completeness` via `FmpMeasure`).
- `modalStepBranchGen_newExps_const` — `CompletenessLoop.lean` origin de-privatized,
  `BDriver.lean`'s `_B` copy deleted (`BDriver` imports `CompletenessLoop` directly).
- `modalApplyOne_boxNeg_mint_fst`/`modalApplyOne_diamondPos_mint_fst` — the plan's grouping named
  `FiveSimplification.lean` as the origin, but the ACTUAL already-public origin is
  `LoopChecking.lean`'s `_S4`-suffixed forms; deleted `FiveSimplification`'s private copies and
  renamed call sites to the suffixed public names (reverse rename direction from every other
  phase).
- `modalApplyOneT_branchingLength`/`modalApplyOneT_persistentFresh` — plan-undocumented, found in
  Phase 1's audit. De-privatized `LoopChecking.lean`'s copies (reached transitively from
  `TDriver.lean` via `CompletenessLoop`→`S5Simplification`), deleted `TDriver`'s duplicates.

**Classified into the Reasoned Exclusions table** (14 families, none touched further):
- 5 confirmed public-origin (`hintikka_congr`, `modalApplyOne_fresh`, `modalExpMeasure_step_lt`,
  `modalSubfmls_self_mem`, `modalApplyOneS5_fresh_local`) — matches the plan's original
  prediction.
- 1 Hashable-instance-dodge (`modalSubfmls_self_mem`, also counted above), 1
  wrong-direction-import (`modalApplyOneS5_fresh_local_local`) — both matching plan predictions.
- **4 reclassified**: `boxProps_outputs_subset`, `diaNegProps_outputs_subset`,
  `modalApplyOne_boxNeg_outputs_subset`, `modalApplyOne_diamondPos_outputs_subset` — the plan
  called these "public-origin duplicates" (class b); this phase found the precise mechanistic
  reason they aren't duplicates at all: each `LoopChecking.lean` `_S4` copy is stated over the
  S4-specific `modalUniverseS4`/`modalWorldBoundS4` types, not the generic types the `FmpMeasure`
  original uses. Same trap as Phase 8's `mem_modalUniverseS4_of` catch — an over-eager deletion
  attempt this phase was caught by a build-time type-mismatch error and reverted before
  committing.
- **5 newly-discovered class (c) unreachable pairs** where the plan's origin-file grouping did
  not survive an actual import-graph check: `accFreshInv_append` (`Soundness.lean` origin,
  `LoopChecking` doesn't reach it), `hasEdge_addEdge_mono` (`CompletenessLoop.lean` origin,
  `FrameSoundness` doesn't reach it), `modalApplyOne_boxPos_acc_eq`/
  `modalApplyOne_diamondNeg_acc_eq`/`not_shape_of_not_or` (`TDriver.lean` originals, `BDriver` and
  `TDriver` are structural siblings, neither reaches the other).

6 + 14 = 20 (the measured phase-start census), fully accounted, zero unclassified survivors.
Final census: **14 duplicates / 14 families**, all documented as Reasoned Exclusions — this is
the expected terminal state for Phase 10.

Full invariants table green throughout: build 3313 jobs (unchanged, no new modules); checkInitImports
0; lint-style 0; shake 0 Modal/Tableau findings; sorry census exactly 1; axiom count 0;
do-not-edit files untouched.

## Continuation pointer

Resume at **Phase 11**: final census, comment cleanup, full gate. Tasks:
- Re-run the census and record the final count/delta from the Phase 1 baseline (74/43 originally
  measured, later corrected — see Phase 1's handoff addendum for the exact reconciliation
  methodology; the census script itself was refined several times during this task, so use the
  CURRENT script's count as authoritative, not a naive subtraction against an early number).
- Sweep for surviving `Local re-derivation` comments — every remaining one must correspond to a
  documented Reasoned Exclusion (the 14 families above); anything else is stale prose.
- Update `LoopChecking.lean`'s module docstring, which the plan says "currently records the
  retired figure '55'" — verify this is still present and correct it to the declaration-level
  accounting, noting the comment census systematically undercounts (this task's own experience is
  strong evidence: 17+ declarations were caught only by declaration-level census or manual grep,
  not by the `Local re-derivation` comment string).
- Run every invariant one final time and record actual output.
- Confirm `modalTableauS4Keyed_complete` and all six `Decidable` instances elaborate (should
  already be true — full build has passed at every phase boundary).
- Recommend the two follow-up tasks: (1) the 8 genuinely public-origin families (per the original
  plan's framing) needing a separate judgement call; (2) the 5 newly-discovered unreachable class
  (c) families, which ARE privacy-caused but need new architectural work (a further
  `Support/`-style module, or a considered new import) out of this task's scope to add
  unilaterally.
