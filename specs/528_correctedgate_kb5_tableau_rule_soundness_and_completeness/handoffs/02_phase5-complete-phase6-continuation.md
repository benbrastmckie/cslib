# Handoff: Task 528, Phase 5 complete, Phase 6 partially complete (Hintikka lift outstanding)

## Status

Phase 5 (truth lemma `modalTruthLemmaKb5`) is **landed, committed, and verified**: zero `sorry`,
zero new axioms (`propext`/`Classical.choice`/`Quot.sound`, identical to the frozen chain).
Phase 5's own first attempt introduced an unsafe hypothesis (`accEdgeIrrefl`) that was discovered
mid-session to be possibly false for a real branch (witness-reuse does not structurally exclude a
self-loop at the trigger's own world) and was corrected to use the already-established, provably
-true `accTargetsNeRoot` instead. See the plan file's Phase 5 section (both deviation notes) for
the full story -- this is NOT a loose thread, it is fully resolved and verified.

Phase 6 is **partially complete**: the `accTargetsNeRoot` + root-known-ness top-loop propagation
(needed because Phase 5's truth lemma takes `hRoot : accTargetsNeRoot acc` and
`h0 : 0 ∈ modalKnownWorlds b` as hypotheses) is landed and verified. The **Hintikka lift**
(`ModalLoopAuxKb5''` + its step-preservation/bounds + `modalLoopInvHintikkaKb5''_initial`) is
**NOT YET STARTED** -- this is the single largest remaining piece of the whole plan, discovered
during this session to be substantially larger than the plan anticipated (~300-500+ lines, not a
quick instantiation). Phases 7 and 8 have not been started (both depend on Phase 6 completing).

Commits (all on `main`, in order, most recent first):
1. `task 528 phase 6.1: top-loop propagation of accTargetsNeRoot and root-known-ness`
2. `task 528 phase 5: fix truth lemma to use accTargetsNeRoot, not unsafe accEdgeIrrefl`
3. `task 528 phase 5: complete truth lemma modalTruthLemmaKb5`
4. (earlier) `task 528: partial implementation handoff (phases 1-4 of 8 complete)` and the full
   Phase 1-4 chain documented in `handoffs/01_phases-1-4-complete-phase5-continuation.md`.

Plan file: `specs/528_correctedgate_kb5_tableau_rule_soundness_and_completeness/plans/
01_corrected-gate-kb5-rule.md` -- Phases 1-5 marked `[COMPLETED]`, Phase 6 marked `[IN PROGRESS]`
with per-bullet deviation annotations reflecting exactly what's landed vs. outstanding.

## What was landed this session

### Phase 5 -- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

- `modalApplyOneKb5''_eq_of_prop_shape` -- propositional-shape dispatcher-agreement bridge,
  mirrors `modalApplyOneFive_eq_of_prop_shape`.
- `modalTruthLemmaKb5` (~200 lines) -- **the lemma that was mathematically FALSE for the frozen
  rule and is now TRUE**. Signature: `(b acc) (hSrc : accSourcesKnown b acc)
  (hTgt : accTargetsKnown b acc) (hRoot : accTargetsNeRoot acc)
  (h0 : (0:WorldIndex) ∈ modalKnownWorlds b) (hH : modalHintikkaSetGen modalApplyOneKb5'' b acc) :
  ∀ φ w, (T(φ)@w ∈ b → Satisfies (extractModelKb5 b acc) w φ) ∧ (F(φ)@w ∈ b → ¬ Satisfies ... )`.
  Strong induction on `modalComplexity`. Box-positive/diamond-negative cases use the trigger-free
  dichotomy: for the `v = 0` sub-case they split on the TRIGGER `w`, using
  `extractModelKb5_clusterNonempty_of_reach_root` (Phase 4, `w ≠ 0`) or the NEW
  `extractModelKb5_clusterNonempty_of_root_selfRelate` (`w = 0`, self-relate case) below.
- `euclGen_symmGen_exists_base` (private) -- fully general, no-side-condition fact: any
  `EuclGen (SymmGen r) a b` derivation contains a genuine base edge SOMEWHERE. Trivial induction
  (`eucl` case uses `ih1` alone). **Do not confuse with an earlier, DELETED, broken draft**
  (`euclGen_symmGen_exists_ne_base` with an `hirr : ∀a,¬r a a` hypothesis) that required full
  irreflexivity -- that draft was replaced because full irreflexivity is not actually derivable
  for a real branch. The final version needs no side conditions at all.
- `extractModelKb5_clusterNonempty_of_root_selfRelate` -- given `hTgt`, `hRoot`
  (`accTargetsNeRoot`), and `(extractModelKb5 b acc).r 0 0`, extracts `∃ u ∈ modalKnownWorlds b,
  u ≠ 0` by taking whichever symmetrized direction of `euclGen_symmGen_exists_base`'s witness
  edge actually fired (its target is both known, via `hTgt`, and non-root, via `hRoot`, for free).

**Key lesson for future work on this file**: when a helper lemma needs induction on
`Relation.EuclGen (Relation.SymmGen r) a b` where one or both of `a`, `b` are tied to a FIXED
point from the ambient context (like the root `0`, or a hypothesis like `hRoot` that mentions a
specific point), do NOT fix that point as a literal argument inside the induction's motive if the
recursive calls might need to re-derive the SAME fact at a DIFFERENT point (this breaks `ih1`/
`ih2`, which are only generated for the EXACT stated motive). Prefer either (a) a motive that
doesn't mention the fixed point until the very end (as `euclGen_symmGen_exists_base` does -- get
a fully general fact first, connect to the fixed point in a separate, non-recursive step), or (b)
if genuine self-reference across symmetrized/transformed sub-terms seems needed, STOP and find
the (a)-style reformulation instead -- self-referential recursion through a transformed subterm
(e.g. calling the lemma being proven on `Relation.EuclGen.symm_of_symm h1` inside its own `eucl`
case) is not straightforwardly supported by the `induction ... with` tactic's auto-generated
`ih1`/`ih2` and leads to a dead end (this was tried and abandoned mid-session; the working
`euclGen_symmGen_exists_base` approach above is the one that shipped).

### Phase 6 (partial) -- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

Landed the `accTargetsNeRoot` + root-known-ness top-loop propagation (needed because
`modalTruthLemmaKb5` takes both as hypotheses), mirroring Five's Phase 21
(`modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot`, `FrameCompleteness.lean:3015`)
extended with a THIRD bundled invariant (root-known-ness) because
`modalApplyOneKb5''Prop_knownWorlds_step` (Phase 3, `FiveSimplification.lean:2923`) needs `h0` as
an ambient hypothesis where Five's analogue did not.

New declarations (placed right after `modalTruthLemmaKb5`, before the pre-existing SCOUT section):
- `modalKnownWorlds_fold_spec_C`/`mem_modalKnownWorlds_C`/`modalKnownWorlds_mono_append_C`
  (private local re-derivations of `FmpMeasure.lean`'s file-private originals, same pattern as
  `FrameSoundness.lean`'s `_FS`-suffixed versions).
- `modalStepBranchGen_knownWorlds_mono_C` (private, RULE-GENERIC) -- any step's new branches are
  the old branch with formulas prepended, hence `modalKnownWorlds`-monotone. Exposes the `hbsub`
  fact that's normally buried inside `FmpMeasure.lean`'s `modalStepBranch_preserves_
  accTargetsKnown_gen` proof as its own reusable lemma.
- `hasEdge_addEdge_cases_C`/`modalNextWorld_ne_zero_C` (private local re-derivations, mirror the
  `_Five`-suffixed originals in the Phase-21 section of `FrameCompleteness.lean:2896+`).
- `modalApplyOneKb5''_edge_target_ne_root` -- per-call root-isolation, mirrors
  `modalApplyOneFive_edge_target_ne_root` (`FrameCompleteness.lean:2945`), consuming
  `modalApplyOneKb5''_agree_or_reuse_ne_root` (`FiveSimplification.lean:2612`, Phase 1/2) and
  `modalApplyOneKb5''Prop_knownWorlds_step` (`FiveSimplification.lean:2923`, Phase 3).
- `modalStepBranchKb5''_preserves_accTargetsNeRoot` (single-step).
- `modalStepBranchKb5''_preserves_accTargetsKnown_and_NeRoot_and_rootKnown` (joint three-way
  bundle: `accTargetsKnown` via the fully-generic `modalStepBranch_preserves_accTargetsKnown_gen`
  at `modalApplyOneKb5''_fresh_local`, `accTargetsNeRoot` via the lemma above, root-known-ness via
  `modalStepBranchGen_knownWorlds_mono_C`).
- `modalExpandBranchesKb5''_openBranch_accTargetsKnown_and_NeRoot_and_rootKnown` -- the top-loop
  theorem, instantiating `modalExpandBranchesGen_openBranch_gen` (`BDriver.lean`) at the conjoined
  predicate `P b acc := accTargetsKnown b acc ∧ 0 ∈ modalKnownWorlds b ∧ accTargetsNeRoot acc`.

All `lean_verify`-clean: `propext`/`Classical.choice`/`Quot.sound` only, zero `sorry`.

**Also clarified (no new code needed)**: `accSourcesKnown` and PLAIN `accTargetsKnown`
(individually, without NeRoot) are BOTH fully rule-generic via existing `BDriver.lean` bridges
(`modalExpandBranchesGen_openBranch_accSourcesKnown`/`_accTargetsKnown`), consuming only
`modalApplyOneKb5''_fresh_local` (already landed, Phase 2). These need NO bespoke top-loop lemma
in this file -- use the generic bridges directly at the Phase 7 assembly site.

## Next: finish Phase 6 -- the Hintikka lift (`ModalLoopAuxKb5''`)

This is genuinely the largest remaining piece of work in the entire plan. Read this section fully
before starting; it front-loads the size/risk assessment so the next session does not have to
re-derive it.

### Why this is large

`modalTableauFive_complete`'s own Hintikka-lift call (`FrameCompleteness.lean:3140-3155`)
instantiates `modalExpandBranchesHintikka` (`CompletenessLoop.lean:1432`) with `Aux :=
ModalLoopAuxFive φ₀` (`FrameCompleteness.lean:3055`). `ModalLoopAuxFive` bundles `modalUniverse`
membership with `FiveWorldInvE` (`FiveSimplification.lean:4151`), an `e`-aware refinement of the
plain world-count invariant `FiveWorldInv` (`FiveSimplification.lean:4027`) that Phase 2 already
confirmed `Kb5''WorldInv` coincides with (`Kb5''WorldInv := FiveWorldInv`, `rfl`,
`FiveSimplification.lean:4781-4798`).

The `e`-awareness is NOT optional convenience -- it exists because a root-triggered mint (a
diamond-positive/box-negative rule firing AT world `0`) consumes a mint-tag that was already
counted the moment its TRIGGER merely appeared on the branch (not when it was processed), so a
bare per-step argument cannot show the tag-count grows in lockstep with `modalMaxWorld` at that
step. `FiveWorldInvE`'s fix threads the expanded-set `e` into a refined counter
(`expandedRootTagsFive`, `FiveSimplification.lean:4099`) that only counts a root tag once its
trigger has been DEQUEUED (is in `e`), restoring the lockstep argument.

**This subtlety applies identically to `modalApplyOneKb5''`**: Phase 1 confirmed the MINT
(existential) shapes are `modalApplyOneFive`'s witness-reuse behavior VERBATIM, unchanged by the
gate fix (only the two PROPAGATION shapes, box-positive/diamond-negative, differ). So the exact
same root-triggered-mint tag-counting subtlety recurs, and the exact same `e`-aware fix is needed
-- there is no shortcut around it via the mint-arm agreement lemmas (`modalApplyOneKb5''_agree_
or_reuse_ne_root` etc.), because those lemmas show OUTPUT-SHAPE agreement, not WORLD-COUNT-MEASURE
agreement, and the latter is what `AuxStepPreserved` needs.

Two Five-side lemmas anchor the actual work, both read in full this session:
- `modalApplyOneFive_worldGrowth` (`FiveSimplification.lean:4320-4497`, ~180 lines including the
  non-mint-shape case): for EVERY shape of `modalApplyOneFive sf b acc`'s output, characterizes
  either "every emitted label is already known" (persistent/branching/non-growing linear) or "a
  genuine NEW tag was consumed, emitted at `modalNextWorld b`" (the two growing-mint sub-cases:
  non-root-triggered mint via `usedTagsFiveNonRoot`, root-triggered mint via the root-tag
  bookkeeping). This is the lemma `modalStepBranchFive_preserves_worldInv` case-splits on.
- `modalStepBranchFive_preserves_worldInv` (`FiveSimplification.lean:4499-4721`, ~220 lines): the
  actual `AuxStepPreserved`-shaped step-preservation proof, consuming `modalApplyOneFive_
  worldGrowth` plus `modalApplyOneFive_outputsSubsetUniverse` (F2, catalog-membership) to show
  `FiveWorldInvE` is preserved across every step, in all FOUR `RuleResult` shapes (`linear`,
  `branching`, `persistent`, `notApplicable`), with the `linear` case itself split three ways
  (known-already / non-root-mint / root-mint) matching `modalApplyOneFive_worldGrowth`'s own
  three-way disjunction.

### What does and does NOT transfer from Five

**Does transfer (verbatim mint-arm behavior means these facts hold identically for Kb5'')**:
- The MINT-shape sub-cases of `modalApplyOneKb5''_worldGrowth` (still-to-be-written) should port
  from `modalApplyOneFive_worldGrowth`'s mint-shape case near-verbatim, substituting
  `modalApplyOneKb5''_diaPos_eq_or_reuse`/`_boxNeg_eq_or_reuse` (Phase 1, mirrors Five's own) for
  the Five originals, and `modalApplyOneKb5''_agree_or_reuse_ne_root`
  (`FiveSimplification.lean:2612`) where Five's proof used its own agree-or-reuse lemma.
- `expandedRootTagsFive`/`usedTagsFiveNonRoot`/`mintTags`/`FiveWorldInvE`/`FiveWorldInv` are all
  ALREADY rule-independent definitions over `φ₀`/`b` (they never mention `modalApplyOneFive` by
  name in their own bodies) -- these can be REUSED DIRECTLY for Kb5'' with no renaming needed, if
  a fresh `Kb5''`-named alias is judged unnecessary (check whether the plan's own file-scope
  convention wants a `Kb5''`-suffixed alias purely for naming hygiene, mirroring how `Kb5''
  WorldInv` was still given its own name despite being definitionally `FiveWorldInv`).

**Does NOT transfer (needs fresh case work)**:
- The box-positive/diamond-negative (propagation) shapes. `modalApplyOneFive_worldGrowth`'s own
  non-mint case (the tail of its `by_cases hmint` split, not fully read this session -- read
  `FiveSimplification.lean:4360-4499` in full before starting) presumably shows "every emitted
  label already known" for whatever Five's OWN propagation-adjacent shapes are. For Kb5'', the
  analogous case needs `modalKb5BoxAllUniv_mem`/`modalKb5DiaNegAllUniv_mem` (Phase 1,
  `FiveSimplification.lean:2213`/`2278`) to show every emitted formula's label is either a known
  non-root world or `0` (both already known, via `h0`) -- this should actually be an EASIER case
  than Five's own (no tag-counting needed at all, since `modalApplyOneKb5''Prop_boxPos_diaNeg_eq`,
  Phase 3, already shows `.snd = acc` unconditionally at these shapes, so `modalMaxWorld` cannot
  grow here regardless of tag bookkeeping).
- `modalStepBranchFive_preserves_worldInv`'s own case split will need the SAME four-way
  `RuleResult` split, but each case's "known-already" sub-branch should be a more direct
  application of the propagation-shape argument above rather than Five's own reasoning.

### Concrete plan for the next session

1. Read `modalApplyOneFive_worldGrowth`'s FULL body (`FiveSimplification.lean:4320-4497` --
   this session only read through line ~4360, i.e. the mint-shape case; the non-mint-shape tail
   was NOT read and must be understood before porting).
2. Decide on naming: either alias `FiveWorldInvE`/`expandedRootTagsFive`/etc. directly (simplest,
   since they are provably rule-independent already) or introduce `Kb5''`-suffixed copies purely
   for file-organization clarity. Recommend the alias route to minimize new surface area -- e.g.
   `def Kb5''WorldInvE := FiveWorldInvE` (mirroring `Kb5''WorldInv := FiveWorldInv`'s own `rfl`
   pattern) rather than a full re-derivation, IF the definitions genuinely need no change; only
   fork them if Kb5'''s box-positive/diamond-negative shapes turn out to need a genuinely
   different counting predicate (unlikely, since those shapes never touch accessibility or grow
   `modalMaxWorld` per `modalApplyOneKb5''Prop_boxPos_diaNeg_eq`).
3. Write `modalApplyOneKb5''_worldGrowth`, porting the mint-shape cases from
   `modalApplyOneFive_worldGrowth` per the "does transfer" bullet above, and writing the
   propagation-shape case fresh (should be short: `.snd = acc` means no accessibility change,
   and every emitted formula is already-known via `modalKb5BoxAllUniv_mem`/`_DiaNegAllUniv_mem`
   plus `h0` for the `label = 0` sub-case).
4. Write `modalStepBranchKb5''_preserves_worldInv`, porting `modalStepBranchFive_preserves_
   worldInv`'s four-way `RuleResult` case split (`FiveSimplification.lean:4499-4721`), consuming
   step 3's lemma plus `modalApplyOneKb5''_outputsSubsetUniverse` (Phase 2, already landed,
   `FiveSimplification.lean:3165`) in place of Five's own F2 discharge.
5. Land `ModalLoopAuxKb5''`/`ModalLoopAuxKb5''_bounds`/`ModalLoopAuxKb5''_stepPreserved`/
   `modalLoopInvHintikkaKb5''_initial`, mirroring `FrameCompleteness.lean:3047-3106` (Five's own,
   ~60 lines) verbatim modulo substitution -- these should be genuinely mechanical once step 4
   lands, since they are thin wrappers around it.
6. `lean_verify` everything; confirm zero `sorry`, identical axiom profile.
7. If any step in 3-4 reveals the propagation-shape case is NOT as easy as predicted (i.e. genuine
   new tag-counting reasoning is needed there too), mark Phase 6 `[BLOCKED]` with the exact
   `lean_goal` state -- do NOT insert a placeholder. Given how directly `modalApplyOneKb5''Prop_
   boxPos_diaNeg_eq`'s `.snd = acc` fact should discharge the accessibility-unchanged half, this
   is assessed LOW risk, but flag it if wrong.

**Split trigger, already exercised once**: this handoff IS the split the plan's own Phase 6
"split trigger" anticipated. Do not re-litigate whether to split -- just execute the plan above.

## After Phase 6: Phases 7, 8

Unchanged from the prior handoff's description, copied here for convenience (verify line numbers
have not drifted further once Phase 6 lands, since this session added ~500 lines to
`FrameCompleteness.lean`):

- **Phase 7** (completeness + decidability assembly): `modalOpenBranchKb5''_countermodel`,
  `modalTableauKb5''_complete`, `kb5Valid_decides`, `instDecidableKb5Valid`. Mirror
  `modalTableauFive_complete`'s assembly (`FrameCompleteness.lean:3131-3198`) directly: call the
  Phase 6 Hintikka lift, the generic `accSourcesKnown`/`accTargetsKnown` bridges (NOT bespoke
  lemmas -- see the "Also clarified" note above), the Phase 6 `accTargetsNeRoot`+rootKnown
  top-loop lemma (`modalExpandBranchesKb5''_openBranch_accTargetsKnown_and_NeRoot_and_
  rootKnown`), and `modalTruthLemmaKb5` (Phase 5) at `F(φ₀)@0` for the countermodel. Depends on
  Phase 3 (done), 5 (done), 6 (Hintikka lift outstanding).
- **Phase 8** (docs reconciliation + regression tests + full CI): reconcile stale
  blocker/scope docstrings (durable anchors only, no task-number citations per
  `no-task-references-in-deliverables.md`), extend `CslibTests/ModalFrameSeparation.lean`,
  diagnose (do not fix) the orthogonal `decide`-reduction kernel stall
  (`S5Simplification.lean:1959-1963`), run the full 7-step CSLib CI pipeline (`lake exe cache get`
  first -- likely already warm from this session's builds).

## Hard constraints (unchanged, still binding)

- `modalApplyOneKb5'`/`modalTableauKb5'`/`modalKb5BoxAllFull`/`modalKb5DiaNegAllFull` (frozen
  task-524 deliverables) are **untouched** -- verified via `git diff` showing only additions,
  never edits, to any pre-existing declaration in the touched files, at every commit this session.
- Zero `sorry`, zero new axioms (verified at every commit via `lean_verify` + `grep`).
- `LoopChecking.lean` is out of scope (owned by a separate task) -- not touched, not built as part
  of this session's scoped builds.

## Verification commands to re-run at the start of the next session

```bash
cd ~/Projects/cslib
lake build Cslib.Logics.Modal.Tableau.FiveSimplification \
  Cslib.Logics.Modal.Tableau.FrameSoundness \
  Cslib.Logics.Modal.Tableau.FrameCompleteness
grep -n "sorry" Cslib/Logics/Modal/Tableau/{FiveSimplification,FrameSoundness,FrameCompleteness}.lean | grep -v '^\S*:.*--\|/--'
git log --oneline -10
```
All three should build green; the sorry grep should return only doc-comment mentions; `git log`
should show the 3 commits from this session (`phase 6.1`, `phase 5` fix, `phase 5` complete) at
the top, followed by the 12 commits from the prior session.
