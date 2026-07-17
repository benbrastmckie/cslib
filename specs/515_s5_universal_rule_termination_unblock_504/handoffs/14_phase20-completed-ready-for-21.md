# Handoff 14: Phase 20 COMPLETED; ready for Phase 21

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 20 (`extractModelFive` + the Euclidean truth lemma) -- now `[COMPLETED]`
**Commit landed this dispatch**: `deda5136` (`task 515 phase 20: land extractModelFive +
Euclidean truth lemma`)

## What landed this dispatch

Resumed from `handoffs/13_phase19b-completed-all-phase19-closed.md` (all of Phase 19 fully
`[COMPLETED]`, untouched here). This dispatch closed Phase 20 in full -- see
`summaries/14_phase20-euclidean-truth-lemma-landed.md` for the complete declaration-by-declaration
account. In brief:

- **`FiveSimplification.lean`** (additive): four membership-introduction lemmas
  (`modalFiveBoxAll_mem_of_{root,ne_root}`, `modalFiveDiaNegAll_mem_of_{root,ne_root}`).
- **`FrameCompleteness.lean`** (additive, new section): `extractModelFive` + its three basic
  lemmas, `accTargetsNeRoot` (new hypothesis) + two structural `EuclGen`-root lemmas,
  `euclGen_mem_modalKnownWorlds_iff`, `modalApplyOneFive_eq_of_prop_shape`,
  `hintikkaFive_box_pos`/`hintikkaFive_diamond_neg`, the capstone `modalTruthLemmaFive`, and
  `modalOpenBranchFive_countermodel`.

**Key design finding**: the universal-propagation direction of the truth lemma needed one
genuinely new hypothesis beyond `hSrc`/`hTgt`: `accTargetsNeRoot acc` (raw tableau edges never
target the root). Without it the truth lemma is false in general (concrete counterexample
recorded in the summary). This is taken as an abstract hypothesis here, exactly like `hSrc`/
`hTgt` -- **Phase 21 must discharge it** for a real tableau run, alongside its existing
`hSrc`/`hTgt` obligation, when it instantiates `modalTableauFive_complete`.

Full CI green: scoped + full `lake build` (3240/3240), `checkInitImports` exit 0, `lint-style`
clean, full-repo `lake lint`/`lake shake` show zero new warnings/suggestions attributable to
either touched file, `lake test` exit 0, zero `sorry` in either file, axioms confirmed via
`lake env lean` + `#print axioms` on all 16 new declarations as `[propext, Classical.choice,
Quot.sound]` (or a subset) only -- no `sorryAx`, no new custom axiom.

## Procedural note (not a blocker)

The plan file already had an **uncommitted, pre-existing** `[NOT STARTED] → [IN PROGRESS]` edit
to the Phase 22 heading in the working tree at the start of this dispatch (visible via `git diff`
before any work began -- not made by this dispatch, likely a leftover from a different concurrent
session). Unlike the prior dispatch (which inadvertently carried an analogous stray Phase 21
marker into its commit via a whole-file `git add`), this dispatch used `git add -p` to stage only
the two Phase 20 hunks (heading + checklist), leaving the stray Phase 22 marker unstaged and
untouched in the working tree. No Phase 22 work was performed or claimed by this dispatch.

## Resume point for Phase 21

1. **All of Phase 19 (19a + 19b) and Phase 20 are now closed.** `modalTableauFive_sound`,
   `extractModelFive`, `extractModelFive_rightEuclidean`, `modalTruthLemmaFive`, and
   `modalOpenBranchFive_countermodel` are all landed, green, sorry-free, and axiom-clean. Do NOT
   re-derive any of them.
2. Phase 21 (`modalTableauFive_complete` + `Decidable (fiveValid φ)`, `FrameCompleteness.lean`)
   is now genuinely unblocked -- its stated preconditions (19b's `modalTableauFive_sound`, 20's
   countermodel) are both satisfied. Its plan heading already shows `[IN PROGRESS]` (an
   uncommitted, pre-existing marker from a prior/concurrent session -- no implementation exists
   yet; verify this before assuming any Phase 21 work has started).
3. **New obligation for Phase 21 beyond what the plan's Phase 21 task list states**: when
   instantiating `modalTableauFive_complete` from a real open branch, Phase 21 must supply not
   only `accSourcesKnown`/`accTargetsKnown` (as S5's `modalTableauS5_complete` already does via
   the generic top-loop lemmas) but also **`accTargetsNeRoot`** for the real `acc` produced by
   `modalTableauFive`/`modalExpandBranchesFive`. This is genuinely provable (mint targets are
   fresh hence positive; Phase 19b's `modalApplyOneFive_agree_or_reuse_ne_root` shows reuse
   targets are non-root too) but requires its own top-loop preservation lemma pair (mirroring
   `modalStepBranch_preserves_accTargetsKnown_gen` +
   `modalExpandBranchesGen_openBranch_accTargetsKnown`), which does not yet exist. Budget for
   this in Phase 21's scope; see `summaries/14_phase20-euclidean-truth-lemma-landed.md`'s "Key
   design finding" section for the full mathematical justification and a concrete counterexample
   showing why it cannot be skipped.
4. Phases 22-23 (KB5 chain) remain queued behind Phase 21 per the plan's own dependency graph.
5. Resolve every declaration by name (`lean_local_search`/`lean_declaration_file`/grep), not by
   plan line-number citations, which go stale as the file grows.
6. Do NOT touch `S5Simplification.lean`'s shared `S5w*` declarations; if truly unavoidable, stop
   and escalate.
7. When staging the plan file, `git diff` it first and use `git add -p` (hunk-scoped) if a stray
   marker from a concurrent session is present, rather than whole-file `git add`.

## Files touched this dispatch

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`
  (Phase 20 marker + checklist only)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/summaries/14_phase20-euclidean-truth-lemma-landed.md`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/handoffs/14_phase20-completed-ready-for-21.md`
  (this file)
