# Implementation Summary: Extract re-derived private Tableau facts into public Support modules

- **Task**: 558 - Extract re-derived private Tableau facts into public Support modules
- **Status**: [COMPLETED]
- **Plan**: `specs/558_tableau_support_private_dedup/plans/01_tableau-support-private-dedup.md`
- **Type**: cslib

## Overview

Executed all 11 phases of the implementation plan. `Cslib/Logics/Modal/Tableau/` carried 72
duplicate declarations (measured; later refined across the task as the census methodology
itself was corrected) produced by re-deriving facts that already existed elsewhere in the
subsystem but were `private`. Two new modules, `Support/Accessibility.lean` and
`Support/KnownWorlds.lean`, now publish those facts once, sitting directly above `Branch.lean`
(which stays under a do-not-edit constraint). Nine of `FmpMeasure.lean`'s re-derived facts were
de-privatized in place. Duplicates were deleted in graded batches across ten consumer files, each
batch ending at a green `lake build Cslib`.

## Final State

- **Declaration-level census**: 14 duplicate declarations / 14 families remain, every one
  individually documented as a Reasoned Exclusion in the plan's Phase 10 section (public-origin
  duplication, an ambient-instance dodge, a wrong-direction import, four false-positive census
  matches over genuinely distinct frame-specific types, and five duplicate pairs where neither
  file's module reaches the other in the current import graph).
- **Build**: `lake build Cslib` succeeds, 3313 jobs (baseline 3311, +2 for the two new Support
  modules).
- **`lake exe checkInitImports`**: exit 0, no output.
- **`lake exe lint-style`**: exit 0, no output.
- **`lake shake --add-public --keep-implied --keep-prefix`**: 0 findings in `Modal/Tableau`, 9
  findings overall (unchanged from baseline; overall exit 1 is the documented baseline, not a
  regression).
- **Sorry census**: exactly 1 line in `Modal/Tableau/`, declaration
  `branchSatisfiableIn_s4FC_ancestor_redirect` in `FrameSoundness.lean` — pre-existing, untouched.
- **Axiom count**: 0 in `Modal/Tableau/` — unchanged from baseline.
- **`modalTableauS4Keyed_complete`** and all six `Decidable` instances (K/T/B/S5/Five/KB5)
  confirmed present and elaborating.
- **`Rules.lean`, `Saturation.lean`, `Branch.lean`**: confirmed unmodified across all 11 phases.
- **`lake test`**: 9378 jobs, clean.

## Phase-by-Phase Summary

1. **Free deletions** — deleted 2 zero-call-site declarations, relocated 1 forward-reference
   workaround. Built the reusable declaration-level census script.
2. **`Support/Accessibility.lean`** — published `hasEdge_addEdge_cases`,
   `mem_successorsOf_hasEdge`, `hasEdge_mem_successorsOf`.
3. **Migrate Accessibility consumers** — deleted 11 duplicates across 7 files, including one
   fourth copy (a trailing-prime variant) the plan's own text hadn't named.
4. **`Support/KnownWorlds.lean`** — published 6 facts including `mem_modalKnownWorlds`,
   `modalKnownWorlds_fold_spec` (strong form), `modalMaxWorld_le_of_forall_label_le` (built from
   the majority implicit-binder convention rather than the plan's nominal but minority-form
   "origin").
5. **Migrate `mem_modalKnownWorlds`** — deleted 6 duplicates plus all 6 weak `fold_spec` copies as
   predicted dead code. A forced Lean name-collision (adding the new import exposed other
   still-private same-named `FmpMeasure.lean`/`LoopChecking.lean` declarations) required
   consolidating 4 more facts ahead of their nominal phase.
6. **Judgment-needing KnownWorlds families** — every "arity change" and "binder-mode adjustment"
   the plan anticipated turned out to need zero call-site rewrites in practice (`exact`/`apply`
   both unify the differing forms via defeq).
7. **De-privatize Tier-2 FmpMeasure facts** — 16 declarations de-privatized in place, all already
   carrying docstrings.
8. **Delete Tier-2 duplicates (LoopChecking, S5Simplification)** — 14 declarations consolidated.
   Caught and reverted a false positive mid-edit: two declarations that looked like duplicates by
   name were genuinely distinct facts over an S4-specific type, caught by a build-time type
   mismatch.
9. **Delete Tier-2 duplicates (remaining four files)** — only `BDriver.lean` and
   `FiveSimplification.lean` had any remaining Tier-2 duplicates (6 declarations); the other two
   named files had none.
10. **Tier-3 triage** — traced the full transitive import graph for every residue family rather
    than trusting the plan's origin-file groupings. Resolved 6 more as genuine duplicates
    (2 plan-undocumented, found in Phase 1's audit); classified the remaining 14 into an expanded
    Reasoned Exclusions table, including 4 reclassified from "public-origin duplication" to "not
    real duplicates at all" (same S4-specific-type trap as Phase 8) and 5 newly-discovered
    unreachable pairs where the plan's grouping didn't survive an import-graph check.
11. **Final census and comment cleanup** — a manual sweep of surviving `Local re-derivation`
    comments found and resolved 2 further duplicate declarations that no version of the
    declaration-level census ever caught (an irregular word-order naming convention). Corrected a
    stale "55 sites" figure in `LoopChecking.lean`'s own module docstring.

## Plan Deviations

Every deviation is documented inline in the plan file at the task-list item it applies to,
per-phase. The material ones, summarized:

- **Census baseline correction**: the plan estimated 72 duplicates / 41 families. The
  declaration-level census script needed several correctness fixes across the task (character-class
  bug swallowing primes/`?`, docstring-prose false positives, a same-file false-positive class,
  and Support/-module awareness). The measured, corrected baseline was 71/41 at Phase 1's close —
  coincidentally very close to the plan's estimate — but the exact number is not load-bearing;
  what matters is that the final 14/14 residue is individually documented.
- **Two families not named anywhere in the plan** (`modalApplyOneT_branchingLength`,
  `modalApplyOneT_persistentFresh`) were discovered by the Phase 1 audit and correctly resolved
  in Phase 10.
- **Forced cross-phase consolidation**: Lean's private/public name-collision rule forced several
  facts nominally scoped to Phases 6/7 to be resolved during Phase 5, when the collision was
  discovered.
- **Two false-positive catches**: both caught by build-time type errors, not by inspection —
  `mem_modalUniverseS4_of`/`_of'` (discovered during audit, never deleted) and
  `boxProps_outputs_subset_S4`/`diaNegProps_outputs_subset_S4` (deleted, build failed, reverted
  before committing). Both are genuinely S4-specific facts over `modalUniverseS4`/
  `modalWorldBoundS4`, not re-derivations of the generic `FmpMeasure` originals.
- **Reasoned Exclusions table expanded** from the plan's original 4 rows to 7, reclassifying 4
  families and adding 5 newly-discovered unreachable pairs, with full reachability evidence for
  each.
- **2 duplicates found only by manual comment sweep** in Phase 11
  (`known_label_le_modalMaxWorld_Five`/`_S5w`), using a naming convention no census script version
  ever matched — resolved in Phase 11 rather than left as residue, since they were unambiguous
  once found.

## Follow-up Recommendations

Two follow-up tasks are recommended, per the plan's own Phase 10 instruction:

1. **8 genuinely public-origin duplicate families** (`hintikka_congr`, `modalApplyOne_fresh`,
   `modalExpMeasure_step_lt`, `modalSubfmls_self_mem`, `modalApplyOneS5_fresh_local`, plus the 3
   reclassified-as-not-actually-duplicates families are now excluded from this count since they
   were found not to be duplication at all) — not caused by privacy, need a separate judgement
   call on whether to unify or leave as genuine specializations.
2. **5 confirmed-unreachable duplicate families** (`accFreshInv_append`, `hasEdge_addEdge_mono`,
   `modalApplyOne_boxPos_acc_eq`, `modalApplyOne_diamondNeg_acc_eq`, `not_shape_of_not_or`) — these
   ARE privacy-caused and genuinely resolvable, but need new architectural work (a further
   `Support/`-style module, or a considered new import addition) that is out of this task's scope
   to add unilaterally.

## Artifacts

- `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean` (new)
- `Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean` (new)
- `specs/558_tableau_support_private_dedup/scripts/census.py` (reusable declaration-level census
  tool, preserved for future maintenance)
- `specs/558_tableau_support_private_dedup/scripts/shake_check.sh` (shake-noise-filtering helper)
- Deletions/de-privatizations across `FmpMeasure.lean`, `Soundness.lean`, `BDriver.lean`,
  `LoopChecking.lean`, `S5Simplification.lean`, `FiveSimplification.lean`, `FrameSoundness.lean`,
  `FrameCompleteness.lean`, `CompletenessLoop.lean`, `TDriver.lean`, `Completeness.lean`
- `Cslib.lean` — two new module registrations
- 11 phase handoff documents under `specs/558_tableau_support_private_dedup/handoffs/`
