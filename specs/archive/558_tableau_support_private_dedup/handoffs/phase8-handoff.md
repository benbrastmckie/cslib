# Phase 8 Handoff — Delete Tier-2 duplicates (LoopChecking, S5Simplification)

**Status**: [COMPLETED]

## What happened

Deleted 14 FmpMeasure-origin Tier-2 duplicates across `LoopChecking.lean` (11:
`modalSubfmls_trans_S4`, `mintGroup_label_eq_freshWorld_S4`, `outDeg_addEdge_self_S4`,
`outDeg_addEdge_ne_S4`, `modalCount_notMem_append_drop_S4`, `modalCount_notMem_mono_S4`,
`modalWork_drop_linear_S4`, `modalWork_drop_persistent_S4`, `modalExpMeasure_split_S4`,
`modalExpMeasure_append_S4`, `modalExpMeasure_const_exp_S4`) and `S5Simplification.lean` (3:
`mem_modalUniverse_of_S5w`, `modalUniverse_mem_formula_S5w`, `modalSubfmls_trans_S5`), routing
call sites to the now-public `FmpMeasure.lean` declarations.

**Important false positive caught and reverted**: `boxProps_outputs_subset_S4` and
`diaNegProps_outputs_subset_S4` were initially deleted per the census match, then the build
immediately failed with a type mismatch — these are genuinely S4-specific facts (stated over
`modalUniverseS4`/`modalWorldBoundS4`, not the generic `modalUniverse`/`modalWorldBound`), the
same trap as the Phase 2-discovered `mem_modalUniverseS4_of`. Restored both verbatim from the
last commit and reverted their 4 call sites.

**Lesson for Phases 9-10**: before deleting ANY `_S4`/`_S5`/`_Five`-suffixed census match, grep
the declaration BODY for a matching type-level suffix (`modalUniverseS4`, `modalWorldBoundS4`,
etc.), not just the lemma-name suffix — a type-level suffix means the fact is genuinely
frame-specific, not a re-derivation duplicate, regardless of the lemma name.

Full invariants table green: build 3313 jobs (unchanged); checkInitImports 0; lint-style 0; shake
0 Modal/Tableau findings; sorry census exactly 1; axiom count 0; six landed Decidable instances +
`modalTableauS4Keyed_complete` confirmed present, full build success confirms elaboration.
Post-phase census: 26 duplicates / 23 families.

## Continuation pointer

Resume at **Phase 9**: delete Tier-2 duplicates in `FiveSimplification.lean`, `BDriver.lean`,
`FrameSoundness.lean`, `FrameCompleteness.lean`. Apply Phase 8's lesson at every deletion: check
the declaration body for a frame-specific type suffix before trusting the lemma-name suffix
alone.

Run `python3 specs/558_tableau_support_private_dedup/scripts/census.py > /tmp/census.txt` then
`awk` for the four target files (as done in this handoff) to get the exact site list. Named
targets from the plan: `modalSubfmls_trans_B` (`BDriver.lean` — note its reordered implicit
binders `{a c} {b}` vs `{a b c}`, harmless since call sites are term-mode with positional
hypotheses), plus the remaining Tier-2 duplicates in `FiveSimplification.lean`,
`FrameSoundness.lean`, `FrameCompleteness.lean`. Preserve the existing
`omit [DecidableEq Atom] [Hashable Atom] in` pattern at `BDriver.lean` ~208 when routing to the
public form if that pattern still applies. Confirm `modalTableauS4Keyed_complete` and the five
`Decidable` instances in `FrameCompleteness.lean` still elaborate after each sub-step (this file
is edited here too).

The plan's own Scope Hypothesis for Phase 9: "the balance of the ~23 Tier-2 duplicates" should
land in these four files, and "Phase 8's remainder plus this phase's enumerated set must sum to
the Tier-2 total measured in Phase 7" — Phase 8 actually resolved 14 (not a fixed ~23-minus-X
figure, since the actual baseline diverged from the plan's estimate throughout). Use the current
26/23 census as the live denominator; do not force a match against the plan's original arithmetic.
