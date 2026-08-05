# Phase 7 Handoff — De-privatize Tier-2 facts in FmpMeasure.lean

**Status**: [COMPLETED]

## What happened

De-privatized 16 `FmpMeasure.lean` declarations (removed `private`, no new docstrings needed —
all already had one): `modalSubfmls_trans`, `mem_modalUniverse_of`, `modalUniverse_mem_formula`,
`modalKnownWorlds_le_modalMaxWorld`, `mintGroup_label_eq_freshWorld`, `modalExpMeasure_split`,
`modalExpMeasure_append`, `modalExpMeasure_const_exp`, `outDeg_addEdge_self`, `outDeg_addEdge_ne`,
`boxProps_outputs_subset`, `diaNegProps_outputs_subset`, `modalCount_notMem_append_drop`,
`modalCount_notMem_mono`, `modalWork_drop_linear`, `modalWork_drop_persistent`.

**Deviation**: only 43 privates remained at phase start (plan assumed 50) since 7 of the plan's
originally-named facts were already moved to `Support/` in Phases 3/5/6 instead of de-privatized
here. Left 27 non-re-derived privates untouched, including `mem_modalUniverse_of'` (confirmed
zero cross-file duplicates via grep, correctly NOT de-privatized despite resembling the
`mem_modalUniverse_of` family).

Additive phase, no consumer changed. Full invariants green: build 3313 jobs; checkInitImports 0;
lint-style 0 (docstring coverage confirmed for all 16 new publics); shake 0 Modal/Tableau
findings; sorry census exactly 1; axiom count 0. Census unchanged at 40/33 (expected — this phase
publishes, doesn't delete duplicates).

## Continuation pointer

Resume at **Phase 8**: delete Tier-2 duplicates in `LoopChecking.lean` and `S5Simplification.lean`,
routing to the now-public `FmpMeasure.lean` declarations. Both files already reach `FmpMeasure`
transitively (confirm no import addition is needed — if one appears necessary, that contradicts
the reachability finding and must be recorded).

Run `python3 specs/558_tableau_support_private_dedup/scripts/census.py --files LoopChecking.lean
S5Simplification.lean` for the exact site list before editing. Expected families in these two
files (from the current 33-family list): `modalSubfmls_trans`, `mem_modalUniverse_of`,
`modalUniverse_mem_formula`, `modalExpMeasure_split`/`_append`/`_const_exp` (all three in
`LoopChecking.lean`), `modalCount_notMem_append_drop`, `modalCount_notMem_mono`,
`modalWork_drop_linear`, `modalWork_drop_persistent`, `outDeg_addEdge_self`/`_ne`. The stale
`mem_modalUniverse_of` comment in at least one of these files ("swapped to plain
`modalUniverse`/`modalWorldBound`") should be treated as stale prose per the plan, not a hazard
signal — the copies are byte-identical to the original.
