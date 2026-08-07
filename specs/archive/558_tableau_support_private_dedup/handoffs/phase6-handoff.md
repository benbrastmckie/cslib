# Phase 6 Handoff — Migrate judgment-needing KnownWorlds families

**Status**: [COMPLETED]

## What happened

All four families the plan flagged as "judgment-needing" turned out to require dramatically less
manual judgment than anticipated, because Phase 5's forced collision cleanup had already
consolidated the FmpMeasure-origin half of each family:

- **`modalKnownWorlds_mono_append`**: 5 remaining copies (not 6), all already in the exact
  published `∀ x ∈` form — deleted and call sites name-substituted with zero arity rewrites.
- **`modalMaxWorld_le_of_forall_label_le`**: 2 remaining copies (`FiveSimplification.lean`,
  `S5Simplification.lean`), both implicit-binder form already. The plan's "4 term-mode sites
  needing manual adjustment" turned out to be exactly what its own parenthetical said — each was
  the wrapper's own internal call to its private `foldl` helper, which became dead code the
  moment the wrapper was deleted, requiring no separate adjustment.
- **`modalKnownWorlds_nodup`**: only `LoopChecking.lean`'s public, live `_S4` copy remained.
  Classified as a pure duplicate wrapper (byte-identical statement) and deleted, confirmed no use
  outside its own file first.
- **`mem_boxPositivesOf`**: 2 remaining copies, byte-identical, deleted.

Full invariants table green throughout: build 3313 jobs (unchanged); checkInitImports 0;
lint-style 0; shake 0 Modal/Tableau findings (9 total); sorry census exactly 1; axiom count 0;
do-not-edit files untouched. Post-phase census: 40 duplicates / 33 families.

## Continuation pointer

Resume at **Phase 7**: de-privatize Tier-2 facts in place in `FmpMeasure.lean`. The plan's
original ~14-declaration target list overlaps heavily with what Phases 4-6 already moved to
`Support/` instead of de-privatizing in place — cross-check each named declaration
(`modalSubfmls_trans`, `mem_modalUniverse_of`, `modalUniverse_mem_formula`, `mem_boxPositivesOf`,
`mem_successorsOf_hasEdge`, `modalKnownWorlds_fold_spec`, `modalKnownWorlds_nodup`,
`mem_modalKnownWorlds`, `modalKnownWorlds_le_modalMaxWorld`, `modalKnownWorlds_mono_append`,
`mintGroup_label_eq_freshWorld`, `modalExpMeasure_split`, `modalExpMeasure_append`,
`modalExpMeasure_const_exp`) against the CURRENT `FmpMeasure.lean` before assuming it's still
there to de-privatize — several (`mem_boxPositivesOf`, `mem_successorsOf_hasEdge`,
`modalKnownWorlds_fold_spec`, `modalKnownWorlds_nodup`, `mem_modalKnownWorlds`,
`modalKnownWorlds_mono_append`) were already DELETED from `FmpMeasure.lean` in Phases 3/5/6 (moved
to `Support/` instead of de-privatized). Run
`grep -c "^private " Cslib/Logics/Modal/Tableau/FmpMeasure.lean` for the fresh baseline (was
exactly 50 at task start; will now be lower) before starting Phase 7's own Scope Hypothesis
check, and use the census-only finds list (`outDeg_addEdge_self`, `outDeg_addEdge_ne`,
`boxProps_outputs_subset`, `diaNegProps_outputs_subset`, `modalCount_notMem_append_drop`,
`modalCount_notMem_mono`, `modalWork_drop_linear`, `modalWork_drop_persistent`,
`modalKnownWorlds_le_modalMaxWorld`) plus `modalSubfmls_trans`/`mem_modalUniverse_of`/
`modalUniverse_mem_formula`/`modalExpMeasure_split`/`_append`/`_const_exp`/
`mintGroup_label_eq_freshWorld` as the actually-remaining de-privatization target list.
