# Phase 3 Handoff — Migrate Accessibility consumers, delete duplicates

**Status**: [COMPLETED]

## What happened

Deleted every duplicate of the three `Support/Accessibility.lean` facts and routed consumers to
the published forms, across 7 files (7 per-substep commits, phase 3.1-3.7):

- **`hasEdge_addEdge_cases`**: deleted 7 copies (BDriver.lean `_B`, FmpMeasure.lean `_local`,
  FrameCompleteness.lean `_Five`/`_C`, FrameSoundness.lean `_anc`/`_FS`, LoopChecking.lean `_S4`)
  plus the `Soundness.lean` original. **Deviation**: no `S5Simplification.lean` copy actually
  exists (confirmed by direct grep) — the plan's family-site list was one file short of disk
  reality; 7 real copies, not 8.
- **`mem_successorsOf_hasEdge`**: deleted 3 copies (LoopChecking.lean `_S4`, S5Simplification.lean
  `_S5` — found genuinely dead, zero call sites anywhere — and FrameSoundness.lean's
  trailing-prime `mem_successorsOf_hasEdge'`, a naming convention `census.py` does not
  mechanically catch and which was NOT named anywhere in the plan text) plus the `FmpMeasure.lean`
  original. **Deviation**: actual duplicate count is 3, not the plan's stated 2.
- **`hasEdge_mem_successorsOf`**: deleted the Phase-1-relocated `LoopChecking.lean` private copy;
  4 call sites needed no text edit (published name is identical).
- Fixed one stale prose reference inside the sorry-carrying
  `branchSatisfiableIn_s4FC_ancestor_redirect` docstring in `FrameSoundness.lean` (cited the
  Phase-1-deleted name `hasEdge_mem_successorsOf_origin`); the sorry and its proof term were not
  touched — build confirms it is unaffected (still exactly 1 sorry in `Modal/Tableau`, same
  declaration).
- Full invariants table re-verified green after every sub-step: build 3312 jobs; checkInitImports
  0; lint-style 0; shake 0 Modal/Tableau findings (9 total, all 6 new
  `Support.Accessibility` imports register as genuinely used, none flagged); sorry census exactly
  1; axiom count 0; do-not-edit files untouched throughout.
- Post-phase census: all three families report `TOTAL_DUPLICATE_DECLARATIONS=0` when scoped via
  `--family`. Running total: 62 duplicates / 39 families (down from 71/41 at Phase 2's close).

## Continuation pointer

Resume at **Phase 4**: create `Support/KnownWorlds.lean`. Publish, in order:
`mem_modalKnownWorlds` (highest leverage — Phase 5 depends on it going first),
`modalKnownWorlds_fold_spec` (strong form), `modalKnownWorlds_nodup`,
`modalKnownWorlds_mono_append` (`∀ x ∈ …` form, not `⊆`), `mem_boxPositivesOf`,
`modalMaxWorld_le_of_forall_label_le` (implicit-binder wrapper form) + its `foldl` helper.

Before Phase 4/5/6 editing, given this phase's pattern of finding plan-unnamed duplicate copies,
run `python3 specs/558_tableau_support_private_dedup/scripts/census.py --family <name>` for each
of the six families PLUS a manual `grep -rn "NAME'" *.lean` prime check for each, the same
two-signal discipline used successfully in Phase 3.
