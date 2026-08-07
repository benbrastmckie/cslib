# Phase 5 Handoff — Migrate mem_modalKnownWorlds; weak fold_spec copies die

**Status**: [COMPLETED]

## What happened

- Deleted all 6 `mem_modalKnownWorlds_*` duplicates (BDriver `_B`, FiveSimplification `_Five`,
  FrameCompleteness `_C`, FrameSoundness `_FS`, LoopChecking `_S4`, S5Simplification `_S5`) and
  the `FmpMeasure.lean` origin. All 6 corresponding weak `modalKnownWorlds_fold_spec_*` copies
  died as dead code exactly as the plan predicted (each one's sole call site was inside its own
  file's now-deleted `mem_modalKnownWorlds_X` proof) and were deleted in the same edit per file.
  Confirmed via full-project build success plus a post-edit repo-wide grep showing zero remaining
  references to any of the twelve deleted names.
- **Forced deviation**: adding the `Support.KnownWorlds` import to `FmpMeasure.lean` and
  `LoopChecking.lean` (needed for those two files' own origin removal to resolve) exposed a Lean
  name-collision error against OTHER still-private same-named declarations in those files
  (`FmpMeasure.lean`'s `modalKnownWorlds_nodup`/`modalKnownWorlds_mono_append`/`mem_boxPositivesOf`;
  `LoopChecking.lean`'s `modalMaxWorld_le_of_forall_label_le`) — nominally Phase 6/7 territory,
  but undeferrable once the import existed. Resolved by deleting all four now. Two turned out to
  need **zero call-site edits** despite a binder-form difference from the published version
  (`modalKnownWorlds_mono_append`'s `⊆` vs `∀ x ∈`, `modalMaxWorld_le_of_forall_label_le`'s
  all-explicit vs implicit binders) — `exact`/`apply` both unify across these forms via defeq.
  This narrows Phase 6's actual remaining risk surface; see below.
- **Census script fix**: `census.py` was silently undercounting after this phase's deletions
  (dropped from 62/39 to an implausible 40/33). Root cause: signal B never scanned `Support/`,
  so once an origin moved there, its remaining suffixed siblings stopped forming a family at all.
  Fixed with `scan_published_names()` + a Support-only exemption from the cross-file-spread
  guard. Corrected running total: **47 duplicates / 38 families**.
- Full invariants table green throughout: build 3313 jobs (unchanged, no new module this phase);
  checkInitImports 0; lint-style 0; shake 0 Modal/Tableau findings (9 total); sorry census exactly
  1; axiom count 0; do-not-edit files untouched.

## Continuation pointer

Resume at **Phase 6**: the judgment-needing phase, but now NARROWER than the plan originally
described since Phase 5's forced cleanup already consolidated several origins:

- **`modalKnownWorlds_mono_append`**: 5 remaining copies (BDriver `_B`, FrameCompleteness `_C`,
  FrameSoundness `_FS`, LoopChecking `_S4`, S5Simplification `_S5`) — NOT 6, `FmpMeasure`'s origin
  is already gone. **Try `exact`/`apply`-based call-site migration FIRST and check whether it
  actually needs the arity rewrite the plan describes** — Phase 5's empirical finding was that it
  did not, for FmpMeasure's 3 internal sites. Confirm per-site before assuming a rewrite is
  needed; only rewrite where the build actually demands it.
- **`modalMaxWorld` family**: `modalMaxWorld_le_of_forall_label_le`'s own duplicate family now has
  only 2 remaining copies (`FiveSimplification.lean` `_Five`, `S5Simplification.lean` `_S5w`) —
  its `LoopChecking.lean`-centric "origin" is already gone too (migrated in Phase 5, not Phase 6).
  The plan's named 4 term-mode sites should be re-checked against the current tree: `FmpMeasure.lean
  ~1884`, `S5Simplification.lean ~1167`, `FiveSimplification.lean ~3328` still plausible;
  `LoopChecking.lean ~6201` no longer applies to `modalMaxWorld_le_of_forall_label_le` itself
  (already migrated) but may still be relevant to `foldl_max_le_of_forall_le`'s own internal use
  if that helper is touched. Also newly surfaced this phase: `modalMaxWorld_foldl_le_of_forall`
  as a census family (`FiveSimplification.lean`'s `_Five`, `S5Simplification.lean`'s `_S5w` foldl
  helpers) — the "internal scaffolding" siblings of the wrapper duplicates, likely resolved as a
  side effect of migrating the wrappers themselves (same call pattern), but confirm.
- **`modalKnownWorlds_nodup`**: only `LoopChecking.lean`'s **public**, **live** (2 uses)
  `modalKnownWorlds_nodup_S4` remains as a census family member. Per the plan: this is NOT
  automatically a deletion target — classify whether it's a pure duplicate wrapper (route to
  published form, delete) or a genuine consumer needing to stay. `FmpMeasure`'s origin is already
  gone (Phase 5).
- **`mem_boxPositivesOf`**: 2 remaining copies (`LoopChecking.lean` `_S4`, `S5Simplification.lean`
  `_S5`) — `FmpMeasure`'s origin is already gone (Phase 5).

Before editing, per established discipline: run
`python3 specs/558_tableau_support_private_dedup/scripts/census.py --family <name>` for each of
the above, PLUS a manual `grep -rn "NAME'" *.lean` prime check.
