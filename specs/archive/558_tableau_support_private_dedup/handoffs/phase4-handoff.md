# Phase 4 Handoff — Create Support/KnownWorlds.lean

**Status**: [COMPLETED]

## What happened

- Created `Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean`, importing only `Branch.lean`.
  Publishes, in file-dependency order (fold_spec must precede its two dependents):
  `modalKnownWorlds_fold_spec` (strong form) -> `modalKnownWorlds_nodup` ->
  `mem_modalKnownWorlds` -> `modalKnownWorlds_mono_append` (`∀ x ∈` form) -> `mem_boxPositivesOf`
  -> `modalMaxWorld_foldl_le_of_forall` (private helper) -> `modalMaxWorld_le_of_forall_label_le`
  (implicit-binder form).
- No typeclass instances declared in the module (none of the six facts need
  `DecidableEq Atom`/`Hashable Atom`), matching Phase 2's Accessibility module.
- Registered in `Cslib.lean` immediately after `Support.Accessibility`.
- **Deviation**: `modalMaxWorld_le_of_forall_label_le`'s nominal origin per the plan
  (`LoopChecking.lean:6155`, unsuffixed) actually uses ALL-EXPLICIT binders — the opposite of
  the implicit form the plan explicitly asks to publish. Built the published form from the two
  OTHER copies instead (`FiveSimplification.lean`'s `_Five`, `S5Simplification.lean`'s `_S5w`),
  which already use implicit binders and represent the majority convention. `FmpMeasure.lean`
  separately has an unrelated, differently-named wrapper `modalMaxWorld_le_of_forall_le`
  (no `_label` in the name) — not touched.
- **Build note for future Support modules**: the `foldl` helper's proof hit an instance-diamond
  mismatch (generic Mathlib `max_le` elaborating against `LinearOrder.toMax` while
  `modalMaxWorld`'s own `max`, defined in the minimally-importing `Branch.lean`, resolves to core
  `Nat.instMax`). Fixed with `Nat.max_le.mpr` instead of generic `max_le`, matching the pattern
  `Branch.lean` itself already uses in `modalMaxWorld_le_append`. Any future Support module
  reasoning about `Nat`/`WorldIndex` `max` should reach for the `Nat`-specific lemma family, not
  the general order-theoretic one, to avoid this class of error.
- Full invariants table green: build 3313 jobs (+1); checkInitImports 0; lint-style 0; shake 0
  Modal/Tableau findings (9 total); sorry census exactly 1; axiom count 0; do-not-edit files
  untouched.

## Continuation pointer

Resume at **Phase 5**: the ordering-critical phase. Route consumers to the published
`mem_modalKnownWorlds`, which should strand all six `modalKnownWorlds_fold_spec_*` copies with
zero call sites (each copy's sole call site is inside the corresponding
`mem_modalKnownWorlds_X` proof, per the plan). **Do not** attempt to route any consumer through
the strong `fold_spec` if a copy retains a call site after migration — stop and report per the
plan's explicit instruction.

Before editing, per Phase 3's established discipline: run
`python3 specs/558_tableau_support_private_dedup/scripts/census.py --family mem_modalKnownWorlds`
and `--family modalKnownWorlds_fold_spec`, PLUS a manual
`grep -rn "mem_modalKnownWorlds'\|modalKnownWorlds_fold_spec'" *.lean` prime check, before
concluding the site list is complete — Phase 3 found the mechanical census under-counts by one
member in two of its three families due to trailing-prime naming.

Known Phase 5 targets (from the plan): 6 `mem_modalKnownWorlds_*` copies across BDriver.lean,
FiveSimplification.lean, FrameCompleteness.lean, FrameSoundness.lean, LoopChecking.lean,
S5Simplification.lean (plus the FmpMeasure.lean origin, same identical-name-no-call-site-edit
pattern as Phase 3's Soundness/FmpMeasure originals). Then the 6 `modalKnownWorlds_fold_spec_*`
copies at their known sole call sites (BDriver.lean ~963, FrameCompleteness.lean ~3792,
FrameSoundness.lean ~2108, FiveSimplification.lean ~820, LoopChecking.lean ~2952,
S5Simplification.lean ~1042 — all line numbers pre-Phase-3-edits, will have shifted; locate by
declaration/call name, not line number, per the task's standing instruction).
