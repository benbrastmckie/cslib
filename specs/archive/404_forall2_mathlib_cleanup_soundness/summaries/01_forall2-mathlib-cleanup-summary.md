# Implementation Summary: Replace local List.Forall₂ re-proofs with Mathlib lemmas

- **Task**: 404 - Replace local private re-proofs of List.Forall2 lemmas with canonical Mathlib lemmas
- **Status**: [COMPLETED]
- **Started**: 2026-07-01T00:00:00Z
- **Completed**: 2026-07-01T00:00:00Z
- **Effort**: ~0.75 hours
- **Dependencies**: None (parent task 402 completed)
- **Artifacts**: plans/01_forall2-mathlib-cleanup.md, reports/01_forall2-mathlib-cleanup.md

## Overview

Replaced four private `List.Forall₂` helper lemmas (`forall₂_of_zip_mem`, `forall₂_append_aux`,
`forall₂_drop_aux`, `forall₂_take_aux`) with their canonical Mathlib counterparts, and rewired
all six call sites in `Cslib/Logics/Modal/Tableau/Soundness.lean`. The change required a single
`import Mathlib.Data.List.Forall2` and no other structural changes.

## What Changed

- `Cslib/Logics/Modal/Tableau/Soundness.lean`: added `import Mathlib.Data.List.Forall2` after the
  `LoopInduction` import; rewrote six call sites to `List.forall₂_iff_zip.mpr`, `List.rel_append`
  (x2), `List.forall₂_drop` (x2), and `List.forall₂_take`.
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean`: deleted the four now-redundant helper lemmas
  (`forall₂_of_zip_mem`, `forall₂_append_aux`, `forall₂_drop_aux`, `forall₂_take_aux`) and updated
  the module docstring/`## Main Lemmas` list accordingly. `forall₂_replicate_right` (out of
  scope, no Mathlib drop-in) was retained unchanged.

## Decisions

- **Deletion site relocated from plan**: the plan and research report (both correct as of their
  drafting time) expected the four helpers to be `private` declarations inside `Soundness.lean`.
  Between research and implementation, an intervening task hoisted them into the shared
  `LoopInduction.lean` module (so `Completeness.lean`/`FmpMeasure.lean` could reuse
  `forall₂_replicate_right` without cross-importing `Soundness.lean`). The deletion was performed
  in `LoopInduction.lean` instead of `Soundness.lean`; the call-site rewrites (all of which live in
  `Soundness.lean`) proceeded exactly as planned.
- **Import placement**: the plain `import Mathlib.Data.List.Forall2` was added directly to
  `Soundness.lean` (where the call sites live), not to `LoopInduction.lean`. A plain (non-public)
  import in `LoopInduction.lean` would not be re-exported to `Soundness.lean` under CSLib's
  `module`/`public import` scheme, so the import must be co-located with its use sites. This was
  confirmed empirically: the first attempt (import in `LoopInduction.lean`) failed with `Unknown
  constant` errors at all six call sites in `Soundness.lean`.

## Impacts

- No public theorem signatures changed; `modalExpandBranches_closed_unsat` and
  `modalTableau_sound` are unaffected in statement, only in proof term.
- `LoopInduction.lean`'s public API is reduced to `forall₂_replicate_right` only; no other file in
  the codebase referenced the four deleted helpers (verified via repo-wide grep before and after).
- Zero sorry, zero new axioms, zero vacuous definitions introduced.

## Follow-ups

- None. The task's non-goals (leaving `forall₂_replicate_right` and the pre-existing unrelated
  warnings untouched) were honored.

## Plan Deviations

- **Task 1.2 (helper deletion location)**: altered — deleted the four helpers from
  `Cslib/Logics/Modal/Tableau/LoopInduction.lean` rather than `Soundness.lean`, because an
  intervening task had already hoisted them there before this task's implementation phase ran.
  The research report's verified lemma-mapping table remained fully valid; only the file location
  of the deletion changed.
- **Task 1.1 (import placement)**: altered — the plan specified placing the import "immediately
  after `import Cslib.Init`" in `Soundness.lean`, but `Soundness.lean` has no direct
  `import Cslib.Init` line (it uses `module`/`public import` of sibling files that transitively
  pull in `Cslib.Init`). The import was placed after the last `public import` line
  (`Cslib.Logics.Modal.Tableau.LoopInduction`) instead, which is the natural insertion point and
  achieves the same effect (a plain, non-public import local to this file).
- No other deviations. All six call-site rewrites, the CI/lint gate, and the zero-sorry/
  zero-axiom/zero-vacuous checks proceeded exactly as planned.

## Verification Results

- `lake build Cslib.Logics.Modal.Tableau.Soundness`: green (493 jobs), 0 errors, 0 sorry.
- `lake build` (full): green (3187 jobs).
- `lake exe checkInitImports`: passed silently.
- `lake lint`: 2 pre-existing errors (`defsWithUnderscore` in
  `Cslib/Logics/Temporal/Theorems.lean`), unrelated to and unmodified by this task.
- `lake exe lint-style`: clean, no output.
- `lake test`: exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: exits 1 due to pre-existing,
  repo-wide import-minimization debt in unrelated Propositional/Temporal modules; grep-confirmed
  neither `Soundness.lean` nor `LoopInduction.lean` appear in shake's add/remove-import findings.
  The only warning shake reports for these two files is the pre-existing `unusedSectionVars` on
  `modalApplyOne_fresh` (now at line 87, shifted by one from the added import line).
- Repo-wide grep confirms all four deleted helper names are gone; `forall₂_replicate_right`
  remains in `LoopInduction.lean`, used at its original two call sites in `Soundness.lean`.

## References

- specs/404_forall2_mathlib_cleanup_soundness/plans/01_forall2-mathlib-cleanup.md
- specs/404_forall2_mathlib_cleanup_soundness/reports/01_forall2-mathlib-cleanup.md
- Cslib/Logics/Modal/Tableau/Soundness.lean
- Cslib/Logics/Modal/Tableau/LoopInduction.lean
