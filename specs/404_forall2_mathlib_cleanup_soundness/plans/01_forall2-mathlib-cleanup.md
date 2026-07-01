# Implementation Plan: Task #404

- **Task**: 404 - Replace local List.Forall₂ re-proofs with Mathlib lemmas in Soundness.lean
- **Status**: [IMPLEMENTING]
- **Effort**: 0.75 hours
- **Dependencies**: None (parent task 402 completed)
- **Research Inputs**: specs/404_forall2_mathlib_cleanup_soundness/reports/01_forall2-mathlib-cleanup.md
- **Artifacts**: plans/01_forall2-mathlib-cleanup.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Replace the four local private `List.Forall₂` helper lemmas in
`Cslib/Logics/Modal/Tableau/Soundness.lean` (`forall₂_of_zip_mem`, `forall₂_append_aux`,
`forall₂_drop_aux`, `forall₂_take_aux`) with their canonical Mathlib counterparts. The research
report verified the exact 1:1 lemma mapping and confirmed the full change builds green (492/492
jobs, 0 errors, 0 sorry) via a trial edit that was then reverted. The change is a single import
addition, four helper deletions, and six call-site rewrites, followed by the full CI gate.

### Research Integration

The report (`01_forall2-mathlib-cleanup.md`) provides a verified lemma-mapping table and the
exact pre-edit line ranges and text for every change:
- Add `import Mathlib.Data.List.Forall2` after `import Cslib.Init` (plain, non-public import —
  the lemmas appear only in proof terms, never in public signatures).
- Delete `forall₂_of_zip_mem`, `forall₂_append_aux`, `forall₂_drop_aux`, `forall₂_take_aux`.
- Keep `forall₂_replicate_right` (out of scope, no trivial Mathlib drop-in).
- Rewrite six call sites to the `List.`-prefixed Mathlib lemmas (`List.forall₂_iff_zip.mpr`,
  `List.rel_append`, `List.forall₂_drop`, `List.forall₂_take`).

The report notes pre-existing, unrelated warnings (`linter.style.longLine` in `SoundnessStep.lean`,
one `unusedSectionVars` on `modalApplyOne_fresh`) that this task does not introduce and must not
be expected to fix.

### Prior Plan Reference

No prior plan supplied as reference input. (A plan file at this path from an interrupted earlier
run is being regenerated; not treated as a template.)

### Roadmap Alignment

No `roadmap_path` provided in delegation context; ROADMAP.md not consulted. This is low-priority
cleanup polish following task 402.

## Goals & Non-Goals

**Goals**:
- Remove the four local `List.Forall₂` re-proofs, replacing them with canonical Mathlib lemmas.
- Add the single `import Mathlib.Data.List.Forall2` and rewire all six call sites.
- Keep the module building green with zero sorry and passing the full CSLib CI/lint gate.

**Non-Goals**:
- Do NOT remove or refactor `forall₂_replicate_right` (out of scope; no clean Mathlib drop-in).
- Do NOT fix pre-existing unrelated warnings in `SoundnessStep.lean` or `modalApplyOne_fresh`.
- Do NOT change any public theorem signatures or add new declarations.
- Do NOT promote the import to `public import` unless shake explicitly requests it.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `List.` namespace prefix omitted at a call site (no `open List`) | L | M | Report gives exact prefixed replacements; scoped build catches immediately |
| `forall₂_iff_zip` call site needs `refine ... .mpr ⟨_, ?_⟩` shape, not `apply` | L | M | Report specifies exact `refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩` form with `intro b a hmem` unchanged |
| `lake shake` requests import promotion or removal | L | L | Run shake in the gate; if it requests promotion, follow its guidance; report predicts plain import is shake-clean |
| Line numbers drift after deletions | L | H | Match on surrounding text (per report), not raw line numbers |
| checkInitImports flags the new import | L | L | Import is module-local, not in Cslib.Init; run checkInitImports in gate to confirm |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Apply import, helper deletions, and call-site rewrites [COMPLETED]

**Goal**: Transform `Soundness.lean` to use Mathlib lemmas, and confirm the scoped module builds.

**Tasks**:
- [x] Add `import Mathlib.Data.List.Forall2` (plain import) to `Soundness.lean`
      *(deviation: added after the `LoopInduction` import in Soundness.lean, not after
      `import Cslib.Init` — this file uses `module`/`public import` syntax with no bare
      `import Cslib.Init` line; the call sites needing the Mathlib lemmas live in
      Soundness.lean, so the import must be direct there, not merely transitive via
      LoopInduction.lean, since plain imports are not re-exported)*.
- [x] Delete the four private helpers: `forall₂_of_zip_mem`, `forall₂_append_aux`,
      `forall₂_drop_aux`, `forall₂_take_aux`. Preserve `forall₂_replicate_right`.
      *(deviation: the helpers were no longer in Soundness.lean — an intervening task
      (see LoopInduction.lean docstring/git history) had already hoisted them into
      `Cslib/Logics/Modal/Tableau/LoopInduction.lean` so Completeness.lean/FmpMeasure.lean
      could share them. Deletion was performed there instead; `forall₂_replicate_right`
      retained in LoopInduction.lean as before)*.
- [x] Rewrite the `forall₂_of_zip_mem` call site:
      `apply forall₂_of_zip_mem hlength_accs.symm`
      → `refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩` (keep the following
      `intro b a hmem` and body unchanged).
- [x] Rewrite both `forall₂_append_aux` call sites to `List.rel_append` (including the nested
      `List.rel_append (List.rel_append hFresh_done hFreshNew) hFresh_rest`).
- [x] Rewrite both `forall₂_drop_aux` call sites to `List.forall₂_drop`.
- [x] Rewrite the `forall₂_take_aux` call site to `List.forall₂_take`.
- [x] Run `lake build Cslib.Logics.Modal.Tableau.Soundness` and confirm green, 0 sorry.

**Timing**: 0.4 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` - add one import, delete four helpers, rewrite
  six call sites to `List.`-prefixed Mathlib lemmas.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Soundness` completes successfully (expect ~492 jobs),
  0 errors, 0 sorry.
- `grep` confirms none of the four deleted helper names remain in the file;
  `forall₂_replicate_right` still present.

---

### Phase 2: Full CI and lint gate [COMPLETED]

**Goal**: Confirm the change passes the complete CSLib CI/lint pipeline with no regressions.

**Tasks**:
- [x] Run full `lake build` (whole library, not just the scoped module). Green, 3187 jobs.
- [x] Run `lake exe checkInitImports` — confirm the new import does not disturb Cslib.Init.
      Passed silently (no violations).
- [x] Run `lake lint`. 2 pre-existing errors reported (`defsWithUnderscore` in
      `Cslib/Logics/Temporal/Theorems.lean`), unrelated and unmodified by this task.
- [x] Run `lake exe lint-style` — confirm no new style violations introduced by this change.
      Clean (no output).
- [x] Run `lake test` (CslibTests suite). Exit 0.
- [x] Run `lake shake --add-public --keep-implied --keep-prefix` — confirm shake is satisfied
      with the plain `import Mathlib.Data.List.Forall2` and requests no promotion/removal.
      *(deviation: repo-wide shake exits 1 due to pre-existing, widespread import-minimization
      debt across many unrelated files (Propositional/Temporal modules); confirmed via grep that
      neither `Soundness.lean` nor `LoopInduction.lean` appear in shake's add/remove-import list
      — only the expected pre-existing `unusedSectionVars` warning on `modalApplyOne_fresh`
      shows up, at line 87 instead of 86 due to the one added import line shifting it down)*.
- [x] Confirm only pre-existing unrelated warnings remain (longLine in SoundnessStep.lean,
      unusedSectionVars on modalApplyOne_fresh); none newly introduced. Confirmed.

**Timing**: 0.35 hours

**Depends on**: 1

**Files to modify**:
- None (verification only).

**Verification**:
- All CI commands exit 0 (or produce only the documented pre-existing warnings).
- `lake shake` reports no required changes to the new import.
- Zero sorry across the build output.

## Testing & Validation

- [x] Scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` green, 0 sorry.
- [x] Full `lake build` green (3187 jobs).
- [x] `lake exe checkInitImports` passes.
- [x] `lake lint` passes (2 pre-existing, unrelated `defsWithUnderscore` errors in
      `Temporal/Theorems.lean`; none in modified files).
- [x] `lake exe lint-style` passes (no new violations).
- [x] `lake test` passes (exit 0).
- [x] `lake shake --add-public --keep-implied --keep-prefix` satisfied with the plain import
      (no add/remove entries for `Soundness.lean` or `LoopInduction.lean`).
- [x] Four helper names absent from the codebase (found and deleted in `LoopInduction.lean`,
      not `Soundness.lean` — see Plan Deviations); `forall₂_replicate_right` retained.

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Tableau/Soundness.lean` (one import added, four helpers removed,
  six call sites rewritten).
- Execution summary at `summaries/01_forall2-mathlib-cleanup-summary.md`.

## Rollback/Contingency

- The change is confined to a single file. If any CI step regresses, `git checkout --
  Cslib/Logics/Modal/Tableau/Soundness.lean` restores the pre-edit state (the local helpers are
  correct as-is and were kept precisely for this reason).
- If `lake shake` requests promoting the import to `public import`, apply that promotion and
  re-run the gate rather than reverting.
- If an unforeseen call site depends on a deleted helper, restore that single helper and document
  in the summary why it was retained (per the task's "or document why the local helpers are kept"
  fallback).
