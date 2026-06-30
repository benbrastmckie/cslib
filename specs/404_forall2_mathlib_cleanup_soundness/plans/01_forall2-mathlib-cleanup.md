# Implementation Plan: Task #404

- **Task**: 404 - forall2_mathlib_cleanup_soundness
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/404_forall2_mathlib_cleanup_soundness/reports/01_forall2-mathlib-cleanup.md
- **Artifacts**: plans/01_forall2-mathlib-cleanup.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Replace four local private `List.Forall₂` re-proofs in
`Cslib/Logics/Modal/Tableau/Soundness.lean` with their canonical Mathlib counterparts.
The change adds one import (`Mathlib.Data.List.Forall2`), deletes the four local helpers,
and swaps six call sites to the library lemmas. The full edit set was already trial-applied
during research and verified to build green (492/492 jobs, 0 errors, 0 sorry), then reverted —
so this is a single-phase, low-risk polish task whose only remaining work is re-applying the
verified edits and running the full CI gate.

### Research Integration

The research report provides a verified lemma mapping and the exact text-anchored edits:
- `forall₂_of_zip_mem` -> `List.forall₂_iff_zip.mpr ⟨hlen, h⟩` (Iff form; `apply` becomes `refine ... .mpr ⟨_, ?_⟩`)
- `forall₂_append_aux` -> `List.rel_append` (Relator `⇒` form, applies directly)
- `forall₂_drop_aux` -> `List.forall₂_drop` (drop-in)
- `forall₂_take_aux` -> `List.forall₂_take` (drop-in)

Keep `forall₂_replicate_right` (out of scope; no trivial Mathlib drop-in). The import is a plain
(non-public) `import` because the lemmas appear only inside proof terms — shake-friendly. Call
sites need the `List.` prefix (no `open List` in the file). Line numbers in the report are
pre-edit; match on surrounding text since deleting the helpers shifts call sites up ~60 lines.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap_flag not set). This task is a Mathlib reuse-first cleanup with
no roadmap dependencies.

## Goals & Non-Goals

**Goals**:
- Add `import Mathlib.Data.List.Forall2` after `import Cslib.Init`.
- Delete the four local private helpers: `forall₂_of_zip_mem`, `forall₂_append_aux`,
  `forall₂_drop_aux`, `forall₂_take_aux`.
- Swap the six call sites to `List.forall₂_iff_zip`, `List.rel_append`, `List.forall₂_drop`,
  `List.forall₂_take`.
- Pass the full CSLib CI gate with 0 errors and 0 sorry.

**Non-Goals**:
- Removing or refactoring `forall₂_replicate_right` (kept).
- Touching any file other than `Cslib/Logics/Modal/Tableau/Soundness.lean`.
- Fixing pre-existing unrelated warnings (`linter.style.longLine` in `SoundnessStep.lean`,
  `unusedSectionVars` on `modalApplyOne_fresh`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Call-site mismatch from stale line numbers | L | L | Match on surrounding text (report quotes exact before/after), not raw line numbers |
| `forall₂_iff_zip` Iff form requires `refine` not `apply` | L | L | Report specifies the `refine ... .mpr ⟨hlength_accs.symm, ?_⟩` rewrite explicitly |
| shake requests import promotion/removal | L | L | Run `lake shake` with documented flags; report confirms plain import is shake-satisfied |
| Accidentally deleting `forall₂_replicate_right` | M | L | Explicit non-goal; verify the kept helper still present after edits |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Apply verified Mathlib swap and pass CI gate [NOT STARTED]

**Goal**: Re-apply the research-verified edit set to `Soundness.lean` and confirm the full CSLib
CI pipeline is green with 0 errors and 0 sorry.

**Tasks**:
- [ ] Add `import Mathlib.Data.List.Forall2` immediately after `import Cslib.Init`.
- [ ] Delete the four local private helpers (`forall₂_of_zip_mem`, `forall₂_append_aux`,
      `forall₂_drop_aux`, `forall₂_take_aux`); keep `forall₂_replicate_right`.
- [ ] Replace call site: `apply forall₂_of_zip_mem hlength_accs.symm`
      -> `refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩` (leave the following
      `intro b a hmem` unchanged).
- [ ] Replace `(forall₂_append_aux hFresh_done` -> `(List.rel_append hFresh_done`.
- [ ] Replace `forall₂_append_aux (forall₂_append_aux hFresh_done hFreshNew) hFresh_rest`
      -> `List.rel_append (List.rel_append hFresh_done hFreshNew) hFresh_rest`.
- [ ] Replace `forall₂_drop_aux done.length hunsat_all` -> `List.forall₂_drop done.length hunsat_all`.
- [ ] Replace `forall₂_drop_aux newBs.length hunsat_newBs_bt`
      -> `List.forall₂_drop newBs.length hunsat_newBs_bt`.
- [ ] Replace `forall₂_take_aux newBs.length hunsat_newBs_bt`
      -> `List.forall₂_take newBs.length hunsat_newBs_bt`.
- [ ] Run the full CI gate (see Verification) and confirm green.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` - add one import, delete four private helpers,
  rewrite six call sites to Mathlib lemmas.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Soundness` then full `lake build` — 0 errors, 0 sorry.
- `lake exe checkInitImports` — passes.
- `lake exe lint-style` — no new style violations introduced by this change.
- `lake test` — CslibTests suite passes.
- `lake shake --add-public --keep-implied --keep-prefix` — satisfied with the plain
  `import Mathlib.Data.List.Forall2`; no promotion/removal requested.
- Confirm `forall₂_replicate_right` is still present in the file.
- Confirm no new declarations added (no naming-convention work needed).

---

## Testing & Validation

- [ ] `lake build` completes with 0 errors and 0 sorry.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` reports no new violations.
- [ ] `lake test` passes (CslibTests suite).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` is satisfied; import stays plain (non-public).
- [ ] `forall₂_replicate_right` retained; four target helpers removed.

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Tableau/Soundness.lean` (one import added, four helpers removed,
  six call sites swapped to Mathlib).
- Execution summary at `specs/404_forall2_mathlib_cleanup_soundness/summaries/01_*-summary.md`.

## Rollback/Contingency

The change is isolated to a single file. If CI fails unexpectedly, revert with
`git checkout -- Cslib/Logics/Modal/Tableau/Soundness.lean` to restore the local helpers, then
re-inspect the specific failing call site against the report's verified mapping. Because the
identical edit set already built green during research, any failure indicates a transcription
error in re-application rather than a flaw in the approach.
