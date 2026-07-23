# Implementation Plan: Task #532

- **Task**: 532 - Reconcile stale [BLOCKED] docstrings in the generic tableau driver
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/532_reconcile_stale_blocked_docstrings_generic_driver/reports/01_stale-blocked-docstring-sweep.md
- **Artifacts**: plans/01_reconcile-stale-blocked-docstrings.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Docstring-only cleanup. The `GenericDriver.lean` header section titled "Completeness Is Generic
...; Soundness Is Not Yet ... blocked" is fully stale: the generic frame-relativized soundness
lift (`FrameSoundness.lean`) and the T/S5/5/Euclidean decision instances (`instDecidableTValid`
et al.) are all live. Replace that stale section with the corrected, durable-anchor-only text
supplied in the research report. Optionally soften two "Phase 2's blocked status" phrasings in
`FrameCompleteness.lean` (lines ~476, ~552) that are historically accurate but risk misleading a
reader into thinking S5/5 are unfinished. Zero proof changes; a `lake build` parse check is the
only verification.

### Research Integration

Report `01_stale-blocked-docstring-sweep.md` provides ground-truth verification (declaration
names + line locations) and ready-to-use replacement prose that introduces zero new task-number
citations. The report's hard constraint — replacement text uses only declaration names and
file/section anchors, never task numbers — is carried into this plan verbatim. Files confirmed
requiring no change: `Saturation.lean`, `CompletenessLoop.lean`, and `FrameCompleteness.lean`
regions 1769-1770 / 565-587 / 4415-4439.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (orchestrator did not pass roadmap context).

## Goals & Non-Goals

**Goals**:
- Replace the stale "Soundness Is Not Yet ... [BLOCKED]" header block in `GenericDriver.lean`
  (lines ~131-158) with corrected text anchored to `FrameSoundness.lean` generics and the live
  `instDecidable*Valid` instances.
- Introduce zero new task-number citations in any replacement text (per
  `no-task-references-in-deliverables.md`).
- (Optional/advisory) Soften `FrameCompleteness.lean` lines ~476 and ~552 to name the
  witness-reuse bypass (`modalApplyOneS5w`) rather than the bare word "blocked".

**Non-Goals**:
- No proof-term, definition, tactic, or signature changes of any kind.
- No sweep of the pervasive existing task-number citations across the `Tableau/` module (a
  separate, larger refactor — explicitly out of scope per the report's cross-cutting note).
- No edits to `Saturation.lean`, `CompletenessLoop.lean`, or the already-correct
  `FrameCompleteness.lean` regions (1769-1770, 565-587, 4415-4439).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Replacement text accidentally reintroduces a "task N" citation | M | L | Grep the edited block for `task ` (case-insensitive) after editing; the report's prose is already task-number-free |
| Docstring edit lands outside the `/-! ... -/` comment and breaks the parse | M | L | Keep the edit strictly inside the existing block comment (lines ~131-159); confirm with `lake build Cslib.Logics.Modal.Tableau.GenericDriver` |
| Line numbers drift from the report | L | L | Match on the stale heading/prose text (anchored strings), not raw line numbers |
| Advisory softenings misstate S5 history | L | L | Use the report's exact recommended phrasing naming `modalApplyOneS5w` (`S5Simplification.lean`); optional — skip if uncertain |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single-phase plan; no parallelism.

### Phase 1: Reconcile stale [COMPLETED]

**Goal**: Correct the stale soundness/BLOCKED narrative in `GenericDriver.lean` and apply the
optional advisory softenings in `FrameCompleteness.lean`, with zero proof changes.

**Tasks**:
- [x] In `Cslib/Logics/Modal/Tableau/GenericDriver.lean`, replace the header section spanning the
  stale heading "## Completeness Is Generic (task 510); Soundness Is Not Yet (task 503 Phase 6,
  blocked)" through the end of that narrative (lines ~131-158, inside the `/-! ... -/` block ending
  at line ~159) with the corrected section from report §1 ("Completeness and Soundness Are Both
  Generic Over `(apply, spec)`"). Preserve factual content; use only declaration names and file
  anchors (`FrameSoundness.lean`, `CompletenessLoop.lean`, `TDriver.lean`, `Completeness.lean`,
  `FrameCompleteness.lean`) and the live instance names (`instDecidableTValid`,
  `instDecidableBValid`, `instDecidableS5Valid`, `instDecidableFiveValid`,
  `instDecidableKb5Valid`, `instDecidableKValid`).
- [x] Verify the edited block contains no `task N` / `Task N` / `Phase N` task-number citations.
- [x] (Optional/advisory) In `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` lines ~476 and
  ~552, soften "delivered here regardless of Phase 2's blocked status" / "independent of the
  blocked Phase 2 rule discharge" to name the witness-reuse bypass, e.g. "the *bypassed* Phase 2
  rule discharge (superseded by the witness-reuse rule `modalApplyOneS5w`,
  `S5Simplification.lean`)". Skip if the exact surrounding phrasing is ambiguous — this is not a
  false-claim fix, only a clarity softening.
- [x] Do NOT touch `Saturation.lean`, `CompletenessLoop.lean`, or `FrameCompleteness.lean`
  regions 1769-1770 / 565-587 / 4415-4439 (confirmed accurate).

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` - replace stale docstring header section
  (~131-158) with corrected text (required).
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` - soften two "blocked Phase 2" phrasings at
  ~476 and ~552 (optional/advisory).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.GenericDriver` succeeds (parse/format sanity check).
- If `FrameCompleteness.lean` was touched: `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`
  also succeeds.
- `grep -niE 'task [0-9]|phase [0-9]' ` over the replaced block returns no matches.
- No `sorry`, no axioms, no proof-term changes introduced (docstring-only edits cannot change
  proof obligations).

---

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Tableau.GenericDriver` passes.
- [x] `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` passes (only if that file was edited).
- [x] Replaced `GenericDriver.lean` block is free of task-number citations.
- [x] Diff contains only comment/docstring lines — no code, signature, or tactic changes.

## Artifacts & Outputs

- Edited `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (docstring header corrected).
- (Optional) Edited `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (two softened phrasings).
- Implementation summary at `summaries/01_reconcile-stale-blocked-docstrings-summary.md`.

## Rollback/Contingency

Docstring-only edits are trivially reversible: `git checkout -- Cslib/Logics/Modal/Tableau/GenericDriver.lean`
(and `FrameCompleteness.lean` if touched) restores the prior text. Since no proof obligations
change, there is no build-state to unwind beyond the comment text itself. If the corrected block
is judged imperfect, re-edit rather than reverting — the stale claims must not be restored.
