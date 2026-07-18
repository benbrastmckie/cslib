# Implementation Summary: Task #532

- **Task**: 532 - Reconcile stale [BLOCKED] docstrings in the generic tableau driver
- **Status**: [COMPLETED]
- **Plan**: `plans/01_reconcile-stale-blocked-docstrings.md`
- **Type**: cslib (docstring-only, zero proof changes)

## What Was Done

### Required: `GenericDriver.lean` (lines 131-155)

Replaced the stale header section "## Completeness Is Generic (task 510); Soundness Is Not Yet
(task 503 Phase 6, blocked)" with the corrected section "## Completeness and Soundness Are Both
Generic Over `(apply, spec)`" from the research report. The new text:

- Removes the false claim that soundness has no generic `(apply, spec)` lift -- the generic
  frame-relativized soundness chain in `FrameSoundness.lean` (`frameValid`,
  `branchSatisfiableIn`, `modalStepBranchGen_preserves_satIn`,
  `modalExpandBranchesGen_closed_unsatIn`, `modalTableau_sound_frame`) is now cited by name.
- Removes the "[BLOCKED]" framing around `Decidable (tValid φ)` -- `instDecidableTValid`,
  `instDecidableBValid`, `instDecidableS5Valid`, `instDecidableFiveValid`, and
  `instDecidableKb5Valid` (all `FrameCompleteness.lean`) are cited as live, alongside K's
  `instDecidableKValid` (`CompletenessLoop.lean`).
- Uses only declaration names and file anchors (`FrameSoundness.lean`, `CompletenessLoop.lean`,
  `TDriver.lean`, `Completeness.lean`, `FrameCompleteness.lean`) -- zero new task-number
  citations.

### Optional/advisory: `FrameCompleteness.lean` (lines ~476, ~552)

Softened the two "Phase 2's blocked status" / "blocked Phase 2 rule discharge" phrasings to name
the witness-reuse bypass explicitly: "the *bypassed* Phase 2 rule discharge (superseded by the
witness-reuse rule `modalApplyOneS5w`, `S5Simplification.lean`)". This preserves the historically
accurate fact (Phase 2's guarded universal rule was never discharged head-on) while removing the
risk that a reader infers S5/5 decidability is unfinished.

### Untouched (per plan, confirmed accurate)

`Saturation.lean`, `CompletenessLoop.lean`, and `FrameCompleteness.lean` regions 1769-1770,
565-587, 4415-4439 were not modified -- verified via `git status --short` that no changes landed
in `Saturation.lean` or `CompletenessLoop.lean`.

## Plan Deviations

None. All plan tasks executed as written; both the required and optional/advisory edits were
completed.

## Verification

- `grep -niE 'task [0-9]|phase [0-9]'` over the replaced `GenericDriver.lean` block (lines
  131-155): no matches.
- `lake build Cslib.Logics.Modal.Tableau.GenericDriver`: succeeded.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`: succeeded (first attempt hit a
  transient race from a concurrently-running agent rebuilding `LoopChecking.lean` in the same
  working tree; retry succeeded cleanly).
- `git diff` over both files: only comment/docstring lines changed -- no code, signature, or
  tactic changes.
- `grep -n "sorry"` / `grep -n "^axiom "` over both files: zero actual `sorry` tactics or new
  axioms (only pre-existing prose mentions of "sorry-free").
- `Saturation.lean` / `CompletenessLoop.lean`: confirmed untouched via `git status --short`.

## Files Modified

- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` -- stale header section replaced (required).
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` -- two "blocked Phase 2" phrasings softened
  (optional/advisory).
