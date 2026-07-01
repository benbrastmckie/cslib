# Implementation Plan: Task #405

- **Task**: 405 - Proof-style cleanup for modal tableau soundness
- **Status**: [COMPLETED]
- **Effort**: 0.75 hours
- **Dependencies**: Task 404 (COMPLETED) — the redesigned `Soundness.lean` this cleanup edits
- **Research Inputs**: specs/405_proof_style_cleanup_modal_soundness/reports/01_proof-style-cleanup-modal-soundness.md
- **Artifacts**: plans/01_proof-style-cleanup-modal-soundness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Apply three research-verified, purely stylistic edits to `Cslib/Logics/Modal/Tableau/Soundness.lean`
to improve readability/robustness of two proof blocks introduced by the task-402/404 redesign.
Every edit was prototyped in the research phase (applied, scoped-built green, then reverted), so
this is a single focused transcription-and-verify phase. Scope is readability only: no
statement/signature changes, zero `sorry`, no new axioms, full build must stay green and
`lint-style` clean. Combined diff is ~1 file changed, +15/−19 lines.

### Research Integration

The research report (`reports/01_...md`) supplies exact before/after tactic blocks, each marked
**VERIFIED GREEN** via a scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` (baseline 493
jobs). The plan carries those recommendations verbatim as the source of truth:

- **R1** — `modalApplyOne_fresh` (lines ~87-104): replace the opaque
  `repeat' first | … | split` loop plus the residual `all_goals first | …` cleanup with a
  structured `split`-based proof that mirrors `modalApplyOne`'s own outer-`if` / rule-`match`
  structure. `extract_lets` (no positional names) is **retained** — the fresh-edge `Or.inr`
  arms fail with a type mismatch without it. No signature change.
- **R2** — `hnewExpLen` sub-block (lines ~249-267) of `modalExpandBranches_closed_unsat`: merge
  the three verbatim-identical `cases result` arms (`linear`/`branching`/`persistent`) into one
  `| _ =>` arm using `simp [List.length_map]`; keep `| notApplicable => simp at hf`. Net −8 lines.
- **R3** — robustness: add `omit [Hashable Atom] in` immediately before `modalApplyOne_fresh` to
  clear the existing `unusedSectionVars` warning the baseline build emits at `Soundness.lean:87`
  (linter-authoritative; matches the existing pattern at lines 61 and 73). Do **not** omit
  `[DecidableEq Atom]` — it is still used.
- **R4** — the per-branch accs / `Forall₂` take/drop extraction blocks (lines ~289-312) are
  **out of scope** for this plan (Non-Goal). Mathlib has no `forall₂_append_iff`; the only option
  is a new private `forall₂_split_mid` helper, which adds a declaration + docstring and was not
  verified. Left as an optional future item.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path`/`roadmap_flag` provided). This task is a
code-hygiene follow-up to the task-402/404 modal tableau soundness redesign.

## Goals & Non-Goals

**Goals**:
- Apply R1 (structured `split` proof for `modalApplyOne_fresh`) exactly as verified.
- Apply R2 (merge three `cases result` arms into one `| _ =>` arm) exactly as verified.
- Apply R3 (`omit [Hashable Atom] in` before `modalApplyOne_fresh`) and confirm the line-87
  `unusedSectionVars` warning disappears.
- Keep the full `lake build` green with zero `sorry` and clean `lint-style` for `Soundness.lean`.

**Non-Goals**:
- No changes to any lemma/theorem statement or signature.
- No rewrite of the `hunsat_*` `Forall₂` extraction blocks (R4, lines ~289-312) — explicitly deferred.
- No change to the `suffices key : …` inner-induction scaffold (lines ~190-206) — structural, not debt.
- No new declarations, axioms, `sorry`/`admit`, or notation changes.
- No edits to any file other than `Cslib/Logics/Modal/Tableau/Soundness.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers drifted from the report's ~87/249 anchors | L | M | Locate targets by declaration name (`modalApplyOne_fresh`, `hnewExpLen`/`cases result`), not by absolute line number, before editing. |
| Dropping `extract_lets` while "simplifying" R1 breaks fresh-edge arms | H | L | Keep `extract_lets` verbatim; the report documents the `Or.inr` type-mismatch failure without it. |
| Merged `| _ =>` arm triggers `unusedSimpArgs` on `List.length_map` | M | L | Report verified a single `simp [List.length_map]` invocation over the merged arm emits no such warning; run `lint-style` to confirm. |
| Omitting `[DecidableEq Atom]` by mistake breaks the build | M | L | Omit only `[Hashable Atom]`; `[DecidableEq Atom]` stays (used via `propResult`/`boxPropagation`). |
| Full build regression elsewhere | M | L | Run scoped build first, then full `lake build`; revert if not green. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Apply and verify the three cleanup edits [COMPLETED]

**Goal**: Transcribe the three verified edits into `Soundness.lean` and confirm scoped + full
build green, zero `sorry`, clean `lint-style`, no signature changes, no new axioms.

**Tasks**:
- [x] Open `Cslib/Logics/Modal/Tableau/Soundness.lean`; locate `modalApplyOne_fresh` by name and
      confirm its current proof matches the report's baseline block (the `repeat' first | … | split`
      loop + `all_goals first | …` cleanup).
- [x] **R3**: Insert `omit [Hashable Atom] in` on its own line immediately before the
      `private lemma modalApplyOne_fresh` declaration (mirroring lines 61/73). Keep `[DecidableEq Atom]`.
- [x] **R1**: Replace the `modalApplyOne_fresh` proof body with the report's verified structured block:
      ```lean
      unfold modalApplyOne
      extract_lets
      split
      · exact Or.inl rfl
      · split <;>
          first
            | exact Or.inl rfl
            | exact Or.inr ⟨_, _, rfl, rfl⟩
            | (left; simp only [apply_ite Prod.snd, ite_self])
      ```
      (Optionally keep the 3-line explanatory comment from the report above the block.) Do **not**
      drop `extract_lets`; do **not** re-add positional names `w propResult`.
- [x] **R2**: In `modalExpandBranches_closed_unsat`, locate the `hnewExpLen` `cases result with`
      block and replace the three `linear`/`branching`/`persistent` arms with a single
      `| _ =>` arm using `simp [List.length_map]`, keeping `| notApplicable => simp at hf`:
      ```lean
      cases result with
      | notApplicable => simp at hf
      | _ =>
        split_ifs at hf
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, _⟩ := hf; simp [List.length_map]
      ```
- [x] Run scoped build: `lake build Cslib.Logics.Modal.Tableau.Soundness` (expect green, ~493 jobs).
- [x] Confirm the `Soundness.lean:87` `unusedSectionVars` warning is gone from the build output.
- [x] Run `grep -nE '\bsorry\b|\badmit\b' Cslib/Logics/Modal/Tableau/Soundness.lean` (expect none).
- [x] Run `lake exe lint-style 2>&1 | grep Soundness.lean` (expect no output).
- [x] Run full `lake build` (expect green).
- [x] Spot-check `git diff --stat` ≈ `1 file changed, 15 insertions(+), 19 deletions(-)` and that
      no lemma signature lines changed.

**Timing**: ~45 minutes (edits are mechanical; most time is the full `lake build`).

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — R1 structured proof for `modalApplyOne_fresh`,
  R3 `omit [Hashable Atom] in` header, R2 merged `cases result` arm in the `hnewExpLen` block.

**Verification**:
- Scoped build `lake build Cslib.Logics.Modal.Tableau.Soundness` green.
- Full `lake build` green.
- `grep` for `sorry`/`admit` returns nothing.
- `lake exe lint-style` emits nothing for `Soundness.lean`; line-87 `unusedSectionVars` warning gone.
- Diff touches only proof bodies / the `omit` header — no statement or signature text changed.

---

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Tableau.Soundness` — scoped build green (~493 jobs).
- [x] `lake build` — full build green.
- [x] `grep -nE '\bsorry\b|\badmit\b' Cslib/Logics/Modal/Tableau/Soundness.lean` — no matches.
- [x] `lake exe lint-style 2>&1 | grep Soundness.lean` — no output.
- [x] `Soundness.lean:87` `unusedSectionVars` warning no longer present in build output.
- [x] `git diff` confirms no lemma/theorem signature changes and no new `axiom` declarations.

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Tableau/Soundness.lean` (R1 + R2 + R3 applied).
- summaries/01_proof-style-cleanup-modal-soundness-summary.md (produced by /implement).

## Rollback/Contingency

Single-file, self-contained change. If any verification step fails, revert with
`git checkout -- Cslib/Logics/Modal/Tableau/Soundness.lean` to restore the settled task-404
baseline (which the research confirmed builds green). Because the three edits are independent, a
partial rollback is possible: R3 (`omit`) and R2 (arm merge) can be kept even if R1 needs rework,
and vice versa — but only commit a state that passes the full build.
