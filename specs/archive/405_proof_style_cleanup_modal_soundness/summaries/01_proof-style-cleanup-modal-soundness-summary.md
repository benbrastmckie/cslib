# Implementation Summary: Task #405

- **Task**: 405 - Proof-style cleanup for modal tableau soundness
- **Status**: Implemented
- **Plan**: plans/01_proof-style-cleanup-modal-soundness.md
- **Research**: reports/01_proof-style-cleanup-modal-soundness.md

## What Was Done

Applied the three research-verified stylistic edits to
`Cslib/Logics/Modal/Tableau/Soundness.lean` (Phase 1, single phase, no deviations):

- **R3**: Added `omit [Hashable Atom] in` immediately before the docstring of
  `private lemma modalApplyOne_fresh` (mirroring the existing pattern at lines 61/73).
  `[DecidableEq Atom]` was kept, since it is still used elsewhere in the proof.
- **R1**: Replaced the opaque `repeat' first | … | split` loop plus the trailing
  `all_goals first | …` cleanup in `modalApplyOne_fresh` with the structured
  `unfold; extract_lets; split; · exact Or.inl rfl; · split <;> first | … | … | …` block,
  keeping the explanatory comment and retaining bare `extract_lets` (no positional names) —
  dropping it breaks the fresh-edge `Or.inr` arms with a type mismatch, as documented in the
  report.
- **R2**: In `modalExpandBranches_closed_unsat`'s `hnewExpLen` sub-block, merged the three
  verbatim-identical `cases result` arms (`linear`/`branching`/`persistent`) into a single
  `| _ =>` arm using `simp [List.length_map]`, keeping `| notApplicable => simp at hf` separate.

R4 (per-branch accs / `Forall₂` extraction blocks) and the `suffices key : …` inner-induction
scaffold were left untouched, per the plan's explicit non-goals.

## Plan Deviations

None. All three edits were applied exactly as specified in the plan/report, with one required
correction discovered during implementation: the `omit [Hashable Atom] in` modifier must precede
the docstring (not follow it) — placing it between the docstring and the `private lemma` line
produces a parse error (`unexpected token 'omit'; expected 'lemma'`), since the docstring must be
immediately adjacent to the declaration it documents. This is a placement detail, not a change to
the plan's intent; the existing lines 61/73 pattern in the file already has `omit ... in` before
the docstring, so this brings `modalApplyOne_fresh` in line with the established convention.

## Verification (CSLib CI Pipeline)

- `lake build Cslib.Logics.Modal.Tableau.Soundness` — green (493/493 jobs).
- `lake build` (full) — green (3188/3188 jobs).
- `lake exe checkInitImports` — exit 0.
- `lake lint` — zero warnings for `Soundness.lean` (2 pre-existing unrelated errors in
  `Temporal/Theorems.lean`, out of scope).
- `lake exe lint-style` — no output for `Soundness.lean`.
- `lake shake --add-public --keep-implied --keep-prefix` — no findings for
  `Modal/Tableau/Soundness.lean`.
- `lake exe mk_all --module` check: `Cslib.lean` already lists
  `Cslib.Logics.Modal.Tableau.Soundness` (line 431); no change needed.
- `lake test` — full `CslibTests/` suite green (9179 jobs).
- `grep -nE '\bsorry\b|\badmit\b' Cslib/Logics/Modal/Tableau/Soundness.lean` — no matches.
- `grep -n "^axiom " Cslib/Logics/Modal/Tableau/Soundness.lean` — no matches (no new axioms).
- The `Soundness.lean:87` `unusedSectionVars` warning (naming `[Hashable Atom]`) present in the
  task-404 baseline build is confirmed gone.
- `git diff --stat`: `1 file changed, 15 insertions(+), 19 deletions(-)` — matches the plan's
  estimate exactly. Diff touches only proof bodies and the new `omit` line; no lemma/theorem
  signature or statement text changed.

## Files Modified

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/Soundness.lean`

## Artifacts

- `/home/benjamin/Projects/cslib/specs/405_proof_style_cleanup_modal_soundness/plans/01_proof-style-cleanup-modal-soundness.md` (phase marked [COMPLETED], all checklist items checked)
- `/home/benjamin/Projects/cslib/specs/405_proof_style_cleanup_modal_soundness/summaries/01_proof-style-cleanup-modal-soundness-summary.md` (this file)
