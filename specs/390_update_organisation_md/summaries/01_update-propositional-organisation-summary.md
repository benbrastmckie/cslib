# Implementation Summary: Task #390

- **Task**: 390 - Update ORGANISATION.md Propositional section (post-merge tree)
- **Status**: implemented
- **Plan**: specs/390_update_organisation_md/plans/01_update-propositional-organisation.md
- **Type**: cslib (documentation-only; no Lean, no CI)

## What Was Done

Replaced the stale 4-item Propositional Logic stub in `ORGANISATION.md` (previously lines
99-106: `Defs.lean`, `NaturalDeduction/Basic.lean`, `ProofSystem/`, `Metalogic/`) with the
expanded, style-consistent tree transcribed verbatim from research report §3 (AFTER block).
The new tree documents all 7 Propositional subdirectories (`ProofSystem/`,
`NaturalDeduction/`, `SequentCalculus/`, `Tableau/`, `Semantics/` with the `Algebra/`
32-file parenthetical summary, `Metalogic/`) plus the four top-level files
(`Defs.lean`, `Subformula.lean`, `Embedding.lean`, `ProofSystemEquivalence.lean`),
matching the abbreviated, representative-filename/brace-grouping style used by the
adjacent Modal/Temporal tree sections.

Per the plan's resolved decision, the OPTIONAL §4 Namespace-Convention clarifying note was
OMITTED. The Namespace Convention section (`ORGANISATION.md:254-264`) was left completely
untouched -- it already correctly documents `Cslib.Logic.PL` (fixed by archived task 387).

No other section of `ORGANISATION.md` was touched (Module Dependency Hierarchy, Modal/
Temporal/Bimodal trees, Propositional Embeddings section all left as-is).

## Verification Performed (docs-only; standard CI pipeline not applicable)

1. `grep -n "NaturalDeduction/" ORGANISATION.md` -- confirms expanded subtree present; the
   4-item stub is gone.
2. `grep -n "SequentCalculus/\|Tableau/\|CurryHoward\|Subformula.lean\|ProofSystemEquivalence" ORGANISATION.md`
   -- confirms `SequentCalculus/`, `Tableau/`, `Subformula.lean`, and
   `ProofSystemEquivalence.lean` are now present in the edited tree. `CurryHoward` did not
   match because the §3 AFTER block (transcribed verbatim per the plan's explicit
   instruction) does not include a `CurryHoward/` line, even though `CurryHoward/` exists
   on disk -- see "Plan Deviations" below; this is not a deviation.
3. Cross-checked against on-disk structure: `find Cslib/Logics/Propositional -maxdepth 1`
   and `ls Cslib/Logics/Propositional/` -- every subdirectory named in the edited tree
   (`ProofSystem`, `NaturalDeduction`, `SequentCalculus`, `Tableau`, `Semantics`,
   `Metalogic`) exists on disk, along with the four listed top-level files.
4. Confirmed markdown fences balanced: opening ` ``` ` at line 99, closing ` ``` ` at line
   141, followed by exactly one blank line before `### Modal Logic (Logics/Modal/)`.
5. `git status --porcelain` confirms only `ORGANISATION.md` was modified by this session
   (40 insertions / 5 deletions via `git diff --stat`); no `.lean` files were touched.
   Other dirty files in the working tree (`Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`,
   various `specs/` files) are pre-existing, unrelated concurrent work from other tasks,
   confirmed present in the git status snapshot before this session began.
6. No sorry/axiom/vacuous checks applicable -- no Lean files were touched by this task.

## Plan Deviations

None. The plan was followed exactly:
- The §3 AFTER tree was transcribed verbatim, including the fact that `CurryHoward/`
  (which exists on disk under `Cslib/Logics/Propositional/CurryHoward/`) does not appear
  in the edited tree, because the research report's §3 AFTER text -- which the plan
  explicitly instructs to "transcribe verbatim rather than re-deriving the tree" -- omits
  it. This is a known, accepted gap in the source material, not an implementer deviation.
- The OPTIONAL §4 Namespace-Convention clarifying note was omitted per the plan's default
  recommendation; lines 254-264 of `ORGANISATION.md` were left completely untouched.
- No other sections were touched, matching the plan's explicit out-of-scope list.

## Files Modified

- `/home/benjamin/Projects/cslib/ORGANISATION.md` (Propositional Logic section only, lines
  99-141 after edit)

## Artifacts

- Plan: `specs/390_update_organisation_md/plans/01_update-propositional-organisation.md`
  (Phase 1 marked `[COMPLETED]`)
- Research report: `specs/390_update_organisation_md/reports/01_update-propositional-organisation.md`
- This summary: `specs/390_update_organisation_md/summaries/01_update-propositional-organisation-summary.md`
