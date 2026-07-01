# Implementation Plan: Task #390

- **Task**: 390 - Update ORGANISATION.md Propositional section (post-merge tree)
- **Status**: [COMPLETED]
- **Effort**: 0.4 hours
- **Dependencies**: None
- **Research Inputs**: specs/390_update_organisation_md/reports/01_update-propositional-organisation.md
- **Artifacts**: plans/01_update-propositional-organisation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib (documentation-only; no Lean, no CI)
- **Lean Intent**: false

## Overview

The Propositional Logic section of `ORGANISATION.md` (lines 97-106) is a stale 4-item stub
(`Defs.lean`, `NaturalDeduction/Basic.lean`, `ProofSystem/`, `Metalogic/`) while the on-disk
tree under `Cslib/Logics/Propositional/` now holds 115 `.lean` files across 7 major
subdirectories. This is a single mechanical Markdown edit: replace the stub fenced block with
the exact expanded tree already authored in the research report (§3 AFTER), matching the
abbreviated style of the neighboring Modal/Temporal sections. A single decision — whether to
append the OPTIONAL Namespace-Convention clarifying note (§4) — is resolved in this plan
(default: omit; the section is already correct). No Lean source changes, no `lake` build,
no CI impact.

### Research Integration

The research report (`reports/01_update-propositional-organisation.md`) is the primary and
sufficient input. It provides:
- The exact BEFORE block to replace (`ORGANISATION.md:99-106`, §1.1 / §3).
- The exact AFTER replacement tree (§3, lines 99-140 of the report) in the abbreviated style.
- Verified on-disk file counts (115 files, per-subdirectory breakdown in §2).
- Confirmation that the Namespace Convention section (lines 254-264) is ALREADY CORRECT —
  fixed by archived task 387 (commit `1845ede5`, keeping `Cslib.Logic.PL`); 105 files declare
  `Cslib.Logic.PL`, zero declare `Cslib.Logic.Propositional` (§4, §5).
- A Definition of Done (§8) and an explicit out-of-scope list (§6).

The implementer should transcribe the §3 AFTER block verbatim rather than re-deriving the tree.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set). Task topic is "Code Hygiene";
the edit brings contributor-facing documentation into agreement with the merged source tree
before the PR lands.

## Goals & Non-Goals

**Goals**:
- Replace the 4-item Propositional stub (`ORGANISATION.md:99-106`) with the expanded tree from
  research report §3 (AFTER), reflecting all 7 subdirectories and top-level files.
- Keep the new tree in the abbreviated, representative-filename style of the adjacent
  Modal/Temporal sections (no exhaustive 115-file listing; brace-grouping for families).
- Verify the edited tree matches the on-disk structure of `Cslib/Logics/Propositional/`.

**Non-Goals**:
- No change to the Namespace Convention section (lines 254-264) — already correct. The optional
  §4 clarifying note is DEFAULT-OMITTED (see decision below).
- No change to the Module Dependency Hierarchy diagram (lines 80-95).
- No change to the Modal/Temporal/Bimodal tree sections (lines 108-153).
- No change to the "Propositional Embeddings and the Classical-Scope Boundary" section
  (lines 213-244).
- No Lean source edits, no `lake build`/`lake test`, no CI runs.
- No exhaustive per-file listing of `Semantics/Algebra/` (32 files) — parenthetical summary only.

**Open Decision (resolved)**: Include the OPTIONAL §4 Namespace-Convention clarifying note?
- **Recommended default: OMIT.** The section already documents `Cslib.Logic.PL` correctly and
  passes as-is; the note is explicitly labeled non-essential in the report. Omitting keeps the
  edit minimal and scoped to the single stale section. The implementer MAY include it (one
  sentence appended after line 264, per §4) if a reviewer requests the directory-vs-leaf
  distinction be made explicit, but this is not required for the task to be complete.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Tree drifts from on-disk reality during transcription | L | L | Transcribe §3 AFTER verbatim; run `find` verification (Phase 1 verification step) |
| Markdown fences left unbalanced, breaking rendering | M | L | Confirm the ` ``` ` closing fence and one blank line before `### Modal Logic` |
| Over-listing `Semantics/Algebra/` breaks the abbreviated style | L | L | Use the parenthetical 32-file summary from §3, not a full listing |
| Accidentally editing the already-correct Namespace section | L | L | Default OMIT; scope edit to lines 99-106 only |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single-phase plan; no parallelism.

### Phase 1: Replace Propositional tree stub in ORGANISATION.md [COMPLETED]

**Goal**: Swap the stale 4-item Propositional fenced block for the expanded, style-consistent
tree from research report §3, and verify it against the on-disk structure.

**Tasks**:
- [ ] Read `reports/01_update-propositional-organisation.md` §3 (AFTER block) and §2 (file counts).
- [ ] In `ORGANISATION.md`, replace the fenced tree block at lines 99-106 (the current 4-item
      stub bounded by the ` ``` ` fences under `### Propositional Logic (Logics/Propositional/)`)
      with the §3 AFTER tree verbatim.
- [ ] Preserve the abbreviated style: representative filenames + brace-grouping; keep the
      `Semantics/Algebra/` line as the parenthetical 32-file summary (do NOT list all 32).
- [ ] Confirm exactly one blank line remains before `### Modal Logic (Logics/Modal/)` and the
      code fence is balanced (opening ` ``` ` after the header, closing ` ``` ` before the blank line).
- [ ] (Optional, DEFAULT-OMIT) If a reviewer requests it, append the §4 clarifying sentence
      after line 264 of the Namespace Convention section; otherwise leave lines 254-264 untouched.

**Timing**: 0.4 hours

**Depends on**: none

**Files to modify**:
- `ORGANISATION.md` - replace the Propositional Logic fenced tree block (lines 99-106) with the
  research report §3 AFTER tree; no other section changes (Namespace note optional/omitted).

**Verification**:
- `grep -n "NaturalDeduction/" ORGANISATION.md` shows the expanded subtree (DerivedRules,
  Normalization, etc.), confirming the 4-item stub is gone.
- `grep -n "SequentCalculus/\|Tableau/\|CurryHoward\|Subformula.lean\|ProofSystemEquivalence" ORGANISATION.md`
  confirms the previously-missing subdirectories/files are now present.
- Cross-check the edited tree against on-disk structure:
  `find Cslib/Logics/Propositional -maxdepth 1 | sort` (top-level entries) and
  `ls Cslib/Logics/Propositional/` — every subdirectory named in the tree exists on disk.
- Visual/style check: the new block reads at the same density as the adjacent
  `### Modal Logic` tree (representative filenames, not exhaustive); one blank line precedes
  `### Modal Logic`; code fences balanced.
- Confirm NO Lean files changed: `git status --porcelain` shows only `ORGANISATION.md`
  (plus task artifacts). No `lake build`/CI required.

---

## Testing & Validation

- [ ] `grep -n "NaturalDeduction/" ORGANISATION.md` returns the expanded subtree (stub removed).
- [ ] All 7 subdirectories (SequentCalculus, CurryHoward, Semantics, Tableau, NaturalDeduction,
      ProofSystem, Metalogic) plus `Subformula.lean` and `ProofSystemEquivalence.lean` appear in
      the edited tree.
- [ ] Edited tree names only subdirectories that exist under `Cslib/Logics/Propositional/`
      (verified via `find`/`ls`).
- [ ] Markdown fences balanced; single blank line before `### Modal Logic`.
- [ ] `git status --porcelain` shows no Lean source changes (only `ORGANISATION.md` + artifacts).
- [ ] No `sorry`, no CI impact (documentation-only).

## Artifacts & Outputs

- Modified `ORGANISATION.md` (Propositional Logic section only).
- This plan: `specs/390_update_organisation_md/plans/01_update-propositional-organisation.md`.
- Execution summary at completion: `summaries/01_update-propositional-organisation-summary.md`.

## Rollback/Contingency

Single-file Markdown edit. To revert: `git checkout -- ORGANISATION.md` (before commit) or
`git revert <commit>` (after). No build state, no downstream dependencies, no CI to unwind.

## Urgency Note

Do this BEFORE the PR lands — the task exists to keep contributor-facing `ORGANISATION.md` in
agreement with the merged Propositional tree at PR time.
