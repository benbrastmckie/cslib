# Implementation Plan: Task #359

- **Task**: 359 - Fix docstring internal refs and citations
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/359_fix_docstring_internal_refs_and_citations/reports/01_docstring-refs-citations.md
- **Artifacts**: plans/01_docstring-refs-citations.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Remove internal development task-number references from three CSLib docstrings and
supplement a Zulip-only citation with the published source. All four edits are
documentation-only (no proof, definition, import, or axiom changes), so the CSLib
zero-debt gate is trivially satisfied. The research report provides exact before/after
text for every edit, including precise file paths and line locations. A single phase
applies all edits and verifies via `lake build` of the three affected modules plus
`lake lint`.

### Research Integration

The research report (`01_docstring-refs-citations.md`) confirmed every target by grep
and supplies concrete replacement text:
- `hilbert_alg_complete_theory` is the named theorem the "task 341" references should
  point to (defined in `HilbertCompleteness.lean`).
- `liftDerivationTree` (`ConjImpConservative.lean`) and
  `ConjImpBotMinAxiom.toMinPropAxiom` (`FragmentAxioms.lean`) are the defining modules
  to replace the "(from task 353)" parenthetical.
- BibKey `TroelstraSchwichtenberg2000` already exists in `references.bib:832` and is
  used elsewhere (e.g. `SequentCalculus/Defs.lean:35`) with the established format.

The report also flags two practical notes incorporated below: `HilbertStrongCompleteness.lean`
has FOUR "task 341" occurrences (lines 31, 111, 114, 118 — one more than the task
description stated), and the `DeductionCharacterization.lean` reference line drifted
to ~35, so edits must be located by content rather than line number.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task; documentation cleanup with no roadmap items.

## Goals & Non-Goals

**Goals**:
- Remove all "task 341" / "task-341" internal references from `HilbertStrongCompleteness.lean`
  (4 occurrences), pointing to the named theorem `hilbert_alg_complete_theory`.
- Replace the "(from task 353)" parenthetical in `MplConservativeChain.lean` with the
  defining modules of `liftDerivationTree` and `ConjImpBotMinAxiom.toMinPropAxiom`.
- Supplement the Zulip-only citation in `DeductionCharacterization.lean` with the
  published source via existing BibKey `TroelstraSchwichtenberg2000` (Ch. 2).
- Verify the three modules build cleanly and pass `lake lint`.

**Non-Goals**:
- No proof, definition, signature, or import changes.
- No new BibKey entries (the required key already exists).
- No removal of the Zulip attribution (supplement, not replace, per report recommendation).
- No edits to files other than the three named modules.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers drift from report (esp. DeductionCharacterization ~35) | L | M | Locate edits by exact docstring content via Edit string matching, not line number |
| Missed 4th "task 341" occurrence | L | L | Post-edit grep `task 341\|task-341\|task 353` across the three files confirms zero matches |
| Docstring edit accidentally breaks a doc-comment delimiter | M | L | `lake build` of each module catches malformed comments; lint confirms style |
| Citation format mismatch with library convention | L | L | Use exact format from report, matching `SequentCalculus/Defs.lean` precedent |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single phase; no parallelism.

### Phase 1: Apply docstring edits and verify [COMPLETED]

**Goal**: Apply all four documentation edits using the exact replacement text from the
research report, then verify the three modules build and lint cleanly.

**Tasks**:
- [ ] Edit `HilbertStrongCompleteness.lean` line ~31: remove "task 341's" so the recovery
      lemma bullet reads `recovers `hilbert_alg_complete_theory` (regression guard).`
- [ ] Edit `HilbertStrongCompleteness.lean` line ~111 section header:
      `/-! ## Recovery of Weak Completeness -/`
- [ ] Edit `HilbertStrongCompleteness.lean` lines ~113–119 (Recovery Lemma docstring):
      replace "task-341's" / "task 341's result" with reference to
      `hilbert_alg_complete_theory` (the weak/empty-context completeness theorem in
      `HilbertCompleteness.lean`) and "the weak-completeness result", per report Replacement 1.
- [ ] Edit `MplConservativeChain.lean` line ~229: replace `(from task 353)` parenthetical
      so the backward direction reads `using `liftDerivationTree` (`ConjImpConservative.lean`)
      and `ConjImpBotMinAxiom.toMinPropAxiom` (`FragmentAxioms.lean`).` per report Replacement 2.
- [ ] Edit `DeductionCharacterization.lean` `## References` block (line ~35): supplement
      with `* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 2.`
      above the existing Zulip bullet, per report Replacement 3.
- [ ] Run `grep -rn "task 341\|task-341\|task 353"` across the three files; confirm zero matches.
- [ ] Run `lake build` for the three affected modules.
- [ ] Run `lake exe lint-style` (and project lint) over the affected files.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertStrongCompleteness.lean` - remove
  four "task 341" references; point to `hilbert_alg_complete_theory`.
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` - replace
  "(from task 353)" parenthetical with defining modules.
- `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` - supplement Zulip
  citation with published `TroelstraSchwichtenberg2000` source, Ch. 2.

**Verification**:
- `grep -rn "task 341\|task-341\|task 353"` over the three files returns no matches.
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertStrongCompleteness` succeeds.
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain` succeeds.
- `lake build Cslib.Foundations.Logic.Metalogic.DeductionCharacterization` succeeds.
- `lake exe lint-style` reports no new violations on the edited files.

---

## Testing & Validation

- [ ] All three target modules build successfully via `lake build`.
- [ ] No remaining `task 341` / `task-341` / `task 353` matches in the three files.
- [ ] `lake exe lint-style` passes for the edited files.
- [ ] Zulip attribution preserved alongside the new published citation in
      `DeductionCharacterization.lean`.
- [ ] No proof, definition, import, or axiom changes (zero-debt gate satisfied).

## Artifacts & Outputs

- Edited `HilbertStrongCompleteness.lean`, `MplConservativeChain.lean`,
  `DeductionCharacterization.lean` (docstrings only).
- Execution summary at `summaries/01_docstring-refs-citations-summary.md` (on implementation).

## Rollback/Contingency

All changes are isolated to docstrings in three files. If `lake build` fails after edits
(e.g. a malformed comment delimiter), revert the offending file with `git checkout --
<file>` and reapply the specific replacement using the exact text from the research
report. Because there are no proof or definition changes, partial application is safe and
any single file can be reverted independently without affecting the others.
