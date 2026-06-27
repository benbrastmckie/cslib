# Implementation Plan: Task #365

- **Task**: 365 - Docstring/comment-only hygiene pass over the Propositional metatheory; ZERO code or proof changes
- **Status**: [NOT STARTED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/365_propositional_docstring_sorry_note_hygiene/.orchestrator-handoff.json
- **Artifacts**: plans/01_docstring-sorry-note-hygiene.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CONTRIBUTING.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a documentation-only hygiene pass over the Propositional metatheory. The Tableau
soundness story has changed since these docstrings were written: the three Tableau soundness
modules (Classical, Intuitionistic, Minimal) are now `sorry`-free, yet several module
docstrings still carry stale "Notes on sorry" sections claiming key lemmas are unproved. In
addition, two files leak internal task numbers ("task 308", "task 332") into reference
docstrings instead of pointing at named obligations, contrary to CONTRIBUTING.md guidance.

The work is split into two independent phases: Phase 1 rewrites the stale sorry-status
docstrings across the Tableau tree (4 required rewrites + 1 optional softening); Phase 2
removes the task-number leaks in `Brouwerian.lean` and `Termination.lean`. NO code, proof,
signature, or behavioral change is permitted. Every edited docstring MUST remain a docstring
(preserve `/-! ... -/` and `/-- ... -/` delimiters) so the `docBlame` linter stays satisfied.

### Research Integration

The research handoff (`.orchestrator-handoff.json`) provides a fully-grounded, file-by-file
`edit_targets` list, each verified against current source, plus a `sorry_inventory` that
distinguishes sorry-free soundness modules from modules with remaining real sorries. Key
grounded facts driving the rewrites:

- `soundness_modules_sorry_free`: Classical, Intuitionistic, and Minimal Tableau `Soundness.lean`.
- `remaining_real_sorries`: Classical Completeness (1), Intuitionistic Completeness (4),
  Minimal Completeness (4), Normalization `Termination.lean` (2).
- Confirmed named theorem `brouwerianEmbeddingLemma` lives at `FreeJoinCompletion.lean:129`.
- `leave_unchanged`: Intuitionistic/Minimal `Completeness.lean` "Notes on sorry" are accurate;
  Intuitionistic `Soundness.lean` has no "Notes on sorry" section. These MUST NOT be touched.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` / `roadmap_flag` provided). This is a
self-contained documentation-hygiene task that advances overall metatheory documentation
accuracy but is not tied to a roadmap item.

## Goals & Non-Goals

**Goals**:
- Rewrite all 4 stale "Notes on sorry" docstring sections in the Tableau tree to reflect the
  current sorry-free soundness state, while accurately describing the remaining
  completeness-direction sorries.
- Replace the inline NOTE in Minimal `Soundness.lean` (line 116) consistent with the rewrite.
- Optionally soften the overstated "Proved" claim in Minimal `DecisionProcedure.lean`.
- Replace internal task-number leaks ("task 308", "task 332") with references to named
  obligations/lemmas per CONTRIBUTING.md.
- Keep all docstrings present and well-formed so `docBlame` and other linters remain green.

**Non-Goals**:
- Any change to Lean code, proofs, signatures, `sorry` count, imports, or namespaces.
- Touching modules listed in `leave_unchanged` (Intuitionistic/Minimal `Completeness.lean`
  "Notes on sorry"; Intuitionistic `Soundness.lean`).
- Adding new lemmas, renaming declarations, or restructuring module layout.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Edit removes a docstring delimiter, triggering docBlame lint failure | M | L | Edit only the prose inside `/-! -/` / `/-- -/`; never alter delimiters; run `lake exe lint-style` and `lake build` in verification |
| New docstring text re-introduces a stale/inaccurate sorry claim | L | L | Cross-check every claim against `sorry_inventory` in the handoff before writing |
| Accidentally editing a `leave_unchanged` file | M | L | Phase task lists name exact files; do not touch Completeness.lean soundness notes or Intuitionistic Soundness.lean |
| Stray whitespace / formatting change flagged by lint-style | L | L | Keep line wrapping consistent with surrounding docstring; run `lake exe lint-style` |
| Build cache cold causing long verify | L | M | Run `lake exe cache get` before `lake build` if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases 1 and 2 touch disjoint files and have no ordering dependency; they can execute in
parallel or in any order. A single final verification covers both.

### Phase 1: Rewrite stale "Notes on sorry" in Tableau tree [COMPLETED]

**Goal**: Make every sorry-status docstring in the Tableau soundness/decision tree accurate:
soundness is proved (sorry-free); only the completeness/countermodel direction still rests on
sorries where applicable.

**Tasks**:
- [ ] `Classical/Soundness.lean` (lines 34-39): rewrite the "## Notes on sorry" section. The
      named lemmas (`branchConsistent`, `classicalBranchSatisfiable`, `classicalTableau_sound`)
      are now proved, not sorry. Reframe as a brief note that soundness is fully proved, or
      remove the now-false "marked sorry" wording while keeping the section heading + prose so
      the docstring stays non-empty.
- [ ] `Minimal/Soundness.lean` (lines 41-44 AND inline NOTE at line 116): rewrite. Module no
      longer inherits a sorry; both Minimal and Intuitionistic soundness are sorry-free. Update
      both the header "Notes on sorry" prose and the inline NOTE comment at line 116 to match.
- [ ] `Classical/DecisionProcedure.lean` (lines 35-40): rewrite stale "Notes on sorry".
      `classicalTableau_sound` is now proved; only the completeness/countermodel direction
      still rests on a Completeness sorry (1 remaining per inventory). State this precisely.
- [ ] `Intuitionistic/DecisionProcedure.lean` (lines 34-37): rewrite. Soundness is now
      sorry-free; completeness still has 4 sorries (per inventory).
- [ ] (OPTIONAL / secondary) `Minimal/DecisionProcedure.lean` (lines 20-23): soften the
      overstated "Proved" claim to match the actual state (Minimal Completeness has 4 sorries).

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - rewrite Notes-on-sorry prose
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - rewrite header notes + inline NOTE
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` - rewrite Notes-on-sorry
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` - rewrite Notes-on-sorry
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - (optional) soften claim

**Do NOT touch** (per handoff `leave_unchanged`):
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`

**Verification**:
- `grep -rn "sorry" Cslib/Logics/Propositional/Tableau/*/Soundness.lean` shows no source
  `sorry` regressions and the docstrings no longer claim soundness lemmas are sorry.
- All edited blocks remain valid `/-! -/` or `/-- -/` docstrings (delimiters intact).
- Defer build/lint to the shared Testing & Validation step.

---

### Phase 2: Remove internal task-number leaks [COMPLETED]

**Goal**: Replace internal task-number references in reference docstrings with references to
named obligations/lemmas, per CONTRIBUTING.md.

**Tasks**:
- [ ] `Semantics/Algebra/Brouwerian.lean` (line 41): replace "This bridge is the subject of
      task 308." with a reference to the named lemma `brouwerianEmbeddingLemma` (defined in
      `Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean:129`). Keep the
      surrounding Design Notes prose intact.
- [ ] `NaturalDeduction/Normalization/Termination.lean` (lines 22 and 1325): replace the two
      "task 332" leaks with named open-obligation references. Use the named obligations:
      `normalize_isStronglyNormal` (line 22 docstring), and for line 1325 the relevant inline
      obligation (`reduceRoot_decreases_normMeasure` h_8 case / `reduceRootSubSN` invariant) per
      CONTRIBUTING.md. State that the proof is currently `sorry` without leaking a task number.

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean` - line 41 task-number leak
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` - lines 22, 1325

**Verification**:
- `grep -rn "task 308\|task 332" Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`
  returns no matches.
- Edited blocks remain valid docstrings/comments (delimiters intact).
- Defer build/lint to the shared Testing & Validation step.

---

## Testing & Validation

Run once after both phases complete (these are the handoff's declared verification steps):

- [ ] `lake build` succeeds (no new errors/warnings; docstrings well-formed).
- [ ] `lake exe lint-style` passes (text/style linters green).
- [ ] `lake lint` shows no new `docBlame` warnings on edited files (docstrings preserved).
- [ ] `git diff` confirms ONLY comment/docstring lines changed — no Lean code, signatures, or
      `sorry` tokens added or removed (`sorry` count unchanged across the repo).
- [ ] No file in the `leave_unchanged` list appears in `git diff`.

## Artifacts & Outputs

- Updated docstrings in 6 required files (+ 1 optional) listed above.
- Implementation summary at `specs/365_propositional_docstring_sorry_note_hygiene/summaries/01_*-summary.md`.
- No new Lean declarations, no behavioral change.

## Rollback/Contingency

All changes are comment/docstring-only and confined to listed files. To revert, `git checkout
--` the affected files or `git revert` the implementation commit. Because no code paths change,
rollback carries zero behavioral risk. If `lake exe lint-style` flags a rewritten docstring,
adjust the prose/wrapping in place (do not remove the docstring delimiters) and re-run.
