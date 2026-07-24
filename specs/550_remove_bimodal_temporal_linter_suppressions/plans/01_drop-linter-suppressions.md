# Implementation Plan: Remove Bimodal/Temporal Linter Suppressions

- **Task**: 550 - Remove ported set_option linter suppressions in Bimodal/Temporal propositional-reasoning files
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/550_remove_bimodal_temporal_linter_suppressions/reports/01_linter-suppression-inventory.md
- **Artifacts**: plans/01_drop-linter-suppressions.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Nine Bimodal/Temporal files carry file-scoped `set_option linter.* false` suppressions inherited
verbatim from the external BimodalLogic port. The research report empirically classified every
suppression by removing it, rebuilding the owning module with `lake build <Module>`, and
recording the findings that fire. The result: ~13 of the ~17 file-scoped suppression lines are
DEAD (drop with zero code change) and only 4 carry real findings, concentrated in three files
(Combinators, Perpetuity/Principles, Connectives). This plan drops the dead suppressions,
performs the three small reformattings, narrows Connectives' `flexible` to per-declaration scope,
and verifies each file plus the whole task against the CSLib CI order. Definition of done: every
target module builds warning-free with the suppressions removed (or narrowed, for
GeneralizedNecessitation's already-scoped `... in` lines which are kept), and the full CSLib CI
pipeline is green.

### Research Integration

The plan is a direct transcription of the report's per-file findings and its mandated fix
ordering (report sections "Per-file inventory" and "Recommended fix ordering"):

- **Fix ordering mechanic 1** — `emptyLine` fires only on an otherwise warning-free file, so it
  is always resolved LAST within any file that also has another real finding.
- **Fix ordering mechanic 2** — `setOption` fires solely as a guard for an unscoped file-scoped
  `linter.flexible` line; narrowing/removing that `flexible` line removes the `setOption` trigger,
  so `setOption` drops automatically once `flexible` is scoped or deleted.
- **Verification mechanic** — these are build-time syntax linters. They surface only under
  `lake build <Module>`, NOT `lake lint` / `lake exe lint-style`. Per-file verification therefore
  uses `lake build <Module>`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap flag set).

## Goals & Non-Goals

**Goals**:
- Remove all DEAD file-scoped linter suppressions across the six pure-DEAD files with zero code change.
- Wrap the 6 over-length lines in Combinators and drop its `longLine` (and dead `emptyLine`) suppression.
- Remove the 5 stray blank lines in Perpetuity/Principles and drop its `emptyLine` (and dead `longLine`) suppression.
- Narrow Connectives' `flexible` to per-declaration `set_option linter.flexible false in` on `iffElimLeft` and `iffElimRight`, dropping the file-scoped `flexible`, `setOption`, `emptyLine`, and `longLine` suppressions.
- Verify each modified module builds warning-free and the full CSLib CI pipeline is green.

**Non-Goals**:
- Do NOT remove GeneralizedNecessitation's three already-narrowed scoped `... in` suppressions (L45 `flexible`, L78/L154 `unusedSimpArgs`); they are live and already in the desired form — keep them.
- Do NOT rewrite the ported `simp` proofs in Connectives to `simp only [...]` (higher risk to a working port; the `... in` narrowing is the recommended, reuse-first fix).
- No new lemmas, `sorry`, axioms, or semantic changes to any proof.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line wraps in Combinators change indentation/tokenization and break a proof | M | L | Wrap only whitespace-safe break points; rebuild the module immediately after each file's edits and confirm zero warnings before moving on |
| Removing a blank line in Perpetuity/Principles alters proof-block structure | L | L | Blank lines flagged are inside command bodies; remove or replace-with-comment only the 5 identified lines, then rebuild |
| Dropping `setOption` while a file-scoped `flexible` line remains re-fires "Unscoped option" | M | L | Follow mandated ordering: narrow/remove `flexible` FIRST, then drop `setOption` (never the reverse) |
| Resolving `emptyLine` before other findings masks its true findings | L | L | Resolve `emptyLine` LAST in any file that also has another real finding |
| Verifying with `lake lint` instead of `lake build` misses the syntax-linter findings | M | L | Per-file verification uses `lake build <Module>` explicitly; whole-task uses the CSLib CI order |
| Line numbers in the report drift from current file state | L | M | Treat report line numbers as guidance; locate findings by content/declaration name, and let `lake build` warnings confirm exact remaining sites |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 1-4 touch disjoint file sets and are
independently verifiable, so they may run in parallel or sequentially in any order. Phase 5 is a
whole-task verification gate that depends on all preceding phases.

### Phase 1: Drop DEAD suppressions in pure-DEAD files [COMPLETED]

**Goal**: Delete the file-scoped suppressions that fire zero findings, with no reformatting, in
the six files whose suppressions are entirely DEAD.

**Tasks**:
- [x] `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`: delete all three file-scoped lines (`linter.style.emptyLine`, `linter.style.setOption`, `linter.flexible`). `flexible` is dead, so removing it also removes the `setOption` trigger.
- [x] `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean`: delete the file-scoped `linter.style.longLine`.
- [x] `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`: delete both file-scoped lines (`linter.style.emptyLine`, `linter.style.longLine`).
- [x] `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`: delete all three file-scoped lines (`linter.unusedSimpArgs`, `linter.style.emptyLine`, `linter.style.longLine`).
- [x] `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`: delete ONLY the file-scoped `linter.style.emptyLine` (near L24). KEEP the three scoped `... in` suppressions (L45 `flexible`, L78/L154 `unusedSimpArgs`).
- [x] `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`: delete the file-scoped `linter.style.emptyLine`.

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` - remove 3 dead suppression lines
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - remove 1 dead suppression line
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - remove 2 dead suppression lines
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - remove 3 dead suppression lines
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` - remove 1 file-scoped dead suppression; keep 3 scoped
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` - remove 1 dead suppression line

**Verification**:
- For each file: `lake build <Module>` produces zero warnings (build the exact module for each edited file).
- Confirm GeneralizedNecessitation still contains its three `... in` scoped suppressions.

---

### Phase 2: Combinators — wrap long lines, drop suppressions [COMPLETED]

**Goal**: Wrap the 6 over-length lines in Combinators so no line exceeds 100 Unicode columns, then
drop the `longLine` (real) and `emptyLine` (dead) file-scoped suppressions.

**Tasks**:
- [x] Locate and wrap the 6 long lines (report original numbering: L82, L108, L140, L164, L184, L185; column counts 108/108/101/107/102/118). Break at whitespace-safe points; these lines span multiple declarations so file-scoped `longLine` cannot be narrowed to a single `... in`.
- [x] Delete the file-scoped `linter.style.emptyLine` (dead) and `linter.style.longLine` suppressions.

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` - wrap 6 lines; remove 2 suppression lines

**Verification**:
- `lake build Cslib.Logics.Bimodal.Theorems.Combinators` produces zero warnings (no residual `longLine`/`emptyLine`).

---

### Phase 3: Perpetuity/Principles — remove blank lines, drop suppressions [COMPLETED]

**Goal**: Remove the 5 stray in-command blank lines flagged by `emptyLine`, then drop the
`longLine` (dead) and `emptyLine` (real) file-scoped suppressions, resolving `emptyLine` last.

**Tasks**:
- [x] Remove (or replace with a comment where it aids readability) the 5 blank lines inside the `persistence` proof and following declarations (report original numbering: L158, L167, L184, L187, L196).
- [x] Delete the file-scoped `linter.style.longLine` (dead) suppression.
- [x] Delete the file-scoped `linter.style.emptyLine` suppression LAST (it only fires once the file is otherwise warning-free).

**Timing**: 25 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - remove 5 blank lines; remove 2 suppression lines

**Verification**:
- `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles` produces zero warnings (no residual `emptyLine`).

---

### Phase 4: Connectives — narrow flexible, drop suppressions [NOT STARTED]

**Goal**: Narrow the `flexible` suppression to per-declaration scope on the two affected
declarations, then drop the now-redundant file-scoped `flexible`, `setOption`, `emptyLine`
(dead), and `longLine` (dead) suppressions in the mandated order.

**Tasks**:
- [ ] Add `set_option linter.flexible false in` immediately before `def iffElimLeft` (~L60) and `def iffElimRight` (~L71) — the two decls whose `simp` side-conditions trigger `flexible` (findings at ~L67 and ~L78). This matches the already-narrowed form in GeneralizedNecessitation.
- [ ] Delete the file-scoped `linter.flexible` line. With `flexible` scoped, the `setOption` trigger disappears.
- [ ] Delete the file-scoped `linter.style.setOption` line (only after `flexible` is scoped — dropping it while the file-scoped `flexible` remains re-fires "Unscoped option").
- [ ] Delete the file-scoped `linter.style.emptyLine` (dead) and `linter.style.longLine` (dead) lines.

**Timing**: 25 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` - add 2 scoped `... in` lines; remove 4 file-scoped suppression lines

**Verification**:
- `lake build Cslib.Logics.Bimodal.Theorems.Propositional.Connectives` produces zero warnings (no `flexible`, `setOption`, `emptyLine`, or `longLine`).

---

### Phase 5: Whole-task verification (build + CSLib CI) [NOT STARTED]

**Goal**: Confirm the entire library builds clean and the CSLib CI pipeline passes with all
suppressions removed/narrowed.

**Tasks**:
- [ ] Run `lake build` for the full library; confirm zero warnings across all nine touched modules.
- [ ] Run the CSLib CI order per `.claude/rules/cslib.md`: `checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`.
- [ ] Confirm GeneralizedNecessitation retains its three scoped `... in` suppressions and no new suppressions were introduced anywhere except the two Connectives `... in` lines.

**Timing**: 20 minutes

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- None (verification only)

**Verification**:
- Full `lake build` clean.
- All four CI steps green.

## Testing & Validation

- [ ] Each edited module builds warning-free under `lake build <Module>` (per-phase gate).
- [ ] Full-library `lake build` is clean.
- [ ] CSLib CI order passes: `checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`.
- [ ] No `sorry`, no new axioms, no semantic proof changes; the only added suppressions are the two Connectives `set_option linter.flexible false in` lines.
- [ ] GeneralizedNecessitation's three scoped `... in` suppressions remain intact.

## Artifacts & Outputs

- plans/01_drop-linter-suppressions.md (this plan)
- summaries/01_drop-linter-suppressions-summary.md (implementation summary, produced by /implement)
- Modified Lean sources (nine files listed across Phases 1-4)

## Rollback/Contingency

- All changes are structural (deletions, line wraps, blank-line removals, one 2-decl scope
  narrowing) confined to nine files. If any module fails to build clean after its edit, revert
  that single file with `git checkout -- <file>` (only on a clean-or-snapshotted tree per
  git-workflow.md) and re-probe the specific finding with `lake build <Module>` before retrying.
- If the Connectives `... in` narrowing does not clear `flexible`, the documented fallback is to
  rewrite the two `simp`s as `simp only [...]`; treat this as a last resort given the higher risk
  to a working ported proof, and verify with `lake build` after any such change.
