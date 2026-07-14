# Implementation Plan: Task #458

- **Task**: 458 - Fix lake shake import findings in shared Measure module + Classical consumer (task 455 vet)
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/458_vet_455_shake_import_hygiene/.orchestrator-handoff.json
- **Artifacts**: plans/01_shake-import-hygiene.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Apply two verified, mechanical `lake shake` import-hygiene edits identified during the task 455 vet. One edit removes an unused Mathlib import from a shared measure module; the other replaces a transitively-relied-upon `public import` in the Classical tableau completeness consumer with two direct `public import` lines for the modules it actually uses. No proofs or declarations change. The concrete edit list, line numbers, and evidence are fully specified in the research handoff JSON, so this is a single execution phase with scoped-build verification.

### Research Integration

The handoff JSON (`.orchestrator-handoff.json`) records both edits with per-line evidence:
- **Measure.lean:11** — `lake shake --add-public --keep-implied --keep-prefix` explicitly printed a "remove" suggestion for `import Mathlib.Algebra.BigOperators.Group.List.Basic`. The `List.sum_cons`/`List.map_cons`/`List.length_cons` uses at line 48 resolve via other imports.
- **Completeness.lean:11** — reference analysis found zero uses of Soundness's 5 own declarations, and heavy use of Expansion decls (100+ refs) and Bool decls (50+ refs) currently obtained transitively through Soundness. Direct public imports are required to preserve availability while dropping the unused Soundness dependency.
- Verification note: a concurrent session is mid-edit on `Cslib.Logics.Temporal.Tableau.*`, which can block a full-environment `lake shake` re-run. Scoped `lake build` of the two touched modules is the reliable, authoritative verification for this task.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap flag not set). Advances CONTRIBUTING.md shake-cleanliness hygiene flagged by the task 455 vet.

## Goals & Non-Goals

**Goals**:
- Remove the unused `import Mathlib.Algebra.BigOperators.Group.List.Basic` from `Measure.lean`.
- Replace the unused `public import ...Classical.Soundness` in `Completeness.lean` with direct `public import` lines for `...Classical.Expansion` and `...Semantics.Bool`.
- Confirm both modules still build via a scoped `lake build`.

**Non-Goals**:
- Fixing the pre-existing, out-of-scope `sorry` in `Minimal/Completeness.lean:104`.
- Editing or re-shaking the concurrently-modified `Cslib.Logics.Temporal.Tableau.*` modules.
- Any proof, declaration, or semantic changes.
- A full-environment `lake shake` re-run while the concurrent Temporal edits are unsettled.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing an import breaks a transitive dependency | M | L | Scoped `lake build` of both modules after edits; revert if build fails |
| `Cslib.Init` import accidentally touched | M | L | Only edit line 11 in each file; never remove `import Cslib.Init` |
| Concurrent Temporal edits block full shake | L | H | Use scoped `lake build` as authoritative verification instead of full shake |
| Line numbers shifted since research | L | L | Match on exact old-line text (from handoff), not line number alone |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single phase; no parallelism required.

### Phase 1: Apply and verify shake import-hygiene edits [COMPLETED]

**Goal**: Apply both verified import edits and confirm the two affected modules build cleanly.

**Tasks**:
- [x] In `Cslib/Foundations/Logic/Tableau/Measure.lean` line 11, remove the line `import Mathlib.Algebra.BigOperators.Group.List.Basic` (match on exact text; do not touch `import Cslib.Init`).
- [x] In `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` line 11, replace `public import Cslib.Logics.Propositional.Tableau.Classical.Soundness` with the two lines `public import Cslib.Logics.Propositional.Tableau.Classical.Expansion` and `public import Cslib.Logics.Propositional.Semantics.Bool`.
- [x] Run scoped build: `lake build Cslib.Foundations.Logic.Tableau.Measure Cslib.Logics.Propositional.Tableau.Classical.Completeness`.
- [x] Confirm the build completes successfully with no new errors or warnings. *(deviation: altered -- dependent-module build of `Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure` failed with "Unknown identifier `classicalTableau_sound`" because that file used `classicalTableau_sound` (from `Soundness.lean`) transitively via `Completeness.lean`'s public import, a path this edit removed. Fixed by adding a direct `public import Cslib.Logics.Propositional.Tableau.Classical.Soundness` to `DecisionProcedure.lean`; not part of the original 2-edit plan but required to keep the build green. Full re-verification: Measure/Completeness build unchanged at 52 pre-existing warnings (baseline-compared via git stash), zero new errors; dependents `Classical.lean`, `DecisionProcedure.lean`, `Foundations/Logic/Tableau.lean` all build green.)*

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Tableau/Measure.lean` - remove unused Mathlib BigOperators list import (line 11)
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - replace transitive Soundness public import with direct Expansion + Bool public imports (line 11)
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` - *(deviation: added)* add direct `public import ...Classical.Soundness` (line 11) to restore `classicalTableau_sound` availability lost when Completeness.lean's transitive Soundness import was removed

**Verification**:
- `lake build Cslib.Foundations.Logic.Tableau.Measure Cslib.Logics.Propositional.Tableau.Classical.Completeness` completes successfully.
- Neither file's `import Cslib.Init` line was altered.
- Optional (only if the concurrent `Cslib.Logics.Temporal.Tableau.*` edits have settled and oleans are current): re-run `lake shake --add-public --keep-implied --keep-prefix Cslib.Logics.Propositional.Tableau.Classical.Completeness` for the authoritative printed suggestion. Skip if blocked; scoped build is sufficient.

---

## Testing & Validation

- [ ] Scoped `lake build` of both modules succeeds.
- [ ] No new sorries, errors, or warnings introduced (import-hygiene only).
- [ ] `import Cslib.Init` preserved in both files.

## Artifacts & Outputs

- Edited `Cslib/Foundations/Logic/Tableau/Measure.lean`
- Edited `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
- Implementation summary: `summaries/01_shake-import-hygiene-summary.md`

## Rollback/Contingency

If the scoped `lake build` fails after edits, `git checkout -- <file>` the affected file(s) to restore the original imports and re-inspect. Because both edits are single-line import changes with no proof impact, reverting is immediate and lossless. If only the Completeness edit fails, the Measure edit is independent and can stand alone.
