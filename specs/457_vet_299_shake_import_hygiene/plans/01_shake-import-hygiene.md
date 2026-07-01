# Implementation Plan: Task #457

- **Task**: 457 - Fix lake shake import findings in modal K tableau files (task 299 vet)
- **Status**: [IMPLEMENTED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/457_vet_299_shake_import_hygiene/.orchestrator-handoff.json
- **Artifacts**: plans/01_shake-import-hygiene.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Apply six verified `lake shake` import-hygiene edits across the `Cslib/Logics/Modal/Tableau/` module tree (two removals of transitively-available imports, two additions of directly-used imports, one re-target, and one further redundant removal). Each edit was confirmed by running `lake shake --add-public --keep-implied --keep-prefix` on the scoped modules during research; import identity (not line number) makes each edit unambiguous. The change is purely mechanical import housekeeping with no proof or definition changes, then verified by a full `lake build` plus a re-run of shake to confirm zero regressions.

### Research Integration

The research handoff (`.orchestrator-handoff.json`, `shake_confirmed: true`, `safe_to_implement: true`) verified all 6 findings against current code and documented exact edits by import identity. Key notes carried forward:
- `Cslib.Init` imports must NOT be removed (systemic, mandatory per checkInitImports / CONTRIBUTING.md); the reported `Cslib.Init` shake suggestions are explicitly out of scope.
- `Measure.lean` removing `Mathlib.Algebra.BigOperators.Group.List.Basic` is out of scope (not one of the 6 findings).
- `LoopInduction` removals are safe: `CompletenessLoop.lean` still receives it transitively via `Soundness`; no module uses `forall₂_replicate_right`.
- Task-text line numbers are approximate (e.g. the `Defs.lean` import is at line 11, not 17); locate edits by import string, not line number.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap flag not set). Task supports CONTRIBUTING.md shake cleanliness ahead of an upstream PR.

## Goals & Non-Goals

**Goals**:
- Apply the 6 verified shake-suggested import edits exactly as documented in the handoff.
- Confirm no build regressions via full `lake build`.
- Confirm shake reports the scoped modules clean via re-run.

**Non-Goals**:
- Removing or altering any `import Cslib.Init` line (mandatory; out of scope).
- Removing `Mathlib.Algebra.BigOperators.Group.List.Basic` from `Measure.lean` (out of scope).
- Any proof, definition, or logic changes.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Accidentally removing an `import Cslib.Init` line | H | L | Edit only the import strings named in the handoff; never touch `Cslib.Init`. `lake exe checkInitImports` in verification catches any lapse. |
| Removing an import that is actually used directly | M | L | Edits are shake-verified; final `lake build` + shake re-run confirm no regression. |
| Line numbers drift from task text | L | M | Locate edits by exact import string (import identity), not by line number. |
| Added import placed before `import Cslib.Init` | L | L | Insert new imports after the existing `import Cslib.Init` line, matching handoff `insert_after_line`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Apply Shake Import Edits [COMPLETED]

**Goal**: Apply all six verified import edits by import identity, preserving every `import Cslib.Init` line.

**Tasks**:
- [x] `Defs.lean`: REMOVE line `public import Cslib.Foundations.Logic.Tableau.PropositionalRules` (~line 11). *(deviation: reverted -- applying this edit broke the build with `unknown namespace 'Cslib.Logic.Tableau'` at the file's `open Cslib.Logic.Tableau` statement (line 48). PropositionalRules.lean is the sole import-path source declaring that namespace for this file; shake does not track bare `open Namespace` usage with no member references, making this a shake false-positive. The import was restored to its original state -- net diff for this file is empty.)*
- [x] `Branch.lean`: ADD `public import Cslib.Foundations.Logic.Tableau.SignedFormula` immediately after the `import Cslib.Init` line.
- [x] `Rules.lean`: ADD `public import Cslib.Foundations.Logic.Tableau.PropositionalRules` immediately after the `import Cslib.Init` line.
- [x] `Closure.lean` (line ~10): REPLACE `public import Cslib.Logics.Modal.Tableau.Rules` with `public import Cslib.Logics.Modal.Tableau.Defs`.
- [x] `Completeness.lean` (line ~10): REMOVE `public import Cslib.Logics.Modal.Tableau.LoopInduction`.
- [x] `FmpMeasure.lean` (line ~20): REMOVE `public import Cslib.Logics.Modal.Tableau.LoopInduction`.

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Defs.lean` - remove unused PropositionalRules import
- `Cslib/Logics/Modal/Tableau/Branch.lean` - add missing SignedFormula import (after Cslib.Init)
- `Cslib/Logics/Modal/Tableau/Rules.lean` - add missing PropositionalRules import (after Cslib.Init)
- `Cslib/Logics/Modal/Tableau/Closure.lean` - retarget Rules import to Defs
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - remove redundant LoopInduction import
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` - remove redundant LoopInduction import

**Verification**:
- Each named import string is added/removed/retargeted as listed.
- Every `import Cslib.Init` line in all six files remains intact.

---

### Phase 2: Verify Build and Shake Cleanliness [COMPLETED]

**Goal**: Confirm the edits introduce no regressions and satisfy shake.

**Tasks**:
- [x] Run `lake build` (full build) and confirm success with no errors.
- [x] Re-run `lake shake` on the scoped Modal/Tableau modules and confirm the findings are resolved with no new findings. *(deviation: altered -- the installed `lake exe shake` binary's `--help` does not list `--add-public`, `--keep-implied`, or `--keep-prefix` as valid options; passing them corrupted argument parsing (`unknown module prefix '[anonymous]'`). Verification was instead performed via `lake exe shake --force --no-downstream --cfg <temp-empty-cfg>` against the 10-module Modal.Tableau tree (our 6 edited files plus Branch/Rules/Closure/Completeness/FmpMeasure's dependents CompletenessLoop, Saturation, Soundness, SoundnessStep), which confirmed: Branch.lean, Rules.lean, Closure.lean, and Completeness.lean report no further reducible imports (5 of 6 edits hold); Defs.lean is still flagged to remove PropositionalRules, corroborating that this is a shake false-positive (see Phase 1 deviation) rather than a valid finding; FmpMeasure.lean surfaces additional findings (Mathlib imports, `Completeness`) that are outside this task's 6-item scope and were left untouched. A full `lake build` (3188/3188 jobs, exit 0) additionally confirms no regressions anywhere in the library.)*
- [x] Run `lake exe checkInitImports` to confirm all `Cslib.Init` imports are present. *(passed, exit 0, no output)*

**Timing**: 0.5 hours (dominated by build time)

**Depends on**: 1

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` exits successfully.
- Shake re-run shows the scoped modules clean (findings resolved, none introduced).
- `checkInitImports` passes.

---

## Testing & Validation

- [x] `lake build` succeeds with no errors or new warnings attributable to these edits (3188/3188 jobs, exit 0).
- [x] `lake shake` (with the tool's actual supported flags -- `--add-public`/`--keep-implied`/`--keep-prefix` are not supported by the installed binary) reports 5 of 6 findings resolved on the scoped modules; the 6th (Defs.lean) was reverted as a confirmed false-positive.
- [x] `lake exe checkInitImports` passes (all `Cslib.Init` imports intact).

## Artifacts & Outputs

- Modified import headers in 6 `Cslib/Logics/Modal/Tableau/` modules.
- Green `lake build` and clean shake re-run for the scoped modules.

## Rollback/Contingency

All edits are confined to import lines. If the build fails or shake reports a new problem, revert the offending file's import header via `git checkout -- <file>` and re-inspect. Because each edit is independent and import-identity-scoped, individual edits can be reverted without affecting the others. No proof or definition state is touched, so rollback is a clean git restore of the import lines.
