# Implementation Plan: Fix Namespace Lint Errors

- **Task**: 209 - Fix namespace lint errors (not namespaced + duplicate namespace)
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/209_lint_namespace_fixes/reports/01_namespace-research.md
- **Artifacts**: plans/01_namespace-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix all 298 namespace lint errors reported by `lake lint` across the CSLib codebase. The errors fall into two linter categories: `topNamespace` (239 errors from instance declarations outside any namespace) and `dupNamespace` (59 errors from duplicate namespace components). The fix is organized into three phases of increasing risk: wrapping instance sections in namespaces, annotating Chronicle structs with nolint, and removing redundant qualified prefixes from Temporal/Bimodal definitions with downstream reference updates.

### Research Integration

The research report (01_namespace-research.md) identified:
- 17 files with topNamespace errors, all in ProofSystem/Instances directories
- 8 files with dupNamespace errors split into two sub-patterns: Chronicle struct naming (30 errors) and redundant Temporal/Bimodal qualifiers (29 errors)
- Zero explicit references to auto-generated instance names (confirming Phase 1 is safe)
- ~463 reference site updates needed for Phase 3 qualified def renames
- One explicit fully-qualified doubled name in PropositionalConservativity.lean that must be updated

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is a linting cleanup that unblocks CI compliance across all modules listed in the roadmap (Modal, Temporal, Bimodal). Clean lint output enables reliable CI for ongoing completeness work in Temporal and Bimodal metalogic.

## Goals & Non-Goals

**Goals**:
- Eliminate all 239 topNamespace lint errors by wrapping instance sections in appropriate namespaces
- Eliminate all 30 Chronicle dupNamespace errors via `@[nolint dupNamespace]` annotation
- Eliminate all 29 Temporal/Bimodal dupNamespace errors by removing redundant qualified prefixes
- Maintain a green `lake build` at each phase boundary
- Remove any `set_option linter.dupNamespace false` directives that become unnecessary

**Non-Goals**:
- Restructuring Chronicle namespace hierarchy (Option 1 from research -- too invasive)
- Renaming the Chronicle struct itself (Option 2 from research -- too many downstream changes)
- Fixing any lint categories other than topNamespace and dupNamespace

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Instance resolution breaks after namespace wrapping | H | L | Auto-generated names are never referenced explicitly; typeclass resolution is name-independent |
| Downstream references break after removing Temporal/Bimodal qualifiers | H | M | Grep all reference sites before editing; build iteratively per-file; revert on failure |
| Missed reference in file not covered by grep | M | L | Full `lake build` after each sub-batch of files; one explicit FQN already identified in research |
| Nolint annotation does not suppress generated sub-declarations | M | L | Test on one file first; nolint on structure suppresses .mk, .rec, and field projectors |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: topNamespace Fixes (239 errors) [NOT STARTED]

**Goal**: Wrap all instance `section` blocks in the 17 affected ProofSystem/Instances files inside the appropriate namespace, eliminating all 239 topNamespace lint errors.

**Tasks**:
- [ ] Add `namespace Cslib.Logic.Modal` / `end Cslib.Logic.Modal` around instance sections in all 15 Modal files:
  - `Cslib/Logics/Modal/ProofSystem/Instances/K.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/B.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/D.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/T.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean`
  - `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean`
- [ ] Add `namespace Cslib.Logic.Bimodal` / `end Cslib.Logic.Bimodal` around instance section in `Cslib/Logics/Bimodal/ProofSystem/Instances.lean`
- [ ] Add `namespace Cslib.Logic.Temporal` / `end Cslib.Logic.Temporal` around instance section in `Cslib/Logics/Temporal/ProofSystem/Instances.lean`
- [ ] Run `lake build` to verify compilation
- [ ] Run `lake lint 2>&1 | grep -c "is not namespaced"` to verify topNamespace error count is 0

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` - Wrap instance section in namespace
- `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` - Wrap instance section in namespace
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` - Wrap instance section in namespace
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - Wrap instance section in namespace

**Verification**:
- `lake build` compiles without errors
- `lake lint 2>&1 | grep "is not namespaced"` returns zero matches
- Instance resolution still works (build success confirms this)

---

### Phase 2: dupNamespace Chronicle Fixes (30 errors) [NOT STARTED]

**Goal**: Suppress dupNamespace lint errors for the `Chronicle` struct in both ChronicleTypes.lean files using `@[nolint dupNamespace]`, eliminating 30 dupNamespace errors.

**Tasks**:
- [ ] Add `@[nolint dupNamespace]` before `structure Chronicle` in `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`
- [ ] Add `@[nolint dupNamespace]` before `structure Chronicle` in `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`
- [ ] Check for and remove any `set_option linter.dupNamespace false` in these files if it exists and is no longer needed
- [ ] Run `lake build` to verify compilation
- [ ] Run `lake lint 2>&1 | grep "Chronicle"` to verify Chronicle-related dupNamespace errors are gone

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - Add nolint annotation to Chronicle struct
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` - Add nolint annotation to Chronicle struct

**Verification**:
- `lake build` compiles without errors
- `lake lint 2>&1 | grep "Chronicle.*duplicated"` returns zero matches
- No `set_option linter.dupNamespace false` remains in these files (unless needed for other declarations)

---

### Phase 3: dupNamespace Qualified Def Renames (29 errors, ~463 reference updates) [NOT STARTED]

**Goal**: Remove redundant `Temporal.` and `Bimodal.` qualifiers from definitions inside their matching namespaces, and update all downstream reference sites, eliminating the remaining 29 dupNamespace errors.

**Tasks**:
- [ ] In definition files, remove the redundant qualifier prefix from each affected declaration:
  - `Cslib/Logics/Temporal/ProofSystem/Derivable.lean`: Remove `Temporal.` prefix from `Temporal.Deriv`, `Temporal.ThDerivable`, etc. (9 declarations)
  - `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean`: Remove `Temporal.` prefix from `Temporal.SetConsistent`, `Temporal.SetMaximalConsistent`, etc. (4 declarations)
  - `Cslib/Logics/Temporal/Metalogic/MCS.lean`: Remove `Temporal.` prefix (2 declarations)
  - `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean`: Remove `Temporal.` prefix (2 declarations)
  - `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean`: Remove `Bimodal.` prefix from `Bimodal.Deriv`, `Bimodal.Derivable`, etc. (10 declarations)
  - `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean`: Remove `Bimodal.` prefix (2 declarations)
- [ ] Update all reference sites for Temporal names (~417 sites):
  - `Temporal.SetMaximalConsistent` -> `SetMaximalConsistent` (within namespace) or full path (270 refs)
  - `Temporal.SetConsistent` -> `SetConsistent` or full path (39 refs)
  - `Temporal.Deriv` -> `Deriv` or full path (39 refs)
  - `Temporal.Derivable` -> `Derivable` or full path (23 refs)
  - `Temporal.SetMaximalConsistentFc` -> `SetMaximalConsistentFc` or full path (15 refs)
  - `Temporal.DerivFc` -> `DerivFc` or full path (14 refs)
  - `Temporal.ThDerivable` -> `ThDerivable` or full path (7 refs)
  - `Temporal.ThDerivableFc` -> `ThDerivableFc` or full path (5 refs)
  - `Temporal.SetConsistentFc` -> `SetConsistentFc` or full path (5 refs)
- [ ] Update all reference sites for Bimodal names (~46 sites):
  - `Bimodal.Derivable` -> `Derivable` or full path (28 refs)
  - `Bimodal.Deriv` -> `Deriv` or full path (13 refs)
  - `Bimodal.ThDerivable` -> `ThDerivable` or full path (5 refs)
- [ ] Fix the explicit fully-qualified doubled name: `Cslib.Logic.Bimodal.Bimodal.ThDerivable` -> `Cslib.Logic.Bimodal.ThDerivable` in `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean:117`
- [ ] Remove any `set_option linter.dupNamespace false` in the 6 definition files if no longer needed
- [ ] Build iteratively: run `lake build` after each batch of reference updates (per-name or per-file)
- [ ] Run `lake lint 2>&1 | grep "dupNamespace"` to verify zero remaining dupNamespace errors

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` - Remove `Temporal.` prefix from 9 definitions
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - Remove `Temporal.` prefix from 4 definitions
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` - Remove `Temporal.` prefix from 2 definitions
- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` - Remove `Temporal.` prefix from 2 definitions
- `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean` - Remove `Bimodal.` prefix from 10 definitions
- `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean` - Remove `Bimodal.` prefix from 2 definitions
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` - Fix explicit FQN
- ~20-30 additional files across `Cslib/Logics/Temporal/` and `Cslib/Logics/Bimodal/` for reference updates (exact file list determined by grep at implementation time)

**Verification**:
- `lake build` compiles without errors after all reference updates
- `lake lint 2>&1 | grep "dupNamespace"` returns zero matches
- `grep -r "Temporal\.Temporal\.\|Bimodal\.Bimodal\." Cslib/` returns zero matches (no doubled namespaces remain)

## Testing & Validation

- [ ] `lake build` compiles the entire Cslib library without errors
- [ ] `lake lint 2>&1 | grep -c "is not namespaced"` returns 0 (was 239)
- [ ] `lake lint 2>&1 | grep -c "is duplicated in the name"` returns 0 (was 59)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes (no new style violations introduced)

## Artifacts & Outputs

- `specs/209_lint_namespace_fixes/plans/01_namespace-plan.md` (this file)
- `specs/209_lint_namespace_fixes/summaries/01_namespace-summary.md` (after implementation)

## Rollback/Contingency

- Phase 1 (namespace wrapping): Revert namespace additions; instances return to root namespace. Zero risk of data loss.
- Phase 2 (nolint annotations): Remove `@[nolint dupNamespace]` annotations. Trivial revert.
- Phase 3 (qualifier removal): This is the highest-risk phase. If reference updates cause cascading build failures, revert the entire phase via `git checkout` of the affected files. The research report identified all reference sites, so partial revert is also possible (revert one name at a time). Keep Phase 1 and Phase 2 changes even if Phase 3 is reverted -- they are independently valuable.
