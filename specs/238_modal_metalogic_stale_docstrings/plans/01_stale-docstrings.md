# Implementation Plan: Fix Stale Module Docstrings in Modal/Metalogic

- **Task**: 238 - Fix stale module docstrings in Modal/Metalogic after task 237 theorem migration
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None (task 237 already completed)
- **Research Inputs**: specs/238_modal_metalogic_stale_docstrings/reports/01_stale-docstrings.md
- **Artifacts**: plans/01_stale-docstrings.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

After task 237 migrated weak completeness theorems from individual Completeness.lean files into
StrongCompleteness.lean (as corollaries of strong completeness), 9 module docstrings became
stale. This plan covers replacing all 9 docstrings: one unique update to the core
Completeness.lean infrastructure file, and 8 templated replacements for empty-body system files
that now serve only as import chain anchors.

### Research Integration

The research report (01_stale-docstrings.md) identified all 9 affected files, catalogued the
exact docstring issues in each, established the target pattern from the already-correct B/S4/S5
files, and provided replacement text for every change. The plan follows the report's change
specifications directly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is a cleanup operation following the modal cube completeness work. It does not directly
advance a specific ROADMAP.md line item but improves codebase documentation quality for the
Modal/Metalogic module.

## Goals & Non-Goals

**Goals**:
- Update the core Completeness.lean docstring to accurately describe its contents (canonical model infrastructure, not completeness theorems)
- Replace 8 stale "proves completeness" docstrings with accurate infrastructure docstrings matching the B/S4/S5 pattern
- Resolve the contradictory hybrid docstring in K5/Completeness.lean

**Non-Goals**:
- Modifying any Lean code (all changes are `/-! ... -/` comment blocks only)
- Updating files that already have correct docstrings (B, S4, S5, K, D, T, TB)
- Running build verification (comment-only changes cannot break the build)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Incorrect theorem name in docstring | L | L | Cross-reference research report's verified inventory of actual file contents |
| Accidental code modification | H | L | Use targeted Edit operations on `/-! ... -/` blocks only |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Update Core Completeness.lean Docstring [COMPLETED]

**Goal**: Replace the stale docstring in `Cslib/Logics/Modal/Metalogic/Completeness.lean` with
an accurate description of the file's current contents (canonical model infrastructure).

**Tasks**:
- [x] Read the current docstring in Completeness.lean (lines 12-37)
- [x] Replace the `/-! ... -/` block with the updated version from the research report:
  - Change title to "Canonical Model Infrastructure for Normal Modal Logics"
  - Remove `completeness` from Main Results
  - Add `canonical_symm`, `canonical_eucl_from_5`, `neg_consistent_of_not_derivable` to Main Results
  - Remove S5-specific wrapper phrasing
  - Update Design section to reference StrongCompleteness.lean modules

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - Replace module docstring

**Verification**:
- Docstring title says "Canonical Model Infrastructure", not "Completeness Theorem"
- Main Results lists 9 items (no `completeness` theorem, includes `canonical_symm`, `canonical_eucl_from_5`, `neg_consistent_of_not_derivable`)
- No mention of S5-specific wrapper

---

### Phase 2: Batch-Update 8 Empty-Body System Docstrings [COMPLETED]

**Goal**: Replace stale "proves completeness" docstrings in 8 empty-body Completeness.lean files
with the infrastructure pattern established by B/S4/S5.

**Tasks**:
- [x] K4/Completeness.lean: Replace docstring with K4 infrastructure pattern (theorem name: `k4_completeness`)
- [x] K5/Completeness.lean: Replace contradictory hybrid docstring with K5 infrastructure pattern (theorem name: `k5_completeness`)
- [x] K45/Completeness.lean: Replace docstring with K45 infrastructure pattern (theorem name: `k45_completeness`)
- [x] KB5/Completeness.lean: Replace docstring with KB5 infrastructure pattern (theorem name: `kb5_completeness`)
- [x] D4/Completeness.lean: Replace docstring with D4 infrastructure pattern (theorem name: `d4_completeness`)
- [x] D5/Completeness.lean: Replace docstring with D5 infrastructure pattern (theorem name: `d5_completeness`)
- [x] D45/Completeness.lean: Replace docstring with D45 infrastructure pattern (theorem name: `d45_completeness`)
- [x] DB/Completeness.lean: Replace docstring with DB infrastructure pattern (theorem name: `db_completeness`)

**Template** (substitute `{SYSTEM}` and `{system}`):
```
/-! # {SYSTEM} Completeness Infrastructure

This module provides import infrastructure for modal logic {SYSTEM}.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `{system}_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.{SYSTEM}.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Completeness.lean` - Replace module docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K5/Completeness.lean` - Replace module docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Completeness.lean` - Replace module docstring
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Completeness.lean` - Replace module docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean` - Replace module docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Completeness.lean` - Replace module docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Completeness.lean` - Replace module docstring
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Completeness.lean` - Replace module docstring

**Verification**:
- All 8 files have title "{SYSTEM} Completeness Infrastructure"
- All 8 files say "provides import infrastructure", not "proves completeness"
- All 8 files cross-reference the correct StrongCompleteness.lean path
- K5/Completeness.lean no longer has the contradictory hybrid docstring

## Testing & Validation

- [x] Verify no file contains the stale phrase "This module proves completeness" in its docstring
- [x] Verify core Completeness.lean does not list `completeness` in Main Results
- [x] Optionally run `lake build` to confirm no regressions (all 9 modules build successfully)

## Artifacts & Outputs

- `specs/238_modal_metalogic_stale_docstrings/plans/01_stale-docstrings.md` (this plan)
- 9 modified Lean files (docstring-only changes)

## Rollback/Contingency

All changes are to `/-! ... -/` comment blocks only. If any issue arises, revert the
specific file's docstring using `git checkout -- <file>`. No code or import changes are
involved, so rollback is trivial.
