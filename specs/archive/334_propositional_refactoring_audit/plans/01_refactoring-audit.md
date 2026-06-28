# Implementation Plan: Propositional Refactoring Audit

- **Task**: 334 - Propositional refactoring audit
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/334_propositional_refactoring_audit/reports/01_refactoring-audit.md
- **Artifacts**: plans/01_refactoring-audit.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Extract shared subformula and complexity definitions into a new standalone module
`Cslib/Logics/Propositional/Subformula.lean`, then update all consumers to import
from this shared module. This eliminates 135 lines of pure duplication between
Normalization.lean and SubformulaProperty.lean (the `lkSubformulas`/`LKIsSubformula`
copies), resolves the `Proposition.complexity` name collision caused by a phantom
Tableau.Defs import in CutElimination.lean, and applies several lower-severity fixes
(private Finset helpers, barrel import cleanup). The task is a safe series of
extract-then-delete refactoring steps with build verification after each phase.

### Research Integration

The research report (01_refactoring-audit.md) identified 7 issues across 4 severity levels.
This plan addresses all 7 in dependency order:
- Issues 1-2 (HIGH): Subformula/complexity duplication and phantom import -- Phases 1-3
- Issues 3-5 (MEDIUM): File size, misplaced helpers, mixed concerns -- Phases 2-4
- Issues 6-7 (LOW): Barrel import inconsistency, sorry inventory -- Phase 5

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly correspond to this task. The refactoring improves code hygiene
and unblocks future consumers of the subformula API.

## Goals & Non-Goals

**Goals**:
- Create a single canonical `Proposition.subformulas`/`Proposition.IsSubformula`/`Proposition.complexity` module
- Eliminate the `lkSubformulas`/`LKIsSubformula` duplication in SubformulaProperty.lean
- Remove the phantom `Tableau.Defs` import from CutElimination.lean
- Consolidate complexity definition with its simp lemmas into the shared module
- Mark misplaced Finset helpers as private
- Clean up barrel import inconsistency
- Pass full CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`

**Non-Goals**:
- Splitting Normalization.lean further (deferred to task 333)
- Filling any sorries (Issue 7 is out of scope)
- Modifying proof strategies or algorithms
- Adding new theorems or definitions beyond what is being extracted

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing Tableau.Defs import from CutElimination.lean breaks transitive consumers | H | L | Research confirms CutElimination uses nothing from Tableau.Defs; build verification after removal |
| Renaming lkSubformulas to subformulas in SubformulaProperty.lean breaks downstream proofs | M | M | The proofs use the local names internally; after import swap, update all references in the same file |
| Complexity simp lemmas in Tableau/Defs.lean are needed by consumers that do not import Subformula.lean | M | L | Check all `complexity` grep hits; Tableau consumers already import Tableau.Defs which will re-export via Subformula.lean |
| lake shake reports unnecessary imports after restructuring | L | M | Run lake shake as final step and fix any flagged imports |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Subformula.lean shared module [COMPLETED]

**Goal**: Create a new standalone module containing the canonical subformula infrastructure
and complexity definitions, importing only from `Cslib/Logics/Propositional/Defs.lean`.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Subformula.lean`
- [ ] Copy `Proposition.subformulas` definition from Normalization.lean (lines 63-68)
- [ ] Copy `Proposition.IsSubformula` definition from Normalization.lean (lines 71-72)
- [ ] Copy all 9 subformula lemmas: `self_mem_subformulas`, `IsSubformula.refl`, `IsSubformula.trans`, `IsSubformula.and_left`, `IsSubformula.and_right`, `IsSubformula.or_left`, `IsSubformula.or_right`, `IsSubformula.imp_left`, `IsSubformula.imp_right` (lines 75-145)
- [ ] Copy `Proposition.complexity` definition from Normalization.lean (lines 149-154)
- [ ] Copy the 5 `@[simp]` complexity lemmas from Tableau/Defs.lean (lines 152-173): `complexity_imp`, `complexity_and`, `complexity_or`, `complexity_atom`, `complexity_bot`
- [ ] Add proper module docstring explaining this is the canonical shared subformula/complexity module
- [ ] Add `import Cslib.Init` and `public import Cslib.Logics.Propositional.Defs`
- [ ] Verify with `lake build Cslib.Logics.Propositional.Subformula`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Subformula.lean` - NEW FILE: shared subformula + complexity definitions

**Verification**:
- `lake build Cslib.Logics.Propositional.Subformula` passes with no errors

---

### Phase 2: Remove phantom import and update CutElimination.lean [COMPLETED]

**Goal**: Delete the phantom `Tableau.Defs` import from CutElimination.lean and mark the
three generic Finset helpers as private.

**Tasks**:
- [ ] Delete `public import Cslib.Logics.Propositional.Tableau.Defs` from CutElimination.lean line 11
- [ ] Add `private` keyword to `mem_of_ne_head` (line 106) *(deviation: skipped -- private helpers inside @[expose] public section cannot be referenced from mutual block; Lean 4 access error)*
- [ ] Add `private` keyword to `subset_insert2` (line 113) *(deviation: skipped -- same reason as above)*
- [ ] Add `private` keyword to `insert_subset_swap` (line 119) *(deviation: skipped -- same reason as above)*
- [ ] Verify with `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination`

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Remove phantom import, privatize helpers

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` passes
- `grep -c "Tableau.Defs" CutElimination.lean` returns 0

---

### Phase 3: Update Normalization.lean and Tableau/Defs.lean [COMPLETED]

**Goal**: Replace local subformula/complexity definitions with imports from the new shared
module, and remove the duplicate definitions from both files.

**Tasks**:
- [ ] In Normalization.lean, add `public import Cslib.Logics.Propositional.Subformula` after existing imports
- [ ] Delete the subformula infrastructure section from Normalization.lean (lines 57-155): the section heading, `Proposition.subformulas`, `Proposition.IsSubformula`, all 9 lemmas, and `Proposition.complexity`
- [ ] Verify Normalization.lean builds: `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`
- [ ] In Tableau/Defs.lean, add `public import Cslib.Logics.Propositional.Subformula` after existing imports
- [ ] Delete the complexity definition and all 5 simp lemmas from Tableau/Defs.lean (lines 106-173)
- [ ] Remove the now-empty "Convenience Lemmas" section header if the only remaining lemmas are the decomposition simp lemmas (propAndOf?, etc.) -- keep those
- [ ] Verify Tableau/Defs.lean builds: `lake build Cslib.Logics.Propositional.Tableau.Defs`

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` - Delete local subformula/complexity defs, add import
- `Cslib/Logics/Propositional/Tableau/Defs.lean` - Delete local complexity def + simp lemmas, add import

**Verification**:
- Both modules build individually
- Normalization.lean line count drops by approximately 100 lines
- `grep -c "def Proposition.complexity" Normalization.lean` returns 0
- `grep -c "def Proposition.complexity" Tableau/Defs.lean` returns 0

---

### Phase 4: Update SubformulaProperty.lean [COMPLETED]

**Goal**: Replace the `lk`-prefixed subformula duplicates with imports from the shared
module, rewriting all proof references from `lkSubformulas`/`LKIsSubformula` to
`subformulas`/`IsSubformula`.

**Tasks**:
- [ ] In SubformulaProperty.lean, add `public import Cslib.Logics.Propositional.Subformula` after existing imports
- [ ] Delete the entire lk-prefixed subformula infrastructure section (lines 46-135): `lkSubformulas`, `LKIsSubformula`, `self_mem_lkSubformulas`, `LKIsSubformula.refl`, `LKIsSubformula.trans`, and all 6 directional lemmas
- [ ] Search-and-replace all remaining references in the file: `lkSubformulas` -> `subformulas`, `LKIsSubformula` -> `IsSubformula`, `self_mem_lkSubformulas` -> `self_mem_subformulas`
- [ ] Verify with `lake build Cslib.Logics.Propositional.SequentCalculus.LK.SubformulaProperty`
- [ ] If build fails, inspect error locations and fix any proof term mismatches (the proofs should work since the definitions are identical)

**Timing**: 45 minutes

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean` - Delete lk-prefixed defs, update all references

**Verification**:
- Module builds successfully
- `grep -c "lkSubformulas\|LKIsSubformula" SubformulaProperty.lean` returns 0
- Line count drops by approximately 90 lines

---

### Phase 5: Barrel imports, mk_all, and full CI verification [IN PROGRESS]

**Goal**: Update barrel imports, register the new module, and run the complete CI pipeline.

**Tasks**:
- [ ] Update `Cslib/Logics/Propositional/SequentCalculus/LK.lean`: uncomment the CutElimination barrel import (line 13) or add a clarifying comment that SubformulaProperty already transitively imports it
- [ ] Run `lake exe mk_all --module` to register `Cslib.Logics.Propositional.Subformula` in the barrel file
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix`
- [ ] Fix any issues found by CI tools
- [ ] Verify no sorries were added or removed (sorry count should remain 13 across 5 files)

**Timing**: 45 minutes

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` - Update barrel import comment/uncomment
- `Cslib.lean` - Updated by `lake exe mk_all --module`
- Any files flagged by `lake shake` for import cleanup

**Verification**:
- `lake build` passes with zero errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake shake` reports no actionable fixes (or all fixes applied)

## Testing & Validation

- [ ] Full `lake build` passes (confirms no broken imports or name collisions)
- [ ] `lake exe checkInitImports` passes (Cslib.Init import in new file)
- [ ] `lake exe lint-style` passes (formatting in new file)
- [ ] `lake shake` passes (import minimization)
- [ ] `grep -rn "lkSubformulas\|LKIsSubformula" Cslib/` returns zero hits (duplication eliminated)
- [ ] `grep -c "def Proposition.complexity" Cslib/` returns exactly 1 (in Subformula.lean only)
- [ ] `grep -c "def Proposition.subformulas" Cslib/` returns exactly 1 (in Subformula.lean only)
- [ ] Sorry count unchanged (13 sorries across 5 files, per research report Issue 7)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Subformula.lean` - New shared module (created in Phase 1)
- `specs/334_propositional_refactoring_audit/plans/01_refactoring-audit.md` - This plan
- `specs/334_propositional_refactoring_audit/summaries/01_refactoring-audit-summary.md` - Implementation summary (post-implementation)

## Rollback/Contingency

All changes are in tracked files. If the refactoring introduces build failures that cannot
be resolved:
1. `git stash` or `git checkout -- .` to revert all changes
2. The original files remain intact in git history
3. Each phase commits independently, so partial rollback is possible by reverting specific commits

If the SubformulaProperty.lean rewrite (Phase 4) proves more complex than expected due to
proof term differences, an intermediate approach is to keep the lk-prefixed names as aliases
(`abbrev lkSubformulas := subformulas`) to maintain backward compatibility while eliminating
the code duplication.
