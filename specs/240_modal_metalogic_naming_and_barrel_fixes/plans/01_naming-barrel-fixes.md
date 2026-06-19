# Implementation Plan: Fix Naming Inconsistencies and Barrel File Issues in Modal/Metalogic

- **Task**: 240 - Fix naming inconsistencies and barrel file issues in Modal/Metalogic
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/240_modal_metalogic_naming_and_barrel_fixes/reports/01_naming-barrel-fixes.md
- **Artifacts**: plans/01_naming-barrel-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This plan addresses six naming and organizational inconsistencies in the Modal/Metalogic module of CSLib. All changes are mechanical (import reordering, find-and-replace renames, comment edits, alias removal) with no proof logic modifications. The highest-risk item is the D/Completeness.lean theorem rename (item 4) which affects 15 code references across 11 files; all other items are zero-risk. The plan groups work into three phases by risk level: safe mechanical changes first, then S5 rename, then D renames with full build verification.

### Research Integration

The research report confirmed all six issues as genuine and provided exact file paths, line numbers, and downstream consumer analysis. Key findings:
- Item 4 (D renames) has 15 code references across 6 files and doc references across 5 additional files
- Item 3 (S5 rename) has only internal references plus docstring updates in 2 files
- Items 1, 2, 5, 6 are zero-risk mechanical changes with no downstream consumers

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is a code-quality cleanup within the Modal metalogic module. It does not directly advance any remaining ROADMAP.md items (which focus on discrete/continuous/dense completeness for Bimodal and Temporal). However, it improves the organization of the completed Modal metalogic component listed in ROADMAP.md's Completed section.

## Goals & Non-Goals

**Goals**:
- Add missing ConservativeExtension import to Metalogic.lean barrel file
- Normalize barrel import ordering so both blocks use the same system order
- Rename S5/Soundness.lean `axiom_sound` to `s5_axiom_sound` for consistency with all 14 other systems
- Rename D/Completeness.lean theorems from suffix to prefix convention, updating all downstream references
- Fix misleading K/Completeness.lean comment wording
- Remove unused S5 completeness alias

**Non-Goals**:
- Modifying any proof logic or tactic scripts
- Renaming theorems in systems other than S5 and D (they already follow convention)
- Restructuring the Modal/Metalogic directory layout

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| D rename misses a downstream reference | H | L | Research identified all 15 code refs; use `replace_all` and grep verification after |
| S5 rename conflicts with Temporal namespace | M | L | Research confirmed separate namespaces; no conflict possible |
| Barrel import reordering breaks compilation | L | L | Import order has no semantic effect in Lean 4 module files |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Safe Mechanical Changes (Items 1, 2, 5, 6) [COMPLETED]

**Goal**: Complete all zero-risk changes that have no downstream code consumers.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension` to `Cslib/Logics/Modal/Metalogic.lean` barrel file, placed in the K block
- [ ] Reorder Soundness/Completeness block in barrel file: move S5.Soundness and S5.Completeness imports from the beginning to the end, matching the StrongCompleteness block order (K, T, D, S4, K4, B, K45, K5, D4, KB5, TB, D45, D5, DB, S5)
- [ ] Change `K-SPECIFIC FIX` to `K-SPECIFIC CASE` on line 111 of `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean`
- [ ] Remove the alias `alias completeness := s5_completeness` and its docstring from `Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean` (lines 207-208)

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - Add missing import, reorder Soundness/Completeness block
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` - Comment wording fix
- `Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean` - Remove unused alias

**Verification**:
- Grep for `ConservativeExtension` in barrel file confirms import added
- Visual inspection of barrel file confirms both blocks use same system order
- Grep for `K-SPECIFIC FIX` returns no results
- Grep for `alias completeness` in S5/StrongCompleteness.lean returns no results

---

### Phase 2: S5 Soundness Rename (Item 3) [COMPLETED]

**Goal**: Rename `axiom_sound` to `s5_axiom_sound` in S5/Soundness.lean for naming consistency with all 14 other systems, and update docstring references.

**Tasks**:
- [ ] Rename definition `axiom_sound` to `s5_axiom_sound` in `Cslib/Logics/Modal/Metalogic/Systems/S5/Soundness.lean` (definition on line 42, internal usage on lines 89, 101, docstring on line 19)
- [ ] Update docstring references in `Cslib/Logics/Modal/Metalogic/Soundness.lean` (lines 20, 24, 29) from `axiom_sound` to `s5_axiom_sound` where they refer to S5

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Soundness.lean` - Rename definition + 3 internal references + docstring
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - Update 3 docstring references

**Verification**:
- Grep for bare `axiom_sound` (not prefixed) in Modal/Metalogic returns no code hits
- `s5_axiom_sound` appears in S5/Soundness.lean definition and usage sites

---

### Phase 3: D/Completeness Renames and Build Verification (Item 4) [COMPLETED]

**Goal**: Rename four D/Completeness.lean theorems from suffix/no-prefix convention to prefix convention, update all 15 code references across 5 StrongCompleteness files and all doc references across 6 additional files, then verify full build.

**Tasks**:
- [ ] In `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean`, rename definitions:
  - `derive_box_from_inconsistency_d` to `d_derive_box_from_inconsistency`
  - `mcs_box_witness_d` to `d_mcs_box_witness`
  - `canonical_serial` to `d_canonical_serial`
  - `truth_lemma_d` to `d_truth_lemma`
- [ ] Update `truth_lemma_d` code references (10 occurrences) in:
  - `D/StrongCompleteness.lean` (lines 99, 109)
  - `D4/StrongCompleteness.lean` (lines 111, 121)
  - `D5/StrongCompleteness.lean` (lines 108, 118)
  - `D45/StrongCompleteness.lean` (lines 118, 131)
  - `DB/StrongCompleteness.lean` (lines 111, 121)
- [ ] Update `canonical_serial` code references (5 occurrences) in:
  - `D/StrongCompleteness.lean` (line 91)
  - `D4/StrongCompleteness.lean` (line 95)
  - `D5/StrongCompleteness.lean` (line 95)
  - `D45/StrongCompleteness.lean` (line 97)
  - `DB/StrongCompleteness.lean` (line 95)
- [ ] Update doc/comment references across:
  - `Cslib/Logics/Modal/Metalogic/Completeness.lean` (line 312-313)
  - `D4/Completeness.lean` (line 19-20)
  - `D5/Completeness.lean` (line 19-20)
  - `D45/Completeness.lean` (line 20-21)
  - `DB/Completeness.lean` (line 19-20)
  - `D/StrongCompleteness.lean` (lines 34, 67, 70)
  - `D4/StrongCompleteness.lean` (lines 34, 70)
  - `D5/StrongCompleteness.lean` (lines 34, 70)
  - `D45/StrongCompleteness.lean` (lines 34, 71)
  - `DB/StrongCompleteness.lean` (lines 34, 70)
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic` to verify no breakage
- [ ] Run `lake exe checkInitImports` as sanity check
- [ ] Grep for old names (`truth_lemma_d`, `canonical_serial`, `mcs_box_witness_d`, `derive_box_from_inconsistency_d`) to confirm zero remaining references

**Timing**: 45 minutes

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` - Rename 4 definitions + internal references
- `Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean` - Update code + doc references
- `Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean` - Update code + doc references
- `Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean` - Update code + doc references
- `Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean` - Update code + doc references
- `Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean` - Update code + doc references
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - Update doc references
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean` - Update doc references
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Completeness.lean` - Update doc references
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Completeness.lean` - Update doc references
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Completeness.lean` - Update doc references

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` passes with no errors
- `lake exe checkInitImports` passes
- Grep for old names returns zero results in Modal/Metalogic tree

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic` compiles cleanly after all phases
- [ ] `lake exe checkInitImports` passes (barrel file import added correctly)
- [ ] Grep verification: no remaining instances of old names (`axiom_sound` bare, `truth_lemma_d`, `canonical_serial`, `mcs_box_witness_d`, `derive_box_from_inconsistency_d`, `K-SPECIFIC FIX`, `alias completeness`)

## Artifacts & Outputs

- `specs/240_modal_metalogic_naming_and_barrel_fixes/plans/01_naming-barrel-fixes.md` (this plan)
- `specs/240_modal_metalogic_naming_and_barrel_fixes/summaries/01_naming-barrel-fixes-summary.md` (post-implementation)

## Rollback/Contingency

All changes are mechanical renames and import edits with no proof logic modifications. If any phase causes build failures, revert the specific file edits using `git checkout -- <file>` for the affected files. The phased approach isolates risk: phases 1 and 2 are independently safe, and phase 3 (the highest-risk D renames) runs last with explicit build verification.
