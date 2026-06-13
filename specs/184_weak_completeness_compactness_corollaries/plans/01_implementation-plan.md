# Implementation Plan: Weak Completeness and Compactness as Corollaries

- **Task**: 184 - Derive weak completeness and compactness as clean corollaries of strong completeness
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: 183 (strong completeness infrastructure)
- **Research Inputs**: specs/184_weak_completeness_compactness_corollaries/reports/01_corollary-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Refactor weak completeness theorems (`prop_completeness`, `int_completeness`, `min_completeness`) and their biconditional wrappers from standalone proofs into 3-line corollaries that delegate to the corresponding strong completeness results via `SetDerivable_empty_iff`. The corollary versions must live in the strong completeness files (import direction constraint). Three downstream files that reference `prop_completeness` need import updates. All compactness corollaries already exist in the strong completeness files; no compactness work is needed.

### Research Integration

Key findings from the research report:
1. All three compactness corollaries already exist -- no new compactness proofs needed.
2. `SetDerivable_empty_iff` provides the bridge: `SetDerivable Axioms empty phi <-> Derivable Axioms phi`.
3. Import direction constraint: strong completeness files import weak completeness files, so corollaries must live in the strong completeness files.
4. Three downstream files use `prop_completeness` and need import updates from `Completeness` to `StrongCompleteness`.
5. `int_completeness` and `min_completeness` have no downstream users, making their refactoring risk-free.
6. Net reduction: ~126 lines of standalone proofs replaced by ~18 lines of corollaries.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly reference this task. This is a code-quality refactoring within the propositional logic completeness module.

## Goals & Non-Goals

**Goals**:
- Add weak completeness corollaries (`prop_completeness`, `int_completeness`, `min_completeness`) and their biconditionals to the strong completeness files
- Remove the standalone weak completeness proofs and biconditionals from the weak completeness files
- Update downstream imports so `prop_completeness` resolves from the new location
- Pass the full CSLib CI pipeline (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`)

**Non-Goals**:
- Adding new compactness proofs (they already exist)
- Adding bridging lemmas like `Tautology_iff_SemanticEntails_empty` (optional enhancement, not in scope)
- Renaming any existing infrastructure (canonical models, truth lemmas stay in weak completeness files)
- Modifying `SemanticConsequence.lean`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe-polymorphic signature mismatch for `int_completeness` / `min_completeness` | M | L | Research report provides exact signatures with `IValid.{u,u}` / `MValid.{u,u}` annotations; verify with `lean_goal` |
| Downstream files may have additional implicit imports from `Completeness` beyond `prop_completeness` | M | L | Run `lake build` after import changes to catch any unresolved references |
| `lake shake` flags unused imports in weak completeness files after theorem removal | L | M | Run `lake shake` and fix any flagged unused imports |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Add Corollaries and Remove Old Proofs [NOT STARTED]

**Goal**: Add weak completeness corollaries to the three strong completeness files and remove the standalone proofs from the three weak completeness files.

**Tasks**:
- [ ] Add `prop_completeness` and `completeness_iff_tautology` as corollaries after `prop_compactness` in `StrongCompleteness.lean`
- [ ] Add `int_completeness` and `int_soundness_completeness` as corollaries after `int_compactness` in `IntStrongCompleteness.lean`
- [ ] Add `min_completeness` and `min_soundness_completeness` as corollaries after `min_compactness` in `MinStrongCompleteness.lean`
- [ ] Remove `prop_completeness` and `completeness_iff_tautology` from `Completeness.lean` (lines ~316-407)
- [ ] Remove `int_completeness` and `int_soundness_completeness` from `IntCompleteness.lean` (lines ~185-208)
- [ ] Remove `min_completeness` and `min_soundness_completeness` from `MinCompleteness.lean` (lines ~199-224)
- [ ] Clean up any now-unused imports in the weak completeness files
- [ ] Verify each corollary type-checks with `lean_goal` or `lean_diagnostic_messages`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Classical/Metalogic/StrongCompleteness.lean` - Add `prop_completeness` and `completeness_iff_tautology` corollaries
- `Cslib/Logics/Propositional/Intuitionistic/Metalogic/IntStrongCompleteness.lean` - Add `int_completeness` and `int_soundness_completeness` corollaries
- `Cslib/Logics/Propositional/Minimal/Metalogic/MinStrongCompleteness.lean` - Add `min_completeness` and `min_soundness_completeness` corollaries
- `Cslib/Logics/Propositional/Classical/Metalogic/Completeness.lean` - Remove standalone `prop_completeness` and `completeness_iff_tautology`
- `Cslib/Logics/Propositional/Intuitionistic/Metalogic/IntCompleteness.lean` - Remove standalone `int_completeness` and `int_soundness_completeness`
- `Cslib/Logics/Propositional/Minimal/Metalogic/MinCompleteness.lean` - Remove standalone `min_completeness` and `min_soundness_completeness`

**Verification**:
- Each strong completeness file compiles without errors
- Each weak completeness file compiles without errors after removal
- `lake build` succeeds (may surface downstream breakage, addressed in Phase 2)

---

### Phase 2: Update Downstream Imports and CI Verification [NOT STARTED]

**Goal**: Fix the three downstream files that reference `prop_completeness` so they import from `StrongCompleteness` instead of `Completeness`, then run the full CI pipeline.

**Tasks**:
- [ ] Update import in `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean`: change `Completeness` import to `StrongCompleteness`
- [ ] Update import in `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`: change `Completeness` import to `StrongCompleteness`
- [ ] Update import in `Cslib/Logics/Temporal/ConservativeExtension.lean`: change `Completeness` import to `StrongCompleteness`
- [ ] Run `lake build` to verify all files compile
- [ ] Run `lake test` to verify tests pass
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for dependency analysis

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean` - Update import from `Completeness` to `StrongCompleteness`
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` - Update import from `Completeness` to `StrongCompleteness`
- `Cslib/Logics/Temporal/ConservativeExtension.lean` - Update import from `Completeness` to `StrongCompleteness`

**Verification**:
- `lake build` exits 0
- `lake test` exits 0
- `lake exe checkInitImports` exits 0
- `lake exe lint-style` exits 0
- `lake shake` reports no issues

## Testing & Validation

- [ ] All six modified Lean files compile individually without errors
- [ ] `lake build` succeeds with zero errors
- [ ] `lake test` passes all tests
- [ ] `lake exe checkInitImports` reports no missing imports
- [ ] `lake exe lint-style` reports no style violations
- [ ] Theorem signatures preserved: `prop_completeness`, `int_completeness`, `min_completeness` callable with identical arguments from the new locations

## Artifacts & Outputs

- `specs/184_weak_completeness_compactness_corollaries/plans/01_implementation-plan.md` (this file)
- `specs/184_weak_completeness_compactness_corollaries/summaries/01_execution-summary.md` (after implementation)

## Rollback/Contingency

All changes are to existing files with no new files created. Revert via `git checkout main -- <file>` for any of the 9 modified files. The original standalone proofs are fully recoverable from git history.
