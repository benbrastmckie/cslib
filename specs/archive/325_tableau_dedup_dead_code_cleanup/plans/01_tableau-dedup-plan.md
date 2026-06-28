# Implementation Plan: Tableau Deduplication and Dead Code Cleanup

- **Task**: 325 - Deduplicate identical definitions across minimal/intuitionistic tableau modules and remove dead code from the MinimalClosure bug fix
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: 324 (LawfulBEq refactoring, completed)
- **Research Inputs**: specs/325_tableau_dedup_dead_code_cleanup/reports/01_tableau-dedup-research.md
- **Artifacts**: plans/01_tableau-dedup-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Remove six items of duplicated and dead Lean code across five files in the propositional tableau module hierarchy. Phase 1 handles deduplication: deleting `minBranchSatisfied` (unused) from Minimal/Soundness.lean and replacing `minExtractValuation` with `intExtractValuation` in Minimal/Completeness.lean (requires adding an import). Phase 2 handles dead code removal: deleting the `MinimalClosure` instance, `IsAtomic` typeclass, `instIsAtomicProposition`, and `atomContradiction` constructor -- all forming a dead-code chain with zero external references. A `lake build` verification confirms no breakage.

### Research Integration

Research report (01_tableau-dedup-research.md) confirmed all six items are safe to remove:
- `minBranchSatisfied` has zero code references outside its definition.
- `minExtractValuation` is referenced only in sorry-bodied type signatures (`minTruthLemma`, `minOpenBranch_countermodel`); replacing with `intExtractValuation` requires adding `import Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness`.
- `MinimalClosure`, `IsAtomic`, `instIsAtomicProposition`, and `atomContradiction` form a closed dead-code chain with no external consumers.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances code quality and maintainability within the Propositional Tableau module layer. It reduces definitional duplication between the Minimal and Intuitionistic sub-modules, clarifying the dependency relationship where Minimal builds on Intuitionistic infrastructure.

## Goals & Non-Goals

**Goals**:
- Delete `minBranchSatisfied` (completely unused duplicate of `intBranchSatisfied`)
- Replace `minExtractValuation` with `intExtractValuation` across Minimal/Completeness.lean
- Remove the dead `MinimalClosure` instance and its entire dependency chain (`IsAtomic`, `instIsAtomicProposition`, `atomContradiction`)
- Update module docstrings to reflect the removals
- Verify the build passes after all changes

**Non-Goals**:
- Renaming `extractValuation` (classical) or `intExtractValuation` (intuitionistic) -- different types justify different names
- Refactoring any proof bodies or changing proof strategies
- Modifying any files outside the five identified in the research report

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing `atomContradiction` constructor breaks exhaustive pattern matches | H | L | Research found zero exhaustive matches on `ClosureReason`; `lake build` will catch any missed ones |
| Adding `Intuitionistic.Completeness` import to Minimal/Completeness.lean creates a cycle | M | L | Import chain analysis confirms no cycle: Minimal.Completeness -> Intuitionistic.Completeness -> Intuitionistic.Soundness (already in existing chain) |
| Line numbers shifted from task 324 changes | L | M | Verified all line numbers against current file contents; research report numbers are accurate |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Deduplication [COMPLETED]

**Goal**: Remove duplicate definitions from Minimal tableau modules and update references.

**Tasks**:
- [ ] Delete `minBranchSatisfied` definition (lines 71-78) from `Minimal/Soundness.lean`
- [ ] Update the module docstring in `Minimal/Soundness.lean` to remove references to `minBranchSatisfied` (lines 19, 38, 69-70)
- [ ] Add `public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` to `Minimal/Completeness.lean`
- [ ] Delete `minExtractValuation` definition (lines 72-73) from `Minimal/Completeness.lean`
- [ ] Replace all references to `minExtractValuation` with `intExtractValuation` in `Minimal/Completeness.lean` (lines 168-171 in `minTruthLemma`, line 182 in `minOpenBranch_countermodel`)
- [ ] Update the module docstring in `Minimal/Completeness.lean` to remove `minExtractValuation` from the main results list (line 19)
- [ ] Run `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness` to verify

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - Delete `minBranchSatisfied` def + update docstrings
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - Add import, delete `minExtractValuation`, replace references, update docstrings

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness` passes (covers both files via import chain)
- `grep -r "minBranchSatisfied" Cslib/` returns zero code references
- `grep -r "minExtractValuation" Cslib/` returns zero code references

---

### Phase 2: Dead Code Removal [COMPLETED]

**Goal**: Remove the dead `MinimalClosure` instance and its entire dependency chain.

**Tasks**:
- [ ] Delete the `MinimalClosure` namespace (lines 116-135) from `ClosureCondition.lean`, including the section header
- [ ] Delete the `IsAtomic` typeclass (lines 70-78) from `ClosureCondition.lean`, including the section header
- [ ] Update the module docstring in `ClosureCondition.lean` to remove `MinimalClosure` from the instance table (line 24) and the `IsAtomic` design paragraph (lines 32-33)
- [ ] Delete `instIsAtomicProposition` and its section header (lines 106-117) from `Defs.lean`
- [ ] Update the module docstring in `Defs.lean` to remove `instIsAtomicProposition` from the main definitions list (lines 24-25)
- [ ] Delete the `atomContradiction` constructor (line 60) from `ClosureReason` in `Closure.lean`
- [ ] Update the module docstring and doc comment in `Closure.lean` to remove `atomContradiction` references (lines 22, 30, 52-53)
- [ ] Run `lake build` to verify full project builds cleanly

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean` - Delete `MinimalClosure` namespace + `IsAtomic` class + update docstrings
- `Cslib/Logics/Propositional/Tableau/Defs.lean` - Delete `instIsAtomicProposition` + section + update docstrings
- `Cslib/Foundations/Logic/Tableau/Closure.lean` - Delete `atomContradiction` constructor + update docstrings

**Verification**:
- `lake build` passes with zero errors
- `lake exe checkInitImports` passes
- `grep -r "MinimalClosure\|IsAtomic\|isAtom\|atomContradiction\|instIsAtomicProposition" Cslib/` returns zero code references (doc comments are acceptable)

## Testing & Validation

- [ ] `lake build` passes with zero errors after all changes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `grep -r "minBranchSatisfied" Cslib/` returns zero code references
- [ ] `grep -r "minExtractValuation" Cslib/` returns zero code references
- [ ] `grep -r "MinimalClosure" Cslib/` returns zero code references (outside comments in other files)
- [ ] `grep -r "IsAtomic\b" Cslib/` returns zero code references
- [ ] `grep -r "atomContradiction" Cslib/` returns zero code references

## Artifacts & Outputs

- `specs/325_tableau_dedup_dead_code_cleanup/plans/01_tableau-dedup-plan.md` (this file)
- `specs/325_tableau_dedup_dead_code_cleanup/summaries/01_tableau-dedup-summary.md` (post-implementation)
- Modified files:
  - `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`
  - `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
  - `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean`
  - `Cslib/Foundations/Logic/Tableau/Closure.lean`
  - `Cslib/Logics/Propositional/Tableau/Defs.lean`

## Rollback/Contingency

All changes are deletions and simple substitutions. If `lake build` fails after any phase:
1. Use `git diff` to identify the problematic change.
2. Revert the specific edit that caused the failure.
3. Investigate whether the research report missed a reference.

For a full rollback: `git checkout -- Cslib/` restores all five files to their pre-edit state.
