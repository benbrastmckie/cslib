# Implementation Plan: Fix --wfail CI Warnings

- **Task**: 206 - Fix --wfail CI warnings across Bimodal, Temporal, and Modal files
- **Status**: [IN PROGRESS]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_ci-warnings-analysis.md
- **Artifacts**: plans/01_ci-warnings-fix-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The CI runs `lake build --wfail --iofail` which treats warnings as fatal errors. The research identified 70 active warnings across 10 files and an estimated 250-350 latent warnings across approximately 50 files in the Bimodal/, Temporal/, and Modal/ subdirectories. All warnings fall into well-defined categories with known mechanical fixes: `push_neg` deprecation (138 occurrences), module docstring ordering (13 files), unscoped `set_option` directives (24+12 files), unused simp arguments (18 occurrences), unused hypotheses (4 occurrences), flexible simp linter violations (18 occurrences), and intro merging (2 occurrences). This plan organizes fixes by warning category since each category has a uniform fix pattern, enabling efficient batch processing.

### Research Integration

Key findings from `reports/01_ci-warnings-analysis.md`:
- CI uses incremental builds with caching, so only 10 of 2980 modules were freshly compiled -- a clean build would reveal the full warning set
- `push_neg` -> `push Not` is a zero-risk mechanical rename (same underlying implementation)
- Module docstring reordering is purely structural and cannot break proofs
- Unused simp arg removal is linter-confirmed safe but requires compilation verification
- Files with `open Classical` and `show` tactic warnings need NOT be fixed (those linters are disabled by default)
- `sorry` warnings are intentional placeholders and must NOT be touched

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is a CI hygiene task that enables clean `--wfail` builds across the entire Bimodal/, Temporal/, and Modal/ codebase. While not directly advancing a specific roadmap item, it unblocks future development by ensuring new code in these modules does not regress on warnings. Clean CI is a prerequisite for all remaining roadmap items (discrete completeness, continuous extension completeness, dense temporal completeness, etc.).

## Goals & Non-Goals

**Goals**:
- Eliminate all `push_neg` deprecation warnings (138 occurrences across 22 files)
- Fix all module docstring ordering warnings (13 files)
- Scope all unscoped `set_option` directives (`linter.flexible false`, `maxHeartbeats`) to pass the setOption linter
- Remove unused simp arguments flagged by the linter (18 occurrences across 3 files)
- Remove unused hypothesis type-class parameters (4 occurrences across 3 files)
- Fix flexible simp linter violations in currently-flagged files
- Merge intro calls where flagged (2 occurrences)
- Achieve a clean `lake build --wfail --iofail` pass (or dramatically reduce warning count)

**Non-Goals**:
- Fixing `sorry` declarations (blocked on upstream tasks 36, 37)
- Enabling `linter.style.openClassical` or `linter.style.show` (disabled by default)
- Converting all flexible simp calls to `simp only` (too large an effort, suppression is acceptable)
- Restructuring proofs or changing proof strategies

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Unused simp arg removal breaks a proof | M | L | Linter confirms arg is unused; verify with `lake build` after each batch |
| Removing DecidablePred/DecidableEq breaks downstream callers | M | L | Files use `open Classical`, so classical decidability fills the gap; verify with full build |
| maxHeartbeats scoping with `in` fails for multi-declaration sequences | L | L | Each `set_option maxHeartbeats` is placed before its target declaration; verify with build |
| Clean build reveals additional warning categories not in research | M | M | Run clean build in Phase 6 and address new categories incrementally |
| push Not syntax differs from push_neg for some argument forms | L | L | Both are the same tactic implementation; global replace is safe |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1 |
| 3 | 5 | 4 |
| 4 | 6 | 5 |

Phases 1, 2, and 3 can execute in parallel. Phases 4-6 are sequential due to build verification dependencies.

---

### Phase 1: push_neg Deprecation Fix [COMPLETED]

**Goal**: Replace all 138 `push_neg` calls with `push Not` across 22 files.

**Tasks**:
- [ ] Run global search-and-replace: `push_neg` -> `push Not` in all files under `Cslib/Logics/Bimodal/`, `Cslib/Logics/Temporal/`, and `Cslib/Logics/Modal/`
- [ ] Verify the replacement preserves `at h`, `at *`, and bare `push_neg` variants (all become `push Not`, `push Not at h`, `push Not at *`)
- [ ] Spot-check 3-5 files to confirm syntax is correct

**Fix Pattern**:
```
-- BEFORE:
push_neg
push_neg at h
push_neg at *

-- AFTER:
push Not
push Not at h
push Not at *
```

**Files to modify** (22 files):
- `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean` - 6 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean` - 2 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` - 8 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` - 14 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` - 12 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` - 4 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCompletion.lean` - 2 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean` - 2 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` - 6 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean` - 4 occurrences
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` - 16 occurrences
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` - 10 occurrences
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` - 4 occurrences
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` - 6 occurrences
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` - 10 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` - 6 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean` - 2 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Soundness/FrameClassVariants.lean` - 4 occurrences
- `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean` - 2 occurrences
- `Cslib/Logics/Modal/Denotation.lean` - 1 occurrence
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` - 12 occurrences
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - 4 occurrences

**Timing**: 0.5 hours

**Depends on**: none

**Verification**:
- `grep -rn "push_neg" Cslib/Logics/Bimodal/ Cslib/Logics/Temporal/ Cslib/Logics/Modal/` returns zero results
- No new syntax errors introduced (verified in Phase 5)

---

### Phase 2: Module Docstring Ordering + Intro Merging [COMPLETED]

**Goal**: Fix module docstring placement in 13 files (move `set_option` after `/-!` block) and merge intro calls in 1 file.

**Tasks**:
- [ ] In each of the 13 files, swap the `set_option` block and the `/-!` docstring block so that the module docstring appears before any `set_option` directives
- [ ] In `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean`, merge the two flagged separate `intro` calls into combined forms (lines ~113, ~155)

**Fix Pattern (docstring ordering)**:
```
-- BEFORE:
import Cslib...

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-! # Module Title
Module docstring here.
-/

-- AFTER:
import Cslib...

/-! # Module Title
Module docstring here.
-/

set_option linter.style.longLine false
set_option linter.style.emptyLine false
```

**Fix Pattern (intro merging)**:
```
-- BEFORE:
intro h1
intro h2

-- AFTER:
intro h1 h2
```

**Files to modify** (13 files for docstring + 1 for intro):
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/NormalForm.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean` - docstring + intro merging
- `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean` - docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` - docstring

**Timing**: 1 hour

**Depends on**: none

**Verification**:
- Each modified file has `/-!` appearing before any `set_option` line (excluding imports)
- No structural changes to proofs

---

### Phase 3: Unscoped set_option Fixes (linter.flexible + maxHeartbeats) [COMPLETED]

**Goal**: Scope all unscoped `set_option` directives to pass the setOption linter. This covers `linter.flexible false` (24 files) and `maxHeartbeats` (16 occurrences in 12 files).

**Tasks**:
- [ ] For the 24 files with unscoped `set_option linter.flexible false`: add `set_option linter.style.setOption false` alongside the existing directive (pragmatic suppression matching Temporal/ convention)
- [ ] For files with few declarations (< 10 using `linter.flexible false`): consider converting to `set_option linter.flexible false in` per declaration instead of global suppression
- [ ] For all 16 unscoped `set_option maxHeartbeats N` occurrences: add `in` suffix to scope to the next declaration

**Fix Pattern (linter.flexible -- pragmatic suppression)**:
```
-- BEFORE:
set_option linter.flexible false

-- AFTER:
set_option linter.style.setOption false
set_option linter.flexible false
```

**Fix Pattern (maxHeartbeats scoping)**:
```
-- BEFORE:
set_option maxHeartbeats 3200000

-- AFTER:
set_option maxHeartbeats 3200000 in
```

**Files to modify (linter.flexible -- 24 files)**:

*Bimodal/ (16 files)*:
- `Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean`
- `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
- `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean`
- `Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean`
- `Metalogic/BXCanonical/Chronicle/PointInsertion.lean`
- `Metalogic/BXCanonical/Completeness/Dense.lean`
- `Metalogic/Completeness.lean`
- `Metalogic/Core/DeductionTheorem.lean`
- `Metalogic/Core/MaximalConsistent.lean`
- `Metalogic/Core/MCSProperties.lean`
- `Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean`
- `Metalogic/Separation/Hierarchy/HierarchyCompletion.lean`
- `Metalogic/Separation/Hierarchy/HierarchyDefs.lean`
- `Metalogic/Separation/Hierarchy/HierarchyInduction.lean`
- `Metalogic/Separation/SeparationThm.lean`
- `Metalogic/Separation/TemporalClosure.lean`

*Temporal/ (8 files)*:
- `Metalogic/Chronicle/ChronicleConstruction.lean`
- `Metalogic/Chronicle/ChronicleToCountermodel.lean`
- `Metalogic/Chronicle/CounterexampleElimination.lean`
- `Metalogic/Chronicle/PointInsertion.lean`
- `Metalogic/Chronicle/TruthLemma.lean`
- `Metalogic/DeductionTheorem.lean`
- `Metalogic/DenseMCS.lean`
- `Metalogic/MCS.lean`

**Files to modify (maxHeartbeats -- 12 files, 16 occurrences)**:
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean` - line 29
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` - line 31
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` - line 46
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` - line 32
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` - line 32
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` - line 31
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - line 42
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` - line 24
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - line 34
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - line 29
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` - line 38
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` - line 26
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` - line 36
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` - line 26
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` - line 39
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - line 41

**Timing**: 1.5 hours

**Depends on**: none

**Verification**:
- `grep -rn "^set_option linter.flexible false$" Cslib/Logics/` returns zero results (all should have `in` suffix or be paired with `linter.style.setOption false`)
- `grep -rn "^set_option maxHeartbeats" Cslib/Logics/ | grep -v " in$"` returns zero results (all should end with `in`)

---

### Phase 4: Unused Simp Args, Unused Hypotheses, and Flexible Simp Suppression [COMPLETED]

**Goal**: Remove unused simp arguments (18 occurrences), remove unused type-class hypotheses (4 occurrences), and suppress flexible simp warnings in the 2 currently-flagged files.

**Tasks**:
- [ ] Remove unused simp arguments in `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` (10 occurrences at lines 354-386: `Formula.neg`, `Formula.and`, `Formula.or`)
- [ ] Remove unused simp arguments in `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean` (6 occurrences: 4 at line 281 for `Formula.allFuture`, `Formula.neg`, `Formula.someFuture`, `Formula.top`; 1 at line 364 for `junctionDepthU`; 1 at line 394 for `junctionDepthS`)
- [ ] Remove unused simp arguments in `Cslib/Logics/Modal/Denotation.lean` (2 occurrences: line 59 `Proposition.neg`, line 67 `Proposition.denotation`)
- [ ] Remove `[DecidablePred pred]` from `Int.exists_least_above` (line 53) and `Int.exists_greatest_below` (line 80) in `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean`
- [ ] Remove `[DecidableEq Atom]` from `exists_n_fresh_atoms` (line 183) in `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean`
- [ ] Add `omit [DecidableEq Atom] in` before `f_nesting_depth_nonneg` (line 34) in `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean`
- [ ] Add `set_option linter.flexible false` (or pair with `linter.style.setOption false`) to `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` (14 flexible simp warnings)
- [ ] Add `set_option linter.flexible false` (or pair with `linter.style.setOption false`) to `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` (4 flexible simp warnings)

**Fix Pattern (unused simp arg)**:
```
-- BEFORE:
simp [Formula.neg, Formula.and, Formula.or, Formula.swapTemporal]

-- AFTER (remove unused args, keep used ones):
simp [Formula.swapTemporal]
```

**Fix Pattern (unused hypothesis)**:
```
-- BEFORE:
theorem Int.exists_least_above [DecidablePred pred] ...

-- AFTER:
theorem Int.exists_least_above ...
```

**Fix Pattern (auto-included section variable)**:
```
-- BEFORE:
theorem f_nesting_depth_nonneg ...

-- AFTER:
omit [DecidableEq Atom] in
theorem f_nesting_depth_nonneg ...
```

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` - remove unused simp args + flexible simp suppression
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean` - remove unused simp args
- `Cslib/Logics/Modal/Denotation.lean` - remove unused simp args
- `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean` - remove unused hypothesis
- `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` - remove unused hypothesis
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - omit section variable
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` - flexible simp suppression

**Timing**: 1.5 hours

**Depends on**: 1 (push_neg fix must land first since some files overlap)

**Verification**:
- `lake build` compiles without errors for all modified files
- Linter warnings for unused simp args, unused hypotheses, and flexible simp are eliminated in modified files

---

### Phase 5: Build Verification and Incremental Fixes [IN PROGRESS]

**Goal**: Run a full `lake build --wfail --iofail` to catch any remaining warnings not covered by the research analysis, and fix them.

**Tasks**:
- [ ] Run `lake build --wfail --iofail` on the full project
- [ ] Capture and categorize any remaining warnings
- [ ] Apply the same mechanical fix patterns for any newly revealed warnings (expected: additional module docstring issues, additional unscoped options, possible additional push_neg occurrences)
- [ ] Re-run `lake build --wfail --iofail` to confirm warning reduction

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- Any files with newly discovered warnings (cannot predict exact list until clean build)

**Verification**:
- `lake build --wfail --iofail` passes cleanly, or remaining warnings are limited to `sorry` declarations and disabled-by-default linters

---

### Phase 6: Final Verification and Cleanup [NOT STARTED]

**Goal**: Confirm CI-clean state and commit all changes.

**Tasks**:
- [ ] Run `lake build --wfail --iofail` one final time to confirm clean build
- [ ] Run `lake test` to verify no test regressions
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Review git diff to ensure all changes are mechanical (no proof restructuring)

**Timing**: 0.5 hours

**Depends on**: 5

**Files to modify**:
- None expected (verification only)

**Verification**:
- All CI verification commands pass
- `git diff --stat` shows only expected files modified
- No `sorry` declarations added or removed

## Testing & Validation

- [ ] `lake build --wfail --iofail` passes with zero warnings (excluding sorry and disabled linters)
- [ ] `lake test` passes with no regressions
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `grep -rn "push_neg" Cslib/Logics/Bimodal/ Cslib/Logics/Temporal/ Cslib/Logics/Modal/` returns zero results
- [ ] No proof restructuring in any modified file (all changes are mechanical)

## Artifacts & Outputs

- `specs/206_fix_wfail_ci_warnings/plans/01_ci-warnings-fix-plan.md` (this plan)
- `specs/206_fix_wfail_ci_warnings/summaries/01_execution-summary.md` (post-implementation)
- Modified Lean files across Bimodal/, Temporal/, and Modal/ (~50 files total)

## Rollback/Contingency

All changes are mechanical text transformations with no proof restructuring. If any change breaks a proof:
1. Revert the specific file with `git checkout -- <file>`
2. Investigate which specific replacement caused the issue
3. Apply a targeted fix (e.g., keep a simp arg that was incorrectly flagged as unused)

For full rollback: `git stash` or `git reset --soft HEAD~1` to undo the commit while preserving changes for inspection.
