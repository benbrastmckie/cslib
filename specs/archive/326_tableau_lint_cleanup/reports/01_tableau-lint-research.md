# Task 326: Tableau Lint Cleanup -- Research Report

## Executive Summary

The original task description assumed all four files would build and only have linter warnings. Investigation reveals a significantly more complex situation: **two of the four files have build errors**, not just lint warnings. Tasks 324 (LawfulBEq refactoring) and 325 (tableau dedup/dead code cleanup) appear to have changed upstream APIs (e.g., `SignedFormula.sign`/`SignedFormula.formula` field accessors, List lemma names) in ways that broke proofs in Completeness.lean and parts of Intuitionistic/Soundness.lean.

## Current State by File

### File 1: Classical/Soundness.lean -- BUILDS, 22 unique warnings

**Status**: Builds successfully. All warnings are mechanical lint fixes.

| # | Line(s) | Category | Description | Fix |
|---|---------|----------|-------------|-----|
| 1-12 | 72, 75, 78, 82, 86, 96, 100, 103, 106, 110, 114, 124 | unusedSectionVars + unusedDecidableInType | 12 private `classicalApplyOne_*` lemmas: unused `[DecidableEq Atom] [Hashable Atom]` | Add `omit [DecidableEq Atom] [Hashable Atom] in` before each lemma (or a single block wrapping lines 72-126) |
| 13 | 137 | unusedSectionVars | `classicalRule_preserves_sat`: unused `[Hashable Atom]` | `omit [Hashable Atom] in` |
| 14 | 130 | unusedDecidableInType | `classicalRule_preserves_sat`: unused `[DecidableEq Atom]` in type | Same `omit` handles both |
| 15 | 401 | unusedSectionVars | `classically_closed_unsatisfiable`: unused `[Hashable Atom]` | `omit [Hashable Atom] in` |
| 16-19 | 176, 179, 303, 305 | style.show | `show True; trivial` used where `change` is needed | Replace `show True` with `change True` |
| 20 | 431 | unusedSimpArgs | `simp only [SignedFormula.formula]` -- `SignedFormula.formula` unused | Remove `SignedFormula.formula` from the simp list |
| 21 | 437 | flexible | `simp [hfind] at hclosed` -- flexible simp | Replace with `simp only [hfind] at hclosed` (or result from `simp?`) |
| 22 | 608 | deprecated | `push_neg` deprecated | Replace with `push Not` |

**Fix strategy**: All 22 warnings are mechanical. A single `omit [DecidableEq Atom] [Hashable Atom] in` block can wrap the entire private lemma section (lines 72-126). Three individual `omit` annotations handle the remaining section variable warnings.

### File 2: Classical/Completeness.lean -- BUILD ERRORS + 12 warnings

**Status**: Build fails with 50+ errors. Warnings are interleaved with errors.

**Build errors** (root causes):
1. **Unknown constants**: `List.findSome?_of_mem` (line 117), `List.find?_of_mem` (line 147) -- likely renamed in recent Lean/Mathlib
2. **`simp_all [SignedFormula.sign]` failures** (lines 110-111, 160, 254, 326, 343, 366, 387): `simp_all` with `SignedFormula.sign` no longer solves goals -- possibly the sign field accessor was removed or renamed during task 324 (LawfulBEq)
3. **`rw [hsign, hform]` failures** (many lines): The rewrite patterns `sf.sign` and `sf.formula` no longer match after field accessor changes
4. **Type mismatch at line 510**: `hnt rfl` expects `classicalTableau phi = .closed` but gets `?m = ?m` -- the `cases` on `classicalTableau` result changed shape

**Warnings** (will become fixable after errors are resolved):

| # | Line(s) | Category | Description |
|---|---------|----------|-------------|
| 1-8 | 110, 111, 160, 254, 326, 343, 366, 387 | unusedSimpArgs | Unused simp arguments (currently also errors) |
| 9-10 | 404, 415 | unusedSectionVars | `mem_extendMany_of_mem` and `hintikka_inv_mono` |
| 11-12 | 468-479 | unreachableTactic | Dead tactic blocks (sorry upstream makes them unreachable) |

**Assessment**: This file needs **proof repair** first, then lint fixes. The proof repair is NOT a lint task -- it is a separate task requiring understanding the LawfulBEq refactoring impact. The lint warnings that are independent of errors (items 9-12) can be fixed alongside the repairs.

### File 3: Intuitionistic/Soundness.lean -- BUILD ERRORS + 3 warnings

**Status**: Build fails with 8+ errors.

**Build errors**:
1. Line 350: Application type mismatch (likely field accessor change)
2. Line 358 (previously 399 in some error reports): `simp` made no progress
3. Line 372: Application type mismatch
4. Lines 452, 546, 566, 573, 576: Various type mismatches and unsolved goals

**Warnings** (can be fixed independently of errors):

| # | Line(s) | Category | Description | Fix |
|---|---------|----------|-------------|-----|
| 1 | 82 | unusedSectionVars | `intRule_preserves_sat`: unused `[Hashable Atom]` | `omit [Hashable Atom] in` |
| 2 | 67 | unusedDecidableInType | `intRule_preserves_sat`: unused `[DecidableEq Atom]` in type | Same `omit` |
| 3 | 276 | unusedSectionVars | `intClosed_unsatisfiable`: unused `[Hashable Atom]` | `omit [Hashable Atom] in` |

**Assessment**: The `omit` annotations (warnings 1-3) can be added even while the file has build errors, since they are syntactic/declarative and don't interact with proof terms. The build errors require upstream investigation.

### File 4: Minimal/Soundness.lean -- BLOCKED (depends on Intuitionistic/Soundness)

**Status**: Cannot build because Intuitionistic/Soundness has errors.

**Expected warnings** (based on task description and code inspection):
- `minClosed_unsatisfiable` (line 67): likely unused `[Hashable Atom]` -- needs `omit`

**Assessment**: The `omit` annotation can be added syntactically, but verification requires Intuitionistic/Soundness to build first.

## Warning Count Summary

| File | Original Estimate | Actual Warnings | Build Errors | Status |
|------|-------------------|-----------------|--------------|--------|
| Classical/Soundness.lean | ~20 | 22 unique | 0 | Ready for lint fixes |
| Classical/Completeness.lean | ~13 | 12 | 50+ | BLOCKED -- needs proof repair |
| Intuitionistic/Soundness.lean | 4 | 3 | 8+ | Partially fixable (omit only) |
| Minimal/Soundness.lean | 1 | 1 (expected) | Blocked | Partially fixable (omit only) |
| **Total** | **~38** | **38** | **58+** | |

## Recommended Approach

### Phase 1: Fix Classical/Soundness.lean (all 22 warnings) -- READY

This file builds cleanly and all warnings are mechanical. Estimated: ~15 edits.

1. Wrap lines 72-126 in `omit [DecidableEq Atom] [Hashable Atom] in` block
2. Add `omit [Hashable Atom] in` before `classicalRule_preserves_sat` (line 130)
3. Add `omit [Hashable Atom] in` before `classically_closed_unsatisfiable` (line 401)
4. Replace 4x `show True` with `change True` (lines 176, 179, 303, 305)
5. Remove `SignedFormula.formula` from simp at line 431
6. Replace `simp [hfind] at hclosed` with `simp only [hfind] at hclosed` at line 437
7. Replace `push_neg` with `push Not` at line 608

### Phase 2: Fix omit annotations in Intuitionistic/Soundness.lean (3 warnings) -- READY

The `omit` annotations are syntactic and can be added regardless of build errors.

1. Add `omit [Hashable Atom] in` before `intRule_preserves_sat` (line 82)
2. Add `omit [Hashable Atom] in` before `intClosed_unsatisfiable` (line 276)

### Phase 3: Fix omit annotation in Minimal/Soundness.lean (1 warning) -- READY

1. Add `omit [Hashable Atom] in` before `minClosed_unsatisfiable` (line 67)

### Phase 4: Classical/Completeness.lean -- BLOCKED

The 12 lint warnings in this file are interleaved with 50+ build errors caused by upstream API changes from tasks 324/325. Fixing lint warnings alone will not make this file build.

**Recommendation**: Create a separate task for Completeness.lean proof repair. The lint warnings can be fixed as part of that repair. Fixing only the 2 `omit` annotations (lines 404, 415) and the 3 dead tactic blocks (lines 468-479) is possible without fixing the build errors, but the unused simp arguments (8 warnings) are entangled with the broken proofs.

### Summary of What This Task Can Accomplish

- **26 warnings fixed** across 3 files (Soundness.lean: 22, Intuitionistic/Soundness.lean: 3, Minimal/Soundness.lean: 1)
- **5 additional warnings** fixable in Completeness.lean (2 omit + 3 dead tactic blocks) without resolving build errors
- **7 remaining warnings** in Completeness.lean are entangled with build errors and require proof repair first

## Blockers

1. **Classical/Completeness.lean** has 50+ build errors from upstream changes. The file's proofs use `simp_all [SignedFormula.sign]`, `rw [hsign, hform]`, and lemma names (`List.findSome?_of_mem`, `List.find?_of_mem`) that no longer work. This is NOT a lint task -- it requires proof repair.

2. **Intuitionistic/Soundness.lean** has 8+ build errors. The `applyAllTImpRules_preserves_sat` and `intExpandBranches_closed_unsat` proofs have type mismatches and simp failures.

3. **Minimal/Soundness.lean** is blocked by Intuitionistic/Soundness.lean errors.

## Recommendation

Scope this task to Phases 1-3 (26 warnings across 3 files + 5 independent warnings in Completeness.lean = 31 total). Create a new task for the Completeness.lean and Intuitionistic/Soundness.lean proof repair, which will naturally resolve the remaining 7 entangled warnings.
