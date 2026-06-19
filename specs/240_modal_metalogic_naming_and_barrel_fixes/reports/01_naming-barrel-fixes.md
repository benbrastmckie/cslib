# Research Report: Modal/Metalogic Naming and Barrel File Fixes

**Task**: 240
**Session**: sess_1750300800_multi_240
**Date**: 2026-06-18

## Executive Summary

All six items in the task description are confirmed as genuine issues. Items (1), (2), (3), (5) are low-risk mechanical changes with no downstream breakage. Item (4) is moderate-risk due to 10+ downstream code references across 10 files. Item (6) is safe to remove -- the alias has no downstream consumers.

---

## Item (1): Missing ConservativeExtension Import in Barrel File

**Status**: Confirmed.

The file `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean` exists and contains `theorem modal_conservative_extension` (K is a conservative extension of CPL). The barrel file `Cslib/Logics/Modal/Metalogic.lean` has no import for this file.

**Fix**: Add `public import Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension` to the barrel file. Placement should be after the K.StrongCompleteness import (or in the K block within the Soundness/Completeness section).

**Risk**: None. Adding a missing import cannot break existing consumers.

---

## Item (2): Barrel Import Ordering Normalization

**Status**: Confirmed. The two blocks use different orderings.

### Current Ordering

**Soundness/Completeness block** (lines 14-43):
S5, K, T, D, S4, K4, B, K45, K5, D4, KB5, TB, D45, D5, DB

**StrongCompleteness block** (lines 45-59):
K, T, D, S4, K4, B, K45, K5, D4, KB5, TB, D45, D5, DB, S5

### Target Ordering (per task description)

Both blocks should use: K, T, D, S4, K4, B, K45, K5, D4, KB5, TB, D45, D5, DB, S5

This means moving the S5.Soundness and S5.Completeness imports from the beginning to the end of the Soundness/Completeness block. The StrongCompleteness block already matches the target order.

**Risk**: None. Import ordering does not affect semantics (these are all `public import` in a `module` file).

---

## Item (3): S5/Soundness.lean `axiom_sound` Naming

**Status**: Confirmed. S5 is the only system using bare `axiom_sound` instead of the `{system}_axiom_sound` prefix convention.

### Naming Convention Across All 15 Systems

| System | Current Name | Expected Name |
|--------|-------------|---------------|
| K | `k_axiom_sound` | (correct) |
| T | `t_axiom_sound` | (correct) |
| D | `d_axiom_sound` | (correct) |
| S4 | `s4_axiom_sound` | (correct) |
| K4 | `k4_axiom_sound` | (correct) |
| B | `b_axiom_sound` | (correct) |
| K45 | `k45_axiom_sound` | (correct) |
| K5 | `k5_axiom_sound` | (correct) |
| D4 | `d4_axiom_sound` | (correct) |
| KB5 | `kb5_axiom_sound` | (correct) |
| TB | `tb_axiom_sound` | (correct) |
| D45 | `d45_axiom_sound` | (correct) |
| D5 | `d5_axiom_sound` | (correct) |
| DB | `db_axiom_sound` | (correct) |
| **S5** | **`axiom_sound`** | **`s5_axiom_sound`** |

### Downstream Consumer Search

`axiom_sound` (bare, not prefixed) is used **only within** `S5/Soundness.lean` itself (4 occurrences: definition on line 42, internal usage on lines 89, 101, and docstring on line 19). No external files reference it.

Note: The bare name `axiom_sound` also exists in `Cslib/Logics/Temporal/Metalogic/Soundness.lean` (temporal logic, completely separate namespace). These are in different namespaces (`Cslib.Logic.Modal` vs `Cslib.Logic.Temporal`) so there is no conflict.

The generic `Metalogic/Soundness.lean` docstring (lines 20, 24, 29) references `axiom_sound` in documentation comments but does not import or use it in code.

**Files to edit**:
1. `Cslib/Logics/Modal/Metalogic/Systems/S5/Soundness.lean` -- rename definition + 3 internal references + docstring
2. `Cslib/Logics/Modal/Metalogic/Soundness.lean` -- update docstring references (lines 20, 24, 29)

**Risk**: Low. Only 1 file contains code references, all internal.

---

## Item (4): D/Completeness.lean Naming Convention (Suffix to Prefix)

**Status**: Confirmed. D/Completeness.lean uses mixed suffix/no-prefix convention while all other systems use prefix convention.

### Proposed Renames

| Current Name | New Name |
|-------------|----------|
| `derive_box_from_inconsistency_d` | `d_derive_box_from_inconsistency` |
| `mcs_box_witness_d` | `d_mcs_box_witness` |
| `canonical_serial` | `d_canonical_serial` |
| `truth_lemma_d` | `d_truth_lemma` |

### Downstream Consumer Analysis

#### `truth_lemma_d` (HIGHEST IMPACT -- 10 code references across 5 files + 5 doc references)

**Code references** (exact `truth_lemma_d` calls):
- `D/StrongCompleteness.lean` lines 99, 109
- `D4/StrongCompleteness.lean` lines 111, 121
- `D5/StrongCompleteness.lean` lines 108, 118
- `D45/StrongCompleteness.lean` lines 118, 131
- `DB/StrongCompleteness.lean` lines 111, 121

**Doc/comment references**:
- `Completeness.lean` (generic) line 312-313
- `D4/Completeness.lean` line 19
- `D5/Completeness.lean` line 19
- `D45/Completeness.lean` line 20
- `DB/Completeness.lean` line 19
- `D/StrongCompleteness.lean` lines 34, 67, 70
- `D4/StrongCompleteness.lean` lines 34, 70
- `D5/StrongCompleteness.lean` lines 34, 70
- `D45/StrongCompleteness.lean` lines 34, 71
- `DB/StrongCompleteness.lean` lines 34, 70

#### `canonical_serial` (5 code references across 5 files + 5 doc references)

**Code references**:
- `D/StrongCompleteness.lean` line 91
- `D4/StrongCompleteness.lean` line 95
- `D5/StrongCompleteness.lean` line 95
- `D45/StrongCompleteness.lean` line 97
- `DB/StrongCompleteness.lean` line 95

**Doc/comment references**:
- `D4/Completeness.lean` line 20
- `D5/Completeness.lean` line 20
- `D45/Completeness.lean` line 21
- `DB/Completeness.lean` line 20

#### `mcs_box_witness_d` (1 doc reference, no code consumers outside D/Completeness.lean)

Only referenced in `Completeness.lean` (generic) line 313 in a doc comment.

#### `derive_box_from_inconsistency_d` (0 external references)

Only used internally within `D/Completeness.lean` itself (called by `mcs_box_witness_d`).

### Total Files Requiring Changes

**Code changes** (11 files):
1. `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` (definitions)
2. `Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean`
3. `Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean`
4. `Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean`
5. `Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean`
6. `Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean`

**Doc-only changes** (5 additional files):
7. `Cslib/Logics/Modal/Metalogic/Completeness.lean`
8. `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean`
9. `Cslib/Logics/Modal/Metalogic/Systems/D5/Completeness.lean`
10. `Cslib/Logics/Modal/Metalogic/Systems/D45/Completeness.lean`
11. `Cslib/Logics/Modal/Metalogic/Systems/DB/Completeness.lean`

**Risk**: Moderate. This is the highest-impact item. All changes are mechanical find-and-replace, but affect 11 files. Use `replace_all` for safety. Must run `lake build` after to verify no breakage.

---

## Item (5): K/Completeness.lean Comment Wording

**Status**: Confirmed.

Line 111 of `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean`:
```
  · -- Case: neg phi NOT in L -- K-SPECIFIC FIX (BRV Lemma 4.20)
```

The fix-it scanner (`/fix-it`) scans for `FIX:` (with colon), so `K-SPECIFIC FIX` without a colon would not trigger it. However, renaming to `K-SPECIFIC CASE` is still reasonable for clarity -- this is not a "fix" but a standard proof case.

**Fix**: Change `K-SPECIFIC FIX` to `K-SPECIFIC CASE` on line 111.

**Risk**: None. This is a comment-only change.

---

## Item (6): S5 Completeness Alias Evaluation

**Status**: Confirmed. The alias has no downstream consumers and should be removed.

### Current State

In `Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean` (lines 207-208):
```lean
/-- Backward-compatible alias for `s5_completeness`. -/
alias completeness := s5_completeness
```

### Downstream Consumer Search

No file in the entire CSLib codebase uses the bare `completeness` name from the `Cslib.Logic.Modal` namespace in code. All grep hits for `\bcompleteness\b` are either:
- In comments/documentation (not code references)
- In different namespaces (e.g., `Cslib.Logic.Temporal`, `Cslib.Logic.Bimodal`)
- Mathlib references (completely unrelated)

### Recommendation

**Remove the alias entirely** (both the docstring and the alias line). Since no downstream consumer uses the bare `completeness` name, there is no need for backward compatibility or a deprecation docstring.

**Risk**: None. No consumers exist.

---

## Implementation Approach Recommendation

### Phase 1: Safe Mechanical Changes (items 1, 2, 5, 6)
- Add ConservativeExtension import to barrel file
- Reorder barrel file imports
- Fix K/Completeness comment
- Remove S5 completeness alias
- These can all be done in a single phase with no risk

### Phase 2: S5 Rename (item 3)
- Rename `axiom_sound` to `s5_axiom_sound` in S5/Soundness.lean
- Update docstrings in Soundness.lean (generic)
- Low risk, 2 files

### Phase 3: D Renames (item 4)
- Rename all 4 theorems in D/Completeness.lean
- Update 10 code references across 5 StrongCompleteness files
- Update doc references across 5 Completeness files + 1 generic file
- Run `lake build` to verify

### Verification
- `lake build Cslib.Logics.Modal.Metalogic` after all phases
- `lake exe checkInitImports` (sanity check)

---

## Tactic Survey

Not applicable -- this task involves naming/organizational changes only, no proof modifications.
