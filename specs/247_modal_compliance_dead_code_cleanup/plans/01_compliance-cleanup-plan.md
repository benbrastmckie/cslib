# Implementation Plan: Task #247 -- Modal/ Compliance and Dead Code Cleanup

- **Task**: 247 - Modal/ compliance and dead code cleanup
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/247_modal_compliance_dead_code_cleanup/reports/02_verified-audit.md
- **Artifacts**: plans/01_compliance-cleanup-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This task performs a systematic cleanup of Modal/ compliance issues and dead code identified by the verified audit report. The work covers 7 categories: 17 missing docstrings, 1 `@[simp]` inconsistency, 1 typo, 11 blank-line normalizations, 26 dead declarations, 1 unused parameter, and 2 redundant imports. All items have confirmed line numbers and are safe to address without breaking any downstream consumers. The final phase updates PR description line-number links and pushes to GitHub PR #662.

### Research Integration

The verified audit at `reports/02_verified-audit.md` confirmed all 26 dead declarations have 0 external references (except `k_soundness_derivable` which is used by `ConservativeExtension.lean` and must be kept). The original audit count of 13 `_soundness_derivable` wrappers was corrected to 14, bringing total dead declarations from 25 to 26. All line numbers were verified against commit `9532b603`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task performs cleanup within `Logics/Modal/` which aligns with the completed "Modal metalogic: DeductionTheorem, MCS, Soundness, Completeness" roadmap item. It is a housekeeping task that does not advance any remaining roadmap item directly but improves code quality of completed Modal infrastructure.

## Goals & Non-Goals

**Goals**:
- Remove all 26 confirmed dead declarations across 6 categories
- Add 17 missing docstrings to comply with CSLib lint requirements
- Remove `@[simp]` from `k_strong_completeness_iff` for cross-system consistency
- Fix "satifies" typo in Basic.lean
- Remove unused `_h_T` parameter from `canonical_eucl`
- Remove 2 redundant imports in K/Completeness.lean and T/Completeness.lean
- Normalize blank lines in 11 Completeness files
- Update PR description line numbers and push to GitHub PR #662
- Pass all CI checks: `lake build`, `lake exe lint-style`, `lake exe checkInitImports`

**Non-Goals**:
- Refactoring any proof bodies or changing proof strategies
- Adding new theorems or lemmas
- Addressing issues outside the Modal/ directory
- Changing the public API surface (all removed items are confirmed dead)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing a declaration that has an undiscovered consumer | H | L | Research confirmed 0 external references for all 26 items; run `lake build` after each phase |
| Parameter removal changes type signature, breaking downstream | M | L | `_h_T` is confirmed unused and already prefixed with `_`; `lake build` will catch any issues |
| Line numbers shift between phases, making later edits harder | M | M | Process files bottom-up within each file (highest line numbers first); PR description update is the final phase |
| Docstring content is rejected by lint | L | L | Follow existing docstring patterns in the codebase |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

All phases are sequential because each phase shifts line numbers that subsequent phases may reference, and Phase 5 (PR description) needs final line numbers, and Phase 6 (CI) needs all code changes complete.

---

### Phase 1: Docstrings, @[simp] removal, typo fix [COMPLETED]

**Goal**: Address all 17 missing docstrings, remove the `@[simp]` attribute from `k_strong_completeness_iff`, and fix the "satifies" typo.

**Tasks**:
- [ ] Add docstring to `instance : Bot (Proposition Atom)` at `Basic.lean:106`
- [ ] Add docstring to `instance : HasInferenceSystem (Judgement World Atom)` at `Basic.lean:187`
- [ ] Add docstring to `theorem derivation_def` at `Basic.lean:192`
- [ ] Add docstring to `theorem TheoryEq.ext_iff` at `Basic.lean:234`
- [ ] Fix "satifies" -> "satisfies" in docstring at `Basic.lean:226`
- [ ] Add docstring to `theorem k_subset_d` at `Cube.lean:99`
- [ ] Add docstring to `theorem k_subset_b` at `Cube.lean:102`
- [ ] Add docstring to `theorem k_subset_four` at `Cube.lean:105`
- [ ] Add docstring to `theorem k_subset_five` at `Cube.lean:108`
- [ ] Add docstring to `theorem d_subset_t` at `Cube.lean:112`
- [ ] Add docstring to `theorem k_subset_t` at `Cube.lean:115`
- [ ] Add docstring to `theorem height_modus_ponens_left` at `DerivationTree.lean:139`
- [ ] Add docstring to `theorem height_modus_ponens_right` at `DerivationTree.lean:144`
- [ ] Add docstring to `theorem height_weakening` at `DerivationTree.lean:149`
- [ ] Add docstring to `theorem mp_deriv` at `DerivationTree.lean:172`
- [ ] Add docstring to `theorem weakening_deriv` at `DerivationTree.lean:178`
- [ ] Add docstring to `theorem assumption_deriv` at `DerivationTree.lean:184`
- [ ] Remove `@[simp]` from `k_strong_completeness_iff` at `K/Completeness.lean:332`

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- 4 docstrings + 1 typo fix
- `Cslib/Logics/Modal/Cube.lean` -- 6 docstrings
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` -- 6 docstrings
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` -- remove `@[simp]`

**Verification**:
- `lake build` succeeds
- `lake exe lint-style` shows no new warnings for these files
- grep confirms no remaining "satifies" typo

---

### Phase 2: Dead Code Removal [COMPLETED]

**Goal**: Remove all 26 confirmed dead declarations across 5 categories.

**Tasks**:
- [ ] Remove 4 S5 backward-compatibility aliases from `Metalogic/DerivationTree.lean` (lines 206-215: `S5DerivationTree`, `S5Deriv`, `S5Derivable`, `s5DerivationSystem`)
- [ ] Remove 2 unused `ModalSetDerivable` lemmas from `Metalogic/Completeness.lean` (lines 440-455: `ModalSetDerivable_of_mem`, `ModalSetDerivable_weakening`). Keep `ModalSetDerivable_of_Derivable` (line 457) which is used internally.
- [ ] Remove 2 dead T wrappers from `Systems/T/Completeness.lean` (lines 52-63: `t_canonical_refl`, lines 65-end: `t_truth_lemma`)
- [ ] Remove 3 dead TB wrappers from `Systems/TB/Completeness.lean` (lines 55-64: `tb_canonical_refl`, lines 66-79: `tb_canonical_symm`, lines 81-end: `tb_truth_lemma`)
- [ ] Remove dead `HasHilbertTree` instance from `Metalogic/DeductionTheorem.lean` (lines 47-53)
- [ ] Remove 14 dead `_soundness_derivable` wrappers (keep K's which is used):
  - `B/Soundness.lean:78` -- `b_soundness_derivable`
  - `D/Soundness.lean:79` -- `d_soundness_derivable`
  - `D4/Soundness.lean:90` -- `d4_soundness_derivable`
  - `D5/Soundness.lean:91` -- `d5_soundness_derivable`
  - `D45/Soundness.lean:99` -- `d45_soundness_derivable`
  - `DB/Soundness.lean:90` -- `db_soundness_derivable`
  - `K4/Soundness.lean:89` -- `k4_soundness_derivable`
  - `K5/Soundness.lean:80` -- `k5_soundness_derivable`
  - `K45/Soundness.lean:100` -- `k45_soundness_derivable`
  - `KB5/Soundness.lean:100` -- `kb5_soundness_derivable`
  - `S4/Soundness.lean:97` -- `s4_soundness_derivable`
  - `S5/Soundness.lean:93` -- `s5_soundness_derivable`
  - `T/Soundness.lean:82` -- `t_soundness_derivable`
  - `TB/Soundness.lean:98` -- `tb_soundness_derivable`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` -- remove 4 S5 aliases
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- remove 2 ModalSetDerivable lemmas
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` -- remove 1 HasHilbertTree instance
- `Cslib/Logics/Modal/Metalogic/Systems/T/Completeness.lean` -- remove 2 dead wrappers
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Completeness.lean` -- remove 3 dead wrappers
- `Cslib/Logics/Modal/Metalogic/Systems/B/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/D/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/K5/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/S4/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/T/Soundness.lean` -- remove 1 dead wrapper
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Soundness.lean` -- remove 1 dead wrapper

**Verification**:
- `lake build` succeeds (confirms no hidden consumers)
- grep for each removed declaration name returns no results

---

### Phase 3: Parameter and Import Cleanup [COMPLETED]

**Goal**: Remove the unused `_h_T` parameter from `canonical_eucl` and remove 2 redundant imports.

**Tasks**:
- [ ] Remove unused `_h_T` parameter from `canonical_eucl` at `Metalogic/Completeness.lean:148`. Update callers if any pass this argument explicitly.
- [ ] Remove redundant `public import Cslib.Logics.Modal.Metalogic.MCS` from `K/Completeness.lean:10`
- [ ] Remove redundant `public import Cslib.Logics.Modal.Metalogic.Soundness` from `K/Completeness.lean:11`
- [ ] Remove redundant `public import Cslib.Logics.Modal.Metalogic.MCS` from `T/Completeness.lean:10`
- [ ] Remove redundant `public import Cslib.Logics.Modal.Metalogic.Soundness` from `T/Completeness.lean:11`

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- remove `_h_T` param from `canonical_eucl`
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` -- remove 2 redundant imports
- `Cslib/Logics/Modal/Metalogic/Systems/T/Completeness.lean` -- remove 2 redundant imports

**Verification**:
- `lake build` succeeds (confirms transitive imports still provide needed symbols)
- `lake shake --add-public --keep-implied --keep-prefix` passes

---

### Phase 4: Blank Line Normalization [COMPLETED]

**Goal**: Remove the extra blank line (line 9) in 11 Completeness files to match the pattern used by D, K, TB, and T.

**Tasks**:
- [ ] Remove blank line 9 in `Systems/B/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/D4/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/D5/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/D45/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/DB/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/K4/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/K5/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/K45/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/KB5/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/S4/Completeness.lean`
- [ ] Remove blank line 9 in `Systems/S5/Completeness.lean`

**Timing**: 15 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/B/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/K5/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/S4/Completeness.lean` -- remove blank line 9
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Completeness.lean` -- remove blank line 9

**Verification**:
- `lake build` succeeds
- All 15 Completeness files have consistent formatting (line 9 is `public import` in all)

---

### Phase 5: PR Description Update [COMPLETED]

**Goal**: Update all line-number links in `pr-description.md` to reflect the new line numbers after Phases 1-4, then push the updated description to GitHub PR #662.

**Tasks**:
- [ ] For each of the 45 GitHub line-number links in `pr-description.md`, determine the new line number by reading the modified file
- [ ] Update `pr-description.md` with corrected line numbers, keeping full GitHub URLs (e.g., `https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/...#L{N}`)
- [ ] Update the PR #662 body on GitHub using `gh pr edit 662 --repo leanprover/cslib --body-file ...`

**Timing**: 30 minutes

**Depends on**: 4

**Files to modify**:
- `specs/247_modal_compliance_dead_code_cleanup/pr-description.md` -- update all 45 line-number links

**Verification**:
- All 45 links point to correct line numbers in modified files
- `gh pr view 662 --repo leanprover/cslib` shows updated description

---

### Phase 6: CI Verification [COMPLETED]

**Goal**: Run the full CSLib CI verification pipeline to confirm all changes are correct.

**Tasks**:
- [ ] Run `lake build` -- full project build
- [ ] Run `lake exe checkInitImports` -- verify Cslib.Init imports
- [ ] Run `lake exe lint-style` -- style linting (should show 0 warnings for Modal/ files)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` -- dependency analysis
- [ ] Verify no `sorry` introduced (should be none since this is cleanup only)

**Timing**: 30 minutes (mostly build time)

**Depends on**: 5

**Files to modify**: None (verification only)

**Verification**:
- All 4 CI commands pass with exit code 0
- No new warnings or errors introduced

## Testing & Validation

- [ ] `lake build` passes after every phase
- [ ] `lake exe lint-style` shows no new warnings for modified Modal/ files
- [ ] `lake exe checkInitImports` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes
- [ ] grep for all 26 removed declaration names returns empty results
- [ ] grep for "satifies" in Basic.lean returns empty
- [ ] All 15 Completeness files have consistent blank-line formatting
- [ ] PR #662 body on GitHub matches updated `pr-description.md`

## Artifacts & Outputs

- `specs/247_modal_compliance_dead_code_cleanup/plans/01_compliance-cleanup-plan.md` (this file)
- `specs/247_modal_compliance_dead_code_cleanup/pr-description.md` (updated with new line numbers)
- Modified Modal/ source files (~30 files across Metalogic/, Systems/, Basic.lean, Cube.lean)

## Rollback/Contingency

All changes are deletions or additions of docstrings with no behavioral impact. If any phase breaks the build:
1. `git stash` or `git checkout -- <file>` the offending changes
2. Investigate which removed declaration has a hidden consumer
3. Restore the declaration and update the audit report

For the PR description update, the previous version can be restored from git history.
