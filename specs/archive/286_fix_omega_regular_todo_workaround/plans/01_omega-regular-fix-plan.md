# Implementation Plan: Fix backward.isDefEq.respectTransparency Workaround

- **Task**: 286 - Fix backward.isDefEq.respectTransparency workaround in OmegaRegularLanguage.lean
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_omega-regular-workaround.md
- **Artifacts**: plans/01_omega-regular-fix-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Remove the `set_option backward.isDefEq.respectTransparency false` workaround and its TODO comment from `Cslib/Computability/Languages/OmegaRegularLanguage.lean`. The fix restructures the proof of `IsRegular.eq_fin_iSup_hmul_omegaPow` to use `eq.symm` instead of `eq.invFun` and replaces `simpa [mem_def]` with an explicit `simp only [Equiv.apply_symm_apply]` followed by `exact h_mem`. This avoids the `isDefEq` transparency issue in `simpa`'s finishing `assumption` step. The fix has been verified to compile in research.

### Research Integration

Research report (`reports/01_omega-regular-workaround.md`) identified:
- Root cause: `simpa`'s finishing `assumption` step uses `isDefEq` at reducible transparency, which cannot unfold `Equiv` structure components to see `eq (eq.invFun x) = x`
- Verified fix: Change `eq.invFun` to `eq.symm`, replace `simpa [mem_def]` with `simp only [Equiv.apply_symm_apply]` + `exact h_mem`
- The fix separates simplification from assumption matching, eliminating the transparency issue entirely
- No new imports needed; `Equiv.apply_symm_apply` is already available

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md alignment -- this task fixes a proof workaround in the Computability module, which is outside the current roadmap scope (BimodalLogic porting).

## Goals & Non-Goals

**Goals**:
- Remove the `set_option backward.isDefEq.respectTransparency false` workaround (lines 193-194)
- Remove the associated TODO comment
- Fix the proof to work correctly with the default `respectTransparency = true` setting
- Pass all CSLib CI checks

**Non-Goals**:
- Refactoring other parts of the theorem or surrounding code
- Investigating other `set_option` workarounds elsewhere in the codebase
- Changing the proof strategy beyond what is necessary to remove the workaround

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fix does not compile on current HEAD | M | L | Research verified fix compiles; re-verify with `lake build` after edit |
| Upstream Mathlib changes break `Equiv.apply_symm_apply` | L | L | Lemma is stable Mathlib API; check with `lean_hover_info` before editing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Apply Proof Fix [COMPLETED]

**Goal**: Edit the proof to remove the `set_option` workaround and fix the proof body.

**Tasks**:
- [ ] Delete lines 193-194 (TODO comment and `set_option backward.isDefEq.respectTransparency false in`)
- [ ] Change `use eq.invFun ((s, h_s), (t, h_t))` to `use eq.symm ((s, h_s), (t, h_t))` (currently line 216)
- [ ] Replace the comment and `simpa [mem_def]` (currently lines 217-218) with `simp only [Equiv.apply_symm_apply]` followed by `exact h_mem`

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - Remove set_option workaround, fix proof body (3 change sites, net -1 line)

**Verification**:
- File contains no `set_option backward.isDefEq.respectTransparency` or associated TODO comment
- Proof uses `eq.symm` instead of `eq.invFun`
- Proof ends with `simp only [Equiv.apply_symm_apply]` and `exact h_mem`

---

### Phase 2: CI Verification [COMPLETED]

**Goal**: Verify the fix passes all CSLib CI checks.

**Tasks**:
- [ ] Run `lake build Cslib.Computability.Languages.OmegaRegularLanguage` (scoped build)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake test`

**Timing**: 15 minutes (build time)

**Depends on**: 1

**Files to modify**: None (verification only)

**Verification**:
- All four CI commands exit with code 0
- No new warnings or errors introduced

## Testing & Validation

- [ ] `lake build Cslib.Computability.Languages.OmegaRegularLanguage` succeeds
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `grep -c 'respectTransparency' Cslib/Computability/Languages/OmegaRegularLanguage.lean` returns 0

## Artifacts & Outputs

- `plans/01_omega-regular-fix-plan.md` (this file)
- `summaries/01_omega-regular-fix-summary.md` (post-implementation)
- Modified: `Cslib/Computability/Languages/OmegaRegularLanguage.lean`

## Rollback/Contingency

Revert with `git checkout -- Cslib/Computability/Languages/OmegaRegularLanguage.lean` to restore the original `set_option` workaround. The workaround is functional and does not cause correctness issues, only a code quality concern.
