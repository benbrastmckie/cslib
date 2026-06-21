# Implementation Plan: Narrow Temporal/Metalogic Linter Suppressions

- **Task**: 259 - Narrow file-wide linter suppressions in Temporal/Metalogic/ to declaration-level scope
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/259_narrow_temporal_metalogic_linter_suppressions/reports/01_linter-suppressions.md
- **Artifacts**: plans/01_linter-suppressions.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Narrow 13 file-wide `set_option linter.*` suppressions across 4 files in `Cslib/Logics/Temporal/Metalogic/` to declaration-level scope. The research report identified 4 suppressions that can be removed entirely, 3 meta-suppressions (`style.setOption`) that disappear once other options use `set_option ... in` form, 4 that must be narrowed to specific declarations, and 1-2 that may remain file-wide due to the `@[expose] public section` pattern. Work is organized file-by-file to minimize context switching and allow incremental build verification.

### Research Integration

Key findings from the research report (01_linter-suppressions.md):
- **TemporalContent.lean**: `longLine` fixable by breaking 6 lines; `emptyLine` likely removable but needs build verification due to `@[expose] public section`
- **DenseCompleteness.lean**: `dupNamespace` is cargo-culted and removable; `unusedSectionVars` fixable by reordering one theorem; 2 declarations need `unusedSimpArgs` scoping
- **CompletenessHelpers.lean**: 4 declarations need `unusedSimpArgs` scoping, 2 need `flexible` scoping, `maxHeartbeats` must be scoped to ~8 declarations
- **GeneralizedNecessitation.lean**: 2 declarations need `unusedSimpArgs`, 1 needs `flexible`; `emptyLine` is structurally unavoidable due to `@[expose] public section`

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task supports the Temporal module cleanup effort in the broader CSLib porting roadmap. Narrowing linter suppressions improves code quality for the Temporal/Metalogic/ module ahead of potential upstream PR submission.

## Goals & Non-Goals

**Goals**:
- Eliminate all file-wide linter suppressions that can be removed or narrowed
- Fix underlying issues (long lines, unused section variables) where possible rather than just scoping the suppression
- Scope remaining necessary suppressions to individual declarations using `set_option ... in`
- Document any suppressions that must remain file-wide with explanatory comments
- Maintain build correctness throughout (no regressions)

**Non-Goals**:
- Refactoring the `@[expose] public section` pattern across temporal metalogic files
- Optimizing simp lemma sets (use `simp?` to find minimal sets) -- just suppress at declaration level
- Reducing `maxHeartbeats` values -- only scope them to specific declarations
- Changing proof strategies to eliminate `flexible` warnings

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Scoping `maxHeartbeats` misses a heavy declaration | M | M | Build will immediately surface the error; add `set_option maxHeartbeats ... in` to that declaration |
| Moving `neg_consistent_of_not_derivable_dense` above `variable [Denumerable]` causes scope issues | M | L | The theorem does not use `Denumerable`; if problems arise, use `set_option linter.unusedSectionVars false in` instead |
| `emptyLine` removal in TemporalContent.lean triggers warnings | L | M | Keep with documenting comment if removal fails (same pattern as GeneralizedNecessitation.lean) |
| Line-breaking long type annotations changes Lean parsing | L | L | Lean is whitespace-insensitive for type annotations; build verification confirms correctness |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: TemporalContent.lean -- Fix Long Lines and Remove Suppressions [NOT STARTED]

**Goal**: Eliminate both file-wide suppressions in TemporalContent.lean by fixing the underlying issues.

**Tasks**:
- [ ] Fix 6 long lines (all `have` type annotations) by breaking after `:` or `[]`:
  - Lines 113, 127, 146 in `f_content_iff_not_neg_in_g_content`
  - Lines 184, 194, 222 in `p_content_iff_not_neg_in_h_content`
- [ ] Remove `set_option linter.style.longLine false` (line 23)
- [ ] Try removing `set_option linter.style.emptyLine false` (line 22)
- [ ] Build `Cslib.Logics.Temporal.Metalogic.TemporalContent` and verify no warnings
- [ ] If `emptyLine` removal triggers warnings (due to `@[expose] public section`), keep it with a documenting comment: `-- Structural: blank lines between declarations inside @[expose] public section`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` - Break 6 long lines, remove 1-2 suppressions

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.TemporalContent` succeeds with no linter warnings
- No lines exceed 100 characters in the file
- Zero or at most one file-wide suppression remains (emptyLine only, with comment)

---

### Phase 2: DenseCompleteness.lean -- Remove, Fix, and Narrow Suppressions [NOT STARTED]

**Goal**: Eliminate all 4 file-wide suppressions in DenseCompleteness.lean through removal, structural fix, and declaration-level scoping.

**Tasks**:
- [ ] Remove `set_option linter.dupNamespace false` (line 35) -- no declarations need it
- [ ] Fix `unusedSectionVars` by moving `neg_consistent_of_not_derivable_dense` (line 217) above the `variable [Denumerable (Formula Atom)]` declaration (line 69), then remove `set_option linter.unusedSectionVars false` (line 32)
- [ ] Add `set_option linter.unusedSimpArgs false in` before:
  - `dense_indicator_in_all_limit_points` (line 85)
  - `neg_consistent_of_not_derivable_dense` (line 217)
- [ ] Remove `set_option linter.unusedSimpArgs false` (line 33)
- [ ] Scope any file-wide `maxHeartbeats` to declarations that need it using `set_option maxHeartbeats ... in`
- [ ] Remove `set_option linter.style.setOption false` (line 34) -- now unnecessary
- [ ] Build `Cslib.Logics.Temporal.Metalogic.DenseCompleteness` and verify

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - Reorder one theorem, remove 2 suppressions, narrow 1, scope maxHeartbeats

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness` succeeds with no linter warnings
- Zero file-wide suppressions remain
- `neg_consistent_of_not_derivable_dense` appears before `variable [Denumerable ...]` line

---

### Phase 3: CompletenessHelpers.lean -- Narrow All Suppressions to Declaration Scope [NOT STARTED]

**Goal**: Eliminate all 3 file-wide suppressions in CompletenessHelpers.lean by scoping `unusedSimpArgs`, `flexible`, and `maxHeartbeats` to individual declarations.

**Tasks**:
- [ ] Add `set_option linter.unusedSimpArgs false in` before 4 declarations:
  - `deriveDne` (line ~80)
  - `deriveHNec` (line ~98)
  - `deriveAndTopIntro` (line ~113)
  - `mcs_dne` (line ~129)
- [ ] Remove `set_option linter.unusedSimpArgs false` (line 29)
- [ ] Add `set_option linter.flexible false in` before 2 declarations:
  - `deriveHNec` (line ~98)
  - `mcs_dne` (line ~129)
- [ ] Remove `set_option linter.flexible false` (line 30)
- [ ] Scope `maxHeartbeats 3200000` to ~8 heavy declarations using `set_option maxHeartbeats 3200000 in`:
  - `deriveDne`, `deriveHNec`, `deriveAndTopIntro`, `mcs_dne`
  - `mcs_ff_imp_f`, `mcs_pp_imp_p`, `mcs_g_trans`, `mcs_h_trans`
- [ ] Remove file-wide `set_option maxHeartbeats 3200000` (line 31)
- [ ] Remove `set_option linter.style.setOption false` (line 28) -- now unnecessary
- [ ] Build `Cslib.Logics.Temporal.Metalogic.CompletenessHelpers` and verify
- [ ] If any declaration fails without `maxHeartbeats`, add `set_option maxHeartbeats 3200000 in` before it

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean` - Scope 3 suppressions + maxHeartbeats to individual declarations, remove all 3 file-wide suppressions

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.CompletenessHelpers` succeeds with no linter warnings
- Zero file-wide suppressions remain
- Each `set_option ... in` appears immediately before its target declaration

---

### Phase 4: GeneralizedNecessitation.lean -- Narrow and Document Suppressions [NOT STARTED]

**Goal**: Narrow `unusedSimpArgs` and `flexible` to declaration scope, document the structural `emptyLine` suppression, and remove the meta-suppression.

**Tasks**:
- [ ] Add `set_option linter.unusedSimpArgs false in` before 2 declarations:
  - `pastNecessitation` (line ~77)
  - `pastKDist` (line ~112)
- [ ] Remove `set_option linter.unusedSimpArgs false` (line 23)
- [ ] Add `set_option linter.flexible false in` before 1 declaration:
  - `reverseDeduction` (line ~48)
- [ ] Remove `set_option linter.flexible false` (line 25)
- [ ] Scope any file-wide `maxHeartbeats` to declarations that need it
- [ ] Remove `set_option linter.style.setOption false` (line 24) -- now unnecessary
- [ ] Add documenting comment to `set_option linter.style.emptyLine false` (line 26):
  `-- Structural: blank lines between declarations inside @[expose] public section`
- [ ] Build `Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation` and verify
- [ ] Run full `lake build` to verify no downstream breakage

**Timing**: 45 minutes

**Depends on**: 1, 2, 3

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` - Narrow 2 suppressions to declarations, document 1 structural suppression, remove 2 suppressions

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation` succeeds with no linter warnings (except documented emptyLine)
- At most 1 file-wide suppression remains (emptyLine with documenting comment)
- Full `lake build` succeeds with no regressions
- `lake exe lint-style` passes

## Testing & Validation

- [ ] Each file builds successfully after its phase completes
- [ ] Full `lake build` succeeds after all phases
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (no behavioral regressions)
- [ ] Zero file-wide suppressions remain except documented `emptyLine` (1-2 instances maximum)
- [ ] All declaration-scoped `set_option ... in` annotations are immediately before their target declaration
- [ ] No `style.setOption` suppressions remain anywhere (all meta-suppressions eliminated)

## Artifacts & Outputs

- `specs/259_narrow_temporal_metalogic_linter_suppressions/plans/01_linter-suppressions.md` (this plan)
- `specs/259_narrow_temporal_metalogic_linter_suppressions/summaries/01_linter-suppressions-summary.md` (post-implementation)
- Modified files:
  - `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean`
  - `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean`
  - `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean`
  - `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`

## Rollback/Contingency

All changes are purely in `set_option` annotations and line formatting -- no proof logic is modified. If any phase causes build failures that cannot be resolved:
1. Revert the file to its pre-phase state using `git checkout -- <file>`
2. Keep the file-wide suppression for the problematic linter with a documenting comment explaining why narrowing failed
3. Continue with remaining phases on other files

The worst-case outcome is that some suppressions remain file-wide with documentation, which is still an improvement over the current undocumented state.
