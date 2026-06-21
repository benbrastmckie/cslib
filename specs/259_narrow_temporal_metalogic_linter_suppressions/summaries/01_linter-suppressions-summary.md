# Implementation Summary: Narrow Temporal/Metalogic Linter Suppressions

- **Task**: 259
- **Status**: Implemented
- **Duration**: ~1 session
- **Session ID**: sess_1781994910_0cdf2d_259

## What Was Done

Narrowed 13 file-wide `set_option linter.*` suppressions across 4 files in
`Cslib/Logics/Temporal/Metalogic/` to declaration-level scope. Zero file-wide
suppressions remain except 2 structurally required `emptyLine` suppressions
(one per file using `@[expose] public section`), each documented with a comment.

## Phase Results

### Phase 1: TemporalContent.lean [COMPLETED]

- Fixed 6 long lines by breaking after `:=` or `:` in `have` type annotations
  (lines 113, 127, 146 in `f_content_iff_not_neg_in_g_content`; lines 184, 194, 222
  in `p_content_iff_not_neg_in_h_content`)
- Removed `set_option linter.style.longLine false` (eliminated -- underlying issue fixed)
- Kept `set_option linter.style.emptyLine false` with documenting comment:
  `-- Structural: blank lines between declarations inside @[expose] public section`

Net change: 1 file-wide suppression removed, 1 retained with documentation.

### Phase 2: DenseCompleteness.lean [COMPLETED]

- Removed `set_option linter.dupNamespace false` (was cargo-culted, no declarations needed it)
- Removed `set_option linter.unusedSectionVars false` by moving
  `neg_consistent_of_not_derivable_dense` before `variable [Denumerable (Formula Atom)]`
  (the theorem does not use `Denumerable`; only `dense_indicator_in_all_limit_points` and
  `chronicleDenselyOrderedDense` require it)
- Added `set_option linter.unusedSimpArgs false in` and `set_option maxHeartbeats 3200000 in`
  with explanatory comment before `dense_indicator_in_all_limit_points`
- Added `set_option linter.unusedSimpArgs false in` before `neg_consistent_of_not_derivable_dense`
- Removed file-wide `linter.unusedSimpArgs false`, `maxHeartbeats 3200000`,
  `linter.style.setOption false`, `linter.dupNamespace false`, `linter.unusedSectionVars false`

Net change: All 4 file-wide suppressions eliminated.

### Phase 3: CompletenessHelpers.lean [COMPLETED]

- Added `set_option linter.unusedSimpArgs false in` before 4 declarations:
  `deriveDne`, `deriveHNec`, `deriveAndTopIntro`, `mcs_dne`
- Added `set_option linter.flexible false in` before 2 declarations:
  `deriveHNec`, `mcs_dne`
- Added `set_option maxHeartbeats 3200000 in` with explanatory comments before 8 declarations:
  `deriveDne`, `deriveHNec`, `deriveAndTopIntro`, `mcs_dne`,
  `mcs_ff_imp_f`, `mcs_pp_imp_p`, `mcs_g_trans`, `mcs_h_trans`
- Removed file-wide `linter.unusedSimpArgs false`, `linter.flexible false`,
  `maxHeartbeats 3200000`, `linter.style.setOption false`

Net change: All 3 file-wide suppressions (+ meta `setOption`) eliminated.

### Phase 4: GeneralizedNecessitation.lean [COMPLETED]

- Added `set_option linter.unusedSimpArgs false in` and `set_option maxHeartbeats 400000 in`
  with explanatory comments before 2 declarations: `pastNecessitation`, `pastKDist`
- Added `set_option linter.flexible false in` and `set_option maxHeartbeats 400000 in`
  with explanatory comment before `reverseDeduction`
- Removed file-wide `linter.unusedSimpArgs false`, `linter.flexible false`,
  `linter.style.setOption false`, `maxHeartbeats 400000`
- Kept `set_option linter.style.emptyLine false` with documenting comment:
  `-- Structural: blank lines between declarations inside @[expose] public section`

Net change: 4 file-wide suppressions removed, 1 retained with documentation.

## CI Verification

| Check | Result |
|-------|--------|
| `lake build Cslib.Logics.Temporal.Metalogic.TemporalContent` | PASS |
| `lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness` | PASS |
| `lake build Cslib.Logics.Temporal.Metalogic.CompletenessHelpers` | PASS |
| `lake build Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation` | PASS |
| `lake build` (full) | PASS |
| `lake exe checkInitImports` | PASS |
| `lake lint` (modified files) | PASS (no warnings) |
| `lake exe lint-style` (modified files) | PASS (no warnings) |
| `lake test` | Pre-existing failure (`CslibTests.Bisimulation` not a module); no regression |
| Sorry count in modified files | 0 |
| New axioms introduced | 0 |

## Plan Deviations

- **DenseCompleteness.lean maxHeartbeats**: The research report mentioned scoping `maxHeartbeats`
  to declarations that need it. After scoping to `dense_indicator_in_all_limit_points`
  (which has a complex three-branch proof), all other theorems in DenseCompleteness compile
  within default heartbeats. Only one declaration needed the scoped `maxHeartbeats`.

- **CompletenessHelpers.lean maxHeartbeats target list**: The plan listed "~8 heavy declarations."
  All 8 listed declarations received scoped `maxHeartbeats 3200000`. Build verified they all
  compile cleanly with the scoped values.

- **GeneralizedNecessitation.lean maxHeartbeats**: The original file used `maxHeartbeats 400000`
  (not 3200000). Kept 400000 as the scoped value for each declaration.

- **`set_option ... in` placement**: Lean 4 requires `set_option ... in` to come BEFORE the
  doc comment, not after it. In one early attempt the doc comment preceded the `set_option`
  which caused a syntax error; corrected in all places.

## Artifacts

- `specs/259_narrow_temporal_metalogic_linter_suppressions/plans/01_linter-suppressions.md`
- `specs/259_narrow_temporal_metalogic_linter_suppressions/summaries/01_linter-suppressions-summary.md` (this file)
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` (modified)
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` (modified)
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean` (modified)
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` (modified)
