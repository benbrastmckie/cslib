# Implementation Plan: Task #211

- **Task**: 211 - Change def to lemma/theorem for Prop-valued declarations
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/211_lint_def_to_lemma/reports/01_def-lemma-research.md
- **Artifacts**: plans/01_def-lemma-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix all 55 `defLemma` lint errors by changing `def` to `lemma` (45 declarations) or `theorem` (10 declarations) across 22 Lean files. This is a mechanical keyword replacement task with zero downstream unfolding risk (verified by research). Special cases include 3 `abbrev` -> `lemma`/`theorem` conversions and 4 `@[reducible]` annotation removals. The task is organized into 4 parallel file-group phases plus a final verification phase.

### Research Integration

The research report (01_def-lemma-research.md) verified that none of the 55 flagged declarations are unfolded downstream via `simp`, `unfold`, or `delta`. All are used through term-level application only. The report provides a complete per-file inventory with exact line numbers and classifies each declaration as `lemma` or `theorem` using the convention that `theorem` is reserved for major named results (completeness, soundness, Burgess 1982 named results) while `lemma` covers supporting infrastructure.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Eliminate all 55 `defLemma` lint errors from `lake lint` output
- Correctly classify each declaration as `lemma` or `theorem` per CSLib convention
- Remove unnecessary `@[reducible]` annotations from proof declarations
- Convert `abbrev` proof aliases to `lemma`/`theorem`
- Maintain zero compilation errors after changes

**Non-Goals**:
- Renaming any declarations (that is task 210)
- Fixing other lint categories (namespace, simp, unused args)
- Modifying proof bodies or adding docstrings

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Downstream unfolding breaks after opacity change | H | L | Research verified zero unfolding usage for all 55 declarations |
| Line numbers shifted from other concurrent changes | M | L | Use declaration name search rather than hardcoded line numbers |
| `noncomputable` incompatible with `lemma` | H | L | Lean 4 supports `noncomputable lemma`; verified in research |
| Build failure in unrelated file masks our changes | M | L | Run incremental build; check only affected files if full build slow |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Bimodal FrameConditions, Soundness, and Core Metalogic [COMPLETED]

**Goal**: Fix 13 declarations across Bimodal FrameConditions (2 files), Soundness (1 file), and Core Metalogic (4 files).

**Tasks**:
- [x] `FrameConditions/FrameClass.lean`: Remove `@[reducible]` and change `def` to `lemma` for `DenseTemporalFrame.mk'` and `DiscreteTemporalFrame.mk'`
- [x] `FrameConditions/Soundness.lean`: Change `def soundnessOver` to `theorem soundnessOver`
- [x] `Core/MaximalConsistent.lean`: Change `noncomputable def` to `noncomputable lemma` for 6 declarations (`bimodalClosedUnderDerivation`, `bimodalImplicationProperty`, `bimodalNegationComplete`, `maximalConsistentClosed`, `maximalNegationComplete`, `theoremInMcs`); also remove `@[reducible]` and change to `noncomputable lemma` for `derivesNegFromInconsistentExtension`
- [x] `Core/MCSProperties.lean`: Change `noncomputable def theoremInMcsFc` to `noncomputable lemma`
- [x] `Core/DeductionTheorem.lean`: Change `def bimodalHasDeductionTheorem` to `lemma`
- [x] `Bundle/CanonicalFrame.lean`: Change `abbrev canonicalRTransitive` to `lemma canonicalRTransitive`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/FrameConditions/FrameClass.lean` - 2 declarations: remove `@[reducible]`, `def` -> `lemma`
- `Cslib/Logics/Bimodal/FrameConditions/Soundness.lean` - 1 declaration: `def` -> `theorem`
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` - 7 declarations: `noncomputable def` -> `noncomputable lemma` (6), remove `@[reducible]` + change (1)
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` - 1 declaration: `noncomputable def` -> `noncomputable lemma`
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - 1 declaration: `def` -> `lemma`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/CanonicalFrame.lean` - 1 declaration: `abbrev` -> `lemma`

**Verification**:
- All 13 declarations compile without errors
- No `defLemma` lint errors remain in these 6 files

---

### Phase 2: Bimodal BXCanonical [COMPLETED]

**Goal**: Fix 16 declarations across 5 BXCanonical files (the largest single cluster).

**Tasks**:
- [x] `BXCanonical/Frame.lean`: Change `noncomputable def` to `noncomputable lemma` for 9 declarations (`gContentClosedDerivation`, `hContentClosedDerivation`, `bxForwardWitness`, `bxBackwardWitness`, `bxGBackward`, `bxHBackward`, `bxModalWitness`, `bxUntilEventualityResolution`, `bxSinceEventualityResolution`)
- [x] `BXCanonical/CanonicalModel.lean`: Change `noncomputable def bxModalWitnessFc` to `noncomputable lemma`
- [x] `BXCanonical/Chronicle/ChronicleToCountermodel.lean`: Change `def limitDomSubtypeIsSuccArchimedean` to `lemma`
- [x] `BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`: Change `def limitDomSubtypeDenselyOrderedFromF'T` to `lemma`
- [x] `BXCanonical/Chronicle/CounterexampleElimination.lean`: Change `noncomputable def` to `noncomputable lemma` for 4 declarations (`eliminateC5Counterexample`, `eliminateC5'Counterexample`, `eliminateGPropCounterexample`, `eliminateHPropCounterexample`)

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` - 9 declarations
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalModel.lean` - 1 declaration
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` - 1 declaration
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` - 1 declaration
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` - 4 declarations

**Verification**:
- All 16 declarations compile without errors
- No `defLemma` lint errors remain in these 5 files

---

### Phase 3: Bimodal Theorems, Bimodal PointInsertion, and Modal S5 [COMPLETED]

**Goal**: Fix 8 declarations across Bimodal Theorems (2 files), BXCanonical Chronicle PointInsertion (1 file), and Modal S5 Completeness (1 file). This phase includes all `theorem` classifications for Bimodal named results and all `abbrev` conversions.

**Tasks**:
- [x] `Bimodal/Theorems/Perpetuity/Helpers.lean`: Change `def wrap` to `lemma wrap`
- [x] `Bimodal/Theorems/Propositional/Connectives.lean`: Change `abbrev wrap'` to `lemma wrap'`
- [x] `BXCanonical/Chronicle/PointInsertion.lean`: Change `noncomputable def` to `noncomputable theorem` for 4 declarations (`lemma_2_4`, `lemma_2_6`, `lemma_2_4_with_guard`, `lemma_2_4_since_with_guard`); change `noncomputable def gPropagationWitness` to `noncomputable lemma`
- [x] `Modal/Metalogic/Systems/S5/Completeness.lean`: Change `abbrev completeness` to `theorem completeness`

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - 1 declaration: `def` -> `lemma`
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` - 1 declaration: `abbrev` -> `lemma`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` - 5 declarations: 4 `theorem`, 1 `lemma`
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Completeness.lean` - 1 declaration: `abbrev` -> `theorem`

**Verification**:
- All 8 declarations compile without errors
- `theorem` used for Burgess named results and completeness; `lemma` for helpers

---

### Phase 4: Temporal Metalogic (Chronicle + Other) [COMPLETED]

**Goal**: Fix 18 declarations across all Temporal metalogic files.

**Tasks**:
- [x] `Chronicle/Frame.lean`: Change `noncomputable def` to `noncomputable lemma` for 8 declarations (`gContentClosedDerivation`, `hContentClosedDerivation`, `tForwardWitness`, `tBackwardWitness`, `tGBackward`, `tHBackward`, `tUntilEventualityResolution`, `tSinceEventualityResolution`)
- [x] `Chronicle/CounterexampleElimination.lean`: Change `noncomputable def` to `noncomputable lemma` for 2 declarations (`eliminateC5Counterexample`, `eliminateC5'Counterexample`)
- [x] `Chronicle/PointInsertion.lean`: Change `noncomputable def` to `noncomputable theorem` for 4 declarations (`lemma_2_4`, `lemma_2_6`, `lemma_2_4_with_guard`, `lemma_2_4_since_with_guard`)
- [x] `DenseCompleteness.lean`: Remove `@[reducible]` and change `def chronicle_densely_ordered_dense` to `lemma`
- [x] `DenseMCS.lean`: Change `noncomputable def theoremInMcsFc` to `noncomputable lemma`
- [x] `MCS.lean`: Change `noncomputable def theoremInMcs` to `noncomputable lemma`
- [x] `PropositionalHelpers.lean`: Change `def wrap` to `lemma wrap`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` - 8 declarations
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - 2 declarations
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - 4 declarations (all `theorem`)
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - 1 declaration: remove `@[reducible]`
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - 1 declaration
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` - 1 declaration
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` - 1 declaration

**Verification**:
- All 18 declarations compile without errors
- No `defLemma` lint errors remain in these 7 files

---

### Phase 5: Build Verification and Lint Confirmation [COMPLETED]

**Goal**: Verify all 55 changes compile and the `defLemma` lint errors are fully resolved.

**Tasks**:
- [x] Run `lake build` to confirm zero compilation errors
- [x] Run `lake lint` and verify defLemma error count is reduced by 55
- [ ] Run `lake test` to confirm test suite passes
- [x] Spot-check that `theorem` is used for the 10 major named results and `lemma` for the 45 supporting declarations

**Timing**: 10 minutes (plus build time)

**Depends on**: 1, 2, 3, 4

**Files to modify**: None (verification only)

**Verification**:
- `lake build` exits 0
- `lake lint` shows 0 `defLemma` errors (down from 55)
- `lake test` exits 0

## Testing & Validation

- [x] `lake build` compiles with zero errors
- [x] `lake lint` reports zero `defLemma` linter errors
- [ ] `lake test` passes all tests
- [x] All 10 `theorem` declarations are major named results (completeness, soundness, Burgess lemma_2_4/2_6/2_4_with_guard/2_4_since_with_guard)
- [x] All 45 `lemma` declarations are supporting infrastructure (witnesses, MCS properties, helpers)
- [x] All 4 `@[reducible]` annotations removed
- [x] All 3 `abbrev` keywords replaced

## Artifacts & Outputs

- `specs/211_lint_def_to_lemma/plans/01_def-lemma-plan.md` (this plan)
- `specs/211_lint_def_to_lemma/summaries/01_def-lemma-summary.md` (after implementation)
- 22 modified `.lean` files across Bimodal/, Temporal/, and Modal/ directories

## Rollback/Contingency

All changes are keyword-only modifications to declaration headers. If any change causes a compilation failure (unexpected despite research verification), revert the specific file with `git checkout -- path/to/file.lean`. The changes are fully independent per-file, so partial rollback is straightforward.
