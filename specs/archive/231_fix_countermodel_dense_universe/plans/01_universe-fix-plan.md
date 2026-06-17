# Implementation Plan: Task #231

- **Task**: 231 - Fix countermodel_dense universe mismatch in ChronicleToCountermodelBasic
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/231_fix_countermodel_dense_universe/reports/01_universe-mismatch-analysis.md
- **Artifacts**: plans/01_universe-fix-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The `countermodel_dense` and `completeness_dense` theorems were blocked by a universe mismatch: the outer section declares `variable {Atom : Type*}` (universe polymorphic) but `ParametricCanonicalTaskFrame` requires `Atom : Type` (universe 0) because `TaskFrame.WorldState : Type` is pinned to universe 0.

The implemented fix uses section-scoped `variable {Atom : Type}` overrides in the two target files, avoiding changes to any infrastructure files. This is more minimal and safer than generalizing the 5 Parametric files to `Type*`.

### Research Integration

Key findings from the research report:
- Root cause: `ParametricCanonicalTaskFrame` requires `Atom : Type` because `TaskFrame.WorldState : Type` is pinned to universe 0
- The 5 Parametric files use `{Atom : Type}` which is correct for the TaskFrame constraint
- The mismatch occurs at the call sites in ChronicleToCountermodelBasic and Dense, where outer sections use `{Atom : Type*}`
- Solution: section-scoped variable overrides specialize `Atom` to `Type` locally, matching the Parametric infrastructure without modifying it

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation needed for this task.

## Goals & Non-Goals

**Goals**:
- Resolve universe mismatch between `Atom : Type*` and `ParametricCanonicalTaskFrame`'s `Atom : Type` requirement
- Fill `countermodel_dense` sorry (ChronicleToCountermodelBasic.lean)
- Fill `completeness_dense` sorry (Dense.lean)
- Pass build verification

**Non-Goals**:
- Filling any other sorry sites in the codebase
- Generalizing the 5 Parametric files (unnecessary given the section-scoped override approach)
- Modifying `validDense`, `TaskFrame`, or other infrastructure definitions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation | Outcome |
|------|--------|------------|------------|---------|
| Universe elaboration failure in Parametric proofs | H | L | Section-scoped override avoids touching Parametric files entirely | N/A — risk eliminated by approach change |
| countermodel_dense proof body more complex than expected | M | M | Research identified the exact construction | Resolved — proof uses cantorBfmcsDense + 3 restricted coherence + fully_restricted_parametric_completeness_from_neg_membership |
| completeness_dense universe mismatch on validDense's D quantifier | M | L | validDense uses D : Type; countermodel uses D = Rat : Type 0 | Resolved — `obtain` destructures countermodel, `h_valid_dense` instantiates directly |
| Downstream breakage in other files | M | L | No downstream callers exist outside the sorry-blocked theorems | No breakage — build succeeds (1659 jobs) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Fill countermodel_dense Sorry [COMPLETED]

**Goal**: Add section-scoped `variable {Atom : Type}` override and implement the proof body for `countermodel_dense` in ChronicleToCountermodelBasic.lean.

**Tasks**:
- [x] Add `section DenseCountermodel` with `variable {Atom : Type} [Denumerable (Formula Atom)]` to override outer `Type*`
- [x] Add `DenselyOrdered D` to the existential statement (required for the dense countermodel)
- [x] Construct the proof using:
  - `cantorBfmcsDense` to get a BFMCS on Rat
  - The three restricted coherence conditions (`cantor_bfmcs_dense_restricted_tc`, `cantor_bfmcs_dense_restricted_buc`, `cantor_bfmcs_dense_restricted_fuc`)
  - `fully_restricted_parametric_completeness_from_neg_membership` to derive the countermodel
  - `rooted_cantor_fmcs_dense_at_s` to show `φ.neg ∈ B.evalFamily.mcs 0`
- [x] Provide existential witnesses: `Rat`, `ParametricCanonicalTaskFrame`, `ParametricCanonicalTaskModel`, `ShiftClosedParametricCanonicalOmega`, `parametricToHistory`
- [x] Close section with `end DenseCountermodel`
- [x] Verify with `lean_verify`: axioms = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`)

**Depends on**: none

**Files modified**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`

---

### Phase 2: Fill completeness_dense Sorry [COMPLETED]

**Goal**: Add section-scoped `variable {Atom : Type}` override and implement the proof body for `completeness_dense` in Dense.lean.

**Tasks**:
- [x] Add `section DenseCompleteness` with `variable {Atom : Type} [Denumerable (Formula Atom)]` to override outer `Type*`
- [x] In the dense case (`□(F'T) ∈ M`), obtain countermodel witnesses via `Chronicle.countermodel_dense`
- [x] Derive contradiction: `h_false` (countermodel falsifies φ) vs `h_valid_dense` (validDense says φ holds)
- [x] Close section with `end DenseCompleteness`
- [x] Update module docstring to reflect sorry-free status
- [x] Verify with `lean_verify`: axioms = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`)

**Depends on**: 1

**Files modified**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean`

---

### Phase 3: Build Verification [COMPLETED]

**Goal**: Verify full build succeeds with no regressions.

**Tasks**:
- [x] Run `lake build` — succeeded (1659 jobs)
- [x] Verify `countermodel_dense` sorry-free via `lean_verify`
- [x] Verify `completeness_dense` sorry-free via `lean_verify`
- [x] Confirm net sorry reduction: 2 sorries eliminated

**Depends on**: 2

**Files modified**: None (verification only)

## Testing & Validation

- [x] `countermodel_dense` proof compiles without sorry (`lean_verify` confirms)
- [x] `completeness_dense` proof compiles without sorry (`lean_verify` confirms)
- [x] Full `lake build` succeeds (1659 jobs)
- [x] No new sorry introduced in any file
- [x] Both theorems use only `[propext, Classical.choice, Quot.sound]` axioms

## Artifacts & Outputs

- `specs/231_fix_countermodel_dense_universe/reports/01_universe-mismatch-analysis.md` (research report)
- `specs/231_fix_countermodel_dense_universe/plans/01_universe-fix-plan.md` (this file)

## Rollback/Contingency

Not needed — implementation succeeded. If the section-scoped override approach causes issues downstream, the alternative is to generalize the 5 Parametric files from `{Atom : Type}` to `{Atom : Type*}` as originally planned in the research report.
