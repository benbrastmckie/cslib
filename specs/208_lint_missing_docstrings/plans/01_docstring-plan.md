# Implementation Plan: Add Missing Documentation Strings

- **Task**: 208 - Add missing documentation strings to Bimodal/Temporal/Modal declarations
- **Status**: [COMPLETED]
- **Effort**: 9 hours
- **Dependencies**: None
- **Research Inputs**: specs/208_lint_missing_docstrings/reports/01_lint-docstring-research.md
- **Artifacts**: plans/01_docstring-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add `/-- ... -/` docstrings to 327 declarations across 35 files in `Cslib/Logics/Bimodal/` (252 declarations, 28 files) and `Cslib/Logics/Temporal/` (75 declarations, 7 files) to resolve all `docBlame` lint errors. The work is comment-only -- no functional code changes. Research confirmed that Modal/ has zero missing docstrings, contrary to the original task estimate.

### Research Integration

The research report (`01_lint-docstring-research.md`) identified exact per-file counts, classified declarations into 7 semantic categories (Hilbert derivations, canonical model components, formula predicates, set constructions, structure fields, inductive types, relations), and documented the existing docstring style conventions. The plan follows the report's recommended 6-phase structure organized by subdirectory.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances overall CSLib code quality. The ROADMAP.md focuses on porting and completeness proofs; lint compliance is a cross-cutting concern that improves maintainability across all roadmap modules (Bimodal and Temporal).

## Goals & Non-Goals

**Goals**:
- Resolve all 327 `docBlame` lint errors across Bimodal/ and Temporal/
- Write docstrings consistent with existing CSLib conventions (formal statement in backticks for theorem-like defs, plain English for structural defs)
- Maintain docstring consistency between parallel Bimodal/Temporal structures

**Non-Goals**:
- Modifying any functional code
- Adding docstrings to declarations not flagged by lint
- Refactoring or improving existing docstrings
- Addressing other lint categories (unused simp args, etc.)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring placement breaks compilation | M | L | Verify with `lake lint` after each phase; docstrings are comments so build risk is minimal |
| Incorrect formal statement in docstring | L | M | Cross-reference declaration body and type signature when writing; reviewer can spot-check |
| Large phase exceeds agent context | M | M | Phases bounded to max 82 declarations; largest files read incrementally |
| Parallel Bimodal/Temporal inconsistency | L | M | Phase 6 (Temporal) explicitly references Bimodal docstrings written in phases 3-4 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 5, 7 | -- |
| 2 | 4 | 3 |
| 3 | 6 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Bimodal/Theorems -- Proof-Bearing Definitions [COMPLETED]

**Goal**: Add docstrings to 78 proof-bearing definitions across 5 theorem files. These are the most formulaic: each definition proves a Hilbert-style derivation, so the docstring follows the pattern `` /-- `formula`: brief description. -/ ``.

**Tasks**:
- [x] Add 41 docstrings to `Bimodal/Theorems/TemporalDerived.lean` (41/41)
- [x] Add 16 docstrings to `Bimodal/Theorems/Propositional/Connectives.lean` (16/16)
- [x] Add 14 docstrings to `Bimodal/Theorems/Propositional/Core.lean` (14/14)
- [x] Add 7 docstrings to `Bimodal/Theorems/GeneralizedNecessitation.lean` (7/7)
- [x] Verify with `lake lint` that docBlame errors are resolved for these files

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - 41 docstrings
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` - 16 docstrings
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - 14 docstrings
- `Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean` - 7 docstrings

**Verification**:
- `lake lint` shows no `docBlame` errors for the 4 modified files
- Each docstring follows the `` `formal statement`: description `` convention

---

### Phase 2: Bimodal/Syntax -- Formula Infrastructure [COMPLETED]

**Goal**: Add docstrings to 34 formula-level definitions across 2 subformula closure files. These are predicates, extractors, and set definitions operating on the formula datatype.

**Tasks**:
- [x] Add 26 docstrings to `Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` (26/26)
- [x] Add 8 docstrings to `Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` (8/8)
- [x] Verify with `lake lint` that docBlame errors are resolved for these files

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` - 26 docstrings
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - 8 docstrings

**Verification**:
- `lake lint` shows no `docBlame` errors for the 2 modified files
- Computation-describing docstrings for predicates and functions

---

### Phase 3: Bimodal/Metalogic/Bundle + Bimodal/Metalogic/Separation + Bimodal/Metalogic/Algebraic [COMPLETED]

**Goal**: Add docstrings to 32 declarations across 8 files in the Bundle, Separation, and Algebraic subdirectories. These are content-set definitions, saturation predicates, and algebraic constructions.

**Tasks**:
- [x] Add 10 docstrings to `Bimodal/Metalogic/Bundle/TemporalCoherence.lean` (10/10)
- [x] Add 7 docstrings to `Bimodal/Metalogic/Bundle/ModalSaturation.lean` (8/7 — exceeded target)
- [x] Add 6 docstrings to `Bimodal/Metalogic/Bundle/TemporalContent.lean` (6/6)
- [x] Add 5 docstrings to `Bimodal/Metalogic/Bundle/Construction.lean` (9/5 — exceeded target)
- [x] Add 1 docstring to `Bimodal/Metalogic/Bundle/FMCSDef.lean`
- [x] Add 3 docstrings to `Bimodal/Metalogic/Separation/Defs.lean` (3/3)
- [x] Add 2 docstrings to `Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` (2/2)
- [x] Add 2 docstrings to `Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean`
- [x] Add 1 docstring to `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean`
- [x] Verify with `lake lint` that docBlame errors are resolved for these files

**Extra work**: Agent also added docstrings to `Bundle/CanonicalFrame.lean` (1), `Separation/DedekindZ/Cases.lean` (6), `Separation/DedekindZ/QLemma.lean` (2), `Separation/Eliminations.lean` (2), `Separation/Hierarchy/HierarchyInduction.lean` (5), `Separation/Hierarchy/HierarchyCompletion.lean` (2), `Separation/Hierarchy/HierarchyCaseSep.lean` (2), `Core/DerivationTree.lean` (1) — 21 extra docstrings in files beyond plan scope.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalCoherence.lean` - 10 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Bundle/ModalSaturation.lean` - 7 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean` - 6 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Bundle/Construction.lean` - 5 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCSDef.lean` - 1 docstring
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` - 3 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` - 2 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` - 2 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` - 1 docstring

**Verification**:
- `lake lint` shows no `docBlame` errors for the 9 modified files
- Content-set docstrings describe what is in the set; structure fields get brief role descriptions

---

### Phase 4: Bimodal/Metalogic/BXCanonical -- Canonical Model Construction [COMPLETED]

**Goal**: Add docstrings to 82 declarations across 10 files in the BXCanonical subdirectory. This is the largest single subdirectory and includes the chronicle data structures, canonical model construction, frame definitions, and quasimodel components.

**Tasks**:
- [x] Add 30 docstrings to `BXCanonical/Chronicle/ChronicleTypes.lean` (43/30 — exceeded target)
- [x] Add 16 docstrings to `BXCanonical/Chronicle/CounterexampleElimination.lean`
- [x] Add 16 docstrings to `BXCanonical/CanonicalModel.lean`
- [x] Add 14 docstrings to `BXCanonical/Frame.lean` (24/14 — exceeded target)
- [x] Add 6 docstrings to `BXCanonical/Chronicle/PointInsertion.lean` (8/6 — exceeded target)
- [x] Add 4 docstrings to `BXCanonical/Quasimodel/HintikkaPoint.lean` (13/4 — exceeded target)
- [x] Add 3 docstrings to `BXCanonical/Quasimodel/SubformulaClosure.lean` (11/3 — exceeded target)
- [x] Add 3 docstrings to `BXCanonical/Quasimodel/Construction.lean` (15/3 — exceeded target)
- [x] Add 3 docstrings to `BXCanonical/Filtration/DefectChain.lean` (9/3 — exceeded target)
- [x] Verify with `lake lint` that docBlame errors are resolved for these files

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` - 30 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` - 16 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalModel.lean` - 16 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` - 14 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` - 6 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/HintikkaPoint.lean` - 4 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/SubformulaClosure.lean` - 3 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/Construction.lean` - 3 docstrings
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Filtration/DefectChain.lean` - 3 docstrings

**Verification**:
- `lake lint` shows no `docBlame` errors for the 9 modified files
- Structure/inductive docstrings describe the data type and its role in the canonical model
- Structure field docstrings are brief (one line)

---

### Phase 5: Bimodal/FrameConditions + Bimodal/Metalogic/Decidability -- Remaining Bimodal [COMPLETED]

**Goal**: Add docstrings to the 7 remaining Bimodal declarations across 3 files: frame condition validity definitions, the tableau axiom matcher identity, and the Perpetuity helper.

**Tasks**:
- [x] Add 5 docstrings to `Bimodal/FrameConditions/Validity.lean` (5/5)
- [x] Add 1 docstring to `Bimodal/FrameConditions/Soundness.lean` (1/1)
- [x] Add 1 docstring to `Bimodal/Metalogic/Decidability/AxiomMatcher.lean` (1/1)
- [x] Verify with `lake lint` that docBlame errors are resolved for these files
- [x] Confirm all 252 Bimodal/ docBlame errors are now resolved

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/FrameConditions/Validity.lean` - 5 docstrings
- `Cslib/Logics/Bimodal/FrameConditions/Soundness.lean` - 1 docstring
- `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` - 1 docstring

**Verification**:
- `lake lint` shows no `docBlame` errors for the 3 modified files
- Running `lake lint 2>&1 | grep docBlame | grep Bimodal` returns zero results

---

### Phase 6: Temporal/ -- All Temporal Declarations [COMPLETED]

**Goal**: Add docstrings to all 75 Temporal/ declarations across 7 files. Many of these parallel Bimodal/ structures (Chronicle, PointInsertion, TemporalContent), so docstrings should be consistent with those written in phases 3-4.

**Tasks**:
- [x] Add 30 docstrings to `Temporal/Metalogic/Chronicle/ChronicleTypes.lean`
- [x] Add 19 docstrings to `Temporal/Metalogic/Chronicle/CounterexampleElimination.lean`
- [x] Add 9 docstrings to `Temporal/Metalogic/Chronicle/Frame.lean` (13/9 — exceeded target)
- [x] Add 6 docstrings to `Temporal/Metalogic/TemporalContent.lean` (6/6)
- [x] Add 6 docstrings to `Temporal/Metalogic/Chronicle/PointInsertion.lean` (10/6 — exceeded target)
- [x] Add 3 docstrings to `Temporal/Metalogic/Chronicle/RRelation.lean` (6/3 — exceeded target)
- [x] Add 2 docstrings to `Temporal/Metalogic/WitnessSeed.lean` (2/2)
- [x] Verify with `lake lint` that all docBlame errors are resolved for Temporal/ files
- [x] Run full `lake lint` to confirm zero remaining docBlame errors across the entire codebase

**Extra work**: Agent also added 1 docstring to `Temporal/Metalogic/DerivationTree.lean` (not in plan).

**Timing**: 1.5 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - 30 docstrings
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - 19 docstrings
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` - 9 docstrings
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` - 6 docstrings
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - 6 docstrings
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - 3 docstrings
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` - 2 docstrings

**Verification**:
- `lake lint` shows no `docBlame` errors for the 7 modified files
- `lake lint 2>&1 | grep docBlame` returns zero results (full codebase clean)
- Docstrings are consistent with parallel Bimodal/ docstrings

---

### Phase 7: Perpetuity Helper [COMPLETED]

**Goal**: Add the single remaining docstring to the Perpetuity helper file.

**Tasks**:
- [x] Add 1 docstring to `Bimodal/Theorems/Perpetuity/Principles.lean` (1/1)

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - 1 docstring

**Verification**:
- `lake lint` shows no `docBlame` error for this file

## Testing & Validation

- [x] After each phase, run `lake lint 2>&1 | grep docBlame` on modified files to confirm errors resolved
- [x] After final phase, run full `lake lint` to confirm zero remaining `docBlame` errors
- [x] Run `lake build` to confirm docstrings do not break compilation (2986 jobs, 0 errors)
- [x] Spot-check 5-10 docstrings per phase for accuracy and style consistency

## Artifacts & Outputs

- `specs/208_lint_missing_docstrings/plans/01_docstring-plan.md` (this file)
- `specs/208_lint_missing_docstrings/summaries/01_docstring-summary.md` (after implementation)
- 35 modified `.lean` files with added docstrings

## Rollback/Contingency

All changes are comment-only additions. If any phase introduces issues:
- `git revert` the phase commit to remove all docstrings from that phase
- Individual docstrings can be removed without affecting other declarations
- No functional code is modified, so rollback risk is minimal

## Progress Audit (post-implementation)

**Final result**: `lake lint` reports **0 docBlame errors**. `lake build` passes (2986 jobs, 0 errors).

Implementation required 3 agent dispatches (first two hit context limits; third completed remaining work).

| Phase | Status | Notes |
|-------|--------|-------|
| 1 (Theorems) | COMPLETED | All 4 files done |
| 2 (Syntax) | COMPLETED | Both files done |
| 3 (Bundle+Sep+Alg) | COMPLETED | All 9 files done (continuation agent filled gaps) |
| 4 (BXCanonical) | COMPLETED | All 9 files done (continuation agent filled gaps) |
| 5 (FrameCond) | COMPLETED | All 3 files done |
| 6 (Temporal) | COMPLETED | All 7 files done (continuation agent filled gaps) |
| 7 (Perpetuity) | COMPLETED | Done |

Additional docstrings added to files beyond original plan scope (Separation/, DedekindZ/, Core/, ProofSystem/Instances/, Modal/ProofSystem/Instances/).
