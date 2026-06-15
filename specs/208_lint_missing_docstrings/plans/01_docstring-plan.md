# Implementation Plan: Add Missing Documentation Strings

- **Task**: 208 - Add missing documentation strings to Bimodal/Temporal/Modal declarations
- **Status**: [NOT STARTED]
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

### Phase 1: Bimodal/Theorems -- Proof-Bearing Definitions [NOT STARTED]

**Goal**: Add docstrings to 78 proof-bearing definitions across 5 theorem files. These are the most formulaic: each definition proves a Hilbert-style derivation, so the docstring follows the pattern `` /-- `formula`: brief description. -/ ``.

**Tasks**:
- [ ] Add 41 docstrings to `Bimodal/Theorems/TemporalDerived.lean` (G/H/F/P distribution, monotonicity, duality derivations)
- [ ] Add 16 docstrings to `Bimodal/Theorems/Propositional/Connectives.lean` (iff, contraposition, De Morgan combinators)
- [ ] Add 14 docstrings to `Bimodal/Theorems/Propositional/Core.lean` (LEM, DNE, RAA, ECQ, disjunction)
- [ ] Add 7 docstrings to `Bimodal/Theorems/GeneralizedNecessitation.lean` (generalized modal/temporal K, past necessitation)
- [ ] Verify with `lake lint` that docBlame errors are resolved for these files

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

### Phase 2: Bimodal/Syntax -- Formula Infrastructure [NOT STARTED]

**Goal**: Add docstrings to 34 formula-level definitions across 2 subformula closure files. These are predicates, extractors, and set definitions operating on the formula datatype.

**Tasks**:
- [ ] Add 26 docstrings to `Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` (deferral closure, seriality formulas, blocking sets, abbreviations)
- [ ] Add 8 docstrings to `Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` (nesting depth functions, extractors, formula predicates)
- [ ] Verify with `lake lint` that docBlame errors are resolved for these files

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` - 26 docstrings
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - 8 docstrings

**Verification**:
- `lake lint` shows no `docBlame` errors for the 2 modified files
- Computation-describing docstrings for predicates and functions

---

### Phase 3: Bimodal/Metalogic/Bundle + Bimodal/Metalogic/Separation + Bimodal/Metalogic/Algebraic [NOT STARTED]

**Goal**: Add docstrings to 32 declarations across 8 files in the Bundle, Separation, and Algebraic subdirectories. These are content-set definitions, saturation predicates, and algebraic constructions.

**Tasks**:
- [ ] Add 10 docstrings to `Bimodal/Metalogic/Bundle/TemporalCoherence.lean` (temporal coherence family, G/H DNE, until/since coherence)
- [ ] Add 7 docstrings to `Bimodal/Metalogic/Bundle/ModalSaturation.lean` (modal saturation, DNE theorems, SaturatedBFMCS inductive)
- [ ] Add 6 docstrings to `Bimodal/Metalogic/Bundle/TemporalContent.lean` (g/h/f/p/u/s content set definitions)
- [ ] Add 5 docstrings to `Bimodal/Metalogic/Bundle/Construction.lean` (context utilities, Lindenbaum MCS, context consistency)
- [ ] Add 1 docstring to `Bimodal/Metalogic/Bundle/FMCSDef.lean` (FMCS.mcs field)
- [ ] Add 3 docstrings to `Bimodal/Metalogic/Separation/Defs.lean` (IntStructure field, junction depth functions)
- [ ] Add 2 docstrings to `Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` (negImpImplies helper lemmas)
- [ ] Add 2 docstrings to `Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` (notation terms for provable equivalence and quotient)
- [ ] Add 1 docstring to `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` (BoolAlgUltrafilter.carrier field)
- [ ] Verify with `lake lint` that docBlame errors are resolved for these files

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

### Phase 4: Bimodal/Metalogic/BXCanonical -- Canonical Model Construction [NOT STARTED]

**Goal**: Add docstrings to 82 declarations across 10 files in the BXCanonical subdirectory. This is the largest single subdirectory and includes the chronicle data structures, canonical model construction, frame definitions, and quasimodel components.

**Tasks**:
- [ ] Add 30 docstrings to `BXCanonical/Chronicle/ChronicleTypes.lean` (chronicle data structures, r-relations, Burgess relations)
- [ ] Add 16 docstrings to `BXCanonical/Chronicle/CounterexampleElimination.lean` (counterexample structure fields, elimination procedures)
- [ ] Add 16 docstrings to `BXCanonical/CanonicalModel.lean` (schedule, chains, FMCS construction)
- [ ] Add 14 docstrings to `BXCanonical/Frame.lean` (BX frame points, ordering, witnesses, content-closed derivation)
- [ ] Add 6 docstrings to `BXCanonical/Chronicle/PointInsertion.lean` (EnrichedEvent/EnrichedEventSince structure fields)
- [ ] Add 4 docstrings to `BXCanonical/Quasimodel/HintikkaPoint.lean` (Hintikka point inductive, signature formulas)
- [ ] Add 3 docstrings to `BXCanonical/Quasimodel/SubformulaClosure.lean` (subformulas, GH enrichment)
- [ ] Add 3 docstrings to `BXCanonical/Quasimodel/Construction.lean` (QuasimodelChain inductive, sinceDefectCount, HintikkaRawChain field)
- [ ] Add 3 docstrings to `BXCanonical/Filtration/DefectChain.lean` (until/since defect predicates and counts)
- [ ] Verify with `lake lint` that docBlame errors are resolved for these files

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

### Phase 5: Bimodal/FrameConditions + Bimodal/Metalogic/Decidability -- Remaining Bimodal [NOT STARTED]

**Goal**: Add docstrings to the 7 remaining Bimodal declarations across 3 files: frame condition validity definitions, the tableau axiom matcher identity, and the Perpetuity helper.

**Tasks**:
- [ ] Add 5 docstrings to `Bimodal/FrameConditions/Validity.lean` (parameterized validity definitions for linear, dense, discrete, Int)
- [ ] Add 1 docstring to `Bimodal/FrameConditions/Soundness.lean` (soundnessOver definition)
- [ ] Add 1 docstring to `Bimodal/Metalogic/Decidability/AxiomMatcher.lean` (identity definition)
- [ ] Verify with `lake lint` that docBlame errors are resolved for these files
- [ ] Confirm all 252 Bimodal/ docBlame errors are now resolved

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

### Phase 6: Temporal/ -- All Temporal Declarations [NOT STARTED]

**Goal**: Add docstrings to all 75 Temporal/ declarations across 7 files. Many of these parallel Bimodal/ structures (Chronicle, PointInsertion, TemporalContent), so docstrings should be consistent with those written in phases 3-4.

**Tasks**:
- [ ] Add 30 docstrings to `Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (chronicle types, r-relations, Burgess relations -- parallel to Bimodal)
- [ ] Add 19 docstrings to `Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (counterexample structures, walk results, elimination procedures)
- [ ] Add 9 docstrings to `Temporal/Metalogic/Chronicle/Frame.lean` (TPoint fields, content-closed derivation, witnesses)
- [ ] Add 6 docstrings to `Temporal/Metalogic/TemporalContent.lean` (g/h/f/p/u/s content set definitions -- parallel to Bimodal)
- [ ] Add 6 docstrings to `Temporal/Metalogic/Chronicle/PointInsertion.lean` (EnrichedEvent/EnrichedEventSince structure fields -- parallel to Bimodal)
- [ ] Add 3 docstrings to `Temporal/Metalogic/Chronicle/RRelation.lean` (deductive closure, r/r3 DCS extensions)
- [ ] Add 2 docstrings to `Temporal/Metalogic/WitnessSeed.lean` (forward/past temporal witness seeds)
- [ ] Verify with `lake lint` that all docBlame errors are resolved for Temporal/ files
- [ ] Run full `lake lint` to confirm zero remaining docBlame errors across the entire codebase

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

### Phase 7: Perpetuity Helper [NOT STARTED]

**Goal**: Add the single remaining docstring to the Perpetuity helper file.

**Tasks**:
- [ ] Add 1 docstring to `Bimodal/Theorems/Perpetuity/Principles.lean` (perpetuity axiom helper)

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - 1 docstring

**Verification**:
- `lake lint` shows no `docBlame` error for this file

## Testing & Validation

- [ ] After each phase, run `lake lint 2>&1 | grep docBlame` on modified files to confirm errors resolved
- [ ] After final phase, run full `lake lint` to confirm zero remaining `docBlame` errors
- [ ] Run `lake build` to confirm docstrings do not break compilation
- [ ] Spot-check 5-10 docstrings per phase for accuracy and style consistency

## Artifacts & Outputs

- `specs/208_lint_missing_docstrings/plans/01_docstring-plan.md` (this file)
- `specs/208_lint_missing_docstrings/summaries/01_docstring-summary.md` (after implementation)
- 35 modified `.lean` files with added docstrings

## Rollback/Contingency

All changes are comment-only additions. If any phase introduces issues:
- `git revert` the phase commit to remove all docstrings from that phase
- Individual docstrings can be removed without affecting other declarations
- No functional code is modified, so rollback risk is minimal
