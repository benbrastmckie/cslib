# Implementation Plan: Propositional and Foundations Improvements

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: Task 265 (ipl_conservative_over_mpl sorry -- coordinate, do not duplicate)
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/01_propositional-foundations-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: true

## Overview

This plan addresses the gaps identified in the Propositional/ module and Foundations/ infrastructure of CSLib. The Propositional/ module is CSLib's most complete logic module (30 files, three logic tiers, two proof systems, four semantic frameworks) but has concrete defects: one sorry, a non-capture-avoiding substitution function, a missing algebraic-to-Hilbert completeness bridge, zero test coverage, and a stale documentation comment. The plan prioritizes filling existing gaps (Priority 1) and extracting shared completeness infrastructure (Priority 2), with new proof systems (sequent calculus, G4ip, decision procedure) deferred as stretch goals.

### Research Integration

- **reports/01_team-research.md**: Team research with 4 teammates covering inventory, alternatives, critic analysis, and strategic horizons. Key findings: 8 gaps identified, CLL provides sequent calculus template, ProofSystem instances already exist (stale comment), BimodalLogic Report 16 is irrelevant to propositional work.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

The ROADMAP.md focuses on porting BimodalLogic to CSLib with remaining items: discrete/continuous completeness for Bimodal and Temporal, dense temporal completeness, and abstract shared completeness infrastructure. This plan directly advances:
- **Abstract shared completeness infrastructure** (Phase 5: extract abstract completeness to Foundations)
- **ProofSystem concretization** supports downstream Bimodal/Temporal completeness work

## Goals & Non-Goals

**Goals**:
- Bridge algebraic completeness to Hilbert-level derivability for all three propositional logics
- Fix the non-capture-avoiding `subs` function in ND using `HasFresh` infrastructure
- Add test coverage for the Propositional/ module via `CslibTests/Propositional.lean`
- Update stale documentation in `ProofSystem.lean`
- Audit and concretize ProofSystem tag instances for Modal.HilbertK and Bimodal.HilbertTM
- Extract abstract completeness infrastructure to `Foundations/Logic/Metalogic/`

**Non-Goals**:
- Filling the `ipl_conservative_over_mpl` sorry (handled by task 265)
- Adding a propositional-specific tableau system (bimodal generalization preferred)
- CNF/DNF normal forms or Craig interpolation
- Curry-Howard correspondence formalization
- Generic sequent calculus framework (future task)
- G4ip or propositional decision procedure (future task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Algebraic-to-Hilbert bridge requires nontrivial intermediate lemmas | M | M | Research existing `alg_complete` and `hilbert_iff_nd` signatures first; bridge is a composition |
| `HasFresh` infrastructure not mature enough for ND `subs` fix | M | L | `HasFresh` already used in CCS/LTS; fall back to de Bruijn-style approach if needed |
| ProofSystem instance audit reveals many missing instances beyond scope | M | M | Scope to Modal.HilbertK and Bimodal.HilbertTM only; create follow-up tasks for others |
| Abstract completeness extraction breaks downstream imports | H | M | Use non-breaking approach: new file that re-exports existing definitions; run full `lake build` after |
| Task 265 changes Conservative.lean in ways that conflict | L | L | Coordinate: Phase 1 does not touch Conservative.lean; check task 265 status before starting |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1 |
| 3 | 5 | 4 |
| 4 | 6 | 1, 2, 3, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Bridge Algebraic Completeness to Hilbert [NOT STARTED]

**Goal**: Compose the existing `alg_complete` theorems with the `hilbert_iff_nd` bridge to produce Hilbert-level completeness corollaries (`Derivable MinPropAxiom phi <-> GHAValid phi`, etc.).

**Tasks**:
- [ ] Read `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` to understand `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical` signatures
- [ ] Read `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` to understand `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl` signatures
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertBridge.lean` with:
  - `MPL.hilbert_alg_complete : Derivable MinPropAxiom phi <-> GHAValid phi`
  - `IPL.hilbert_alg_complete : Derivable IntPropAxiom phi <-> HAValid phi`
  - `CPL.hilbert_alg_complete : Derivable ClPropAxiom phi <-> BAValid phi`
- [ ] Register the new file in the appropriate `.lean` import hierarchy
- [ ] Verify with `lake build`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertBridge.lean` - new file with bridge theorems
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - add import

**Verification**:
- `lake build` succeeds
- Bridge theorems state the correct iff between Hilbert derivability and algebraic validity

---

### Phase 2: Fix ND Substitution Capture Avoidance [NOT STARTED]

**Goal**: Replace the non-capture-avoiding `Theory.Derivation.subs` at `NaturalDeduction/Basic.lean:275-297` with a capture-avoiding implementation using `HasFresh` infrastructure.

**Tasks**:
- [ ] Read `Cslib/Foundations/Data/HasFresh.lean` (or equivalent) to understand the `HasFresh` typeclass and its API
- [ ] Analyze the current `subs` function at `NaturalDeduction/Basic.lean:275-297` to understand where capture can occur (under `impI` and `orE` binders)
- [ ] Implement capture-avoiding substitution:
  - Under `impI`: when substituting into `impI (A)`, rename `A` if it appears free in any substitution derivation
  - Under `orE`: similarly rename bound hypotheses if needed
- [ ] Remove the TODO comment at line 275-276
- [ ] Verify all downstream uses of `subs` still typecheck
- [ ] Run `lake build` to confirm no regressions

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - fix `subs` implementation, remove TODO

**Verification**:
- `lake build` succeeds
- The TODO comment about capture avoidance is removed
- Substitution under `impI` and `orE` binders correctly avoids variable capture

---

### Phase 3: Update Stale ProofSystem Documentation [NOT STARTED]

**Goal**: Fix the misleading comment in `ProofSystem.lean:50` that says instances are "future work" when `Instances.lean` and `IntMinInstances.lean` already register concrete instances.

**Tasks**:
- [ ] Read `Cslib/Foundations/Logic/ProofSystem.lean` to locate the stale comment at line 50
- [ ] Read `Cslib/Logics/Propositional/ProofSystem/Instances.lean` and `IntMinInstances.lean` to confirm which instances exist
- [ ] Update the comment to accurately describe the current state: concrete propositional instances exist; modal/temporal/bimodal instances may vary
- [ ] Run `lake build` to confirm no issues

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` - update stale documentation comment

**Verification**:
- Comment accurately reflects the current instance registration state
- `lake build` succeeds

---

### Phase 4: Audit and Concretize ProofSystem Tag Instances [NOT STARTED]

**Goal**: Verify which logic tags beyond propositional have concrete `ProofSystem` instances and fill missing ones for Modal.HilbertK and Bimodal.HilbertTM.

**Tasks**:
- [ ] Search the codebase for all `instance : ProofSystem` declarations to build a complete inventory
- [ ] Identify which tag types (Modal, Temporal, Bimodal) lack `ProofSystem` instances
- [ ] For Modal.HilbertK: create a `ProofSystem` instance connecting `ModalAxiom` derivability to the `ProofSystem` typeclass (if missing)
- [ ] For Bimodal.HilbertTM: create a `ProofSystem` instance connecting `BimodalAxiom` derivability to the `ProofSystem` typeclass (if missing)
- [ ] Register new instances in the appropriate module files
- [ ] Run `lake build` to confirm

**Timing**: 1.5 hours

**Depends on**: 1 (Phase 1 establishes the pattern for bridge theorems; understanding the propositional instances informs the modal/bimodal approach)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/` - new or modified instance file (if needed)
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` - new instance (if needed)

**Verification**:
- All tag types for Modal.HilbertK and Bimodal.HilbertTM have `ProofSystem` instances
- `lake build` succeeds

---

### Phase 5: Extract Abstract Completeness Infrastructure [NOT STARTED]

**Goal**: Factor out the shared MCS-to-canonical-model-to-truth-lemma-to-countermodel pattern into `Foundations/Logic/Metalogic/` so downstream logics (Bimodal, Temporal) can reuse the pattern without reimplementing it.

**Tasks**:
- [ ] Audit the completeness proofs in Propositional, Modal, and Bimodal to identify the shared pattern:
  - MCS construction (Lindenbaum's lemma)
  - Canonical model definition
  - Truth lemma
  - Countermodel extraction
- [ ] Design the abstract interface: parameterize over formula type, proof system, and model construction
- [ ] Create `Cslib/Foundations/Logic/Metalogic/AbstractCompleteness.lean` with:
  - Abstract completeness theorem structure
  - Shared lemmas about MCS properties used across all logics
  - Helper infrastructure for canonical model construction
- [ ] Verify the abstraction compiles and can be imported by downstream modules
- [ ] Create follow-up documentation noting how Bimodal/Temporal completeness tasks can use this infrastructure
- [ ] Run `lake build`

**Timing**: 2 hours

**Depends on**: 4 (understanding the full instance landscape informs what can be abstracted)

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/AbstractCompleteness.lean` - new file with shared infrastructure
- `Cslib/Foundations/Logic/Metalogic.lean` - add import (if barrel file exists)

**Verification**:
- New file compiles successfully
- Abstract types and lemmas are general enough to apply to Propositional, Modal, and Bimodal completeness patterns
- `lake build` succeeds with no regressions

---

### Phase 6: Add Propositional Test Coverage [NOT STARTED]

**Goal**: Create `CslibTests/Propositional.lean` exercising derivability, soundness, completeness, and the new algebraic-to-Hilbert bridge with concrete instances.

**Tasks**:
- [ ] Create `CslibTests/Propositional.lean` with test cases:
  - Derivability: derive `p -> p`, `p -> q -> p`, `((p -> q) -> p) -> p` (Peirce's law, CPL only)
  - Soundness: verify that derived formulas are valid under Boolean evaluation
  - Completeness: verify that valid formulas are derivable (round-trip)
  - ND equivalence: verify `hilbert_iff_nd` on concrete instances
  - Algebraic bridge: verify `hilbert_alg_complete` on concrete instances (from Phase 1)
  - Non-derivability: verify that Peirce's law is not derivable in IPL/MPL (if decidability allows)
- [ ] Register the test file in `CslibTests.lean` (or the test suite barrel import)
- [ ] Run `lake test` to confirm all tests pass
- [ ] Run full CI pipeline: `lake exe checkInitImports`, `lake exe lint-style`

**Timing**: 1 hour

**Depends on**: 1, 2, 3, 5 (tests should exercise the new bridge theorems and fixed `subs`)

**Files to modify**:
- `CslibTests/Propositional.lean` - new test file
- `CslibTests.lean` - add import (if barrel file exists)

**Verification**:
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- Tests cover derivability, soundness, completeness, and the Hilbert-algebraic bridge

---

## Testing & Validation

- [ ] `lake build` succeeds after all phases
- [ ] `lake test` passes with new `CslibTests/Propositional.lean`
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No new `sorry` introduced (check with `grep -rn sorry Cslib/Logics/Propositional/`)
- [ ] Bridge theorems correctly compose algebraic completeness with Hilbert-ND equivalence
- [ ] `subs` function no longer has the capture-avoidance TODO
- [ ] ProofSystem.lean documentation is accurate
- [ ] Modal/Bimodal ProofSystem instances are registered

## Artifacts & Outputs

- `specs/266_research_propositional_and_foundations_improvements/plans/01_propositional-foundations-plan.md` (this file)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertBridge.lean` (new, Phase 1)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (modified, Phase 2)
- `Cslib/Foundations/Logic/ProofSystem.lean` (modified, Phase 3)
- `Cslib/Foundations/Logic/Metalogic/AbstractCompleteness.lean` (new, Phase 5)
- `CslibTests/Propositional.lean` (new, Phase 6)

## Rollback/Contingency

All changes are additive (new files) or localized edits (comment update, `subs` fix). If any phase causes build failures:
1. Revert the specific phase's changes with `git checkout -- <file>`
2. Other phases can proceed independently (Waves 1 phases are fully independent)
3. The abstract completeness extraction (Phase 5) is the highest-risk phase -- if the abstraction does not compile cleanly, defer to a follow-up task and keep the existing per-logic implementations unchanged
