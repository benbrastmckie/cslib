# Implementation Plan: Modal Cube Inter-System Conservativity

- **Task**: 276 - modal_cube_inter_system_conservativity
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None (axiom predicates and DerivationTree already exist for all 15 systems)
- **Research Inputs**: specs/276_modal_cube_inter_system_conservativity/reports/01_modal-cube-conservativity.md
- **Artifacts**: plans/01_modal-cube-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove inter-system conservative extension results across the modal cube by implementing a generic `lift_derivation` lemma parameterized by an axiom subsumption callback, axiom subsumption lemmas for all 24 direct edges of the cube, and instantiated derivability monotonicity theorems. All 15 systems share the same formula type (`Modal.Proposition Atom`) so no formula translation is needed. The proofs are entirely mechanical: structural induction for lifting and case-splits for subsumption.

### Research Integration

The research report (01_modal-cube-conservativity.md) confirmed:
- All 15 axiom predicates share the same 4 propositional + 1 modal K constructors with identical names, making subsumption proofs mechanical.
- S5 uses `ModalAxiom` (defined in DerivationTree.lean), not a separate `S5Axiom`.
- The `DerivationTree` has 5 constructors (`ax`, `assumption`, `modus_ponens`, `necessitation`, `weakening`), all handled uniformly by the generic lifting lemma.
- Zero-sorry feasibility: all proofs are structural/mechanical with no novel mathematical content.
- Recommended file organization: 3 files under `Cslib/Logics/Modal/Metalogic/InterSystem/`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Generic `lift_derivation` lemma that maps derivation trees across axiom predicates
- Generic `Derivable_mono` corollary lifting from `Derivable` to `Derivable`
- Axiom subsumption lemmas for all 24 direct edges in the modal cube
- Instantiated conservativity theorems (`k_derivable_implies_t_derivable`, etc.) for all 24 edges

**Non-Goals**:
- Semantic conservativity proofs (trivially reduce to completeness, not needed)
- Transitive closure lemmas (follow from composing direct-edge results)
- Modifications to existing Cube.lean or axiom predicate files
- Full partial order proof for the derivability cube

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe level issues with `DerivationTree` lifting | M | L | DerivationTree is `Type _`, all arguments are in compatible universes |
| Diamond encoding mismatch between D/B axiom variants | L | L | All systems use the same `Proposition.diamond` and `Proposition.imp` encoding, confirmed by source inspection |
| Large file size for 24 subsumption lemmas | L | M | Mechanical code; each lemma is 5-8 lines; total ~180 lines is manageable in one file |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Generic Lifting Lemma [COMPLETED]

**Goal**: Create the `Lifting.lean` file with the generic `lift_derivation` and `Derivable_mono` lemmas.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Modal/Metalogic/InterSystem/`
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean` with:
  - `lift_derivation`: structural induction on `DerivationTree Axioms1 Gamma phi` producing `DerivationTree Axioms2 Gamma phi`, using an `h_sub : forall phi, Axioms1 phi -> Axioms2 phi` callback
  - `Derivable_mono`: lifts from `Derivable Axioms1 phi` to `Derivable Axioms2 phi` using `lift_derivation`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Lifting`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean` - New file (~30 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Lifting` succeeds with no errors or sorries

---

### Phase 2: Axiom Subsumption Lemmas [COMPLETED]

**Goal**: Prove all 24 direct-edge axiom subsumption lemmas establishing that the weaker system's axiom predicate implies the stronger system's axiom predicate.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean`
- [ ] Implement the following 24 subsumption lemmas (each is a case-split on the source axiom predicate, mapping each constructor to the corresponding target constructor):

  **K-based edges (K is weakest, maps into 4 direct extensions)**:
  - [ ] `KAxiom_implies_TAxiom` (K -> T: add modalT)
  - [ ] `KAxiom_implies_DAxiom` (K -> D: add modalD)
  - [ ] `KAxiom_implies_BAxiom` (K -> B: add modalB)
  - [ ] `KAxiom_implies_K4Axiom` (K -> K4: add modalFour)
  - [ ] `KAxiom_implies_K5Axiom` (K -> K5: add modalFive)

  **D-based edges (D extends K, maps into D-family)**:
  - [ ] `DAxiom_implies_TAxiom` (D -> T: replace modalD with modalT)
  - [ ] `DAxiom_implies_D4Axiom` (D -> D4: add modalFour)
  - [ ] `DAxiom_implies_D5Axiom` (D -> D5: add modalFive)
  - [ ] `DAxiom_implies_DBAxiom` (D -> DB: add modalB)

  **T-based edges**:
  - [ ] `TAxiom_implies_S4Axiom` (T -> S4: add modalFour)
  - [ ] `TAxiom_implies_TBAxiom` (T -> TB: add modalB)

  **B-based edges**:
  - [ ] `BAxiom_implies_TBAxiom` (B -> TB: add modalT)
  - [ ] `BAxiom_implies_DBAxiom` (B -> DB: add modalD)
  - [ ] `BAxiom_implies_KB5Axiom` (B -> KB5: add modalFive)

  **K4-based edges**:
  - [ ] `K4Axiom_implies_S4Axiom` (K4 -> S4: add modalT)
  - [ ] `K4Axiom_implies_D4Axiom` (K4 -> D4: add modalD)
  - [ ] `K4Axiom_implies_K45Axiom` (K4 -> K45: add modalFive)

  **K5-based edges**:
  - [ ] `K5Axiom_implies_D5Axiom` (K5 -> D5: add modalD)
  - [ ] `K5Axiom_implies_K45Axiom` (K5 -> K45: add modalFour)
  - [ ] `K5Axiom_implies_KB5Axiom` (K5 -> KB5: add modalB)

  **K45-based edges**:
  - [ ] `K45Axiom_implies_D45Axiom` (K45 -> D45: add modalD)

  **D4/D5-based edges**:
  - [ ] `D4Axiom_implies_D45Axiom` (D4 -> D45: add modalFive)
  - [ ] `D5Axiom_implies_D45Axiom` (D5 -> D45: add modalFour)

  **Top-level edges (into S5)**:
  - [ ] `S4Axiom_implies_ModalAxiom` (S4 -> S5: add modalB)
  - [ ] `TBAxiom_implies_ModalAxiom` (TB -> S5: add modalFour)
  - [ ] `KB5Axiom_implies_ModalAxiom` (KB5 -> S5: add modalT)

- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.InterSystem.AxiomSubsumption`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` - New file (~180 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.InterSystem.AxiomSubsumption` succeeds with no errors or sorries
- Each lemma is sorry-free

---

### Phase 3: Conservativity Theorems and CI [COMPLETED]

**Goal**: Instantiate all 24+3 conservativity theorems using `Derivable_mono` + subsumption lemmas, update barrel imports, and pass full CI.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/Conservativity.lean`
- [ ] Instantiate derivability monotonicity for all 24 direct edges:
  ```
  theorem k_derivable_implies_t_derivable : Derivable (@KAxiom Atom) phi -> Derivable (@TAxiom Atom) phi
  ```
  Each is a one-liner applying `Derivable_mono` with the corresponding subsumption lemma.
- [ ] Add 3 transitive chain theorems for the main paths:
  - `k_derivable_implies_s5_derivable` (K -> T -> S4 -> S5)
  - `k_derivable_implies_d45_derivable` (K -> D -> D4 -> D45)
  - `d_derivable_implies_s5_derivable` (D -> T -> S4 -> S5)
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Run full CI pipeline: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/Conservativity.lean` - New file (~120 lines)
- `Cslib.lean` - Updated by `mk_all` to include new module paths

**Verification**:
- `lake build` succeeds (full project, no errors)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- All theorems are sorry-free (`lean_verify` on key declarations)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Lifting` -- generic lemma compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.InterSystem.AxiomSubsumption` -- all 24+3 subsumption lemmas compile
- [ ] `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Conservativity` -- all instantiated theorems compile
- [ ] `lake build` -- full project builds clean
- [ ] `lake exe checkInitImports` -- all files import `Cslib.Init`
- [ ] `lake exe lint-style` -- style check passes
- [ ] `lake test` -- test suite passes
- [ ] `lean_verify` on `lift_derivation`, `Derivable_mono`, and at least 3 conservativity theorems -- no sorry, no axiom abuse

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean` -- Generic `lift_derivation` and `Derivable_mono` lemmas
- `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` -- 24+3 axiom subsumption lemmas for cube edges
- `Cslib/Logics/Modal/Metalogic/InterSystem/Conservativity.lean` -- 24+3 instantiated derivability monotonicity theorems
- `specs/276_modal_cube_inter_system_conservativity/plans/01_modal-cube-plan.md` -- This plan

## Rollback/Contingency

All changes are additive (3 new files in a new directory). Rollback is trivial: delete `Cslib/Logics/Modal/Metalogic/InterSystem/` and re-run `lake exe mk_all --module` to remove the barrel imports. No existing files are modified except the auto-generated `Cslib.lean`.
