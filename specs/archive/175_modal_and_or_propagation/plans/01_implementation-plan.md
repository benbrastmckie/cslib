# Implementation Plan: Task #175

- **Task**: 175 - Propagate the hybrid five-primitive design to the Modal layer
- **Status**: [NOT STARTED]
- **Effort**: 12 hours
- **Dependencies**: Task 173 (PL five-primitive design, completed)
- **Research Inputs**: specs/175_modal_and_or_propagation/reports/01_modal-propagation-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan propagates the hybrid five-primitive design from Propositional to Modal logic.
Modal.Proposition currently has 4 constructors `{atom, bot, imp, box}` with `and`/`or` as
Lukasiewicz-derived abbrevs. The target is 6 constructors `{atom, bot, imp, and, or, box}` with
`diamond`/`neg`/`top`/`iff` remaining derived. This change touches 55 files across 5 layers:
core definitions, semantic infrastructure, 16 proof system instance files, 3 parameterized truth
lemma families, and 30 system-specific soundness/completeness files. Two existing `sorry` entries
in `FromPropositional.lean` are resolved as a side effect.

### Research Integration

The research report (01_modal-propagation-research.md) provided:
- Complete file-by-file change analysis across 5 layers
- Confirmation that parameterized infrastructure (DerivationTree, DeductionTheorem, MCS,
  parameterized Soundness) needs NO modification
- Classification of 15 systems into 3 truth lemma families (T-based: 4 systems, K-based: 6
  systems, D-based: 5 systems)
- Risk analysis: DecidableEq/BEq safe, notation compatible, grind annotations auto-update
- Identification of the truth lemma `.or` case as the hardest proof obligation

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the porting effort by bringing Modal logic to parity with the Propositional
five-primitive design completed in task 173. It is infrastructure work that enables cleaner
embeddings (FromPropositional.lean sorry resolution) and aligns with the Foundations/Logic
connective architecture.

## Goals & Non-Goals

**Goals**:
- Add `.and` and `.or` constructors to `Modal.Proposition`
- Add corresponding structural clauses to `Satisfies`
- Register `HasAnd`/`HasOr` instances for `Modal.Proposition`
- Add 6 and/or axiom constructors to all 16 axiom predicates (ModalAxiom + 15 system axioms)
- Register `HasAxiomAndI`/`HasAxiomAndE1`/`HasAxiomAndE2`/`HasAxiomOrI1`/`HasAxiomOrI2`/`HasAxiomOrE` instances for all 15 systems
- Extend all 3 truth lemma families with `.and`/`.or` cases
- Add 6 propositional axiom-sound cases to all 15 soundness files
- Pass through 6 new axiom hypotheses in all 15 completeness files
- Resolve 2 existing `sorry` in `FromPropositional.lean`
- Pass full CI verification pipeline

**Non-Goals**:
- Changing Temporal or Bimodal logic layers (separate tasks)
- Modifying `ModalConnectives` class definition
- Changing `diamond`/`neg`/`top`/`iff` from derived to primitive
- Adding natural deduction rules or non-Hilbert proof systems

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Truth lemma `.or` case backward direction is hard to prove | H | M | Follow PL MCS completeness pattern; use OrE + negation completeness |
| Notation conflict when `Proposition.and`/`.or` change from abbrev to constructor | M | L | Lean resolves by name not definition kind; research confirms compatibility |
| Truth lemma signature growth (6 to 12 axiom hypotheses) causes upstream type errors | M | L | Mechanical: add hypotheses and thread them through |
| 30 system files with identical changes risk copy-paste errors | M | M | Template-driven approach: verify one exemplar per truth lemma family, then replicate |
| `grind`/`simp` annotations on `Satisfies` break with new constructors | M | L | `@[scoped grind]` auto-picks up new cases; `and_iff`/`or_iff` become `Iff.rfl` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1 |
| 4 | 4 | 2, 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Core Definitions (Basic.lean) [COMPLETED]

**Goal**: Add `.and` and `.or` constructors to `Modal.Proposition`, update `Satisfies` with
structural clauses, register `HasAnd`/`HasOr` instances, and update satisfaction lemmas.

**Tasks**:
- [ ] Add `| and (phi1 phi2 : Proposition Atom)` constructor to `Proposition` inductive (before `box`)
- [ ] Add `| or (phi1 phi2 : Proposition Atom)` constructor to `Proposition` inductive (before `box`)
- [ ] Delete the `abbrev Proposition.or` definition (Lukasiewicz encoding, line 64-65)
- [ ] Delete the `abbrev Proposition.and` definition (Lukasiewicz encoding, line 68-69)
- [ ] Add `| .and phi1 phi2 => Satisfies m w phi1 /\ Satisfies m w phi2` clause to `Satisfies`
- [ ] Add `| .or phi1 phi2 => Satisfies m w phi1 \/ Satisfies m w phi2` clause to `Satisfies`
- [ ] Add `instance : HasAnd (Proposition Atom) where and := .and`
- [ ] Add `instance : HasOr (Proposition Atom) where or := .or`
- [ ] Update `Satisfies.and_iff` to become trivial (`Iff.rfl` or `by constructor <;> id`)
- [ ] Update `Satisfies.or_iff` to become trivial
- [ ] Update `Satisfies.iff` definition if needed (uses `.and` which is now a constructor)
- [ ] Verify `Satisfies.dual` still works (unfolds through diamond/neg, no and/or)
- [ ] Verify notation declarations (`scoped infix` for `/\` and `\/`) still work with constructors
- [ ] Run `lake build Cslib.Logics.Modal.Basic` to verify

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - Add constructors, update Satisfies, register instances

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` compiles without errors
- `sorry` count unchanged or decreased

---

### Phase 2: Semantic Infrastructure (Denotation, LogicalEquivalence) [COMPLETED]

**Goal**: Extend `Proposition.denotation`, `Context`, and `LogicallyEquivalent.congruence`
with and/or cases.

**Tasks**:
- [ ] Add `.and` and `.or` cases to `Proposition.denotation` in `Denotation.lean`:
  - `.and phi1 phi2 => phi1.denotation m ∩ phi2.denotation m`
  - `.or phi1 phi2 => phi1.denotation m ∪ phi2.denotation m`
- [ ] Add `.and` and `.or` induction cases to `satisfies_mem_denotation`
- [ ] Add 4 new constructors to `Proposition.Context` in `LogicalEquivalence.lean`:
  - `| andL (c : Context Atom) (phi : Proposition Atom)`
  - `| andR (phi : Proposition Atom) (c : Context Atom)`
  - `| orL (c : Context Atom) (phi : Proposition Atom)`
  - `| orR (phi : Proposition Atom) (c : Context Atom)`
- [ ] Add 4 cases to `Proposition.Context.fill`
- [ ] Add 4 induction cases to `LogicallyEquivalent.congruence`
- [ ] Run `lake build Cslib.Logics.Modal.Denotation Cslib.Logics.Modal.LogicalEquivalence`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Denotation.lean` - Add and/or denotation cases
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - Add and/or context constructors

**Verification**:
- Both files compile without errors
- `neg_denotation` proof still works (operates on negation, not and/or)

---

### Phase 3: FromPropositional.lean (sorry resolution) [COMPLETED]

**Goal**: Update `toModal` embedding to use native constructors and resolve 2 existing `sorry` entries.

**Tasks**:
- [ ] Update `PL.Proposition.toModal` and/or cases to use native constructors:
  - `.and phi1 phi2 => .and (phi1.toModal) (phi2.toModal)` (was Lukasiewicz)
  - `.or phi1 phi2 => .or (phi1.toModal) (phi2.toModal)` (was Lukasiewicz)
- [ ] Complete `modal_satisfies_toModal_iff_evaluate` `and` case (line 97, currently `sorry`):
  - Forward: unfold Satisfies, use `ih1.mp` and `ih2.mp` on both conjuncts
  - Backward: use `ih1.mpr` and `ih2.mpr`
- [ ] Complete `modal_satisfies_toModal_iff_evaluate` `or` case (line 101, currently `sorry`):
  - Forward: case split on `Or.inl`/`Or.inr`, use `ih1.mp` or `ih2.mp`
  - Backward: case split, use `ih1.mpr` or `ih2.mpr`
- [ ] Update docstring to reflect native constructors (remove Lukasiewicz encoding mention)
- [ ] Run `lake build Cslib.Logics.Modal.FromPropositional`
- [ ] Verify zero `sorry` in the file

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` - Update toModal, resolve 2 sorry

**Verification**:
- `lake build Cslib.Logics.Modal.FromPropositional` compiles
- `lean_verify` confirms no sorry/axiom usage

---

### Phase 4: ProofSystem Axiom Predicates and Instance Registration [COMPLETED]

**Goal**: Add 6 and/or axiom constructors to all 16 axiom predicates (ModalAxiom + 15 system
axioms) and register `HasAxiomAndI/AndE1/AndE2/OrI1/OrI2/OrE` instances for all 15 systems.

**Tasks**:
- [ ] Add 6 constructors to `ModalAxiom` in `DerivationTree.lean`:
  - `| andI (phi psi) : ModalAxiom (phi.imp (psi.imp (phi.and psi)))`
  - `| andE1 (phi psi) : ModalAxiom ((phi.and psi).imp phi)`
  - `| andE2 (phi psi) : ModalAxiom ((phi.and psi).imp psi)`
  - `| orI1 (phi psi) : ModalAxiom (phi.imp (phi.or psi))`
  - `| orI2 (phi psi) : ModalAxiom (psi.imp (phi.or psi))`
  - `| orE (phi psi chi) : ModalAxiom ((phi.imp chi).imp ((psi.imp chi).imp ((phi.or psi).imp chi)))`
- [ ] Add same 6 constructors to all 15 system axiom predicates:
  - `KAxiom`, `TAxiom`, `DAxiom`, `BAxiom`, `K4Axiom`, `K5Axiom`, `K45Axiom`, `KB5Axiom`,
    `D4Axiom`, `D5Axiom`, `D45Axiom`, `DBAxiom`, `TBAxiom`, `S4Axiom`, `S5Axiom`
  - Located in `Cslib/Logics/Modal/ProofSystem/Instances/*.lean`
- [ ] Register 6 `HasAxiom*` instances for each of the 15 Hilbert systems:
  - `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`
  - `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE`
  - Pattern: `instance : HasAxiomAndI Modal.HilbertX (F := Modal.Proposition Atom) where andI := ...`
- [ ] Run `lake build Cslib.Logics.Modal.ProofSystem.Instances`

**Timing**: 2.5 hours

**Depends on**: 1 (ModalAxiom uses `.and`/`.or` constructors), 3 is NOT a dependency here

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - Add 6 constructors to ModalAxiom
- `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` - Add 6 constructors to KAxiom + 6 instances
- `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` - Same pattern
- `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` - Same pattern (uses ModalAxiom already)

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.Instances` compiles
- Each axiom predicate has 6 new constructors
- Each system has 6 new `HasAxiom*` instances

---

### Phase 5: Metalogic Truth Lemmas and Supporting Infrastructure [COMPLETED]

**Goal**: Extend all 3 truth lemma families (`truth_lemma`, `k_truth_lemma`, `truth_lemma_d`)
with `.and`/`.or` cases and add 6 new axiom hypotheses to each.

**Tasks**:
- [ ] Add 6 axiom hypotheses to `truth_lemma` signature in `Completeness.lean`:
  - `h_andI`, `h_andE1`, `h_andE2`, `h_orI1`, `h_orI2`, `h_orE`
- [ ] Add `.and phi psi` case to `truth_lemma`:
  - Forward (Satisfies -> mem): from `phi in S` and `psi in S`, derive `phi.and psi in S`
    using `h_andI` + double MP
  - Backward (mem -> Satisfies): from `phi.and psi in S`, derive `phi in S` via `h_andE1`
    and `psi in S` via `h_andE2`, then recurse
- [ ] Add `.or phi psi` case to `truth_lemma`:
  - Forward: case split on `Or.inl`/`Or.inr`; use `h_orI1`/`h_orI2` + MP
  - Backward: use negation completeness -- either `phi in S` (done) or `neg phi in S`, then
    from `neg phi in S` and `phi.or psi in S` derive `psi in S` using `h_orE` + MP
- [ ] Add same 6 hypotheses and 2 cases to `k_truth_lemma` in `K/Completeness.lean`
- [ ] Add same 6 hypotheses and 2 cases to `truth_lemma_d` in `D/Completeness.lean`
- [ ] Verify that `k_derive_box_from_inconsistency` and `k_mcs_box_witness` do NOT need
  changes (they match on DerivationTree constructors, not Proposition)
- [ ] Verify `neg_consistent_of_not_derivable` does NOT need changes
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.Completeness`
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.Systems.K.Completeness`
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.Systems.D.Completeness`

**Timing**: 3 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - Add 6 hypotheses + 2 cases to `truth_lemma`
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` - Add 6 hypotheses + 2 cases to `k_truth_lemma`
- `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` - Add 6 hypotheses + 2 cases to `truth_lemma_d`

**Verification**:
- All 3 truth lemma files compile
- No new `sorry` introduced
- The `.or` backward case uses negation completeness correctly

---

### Phase 6: System Soundness and Completeness Files [COMPLETED]

**Goal**: Add 6 propositional axiom-sound cases to all 15 soundness files and thread 6 new
axiom hypotheses through all 15 completeness files.

**Tasks**:
- [ ] Add 6 cases to `k_axiom_sound` in `K/Soundness.lean` (exemplar):
  - `| andI phi psi => intro h1 h2; exact And.intro h1 h2`
  - `| andE1 phi psi => intro h; exact h.1`
  - `| andE2 phi psi => intro h; exact h.2`
  - `| orI1 phi psi => intro h; exact Or.inl h`
  - `| orI2 phi psi => intro h; exact Or.inr h`
  - `| orE phi psi chi => intro h1 h2 h3; exact h3.elim h1 h2`
- [ ] Replicate same 6 cases to remaining 14 soundness files:
  - T, D, B, K4, K5, K45, KB5, D4, D5, D45, DB, TB, S4, S5
  - All cases are frame-independent (pure propositional) and identical across systems
- [ ] Thread 6 new axiom constructor arguments through all 15 completeness files:
  - Systems using `truth_lemma` (S5, T, S4, TB): pass `(.andI _ _)`, `(.andE1 _ _)`,
    `(.andE2 _ _)`, `(.orI1 _ _)`, `(.orI2 _ _)`, `(.orE _ _ _)`
  - Systems using `k_truth_lemma` (K, B, K4, K5, K45, KB5): same pattern
  - Systems using `truth_lemma_d` (D, D4, D5, D45, DB): same pattern
- [ ] Build one exemplar per truth lemma family first (K, S5, D), verify, then replicate
- [ ] Run `lake build` for full project verification

**Timing**: 3.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K/Soundness.lean` - 6 new cases
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` - Thread 6 axiom args
- `Cslib/Logics/Modal/Metalogic/Systems/T/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/T/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` - Thread (already modified in Phase 5 for truth_lemma_d; here add the call-site args)
- `Cslib/Logics/Modal/Metalogic/Systems/B/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/B/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/K5/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/K5/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/S4/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/S4/Completeness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Soundness.lean` - Same pattern
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Completeness.lean` - Same pattern

**Verification**:
- `lake build` full project passes
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- All 15 soundness files have 6 new identical propositional cases
- All 15 completeness files thread 6 new axiom constructor arguments
- Zero `sorry` introduced; 2 existing `sorry` resolved (FromPropositional)

## Testing & Validation

- [ ] `lake build` -- full project compiles with zero errors
- [ ] `lake test` -- CslibTests suite passes
- [ ] `lake exe checkInitImports` -- all files import Cslib.Init
- [ ] `lake exe lint-style` -- style linting passes
- [ ] Verify zero `sorry` in `FromPropositional.lean` (previously 2)
- [ ] Verify `Satisfies.and_iff` and `Satisfies.or_iff` are trivial proofs
- [ ] Verify all 15 soundness theorems still hold (6 new propositional cases each)
- [ ] Verify all 15 completeness theorems still hold (6 new axiom hypothesis pass-through each)

## Artifacts & Outputs

- `specs/175_modal_and_or_propagation/plans/01_implementation-plan.md` (this file)
- `specs/175_modal_and_or_propagation/summaries/01_execution-summary.md` (after implementation)
- Modified files: ~55 Lean source files across 5 layers

## Rollback/Contingency

If implementation fails:
- `git stash` or `git checkout` to revert all changes
- The existing Lukasiewicz encoding is self-consistent; reverting to 4-constructor design is clean
- If specific truth lemma cases (especially `.or` backward) prove too difficult, they can be
  left as `sorry` with a `[PARTIAL]` status and addressed in a follow-up task
- Phase-by-phase commits enable partial rollback to any completed phase
