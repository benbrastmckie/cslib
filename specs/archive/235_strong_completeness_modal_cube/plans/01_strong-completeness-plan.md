# Implementation Plan: Task #235 -- Strong Completeness for Modal Cube

- **Task**: 235 - Upgrade weak completeness to strong completeness for all 15 modal cube systems
- **Status**: [COMPLETED]
- **Effort**: 8 hours
- **Dependencies**: None (all building blocks already exist)
- **Research Inputs**: specs/235_strong_completeness_modal_cube/reports/01_strong-completeness-research.md
- **Artifacts**: plans/01_strong-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Upgrade the 15 modal cube systems (K, T, B, D, S4, S5, K4, K5, K45, KB5, D4, D5, D45, DB, TB)
from weak completeness (validity implies derivability from empty context) to strong completeness
(semantic entailment from a set of premises implies set-derivability). The proof strategy mirrors
the existing propositional strong completeness in `StrongCompleteness.lean`: define
`ModalSetDerivable` and `ModalSemanticEntails`, prove a key consistency lemma
(`modal_not_SetDerivable_union_neg_consistent`), then instantiate per system. All building
blocks (Lindenbaum's lemma, deduction theorem with member removal, truth lemmas, canonical frame
properties) already exist.

### Research Integration

The research report (01_strong-completeness-research.md) confirmed:
- The propositional `StrongCompleteness.lean` (562 lines) serves as the complete template
- All 15 per-system soundness theorems already handle list contexts (strong soundness structurally)
- Three truth lemma families cover the 15 systems: `truth_lemma` (T-group), `k_truth_lemma` (K-group), `truth_lemma_d` (D-group)
- The `deductionWithMem` and `deductionTheorem` for modal `DerivationTree` already exist
- Estimated total: ~1100-1230 new lines across 16 files

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the CSLib Roadmap by completing the modal metalogic infrastructure. Strong completeness is a standard result expected in any complete formalization of modal logic.

## Goals & Non-Goals

**Goals**:
- Define `ModalSetDerivable` and `ModalSemanticEntails` (parameterized over frame class) in a shared file
- Prove the key consistency lemma `modal_not_SetDerivable_union_neg_consistent`
- Prove `{sys}_strong_soundness`, `{sys}_strong_completeness`, `{sys}_strong_completeness_iff`, and `{sys}_compactness` for all 15 systems
- Update the `Metalogic.lean` barrel import file with all new `StrongCompleteness.lean` modules
- All new declarations have docstrings (docBlame linter compliance)

**Non-Goals**:
- Refactoring existing weak completeness proofs (they remain unchanged)
- Proving decidability or finite model property results
- Adding automation or tactic-based proof shortcuts

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism mismatch in ModalSemanticEntails | H | L | Follow exact universe annotation pattern from existing completeness theorems (`universe u`, `Type u` for World) |
| DNE helper needs adaptation for modal DerivationTree | M | L | Modal DerivationTree has same propositional constructors; `necessitation` case is vacuous (empty context) |
| Per-system frame condition encoding mismatches | M | L | Copy exact frame condition signatures from existing `{sys}_completeness` theorems |
| Build time for 16 new files | L | M | Verify with scoped `lake build Module.Name` per phase, full `lake build` only at end |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Shared Infrastructure [COMPLETED]

**Goal**: Create the shared `StrongCompleteness.lean` file with `ModalSetDerivable`, `ModalSemanticEntails`, basic lemmas, DNE helper, and the key consistency lemma.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean`
- [x] Define `ModalSetDerivable Axioms Gamma phi` using `modalDerivationSystem`
- [x] Define `ModalSemanticEntails FC Gamma phi` parameterized over frame class predicate `FC`
- [x] Prove `ModalSetDerivable_of_mem` (membership implies set-derivability)
- [x] Prove `ModalSetDerivable_weakening` (monotonicity in premise set)
- [x] Prove `ModalSetDerivable_of_Derivable` (theorems are set-derivable from any set)
- [x] Prove `ModalSetDerivable_empty_iff` (empty set equivalence with `Derivable`)
- [x] Prove `ModalSemanticEntails_of_Valid` (validity implies semantic entailment from any set, parameterized over frame class)
- [x] Implement `modal_dne_from_neg_neg` (DNE helper adapting propositional version to modal `DerivationTree`)
- [x] Prove `modal_not_SetDerivable_union_neg_consistent` (key consistency lemma: if phi not set-derivable from Gamma, then Gamma union {neg phi} is `SetConsistent Axioms`)
- [x] Add docstrings to all declarations
- [x] Verify: `lake build Cslib.Logics.Modal.Metalogic.StrongCompleteness`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean` -- new file (~150 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.StrongCompleteness` compiles without errors
- All 10 declarations have docstrings

---

### Phase 2: K-Group Strong Completeness (K, B, K4, K5, K45, KB5) [COMPLETED]

**Goal**: Create `StrongCompleteness.lean` for the 6 systems that use `k_truth_lemma` (systems without axiom T or D).

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/K/StrongCompleteness.lean`
  - [x] `k_strong_soundness`: unfold `ModalSetDerivable`, apply `k_soundness`
  - [x] `k_strong_completeness`: contrapositive via `modal_not_SetDerivable_union_neg_consistent` + `modal_lindenbaum` + `k_truth_lemma`
  - [x] `k_strong_completeness_iff`: biconditional wrapper
  - [x] `k_compactness`: corollary from strong soundness + completeness
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/B/StrongCompleteness.lean`
  - [x] `b_strong_soundness`, `b_strong_completeness`, `b_strong_completeness_iff`, `b_compactness`
  - [x] Frame condition: `∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁` (symmetric)
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/K4/StrongCompleteness.lean`
  - [x] `k4_strong_soundness`, `k4_strong_completeness`, `k4_strong_completeness_iff`, `k4_compactness`
  - [x] Frame condition: `∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃` (transitive)
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/K5/StrongCompleteness.lean`
  - [x] `k5_strong_soundness`, `k5_strong_completeness`, `k5_strong_completeness_iff`, `k5_compactness`
  - [x] Frame condition: `∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃` (Euclidean)
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/K45/StrongCompleteness.lean`
  - [x] `k45_strong_soundness`, `k45_strong_completeness`, `k45_strong_completeness_iff`, `k45_compactness`
  - [x] Frame conditions: transitive + Euclidean
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/KB5/StrongCompleteness.lean`
  - [x] `kb5_strong_soundness`, `kb5_strong_completeness`, `kb5_strong_completeness_iff`, `kb5_compactness`
  - [x] Frame conditions: symmetric + Euclidean
- [x] Add docstrings to all declarations in all 6 files
- [x] Verify: `lake build` for each new module

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/B/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/K4/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/K5/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/K45/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/StrongCompleteness.lean` -- new file (~65 lines)

**Verification**:
- Each module builds individually without errors
- All declarations have docstrings

**Key patterns per file**:
- Import: existing `{Sys}/Completeness`, `{Sys}/Soundness`, and `StrongCompleteness` (shared)
- `{sys}_strong_soundness`: Unfold `ModalSetDerivable`, extract `L`, `hL_sub`, `hL_deriv`, apply `{sys}_soundness` with context `(fun psi hpsi => h_sat psi (hL_sub psi hpsi))`
- `{sys}_strong_completeness`: `by_contra h_not`, `modal_not_SetDerivable_union_neg_consistent`, `modal_lindenbaum`, construct canonical world, apply `k_truth_lemma` + canonical frame properties, derive contradiction
- K is special: `ModalSemanticEntails` uses `FC := fun _ => True` (no frame condition)

---

### Phase 3: T-Group Strong Completeness (T, S4, S5, TB) [COMPLETED]

**Goal**: Create `StrongCompleteness.lean` for the 4 systems that use `truth_lemma` (systems with axiom T, which provides reflexivity).

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/T/StrongCompleteness.lean`
  - [x] `t_strong_soundness`, `t_strong_completeness`, `t_strong_completeness_iff`, `t_compactness`
  - [x] Frame condition: `∀ w, m.r w w` (reflexive)
  - [x] Uses `truth_lemma` (not `k_truth_lemma`), via `t_truth_lemma` wrapper
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/S4/StrongCompleteness.lean`
  - [x] `s4_strong_soundness`, `s4_strong_completeness`, `s4_strong_completeness_iff`, `s4_compactness`
  - [x] Frame conditions: reflexive + transitive
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean`
  - [x] `s5_strong_soundness`, `s5_strong_completeness`, `s5_strong_completeness_iff`, `s5_compactness`
  - [x] Frame conditions: reflexive + transitive + Euclidean
  - [x] Uses `ModalAxiom` (the S5 axiom predicate)
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/TB/StrongCompleteness.lean`
  - [x] `tb_strong_soundness`, `tb_strong_completeness`, `tb_strong_completeness_iff`, `tb_compactness`
  - [x] Frame conditions: reflexive + symmetric
- [x] Add docstrings to all declarations in all 4 files
- [x] Verify: `lake build` for each new module

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/T/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/S4/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean` -- new file (~65 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/TB/StrongCompleteness.lean` -- new file (~65 lines)

**Verification**:
- Each module builds individually without errors
- All declarations have docstrings

**Key patterns per file**:
- T-group systems use `truth_lemma` (or `t_truth_lemma` wrapper) instead of `k_truth_lemma`
- `truth_lemma` requires `h_T` (axiom T for reflexivity) in addition to implyK, implyS, efq, peirce, K
- Canonical frame properties: `canonical_refl` (from T), `canonical_trans` (from 4), `canonical_eucl` (from B+T+4+K), `canonical_symm` (from B+K)

---

### Phase 4: D-Group Strong Completeness (D, D4, D5, D45, DB) [COMPLETED]

**Goal**: Create `StrongCompleteness.lean` for the 5 systems that use `truth_lemma_d` (systems with axiom D but not T, providing seriality).

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean`
  - [x] `d_strong_soundness`, `d_strong_completeness`, `d_strong_completeness_iff`, `d_compactness`
  - [x] Frame condition: `Relation.Serial m.r`
  - [x] Uses `truth_lemma_d` + `canonical_serial`
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean`
  - [x] `d4_strong_soundness`, `d4_strong_completeness`, `d4_strong_completeness_iff`, `d4_compactness`
  - [x] Frame conditions: serial + transitive
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean`
  - [x] `d5_strong_soundness`, `d5_strong_completeness`, `d5_strong_completeness_iff`, `d5_compactness`
  - [x] Frame conditions: serial + Euclidean
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean`
  - [x] `d45_strong_soundness`, `d45_strong_completeness`, `d45_strong_completeness_iff`, `d45_compactness`
  - [x] Frame conditions: serial + transitive + Euclidean
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean`
  - [x] `db_strong_soundness`, `db_strong_completeness`, `db_strong_completeness_iff`, `db_compactness`
  - [x] Frame conditions: serial + symmetric
- [x] Add docstrings to all declarations in all 5 files
- [x] Verify: `lake build` for each new module

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean` -- new file (~70 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean` -- new file (~70 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean` -- new file (~70 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean` -- new file (~70 lines)
- `Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean` -- new file (~70 lines)

**Verification**:
- Each module builds individually without errors
- All declarations have docstrings

**Key patterns per file**:
- D-group systems use `truth_lemma_d` which requires `h_D` (axiom D for seriality) instead of `h_T`
- Frame condition `Relation.Serial m.r` requires `⟨constructor; intro S; exact canonical_serial ... S⟩`
- `canonical_serial` uses efq + K + D axioms

---

### Phase 5: Module Updates and Final Verification [COMPLETED]

**Goal**: Update barrel import file, run CI verification pipeline, ensure all 16 new files are registered.

**Tasks**:
- [x] Update `Cslib/Logics/Modal/Metalogic.lean` to add 16 new `public import` lines (1 shared + 15 per-system `StrongCompleteness`)
- [x] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [x] Run `lake build` (full project build)
- [x] Run `lake exe checkInitImports` (verify all files import `Cslib.Init`)
- [x] Run `lake exe lint-style` (style linting)
- [x] Verify no `sorry` in any new file: `grep -r "sorry" Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean Cslib/Logics/Modal/Metalogic/Systems/*/StrongCompleteness.lean`

**Timing**: 1 hour

**Depends on**: 2, 3, 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add 16 import lines
- `Cslib.lean` -- auto-updated by `lake exe mk_all --module`

**Verification**:
- `lake build` succeeds (full project)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- No `sorry` in any new file
- All 16 new modules are importable via `Cslib.Logics.Modal.Metalogic`

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Metalogic.StrongCompleteness` compiles (shared infrastructure)
- [x] All 15 per-system `StrongCompleteness.lean` files compile individually
- [x] `lake build` (full project) succeeds
- [x] `lake exe checkInitImports` passes
- [x] `lake exe lint-style` passes
- [x] No `sorry` in any new file
- [x] All declarations have docstrings (docBlame compliance)
- [x] Strong completeness theorems have correct type signatures matching strong soundness duals

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean` -- shared definitions and key consistency lemma
- `Cslib/Logics/Modal/Metalogic/Systems/{K,T,B,D,S4,S5,K4,K5,K45,KB5,D4,D5,D45,DB,TB}/StrongCompleteness.lean` -- per-system strong completeness (15 files)
- `Cslib/Logics/Modal/Metalogic.lean` -- updated barrel import
- `specs/235_strong_completeness_modal_cube/plans/01_strong-completeness-plan.md` -- this plan

## Rollback/Contingency

All changes are new files only; no existing files are modified except the barrel import
`Metalogic.lean`. If the implementation fails:
1. Delete all new `StrongCompleteness.lean` files
2. Revert the import additions in `Metalogic.lean`
3. Run `lake exe mk_all --module` to regenerate `Cslib.lean`
4. The codebase returns to its pre-task state with zero impact on existing proofs
