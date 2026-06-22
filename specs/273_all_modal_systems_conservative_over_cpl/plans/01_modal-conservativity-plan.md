# Implementation Plan: Conservative Extension of Modal Systems over CPL

- **Task**: 273 - all_modal_systems_conservative_over_cpl
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: None (all soundness proofs already exist for all 14 systems)
- **Research Inputs**: specs/273_all_modal_systems_conservative_over_cpl/reports/01_modal-conservativity-survey.md
- **Artifacts**: plans/01_modal-conservativity-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Create `ConservativeExtension.lean` files for all 14 remaining modal systems (T, B, D, K4, K5, K45, D4, D5, D45, DB, TB, KB5, S4, S5), proving that each is a conservative extension of CPL for propositional formulas. The K proof already exists and serves as the template. Research verified that all 14 proofs compile via `lean_run_code` using a universal model approach: construct `(Unit, fun _ _ => True, fun _ => v)` and discharge frame conditions with `trivial`/seriality. Each file is approximately 55-60 lines.

### Research Integration

The research report identified two groups:
- **Group A (9 systems)**: T, B, K4, K5, K45, TB, KB5, S4, S5 -- frame conditions (reflexivity, symmetry, transitivity, Euclideanness) are vacuously satisfied by `fun _ ... => trivial`.
- **Group B (5 systems)**: D, D4, D5, D45, DB -- require seriality proof `Relation.Serial` via `fun w => ⟨w, trivial⟩`.

Key finding: no `_soundness_derivable` wrappers are needed. The proof works directly with `_soundness` by destructuring `Derivable` into its `DerivationTree` and discharging the empty context with `fun _ h => nomatch h`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Modal metalogic module in the CSLib project structure. The modal systems' soundness proofs are listed under Completed in ROADMAP.md; conservative extension theorems complete the metalogic pipeline for these 14 systems.

## Goals & Non-Goals

**Goals**:
- Create 14 `ConservativeExtension.lean` files, one per modal system
- Each file proves: if `phi.toModal` is derivable in the system, then `phi` is CPL-derivable
- All files pass `lake build`, `lake exe checkInitImports`, `lake exe lint-style`
- Run `lake exe mk_all --module` to update barrel imports

**Non-Goals**:
- Adding `_soundness_derivable` wrappers to Soundness.lean files (research showed they are unnecessary)
- Modifying existing K/ConservativeExtension.lean
- Proving any new soundness results (all 14 already exist)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Soundness argument order varies by system | L | L | Research catalogued exact args for all 14; verified via lean_run_code |
| Line length exceeds 100 chars for S5 (3 frame condition proofs) | L | M | Break soundness call across multiple lines |
| `lake exe mk_all --module` fails or produces unexpected changes | L | L | Run after all 14 files created; review diff before committing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Group A -- Systems with Vacuous Frame Conditions [COMPLETED]

**Goal**: Create ConservativeExtension.lean for the 9 systems whose frame conditions are all satisfied by `trivial`: T, B, K4, K5, K45, TB, KB5, S4, S5.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/T/ConservativeExtension.lean`
  - Axiom: `TAxiom`, soundness args: `(fun _ => trivial)`
  - Theorem name: `t_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/B/ConservativeExtension.lean`
  - Axiom: `BAxiom`, soundness args: `(fun _ _ _ => trivial)`
  - Theorem name: `b_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/K4/ConservativeExtension.lean`
  - Axiom: `K4Axiom`, soundness args: `(fun _ _ _ _ _ => trivial)`
  - Theorem name: `k4_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/K5/ConservativeExtension.lean`
  - Axiom: `K5Axiom`, soundness args: `(fun _ _ _ _ _ => trivial)`
  - Theorem name: `k5_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/K45/ConservativeExtension.lean`
  - Axiom: `K45Axiom`, soundness args: `(fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)`
  - Theorem name: `k45_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/TB/ConservativeExtension.lean`
  - Axiom: `TBAxiom`, soundness args: `(fun _ => trivial) (fun _ _ _ => trivial)`
  - Theorem name: `tb_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/KB5/ConservativeExtension.lean`
  - Axiom: `KB5Axiom`, soundness args: `(fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial)`
  - Theorem name: `kb5_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/S4/ConservativeExtension.lean`
  - Axiom: `S4Axiom`, soundness args: `(fun _ => trivial) (fun _ _ _ _ _ => trivial)`
  - Theorem name: `s4_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/S5/ConservativeExtension.lean`
  - Axiom: `ModalAxiom`, soundness args: `(fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)`
  - Theorem name: `s5_conservative_extension`
- [ ] Verify all 9 files compile: `lake build Cslib.Logics.Modal.Metalogic.Systems.T.ConservativeExtension` (repeat for each)

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/T/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/B/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/K4/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/K5/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/K45/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/TB/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/S4/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/S5/ConservativeExtension.lean` - new file

**Verification**:
- Each file compiles without errors via `lake build`
- Each file follows the K pattern structure (copyright, module, imports, docstring, expose section, namespace, theorem, end)

---

### Phase 2: Group B -- Systems Requiring Seriality [COMPLETED]

**Goal**: Create ConservativeExtension.lean for the 5 systems that require a `Relation.Serial` proof: D, D4, D5, D45, DB.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/D/ConservativeExtension.lean`
  - Axiom: `DAxiom`, soundness args: `⟨fun w => ⟨w, trivial⟩⟩`
  - Theorem name: `d_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/D4/ConservativeExtension.lean`
  - Axiom: `D4Axiom`, soundness args: `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial)`
  - Theorem name: `d4_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/D5/ConservativeExtension.lean`
  - Axiom: `D5Axiom`, soundness args: `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial)`
  - Theorem name: `d5_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/D45/ConservativeExtension.lean`
  - Axiom: `D45Axiom`, soundness args: `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)`
  - Theorem name: `d45_conservative_extension`
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/DB/ConservativeExtension.lean`
  - Axiom: `DBAxiom`, soundness args: `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ => trivial)`
  - Theorem name: `db_conservative_extension`
- [ ] Verify all 5 files compile: `lake build Cslib.Logics.Modal.Metalogic.Systems.D.ConservativeExtension` (repeat for each)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/D/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/D4/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/D5/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/D45/ConservativeExtension.lean` - new file
- `Cslib/Logics/Modal/Metalogic/Systems/DB/ConservativeExtension.lean` - new file

**Verification**:
- Each file compiles without errors via `lake build`
- Seriality proof `⟨fun w => ⟨w, trivial⟩⟩` correctly provides `Relation.Serial` instance

---

### Phase 3: Barrel Update and CI Verification [COMPLETED]

**Goal**: Update barrel imports, run full CI pipeline to verify all 14 files integrate correctly.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` with 14 new module imports
- [ ] Run `lake build` to verify full project compiles
- [ ] Run `lake exe checkInitImports` to verify all files have correct imports
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake test` to verify no regressions
- [ ] Review that each theorem name follows the naming convention (`{sys}_conservative_extension`)

**Timing**: 0.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib.lean` - updated by `mk_all` to include 14 new imports

**Verification**:
- All CI commands pass with exit code 0
- `Cslib.lean` contains 14 new import lines for ConservativeExtension modules
- No warnings or errors in build output

## Testing & Validation

- [ ] Each of the 14 ConservativeExtension.lean files compiles individually
- [ ] `lake build` succeeds for the full project
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes with no regressions
- [ ] Each theorem has the correct type signature: `Derivable (@{SysAxiom} Atom) phi.toModal -> PL.Derivable PropositionalAxiom phi`

## Artifacts & Outputs

- 14 new files: `Cslib/Logics/Modal/Metalogic/Systems/{System}/ConservativeExtension.lean`
- Updated barrel file: `Cslib.lean`
- Plan: `specs/273_all_modal_systems_conservative_over_cpl/plans/01_modal-conservativity-plan.md`

## Rollback/Contingency

Delete the 14 new ConservativeExtension.lean files and revert `Cslib.lean` via `git checkout -- Cslib.lean`. No existing files are modified, so rollback is clean deletion.
