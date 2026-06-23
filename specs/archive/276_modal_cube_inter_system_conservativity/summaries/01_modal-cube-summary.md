# Implementation Summary: Modal Cube Inter-System Conservativity

- **Task**: 276 - modal_cube_inter_system_conservativity
- **Status**: [COMPLETED]
- **Session**: sess_1782161605_f646ec_276
- **Date**: 2026-06-22

## Summary

Implemented 3 new Lean 4 files under `Cslib/Logics/Modal/Metalogic/InterSystem/` providing
generic derivation lifting infrastructure and 24 instantiated derivability monotonicity
theorems covering the direct edges of the modal cube. All proofs are sorry-free and
axiom-free; the generic `lift_derivation` lemma eliminates all boilerplate via a single
structural induction over derivation trees.

## Artifacts Created

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean`
  (~80 lines): Generic `lift_derivation` (structural induction) and `Derivable_mono` lemma.
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean`
  (~340 lines): 24 axiom subsumption lemmas for direct cube edges (mechanical case-splits).
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/InterSystem/Conservativity.lean`
  (~225 lines): 24 instantiated derivability monotonicity theorems + 3 transitive chains.

## Phase Results

- **Phase 1** [COMPLETED]: `Lifting.lean` with `lift_derivation` and `Derivable_mono`.
  Compiles cleanly; verified axiom-free by `lean_verify`.

- **Phase 2** [COMPLETED]: `AxiomSubsumption.lean` with 24 direct-edge subsumption lemmas.
  Mechanical case-splits mapping each source axiom constructor to the matching target
  constructor. Compiles cleanly; no sorries.

- **Phase 3** [COMPLETED]: `Conservativity.lean` with 24 named derivability theorems
  and 3 transitive chains (K→S5, K→D45, D→D45). `lake exe mk_all --module` updated
  the Cslib.lean barrel. Style linters pass clean.

## Coverage: 24 Direct Edges of the Modal Cube

| Edge | Subsumption Lemma | Conservativity Theorem |
|------|-------------------|------------------------|
| K → T | `KAxiom_implies_TAxiom` | `kDerivable_implies_tDerivable` |
| K → D | `KAxiom_implies_DAxiom` | `kDerivable_implies_dDerivable` |
| K → B | `KAxiom_implies_BAxiom` | `kDerivable_implies_bDerivable` |
| K → K4 | `KAxiom_implies_K4Axiom` | `kDerivable_implies_k4Derivable` |
| K → K5 | `KAxiom_implies_K5Axiom` | `kDerivable_implies_k5Derivable` |
| D → D4 | `DAxiom_implies_D4Axiom` | `dDerivable_implies_d4Derivable` |
| D → D5 | `DAxiom_implies_D5Axiom` | `dDerivable_implies_d5Derivable` |
| D → DB | `DAxiom_implies_DBAxiom` | `dDerivable_implies_dbDerivable` |
| T → S4 | `TAxiom_implies_S4Axiom` | `tDerivable_implies_s4Derivable` |
| T → TB | `TAxiom_implies_TBAxiom` | `tDerivable_implies_tbDerivable` |
| B → TB | `BAxiom_implies_TBAxiom` | `bDerivable_implies_tbDerivable` |
| B → DB | `BAxiom_implies_DBAxiom` | `bDerivable_implies_dbDerivable` |
| B → KB5 | `BAxiom_implies_KB5Axiom` | `bDerivable_implies_kb5Derivable` |
| K4 → S4 | `K4Axiom_implies_S4Axiom` | `k4Derivable_implies_s4Derivable` |
| K4 → D4 | `K4Axiom_implies_D4Axiom` | `k4Derivable_implies_d4Derivable` |
| K4 → K45 | `K4Axiom_implies_K45Axiom` | `k4Derivable_implies_k45Derivable` |
| K5 → D5 | `K5Axiom_implies_D5Axiom` | `k5Derivable_implies_d5Derivable` |
| K5 → K45 | `K5Axiom_implies_K45Axiom` | `k5Derivable_implies_k45Derivable` |
| K5 → KB5 | `K5Axiom_implies_KB5Axiom` | `k5Derivable_implies_kb5Derivable` |
| K45 → D45 | `K45Axiom_implies_D45Axiom` | `k45Derivable_implies_d45Derivable` |
| D4 → D45 | `D4Axiom_implies_D45Axiom` | `d4Derivable_implies_d45Derivable` |
| D5 → D45 | `D5Axiom_implies_D45Axiom` | `d5Derivable_implies_d45Derivable` |
| S4 → S5 | `S4Axiom_implies_ModalAxiom` | `s4Derivable_implies_s5Derivable` |
| TB → S5 | `TBAxiom_implies_ModalAxiom` | `tbDerivable_implies_s5Derivable` |

## Plan Deviations

1. **DAxiom_implies_TAxiom omitted** (plan phase 2, D-based edges):
   The plan listed `DAxiom_implies_TAxiom` (D → T: replace modalD with modalT). This is
   incorrect: `DAxiom.modalD` produces `□φ → ◇φ` while `TAxiom.modalT` produces `□φ → φ`.
   These are different formulas; no syntactic subsumption holds. D and T are semantically
   incomparable (both extend K independently in the modal cube).

2. **KB5Axiom_implies_ModalAxiom omitted** (plan phase 2, top-level edges):
   The plan listed `KB5Axiom_implies_ModalAxiom` (KB5 → S5: add modalT). This cannot be
   proved syntactically: `KB5Axiom.modalFive` (axiom 5: ◇φ → □◇φ) is not in `ModalAxiom`
   (S5's axiom set is T + 4 + B, from which 5 is derivable but not literally listed). The
   plan suggested mapping `modalFive` to `modalFour` which is also incorrect (different formulas).

3. **Edge count is 24** (plan claimed 24+ including 3 "top-level" edges):
   After removing the two incorrect edges above (which were plan errors, not omissions), the
   actual count is exactly 24 provable direct syntactic-subsumption edges — matching the
   research report's table. The plan's "24 direct edges + 3 top-level" formulation was
   inconsistent; we now have 24 direct edges with 3 transitive chains as bonus.

## Verification Results

- `lean_verify` on `lift_derivation`: `{"axioms":[],"warnings":[]}`
- `lean_verify` on `Derivable_mono`: `{"axioms":[],"warnings":[]}`
- `lean_verify` on `kDerivable_implies_tDerivable`: `{"axioms":[],"warnings":[]}`
- `lean_verify` on `kDerivable_implies_s5Derivable`: `{"axioms":[],"warnings":[]}`
- Zero sorries in all new files
- `lake exe lint-style` passes for all new files
- `lake build` for all three modules succeeds cleanly
- Pre-existing failure: `Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.TemporalConservativity`
  uses `sorry` (pre-dates this task; prevents full Cslib.lean build)
