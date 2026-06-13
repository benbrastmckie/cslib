# Implementation Plan: Propagate Hybrid Five-Primitive Design to Temporal Layer

- **Task**: 176 - Propagate the hybrid five-primitive design to the Temporal layer
- **Status**: [IN PROGRESS]
- **Effort**: 8 hours
- **Dependencies**: Task 173 (completed)
- **Research Inputs**: specs/176_temporal_and_or_propagation/reports/01_temporal-propagation-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Upgrade `Cslib.Logic.Temporal.Formula` from a five-primitive inductive `{atom, bot, imp, untl, snce}` to a seven-primitive `{atom, bot, imp, and, or, untl, snce}` design, mirroring what task 173 accomplished for `Cslib.Logic.PL.Proposition`. Currently `and` and `or` are `abbrev` definitions that encode through `imp`/`bot`; making them primitive constructors requires updating 10 of 37 Temporal files (approximately 640 lines of changes). The change simplifies the embedding from Propositional to Temporal (now homomorphic) and provides direct semantic clauses for conjunction and disjunction.

### Research Integration

The research report (01_temporal-propagation-research.md) identified: (1) exactly 10 files needing changes across Syntax, Semantics, ProofSystem, and Metalogic layers; (2) the heaviest change is `Syntax/Formula.lean` at approximately 300 lines including `encodeNat_injective` (7x7 = 49 case pairs); (3) Chronicle files (6,800+ lines) use `Formula.and`/`Formula.or` as term constructors only (not pattern matching), so they require no changes; (4) `TruthLemma.lean` needs 2 new structural induction cases backed by MCS helper lemmas; (5) 6 new axiom constructors are needed (and_intro, and_elim_left, and_elim_right, or_intro_left, or_intro_right, or_elim); (6) no blockers -- PR #642 and task 173 are both merged.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Temporal module toward structural parity with the Propositional layer (five-primitive design). It supports the Temporal metalogic completeness infrastructure listed under "Remaining" in the roadmap (Dense, Discrete, and Continuous temporal completeness).

## Goals & Non-Goals

**Goals**:
- Add `and` and `or` as primitive constructors to `Temporal.Formula`
- Update all structural functions that pattern-match on `Formula` (encodeNat, complexity, temporalDepth, countImplications, swapTemporal, atoms, beq_refl, eq_of_beq, needsPositiveHypotheses, subformulas)
- Add direct `and`/`or` clauses to `Satisfies` with simp lemmas
- Add 6 new axiom constructors with soundness proofs
- Add MCS helper lemmas and TruthLemma induction cases
- Simplify `FromPropositional.toTemporal` to a homomorphic mapping
- Pass full CI pipeline (lake build, lake test, checkInitImports, lint-style)

**Non-Goals**:
- Promoting `neg`, `top`, or `iff` to primitive constructors (they remain derived)
- Modifying Chronicle construction files (RRelation, PointInsertion, CounterexampleElimination) -- research confirmed no changes needed
- Extending dense/discrete completeness (future tasks)
- Modifying Bimodal layer (separate future task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `encodeNat_injective` proof explosion (49 vs 25 case pairs) | H | H | Follow existing discrimination pattern mechanically; budget extra time for this single proof |
| Existing axiom soundness proofs break due to `sat_and_iff`/`sat_or_iff` changes | M | M | After adding direct Satisfies clauses, existing `sat_and_iff`/`sat_or_iff` become trivial Iff.rfl -- verify and simplify |
| Chronicle files relying on definitional unfolding of `Formula.and` to `imp`/`bot` | H | L | Research found no such pattern; verify with scoped `lake build` after Phase 1 |
| Complexity function ordering -- derived temporal patterns (G, H, etc.) must match before generic and/or | M | L | Place and/or cases after all derived-pattern cases, before generic imp/untl/snce cases |
| DenseSoundness/DenseCompleteness breakage from axiom changes | M | L | New axioms use `minFrameClass = .Base`, compatible with all frame classes |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are fully sequential: each layer depends on the previous layer compiling correctly.

---

### Phase 1: Syntax Foundation [COMPLETED]

**Goal**: Add `and`/`or` constructors to `Formula` and update all structural functions and proofs in the Syntax layer.

**Tasks**:
- [ ] Add `.and` and `.or` constructors to `Formula` inductive (between `imp` and `untl`)
- [ ] Remove `abbrev Formula.and` and `abbrev Formula.or` (constructor replaces them)
- [ ] Update `Formula.iff` to use the new `.and` constructor directly
- [ ] Add `instance : HasAnd (Formula Atom)` and `instance : HasOr (Formula Atom)` (if not already covered by TemporalConnectives)
- [ ] Update `encodeNat`: add `.and` (pair 5) and `.or` (pair 6) cases; renumber `.untl` and `.snce` if needed
- [ ] Update `encodeNat_injective`: add discrimination cases for all new constructor pairs (from 25 to 49 cases)
- [ ] Update `complexity`: add `.and`/`.or` cases (positioned after derived-pattern cases)
- [ ] Update `temporalDepth`: add `.and`/`.or` cases (max of children)
- [ ] Update `countImplications`: add `.and`/`.or` cases (sum of children, no +1)
- [ ] Update `swapTemporal`: add `.and`/`.or` cases (recursive structural)
- [ ] Update `swapTemporal_involution`: add `.and`/`.or` induction cases
- [ ] Update `atoms` function: add `.and`/`.or` cases (union of children)
- [ ] Update `atoms_swapTemporal`: add `.and`/`.or` cases
- [ ] Update `needsPositiveHypotheses`: add `.and _ _ => true` and `.or _ _ => true` plus simp lemmas
- [ ] Update `beq_refl` and `eq_of_beq`: add `.and`/`.or` cases mirroring `imp`/`untl`/`snce` pattern
- [ ] Update `Subformulas.lean`: add `.and`/`.or` cases to `subformulas`, `subformulaCount`, and membership lemmas
- [ ] Verify `BigConj.lean` compiles without changes (it calls `.and` which is now a constructor)
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` and `lake build Cslib.Logics.Temporal.Syntax.Subformulas`

**Timing**: 3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Add constructors, update all structural functions and proofs (~300 lines)
- `Cslib/Logics/Temporal/Syntax/Subformulas.lean` - Add and/or cases to subformula functions and lemmas (~40 lines)

**Files to verify (no changes expected)**:
- `Cslib/Logics/Temporal/Syntax/BigConj.lean` - Verify compiles unchanged
- `Cslib/Logics/Temporal/Syntax/Context.lean` - Verify compiles unchanged

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` succeeds
- `lake build Cslib.Logics.Temporal.Syntax.Subformulas` succeeds
- `lake build Cslib.Logics.Temporal.Syntax.BigConj` succeeds (no changes)

---

### Phase 2: Semantics and ProofSystem [NOT STARTED]

**Goal**: Add direct `and`/`or` satisfaction clauses and 6 new axiom constructors with HasAxiom instances.

**Tasks**:
- [ ] Add `and`/`or` cases to `Satisfies` definition in `Satisfies.lean`:
  - `.and phi psi => Satisfies M t phi /\ Satisfies M t psi`
  - `.or phi psi => Satisfies M t phi \/ Satisfies M t psi`
- [ ] Add simp lemmas `and_iff` and `or_iff` for the new satisfaction clauses
- [ ] Verify or simplify existing `sat_and_iff`/`sat_or_iff` (should become trivial after direct clauses)
- [ ] Add 6 new axiom constructors to `Axioms.lean` (and_intro, and_elim_left, and_elim_right, or_intro_left, or_intro_right, or_elim) with `minFrameClass = .Base`
- [ ] Register `HasAxiom` instances for new axioms in `Instances.lean`
- [ ] Update `TemporalBXHilbert` bundle if it extends `HasAnd`/`HasOr` axiom requirements
- [ ] Run scoped build for Semantics and ProofSystem modules

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` - Add and/or clauses, simp lemmas (~40 lines)
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - Add 6 axiom constructors (~50 lines)
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - Register HasAxiom instances (~30 lines)

**Files to verify (no changes expected)**:
- `Cslib/Logics/Temporal/Semantics/Model.lean`
- `Cslib/Logics/Temporal/Semantics/Validity.lean`
- `Cslib/Logics/Temporal/ProofSystem/Derivation.lean`
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean`

**Verification**:
- `lake build Cslib.Logics.Temporal.Semantics.Satisfies` succeeds
- `lake build Cslib.Logics.Temporal.ProofSystem.Axioms` succeeds
- `lake build Cslib.Logics.Temporal.ProofSystem.Instances` succeeds

---

### Phase 3: Soundness Layer [NOT STARTED]

**Goal**: Add axiom soundness proofs for 6 new axioms and update `swapTemporal_dual` with and/or cases.

**Tasks**:
- [ ] Add soundness cases for `and_intro`, `and_elim_left`, `and_elim_right`, `or_intro_left`, `or_intro_right`, `or_elim` in `axiom_sound` (Soundness.lean)
- [ ] Update `swapTemporal_dual` with `.and`/`.or` cases
- [ ] Simplify or update `sat_and_iff`/`sat_or_iff` -- these should become trivial wrappers around the direct Satisfies clauses
- [ ] Add soundness cases for new axioms in `DenseSoundness.lean` (axiom_sound_dense) -- these are trivial since all new axioms have `minFrameClass = .Base`
- [ ] Run scoped build for Soundness and DenseSoundness

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` - Add 6 axiom soundness cases, update swapTemporal_dual (~80 lines)
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` - Propagate new axiom cases (~20 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Soundness` succeeds
- `lake build Cslib.Logics.Temporal.Metalogic.DenseSoundness` succeeds

---

### Phase 4: TruthLemma and MCS Helpers [NOT STARTED]

**Goal**: Add MCS conjunction/disjunction properties and extend the truth lemma structural induction with and/or cases.

**Tasks**:
- [ ] Add `mcs_and_iff` to `MCS.lean`: `Formula.and phi psi in M <-> phi in M /\ psi in M` (using and_intro, and_elim_left, and_elim_right axioms + MCS closed-under-derivation)
- [ ] Add `mcs_or_iff` to `MCS.lean`: `Formula.or phi psi in M <-> phi in M \/ psi in M` (using or_intro_left, or_intro_right, or_elim axioms + MCS maximality)
- [ ] Add `.and` induction case to `chronicle_truth_lemma` in `TruthLemma.lean` using `mcs_and_iff` and recursive hypotheses
- [ ] Add `.or` induction case to `chronicle_truth_lemma` in `TruthLemma.lean` using `mcs_or_iff` and recursive hypotheses
- [ ] Run scoped build for MCS and TruthLemma

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` - Add mcs_and_iff and mcs_or_iff helper lemmas (~40 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` - Add and/or induction cases (~40 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.MCS` succeeds
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma` succeeds
- `lake build Cslib.Logics.Temporal.Metalogic.Completeness` succeeds (downstream)

---

### Phase 5: FromPropositional and CI Verification [NOT STARTED]

**Goal**: Simplify the propositional embedding to a homomorphic mapping and verify the full CI pipeline.

**Tasks**:
- [ ] Update `toTemporal` in `FromPropositional.lean`:
  - Change `.and phi1 phi2 => .imp (.imp phi1.toTemporal (.imp phi2.toTemporal .bot)) .bot` to `.and phi1 phi2 => .and phi1.toTemporal phi2.toTemporal`
  - Change `.or phi1 phi2 => .imp (.imp phi1.toTemporal .bot) phi2.toTemporal` to `.or phi1 phi2 => .or phi1.toTemporal phi2.toTemporal`
- [ ] Update simp lemmas for `toTemporal` if any reference the old encoding
- [ ] Run full `lake build` (entire project)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Temporal/FromPropositional.lean` - Switch to homomorphic and/or embedding (~20 lines)

**Verification**:
- `lake build` succeeds (full project)
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Syntax.Formula` -- Phase 1 syntax changes compile
- [ ] `lake build Cslib.Logics.Temporal.Syntax.Subformulas` -- Phase 1 subformulas compile
- [ ] `lake build Cslib.Logics.Temporal.Semantics.Satisfies` -- Phase 2 semantics compile
- [ ] `lake build Cslib.Logics.Temporal.ProofSystem.Axioms` -- Phase 2 axioms compile
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Soundness` -- Phase 3 soundness compiles
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma` -- Phase 4 truth lemma compiles
- [ ] `lake build` -- Full project compiles after all phases
- [ ] `lake test` -- All tests pass
- [ ] `lake exe checkInitImports` -- Import verification passes
- [ ] `lake exe lint-style` -- Style linting passes
- [ ] Verify no `sorry` in modified files via `lean_verify` or grep

## Artifacts & Outputs

- `specs/176_temporal_and_or_propagation/plans/01_implementation-plan.md` (this file)
- `specs/176_temporal_and_or_propagation/summaries/01_implementation-summary.md` (created after implementation)
- Modified source files in `Cslib/Logics/Temporal/` (10 files total)

## Rollback/Contingency

All changes are confined to the Temporal module (`Cslib/Logics/Temporal/`). If implementation fails:

1. `git stash` or `git checkout -- Cslib/Logics/Temporal/` to revert all Temporal changes
2. No changes touch Foundations, Propositional, Modal, or Bimodal modules
3. If `encodeNat_injective` proves intractable, it can be temporarily marked `sorry` and addressed in a follow-up task (not recommended but provides a fallback)
4. Phase-by-phase commits allow reverting to any successfully completed phase boundary
