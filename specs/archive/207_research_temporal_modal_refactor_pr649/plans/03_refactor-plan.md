# Implementation Plan: Generic MCS Properties Refactoring

- **Task**: 207 - Research refactoring Temporal/ and Modal/ implementations based on PR #649 review feedback
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None (PR #649 must be merged first, but the generic file builds independently)
- **Research Inputs**: reports/01_team-research.md, reports/02_reviewer-directed-research.md
- **Artifacts**: plans/03_refactor-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The PR #649 reviewer identified that CSLib's MCS (Maximal Consistent Set) properties are duplicated across four logics (Propositional, Modal, Temporal, Bimodal). Each logic wraps the same generic `Consistency.lean` lemmas (`closed_under_derivation`, `implication_property`, `negation_complete`) and reproves identical bot/negation lemmas (`mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`). This plan creates a single `MCSProperties.lean` file that proves these common lemmas once, then migrates each logic to use the generic versions. The deduction theorem proofs remain per-logic (they require concrete pattern matching on `DerivationTree` constructors). Definition of done: all four logics use generic MCS properties, full CI passes, zero sorrys, API preserved via aliases.

### Research Integration

Two research rounds inform this plan:

- **Round 1** (team research, 4 teammates): Quantified ~890 LOC of duplication across logics, evaluated three refactoring approaches (FormulaFunctor, Mixin Property Classes, Isabelle-Style), recommended phased Mixin approach.
- **Round 2** (reviewer-directed): Performed line-by-line comparison of all four MCS files, confirmed the deduction theorem cannot be fully genericized (Type-valued trees require concrete pattern matching), identified the "simplest viable approach" as creating generic MCS properties without touching `DerivationTree` or `HasHilbertTree`.

Key finding: The existing `DerivationSystem` + `HasDeductionTheorem` abstraction in `Consistency.lean` already provides the infrastructure. The missing piece is a convenience layer that proves the common derived properties (`mcs_bot_not_mem`, negation lemmas, `mcs_mp_axiom`) once at the generic level.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the ROADMAP.md item "Abstract shared completeness infrastructure" (Phase 3). It specifically targets the MCS property layer, which is the lowest-risk, highest-value extraction point identified by research.

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` with generic MCS lemmas
- Simplify Propositional, Modal, Temporal, and Bimodal MCS files to use generic versions
- Preserve all existing API names via `alias` or re-export for downstream compatibility
- Pass full CI pipeline (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`)
- Produce PRs suitable for upstream (~300-500 LOC each)

**Non-Goals**:
- Genericizing the deduction theorem proof (requires concrete `DerivationTree` pattern matching)
- Introducing a generic `DerivationTree` type (positivity/height issues make this impractical)
- Touching Bimodal's internal metalogic beyond the MCS wrapper layer (~51K LOC)
- Fixing the axiom name swap (`.imp_s` vs `.imp_k`) in Temporal/Bimodal (separate task)
- Connecting `ProofSystem.lean`/`InferenceSystem.lean` to `HasDeductionTheorem` (future work)
- Unifying formula types across logics

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking downstream imports in completeness files | High | Low | Use `alias`/`abbrev` to preserve all existing names; run full `lake build` after each logic |
| Bimodal cascading breakage (51K LOC) | High | Low | Touch Bimodal last; Bimodal already delegates to generic framework minimally; use aliases only |
| Typeclass resolution slowdown from new file | Medium | Low | No new typeclasses -- only parametric theorem defs; benchmark build time before/after |
| Temporal MCS has `set_option maxHeartbeats 1600000` and may be fragile | Medium | Medium | Only remove wrapper lemmas, do not touch temporal-specific proofs (G/H witness, contrapositive) |
| `lake shake` may flag new import as unused if aliases are not used transitively | Low | Medium | Run `lake shake` incrementally; add `public import` where needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Create Generic MCSProperties.lean [NOT STARTED]

**Goal**: Create the shared generic MCS properties file in Foundations that proves the common lemmas once, parameterized over `DerivationSystem` and `HasDeductionTheorem`.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` with module header and copyright
- [ ] Add `import Cslib.Foundations.Logic.Metalogic.Consistency`
- [ ] Implement `mcs_bot_not_mem`: If `S` is MCS, then `bot not in S` (generic over any `DerivationSystem`)
- [ ] Implement `mcs_neg_of_not_mem`: If `phi not in S` (MCS), then `(phi -> bot) in S`
- [ ] Implement `mcs_not_mem_of_neg`: If `(phi -> bot) in S` (MCS), then `phi not in S`
- [ ] Implement `mcs_mem_iff_neg_not_mem`: `phi in S <-> (phi -> bot) not in S` for MCS `S`
- [ ] Implement `mcs_mp_axiom`: Derive `psi in S` from `phi in S` and `Deriv [] (phi -> psi)` via `closed_under_derivation`
- [ ] Implement `mcs_theorem_in_mcs`: Theorems (derivable from empty context) belong to every MCS
- [ ] Add `Cslib.Foundations.Logic.Metalogic.MCSProperties` to `Cslib.lean` barrel import
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.MCSProperties` to verify
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` - NEW: ~80-100 LOC of generic lemmas
- `Cslib.lean` - Add import line

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.MCSProperties` succeeds with zero warnings
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- All lemmas have the correct type signatures matching what each logic currently uses

---

### Phase 2: Migrate Propositional MCS [NOT STARTED]

**Goal**: Simplify `Cslib/Logics/Propositional/Metalogic/MCS.lean` to use generic `MCSProperties.lean`, serving as the proof-of-concept for the migration pattern.

**Tasks**:
- [ ] Add `import Cslib.Foundations.Logic.Metalogic.MCSProperties` to PL MCS file
- [ ] Replace `prop_mcs_bot_not_mem` body with call to generic `Metalogic.mcs_bot_not_mem`
- [ ] Replace `prop_mcs_neg_of_not_mem` body with call to generic `Metalogic.mcs_neg_of_not_mem`
- [ ] Replace `prop_mcs_not_mem_of_neg` body with call to generic `Metalogic.mcs_not_mem_of_neg`
- [ ] Replace `prop_mcs_mem_iff_neg_not_mem` body with call to generic `Metalogic.mcs_mem_iff_neg_not_mem`
- [ ] Verify wrapper lemma signatures remain identical (no API breakage)
- [ ] Run `lake build Cslib.Logics.Propositional` (scoped build)
- [ ] Run `lake exe lint-style`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - Replace duplicated lemma bodies with generic calls (~40 LOC reduction)

**Verification**:
- `lake build Cslib.Logics.Propositional` succeeds
- All existing theorem names still resolve (downstream completeness files unaffected)
- `lake exe lint-style` passes

---

### Phase 3: Migrate Modal MCS [NOT STARTED]

**Goal**: Simplify `Cslib/Logics/Modal/Metalogic/MCS.lean` to use generic MCS properties while preserving modal-specific lemmas (box witness, box closure, etc.).

**Tasks**:
- [ ] Add `import Cslib.Foundations.Logic.Metalogic.MCSProperties` to Modal MCS file
- [ ] Replace `mcs_bot_not_mem` body with call to generic `Metalogic.mcs_bot_not_mem`
- [ ] Replace `mcs_neg_of_not_mem` body with call to generic `Metalogic.mcs_neg_of_not_mem`
- [ ] Replace `mcs_not_mem_of_neg` body with call to generic `Metalogic.mcs_not_mem_of_neg`
- [ ] Replace `mcs_mem_iff_neg_not_mem` body with call to generic `Metalogic.mcs_mem_iff_neg_not_mem`
- [ ] Replace `mcs_mp_axiom` body with call to generic `Metalogic.mcs_mp_axiom` (or adapt signature)
- [ ] Preserve all modal-specific lemmas (`mcs_box_closure`, `mcs_box_box`, `mcs_box_diamond`, `mcs_box_mp`, `mcs_box_witness`, `iteratedDeduction`, `derive_box_from_box_context`, `derive_box_from_inconsistency`) unchanged
- [ ] Run `lake build Cslib.Logics.Modal` (scoped build)
- [ ] Run `lake exe lint-style`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/MCS.lean` - Replace duplicated lemma bodies (~50 LOC reduction), keep modal-specific proofs intact

**Verification**:
- `lake build Cslib.Logics.Modal` succeeds
- Modal completeness files compile without changes
- `lake exe lint-style` passes

---

### Phase 4: Migrate Temporal MCS [NOT STARTED]

**Goal**: Simplify `Cslib/Logics/Temporal/Metalogic/MCS.lean` to use generic MCS properties while preserving temporal-specific lemmas (G/H witness, contrapositive, distribution).

**Tasks**:
- [ ] Add `import Cslib.Foundations.Logic.Metalogic.MCSProperties` to Temporal MCS file
- [ ] Replace `mcs_bot_not_mem` body with call to generic `Metalogic.mcs_bot_not_mem`
- [ ] Replace `mcs_neg_of_not_mem` body with call to generic version
- [ ] Replace `mcs_not_mem_of_neg` body with call to generic version
- [ ] Replace `mcs_mem_iff_neg_not_mem` body with call to generic version
- [ ] Evaluate whether `mcs_mp_axiom` can delegate to generic version (Temporal version has extra `h_fc` parameter for `minFrameClass`; may need adaptation)
- [ ] Preserve all temporal-specific lemmas (`mcs_g_mp`, `mcs_h_mp`, `mcs_g_witness`, `mcs_h_witness`, `derive_g_contradiction`, `derive_h_contradiction`, `deriveContrapositive`, `theoremInMcs`, `futureSet`, `pastSet`) unchanged
- [ ] Run `lake build Cslib.Logics.Temporal` (scoped build; may be slow due to `maxHeartbeats 1600000`)
- [ ] Run `lake exe lint-style`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` - Replace duplicated lemma bodies (~30 LOC reduction), keep temporal-specific proofs intact

**Verification**:
- `lake build Cslib.Logics.Temporal` succeeds (including completeness files downstream)
- `lake exe lint-style` passes
- No increase in `maxHeartbeats` required

---

### Phase 5: Migrate Bimodal MCS and Final CI Verification [NOT STARTED]

**Goal**: Simplify `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` to use generic MCS properties, then run full CI to confirm nothing is broken.

**Tasks**:
- [ ] Add `import Cslib.Foundations.Logic.Metalogic.MCSProperties` to Bimodal MCS file
- [ ] Evaluate which Bimodal wrapper lemmas can delegate to generic versions (Bimodal already delegates most to `Consistency.lean`; the set-based wrappers `bimodalClosedUnderDerivation`, `bimodalImplicationProperty`, `bimodalNegationComplete` are thin wrappers)
- [ ] Add generic `mcs_bot_not_mem` equivalent for Bimodal if not already present (Bimodal's list-based `Consistent` and set-based `BimodalSetConsistent` are separate layers)
- [ ] Preserve all Bimodal list-based MCS definitions and helpers (they serve the 51K LOC downstream)
- [ ] Run `lake build Cslib.Logics.Bimodal` (scoped build)
- [ ] Run full CI pipeline: `lake build` (full), `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`
- [ ] Verify zero sorrys via `lean_verify` on key new lemmas

**Timing**: 1.5 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` - Add imports and evaluate delegation (~20 LOC reduction)

**Verification**:
- Full `lake build` succeeds with zero errors and zero sorrys
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake shake` reports no unnecessary imports

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Metalogic.MCSProperties` -- new file compiles
- [ ] `lake build Cslib.Logics.Propositional` -- PL migration succeeds
- [ ] `lake build Cslib.Logics.Modal` -- Modal migration succeeds
- [ ] `lake build Cslib.Logics.Temporal` -- Temporal migration succeeds
- [ ] `lake build Cslib.Logics.Bimodal` -- Bimodal migration succeeds
- [ ] `lake build` -- full project builds cleanly
- [ ] `lake test` -- all tests pass
- [ ] `lake exe checkInitImports` -- all files import `Cslib.Init`
- [ ] `lake exe lint-style` -- style checks pass
- [ ] `lake shake --add-public --keep-implied --keep-prefix` -- import analysis clean
- [ ] Verify zero sorrys in `MCSProperties.lean` via `lean_verify`
- [ ] Verify no regression in heartbeat counts for Temporal/Bimodal builds

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` -- NEW: generic MCS properties (~80-100 LOC)
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` -- SIMPLIFIED: delegates to generic (~40 LOC saved)
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- SIMPLIFIED: delegates to generic (~50 LOC saved)
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` -- SIMPLIFIED: delegates to generic (~30 LOC saved)
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` -- SIMPLIFIED: delegates to generic (~20 LOC saved)
- Net change: ~80-100 LOC added, ~140 LOC removed = ~40-60 LOC net reduction
- `specs/207_research_temporal_modal_refactor_pr649/plans/03_refactor-plan.md` -- this plan

## Rollback/Contingency

If any migration phase breaks downstream files:
1. Revert the specific logic's MCS file to its pre-migration state (`git checkout -- path/to/MCS.lean`)
2. The generic `MCSProperties.lean` is additive and cannot break existing code on its own
3. Each phase is independently revertible -- a failure in Modal migration does not affect Propositional
4. If Bimodal migration causes cascading issues in the 51K LOC downstream, skip Bimodal migration entirely and keep the existing thin delegation wrappers
5. Worst case: delete `MCSProperties.lean` and revert all MCS files -- zero net change to the repository
