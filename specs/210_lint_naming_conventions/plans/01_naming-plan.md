# Implementation Plan: Task #210

- **Task**: 210 - Fix naming convention violations (underscore to camelCase)
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None (coordinate with task 211 for 9 overlapping declarations)
- **Research Inputs**: specs/210_lint_naming_conventions/reports/01_naming-research.md
- **Artifacts**: plans/01_naming-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix all 105 `defsWithUnderscore` lint violations across the Bimodal (87) and Temporal (18) namespaces by renaming declarations from snake_case to lowerCamelCase per Mathlib convention. The work is organized into 5 phases by file cluster, with the highest-reference renames (Q_Z at 100 refs, U_nesting_depth at 88 refs) handled carefully with full cross-file verification. Each phase performs definition-site renames followed by reference updates and build verification.

### Research Integration

The research report (01_naming-research.md) categorized all 105 violations into 6 categories (letter-prefix, snake_case, numeric suffix, abbreviated prefix, structure fields, UpperCamelCase) and recommended Option 1 (full rename) over suppression or keyword changes. Key findings integrated:
- 15 Bimodal/Temporal duplicate pairs account for 30 violations that must be renamed in both namespaces consistently
- 9 declarations overlap with task 211 (defLemma); we rename them anyway for naming consistency
- Structure field renames (h_impl, h_snce, h_untl, task_rel) affect dot-notation access patterns and need special attention

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances overall CSLib code quality and Mathlib-compatibility. It does not directly correspond to a specific ROADMAP.md remaining item, but is prerequisite work for clean CI on all existing modules.

## Goals & Non-Goals

**Goals**:
- Eliminate all 105 `defsWithUnderscore` lint violations
- Rename all definition sites and every reference site across the codebase
- Maintain build success (`lake build`) after each phase
- Keep Bimodal/Temporal namespace pairs consistent

**Non-Goals**:
- Changing `def` to `theorem` (that is task 211's scope)
- Fixing any other lint categories (e.g., `defLemma`, `unusedHavesSuffices`)
- Refactoring proof strategies or simplifying proofs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Partial match on short names (Q_Z, F_top) corrupts unrelated code | H | M | Use precise regex with word boundaries; verify build after each rename |
| Structure field rename breaks dot-notation access | H | M | Grep for `.h_impl`, `.h_snce`, `.h_untl`, `.task_rel` patterns; test all match sites |
| High-reference renames (Q_Z=100, U_nesting_depth=88) miss some sites | H | L | Use `grep -rn` across entire Cslib/ tree; rebuild verifies completeness |
| Conflict with task 211 on overlapping 9 declarations | M | L | Rename in this task; if task 211 later changes to theorem, names will already be correct |
| Rebuild time between phases slows iteration | M | M | Group renames by file cluster to minimize incremental rebuild scope |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are sequential because later phases depend on a clean build from earlier phases. Some renames span files touched in multiple phases, so sequential execution prevents conflicts.

---

### Phase 1: Bimodal Theorems -- TemporalDerived.lean (23 violations) [COMPLETED]

**Goal**: Rename all 23 violations in the highest-violation single file, plus update references in downstream files. This file contains temporal operator abbreviations (G_, H_, F_, P_ prefix) and snake_case definitions.

**Tasks**:
- [ ] Rename letter-prefix definitions in `Bimodal/Theorems/TemporalDerived.lean`:
  - `G_distribution` -> `gDistribution` (11 refs, 2 files)
  - `H_distribution` -> `hDistribution` (11 refs, 2 files)
  - `G_transitivity` -> `gTransitivity` (1 ref, 1 file)
  - `H_transitivity` -> `hTransitivity` (1 ref, 1 file)
  - `G_implies_G_id` -> `gImpliesGId` (1 ref, 1 file)
  - `F_mono` -> `fMono` (4 refs, 2 files)
  - `P_mono` -> `pMono` (3 refs, 2 files)
  - `G_mono` -> `gMono` (1 ref, 1 file)
  - `H_mono` -> `hMono` (1 ref, 1 file)
  - `F_neg_G` -> `fNegG` (2 refs, 2 files)
  - `P_neg_H` -> `pNegH` (2 refs, 2 files)
  - `G_and_intro` -> `gAndIntro` (3 refs, 2 files)
  - `H_and_intro` -> `hAndIntro` (3 refs, 2 files)
  - `G_imp_trans` -> `gImpTrans` (3 refs, 2 files)
  - `H_imp_trans` -> `hImpTrans` (3 refs, 2 files)
  - `G_contrapose` -> `gContrapose` (3 refs, 2 files)
  - `H_contrapose` -> `hContrapose` (3 refs, 2 files)
  - `G_dne_theorem` -> `gDneTheorem` (1 ref, 1 file)
  - `H_dne_theorem` -> `hDneTheorem` (1 ref, 1 file)
- [ ] Rename snake_case definitions in `Bimodal/Theorems/TemporalDerived.lean`:
  - `eval_family` -> `evalFamily` (9 refs, 4 files)
  - `modal_5_collapse_theorem` -> `modal5CollapseTheorem` (2 refs, 1 file)
  - `axiom_5_negative_introspection` -> `axiom5NegativeIntrospection` (3 refs, 2 files)
- [ ] Rename numeric suffix definition:
  - `modal_5` -> `modal5` (3 refs, 1 file)
- [ ] Update all references in downstream files (Perpetuity/, Embedding/, Bundle/, Separation/)
- [ ] Run `lake build` to verify

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - 23 definition-site renames
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - reference updates
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` - reference updates
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - reference updates
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalCoherence.lean` - reference updates (eval_family)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/BFMCS.lean` - reference updates (eval_family)
- Other files referencing renamed definitions (find via grep)

**Verification**:
- `lake build` succeeds with no errors
- `grep -rn 'G_distribution\|H_distribution\|eval_family\|modal_5_collapse' Cslib/Logics/Bimodal/` returns no matches for old names at definition or reference sites

---

### Phase 2: PointInsertion Pair + Chronicle Types (30 violations) [COMPLETED]

**Goal**: Rename all violations in the Bimodal and Temporal PointInsertion.lean files and their shared chronicle types. This phase handles the highest-reference names: Q_Z (100 refs), U_nesting_depth (88 refs), lemma_2_7_seed (48 refs), case1_psi (44 refs), and all abbreviated-prefix names (l27_, l27s_, c5_, d21_, case_).

**Tasks**:
- [ ] Rename high-reference names in Bimodal PointInsertion + related files:
  - `Q_Z` -> `qZ` (100 refs, 3 files)
  - `U_nesting_depth` -> `uNestingDepth` (88 refs, 2 files)
  - `lemma_2_7_seed` -> `lemma27Seed` (48 refs, 2 files)
  - `lemma_2_7_since_seed` -> `lemma27SinceSeed` (30 refs, 2 files)
  - `lemma_2_4` -> `lemma24` (29 refs, 4 files)
  - `lemma_2_6` -> `lemma26` (29 refs, 4 files)
  - `case1_psi` -> `case1Psi` (44 refs, 3 files)
  - `case3_alpha` -> `case3Alpha` (31 refs, 3 files)
  - `d21_sep` -> `d21Sep` (24 refs, 2 files)
  - `case2_psi` -> `case2Psi` (11 refs, 2 files)
  - `case3_rhs` -> `case3Rhs` (18 refs, 3 files)
- [ ] Rename abbreviated-prefix names in Bimodal PointInsertion:
  - `l27_guard` -> `l27Guard` (12 refs, 2 files)
  - `l27_collect_guards` -> `l27CollectGuards` (22 refs, 2 files)
  - `l27_a_event_list` -> `l27AEventList` (18 refs, 2 files)
  - `l27s_c5_event_list` -> `l27sC5EventList` (16 refs, 2 files)
  - `l27s_b5_guard_list` -> `l27sB5GuardList` (16 refs, 2 files)
  - `c5_forward_walk` -> `c5ForwardWalk` (2 refs, 2 files)
  - `c5_backward_walk` -> `c5BackwardWalk` (2 refs, 2 files)
- [ ] Rename numeric-suffix and guard names in Bimodal PointInsertion:
  - `lemma_2_4_with_guard` -> `lemma24WithGuard` (9 refs, 4 files)
  - `lemma_2_4_since_with_guard` -> `lemma24SinceWithGuard` (10 refs, 4 files)
- [ ] Rename structure fields in Bimodal chronicle types:
  - `EnrichedEvent.h_impl` -> `EnrichedEvent.hImpl` (across all usage sites)
  - `EnrichedEvent.h_snce` -> `EnrichedEvent.hSnce` (across all usage sites)
  - `EnrichedEventSince.h_impl` -> `EnrichedEventSince.hImpl` (across all usage sites)
  - `EnrichedEventSince.h_untl` -> `EnrichedEventSince.hUntl` (across all usage sites)
- [ ] Apply identical renames in Temporal PointInsertion + chronicle types (15 duplicate pairs):
  - Same names as above in `Cslib/Logics/Temporal/Metalogic/Chronicle/` files
- [ ] Rename `U_depth_under_S` -> `uDepthUnderS` (5 refs, 1 file)
- [ ] Rename `S_nesting_above_U` -> `sNestingAboveU` (4 refs, 2 files)
- [ ] Rename `S_nesting_above_U_inner` -> `sNestingAboveUInner` (1 ref, 1 file)
- [ ] Update all references in downstream files (ChronicleConstruction, CounterexampleElimination, TruthLemma, ChronicleToCountermodel, OrderedSeedConsistency)
- [ ] Run `lake build` to verify

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` - definition + reference renames
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` - structure field renames
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/OrderedSeedConsistency.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/TruthLemma.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` - Q_Z reference updates
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` - case reference updates
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - U_nesting_depth, S_nesting references
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` - reference updates
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - Temporal duplicate renames
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - Temporal structure field renames
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` - reference updates
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - reference updates
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` - reference updates
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` - reference updates
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` - reference updates
- Additional files found via `grep -rn` for old names

**Verification**:
- `lake build` succeeds
- `grep -rn 'Q_Z\|U_nesting_depth\|lemma_2_7_seed\|case1_psi\|h_impl\|h_snce\|h_untl' Cslib/` returns no definition-site or reference-site matches for old names (excluding comments)

---

### Phase 3: Bundle Files (13 violations) [COMPLETED]

**Goal**: Rename all violations in the Bimodal Bundle/ directory files: TemporalCoherence, BFMCS, CanonicalFrame, ModalSaturation, and UntilSinceCoherence.

**Tasks**:
- [ ] Rename in `Bimodal/Metalogic/Bundle/TemporalCoherence.lean`:
  - `F_top` -> `fTop` (23 refs, 7 files)
  - `P_top` -> `pTop` (20 refs, 6 files)
  - `G_neg_neg_bot` -> `gNegNegBot` (8 refs, 1 file)
  - `H_neg_neg_bot` -> `hNegNegBot` (8 refs, 1 file)
  - `temporally_coherent` -> `temporallyCoherent` (18 refs, 5 files)
  - `restricted_temporally_coherent` -> `restrictedTemporallyCoherent` (3 refs, 2 files)
- [ ] Rename in `Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean`:
  - `until_since_coherent` -> `untilSinceCoherent` (4 refs, 1 file)
  - `backward_until_since_coherent` -> `backwardUntilSinceCoherent` (12 refs, 4 files)
  - `forward_until_since_coherent` -> `forwardUntilSinceCoherent` (12 refs, 4 files)
  - `restricted_forward_until_since_coherent` -> `restrictedForwardUntilSinceCoherent` (6 refs, 3 files)
  - `restricted_backward_until_since_coherent` -> `restrictedBackwardUntilSinceCoherent` (6 refs, 3 files)
- [ ] Rename in `Bimodal/Metalogic/Bundle/CanonicalFrame.lean` or `BFMCS.lean`:
  - `F_top_deferral` -> `fTopDeferral` (4 refs, 1 file)
  - `P_top_deferral` -> `pTopDeferral` (4 refs, 1 file)
- [ ] Update all references across Bundle/, BXCanonical/, Algebraic/ directories
- [ ] Run `lake build` to verify

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalCoherence.lean` - definition renames
- `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` - definition renames
- `Cslib/Logics/Bimodal/Metalogic/Bundle/BFMCS.lean` - definition renames + reference updates
- `Cslib/Logics/Bimodal/Metalogic/Bundle/CanonicalFrame.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Bundle/ModalSaturation.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Bundle/Construction.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalModel.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricHistory.lean` - reference updates
- Additional files referencing F_top, P_top, temporally_coherent (find via grep)

**Verification**:
- `lake build` succeeds
- `grep -rn 'F_top\|P_top\|temporally_coherent\|until_since_coherent' Cslib/Logics/Bimodal/` returns no matches for old names

---

### Phase 4: Separation Files + SubformulaClosure (14 violations) [COMPLETED]

**Goal**: Rename violations in Separation/ directory files (QLemma, Defs, Eliminations, HierarchyInduction, Cases) and SubformulaClosure/TemporalFormulas.lean.

**Tasks**:
- [ ] Rename in `Bimodal/Metalogic/Separation/` files:
  - `G_quot` -> `gQuot` (5 refs, 2 files)
  - `H_quot` -> `hQuot` (5 refs, 2 files)
  - `F_neg_contra_imp_F_neg` -> `fNegContraImpFNeg` (2 refs, 1 file)
  - `G_imp_to_G_contra` -> `gImpToGContra` (2 refs, 1 file)
  - `G_contra_to_GK` -> `gContraToGK` (2 refs, 1 file)
  - `FF_to_F_top_and` -> `ffToFTopAnd` (2 refs, 1 file)
  - `F_top_and_absorb` -> `fTopAndAbsorb` (2 refs, 1 file)
- [ ] Rename in `Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean`:
  - `subformulaClosure_fintype` -> `subfomrulaClosureFintype` (1 ref, 1 file) -- NOTE: verify correct target name; research report shows typo in proposed name, should be `subformulaClosureFintype`
- [ ] Rename Gamma/ExistsTask names:
  - `Gamma_plus` -> `gammaPlus` (3 refs, 1 file)
  - `Gamma_minus` -> `gammaMinus` (3 refs, 1 file)
  - `ExistsTask_past` -> `ExistsTaskPast` (14 refs, 1 file) -- NOTE: this is UpperCamelCase because it defines a type-like entity
- [ ] Update all references in Separation/ subdirectory and downstream files
- [ ] Run `lake build` to verify

**Timing**: 0.75 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` - definition renames (G_quot, H_quot)
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` - definition renames
- `Cslib/Logics/Bimodal/Metalogic/Separation/DualEliminations.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` - definition renames (Gamma_plus, Gamma_minus)
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean` - reference updates
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` - reference updates
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` - definition rename
- `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` - ExistsTask_past rename
- Additional files found via grep

**Verification**:
- `lake build` succeeds
- `grep -rn 'G_quot\|H_quot\|Gamma_plus\|Gamma_minus\|ExistsTask_past\|subformulaClosure_fintype' Cslib/` returns no matches

---

### Phase 5: Remaining Files -- Perpetuity, Combinators, TaskFrame, Temporal Theorems (25 violations) [COMPLETED]

**Goal**: Rename all remaining violations in Perpetuity/Principles.lean, Theorems/Combinators.lean, Semantics/TaskFrame.lean, and Temporal/Theorems/ files. Run full CI verification.

**Tasks**:
- [ ] Rename in `Bimodal/Theorems/Perpetuity/Principles.lean`:
  - `perpetuity_3` -> `perpetuity3` (3 refs, 1 file)
  - `perpetuity_4` -> `perpetuity4` (3 refs, 1 file)
  - `perpetuity_5` -> `perpetuity5` (3 refs, 2 files)
  - `perpetuity_6` -> `perpetuity6` (2 refs, 1 file)
- [ ] Rename in `Bimodal/Theorems/Combinators.lean`:
  - `combineImpConj_3` -> `combineImpConj3` (3 refs, 1 file) -- both Bimodal and Foundations versions
  - `boxConjIntroImp_3` -> `boxConjIntroImp3` (3 refs, 1 file)
- [ ] Rename in `Bimodal/Semantics/TaskFrame.lean`:
  - `task_rel` -> `taskRel` (31 refs, 4 files)
- [ ] Rename in Temporal-specific files:
  - `K_plus` -> `kPlus` (5 refs, 1 file)
  - `K_minus` -> `kMinus` (5 refs, 1 file)
  - `temp_4_derived` -> `temp4Derived` (9 refs, 4 files) -- both Bimodal and Temporal
  - `temp_4_past` -> `temp4Past` (2 refs, 1 file)
  - `chronicle_densely_ordered_dense` -> `chronicleDenselyOrderedDense` (3 refs, 1 file)
- [ ] Update all downstream references for `task_rel` (high-ref: 31 refs across 4 files)
- [ ] Update all downstream references for `temp_4_derived` (9 refs across 4 files)
- [ ] Run full CI verification:
  - `lake build`
  - `lake lint` (verify defsWithUnderscore count is 0)
  - `lake exe lint-style`
- [ ] Verify no remaining underscore violations: `lake lint 2>&1 | grep -i "underscore"` returns empty

**Timing**: 0.75 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - definition renames
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` - reference updates (perpetuity_5)
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` - definition renames
- `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` - definition rename (task_rel)
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` - reference updates (task_rel)
- `Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` - reference updates (task_rel)
- `Cslib/Logics/Bimodal/FrameConditions/Soundness.lean` - reference updates (task_rel)
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - chronicle_densely_ordered_dense
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - combineImpConj_3 if defined here
- Additional files found via grep for task_rel, temp_4_derived, K_plus, K_minus

**Verification**:
- `lake build` succeeds with zero errors
- `lake lint 2>&1 | grep -c "defsWithUnderscore"` shows 0 remaining violations (or significantly reduced from 105)
- `lake exe lint-style` passes
- All CI checks pass

## Testing & Validation

- [ ] `lake build` succeeds after each phase (phases 1-5)
- [ ] `lake lint` shows 0 `defsWithUnderscore` violations after phase 5
- [ ] `lake exe lint-style` passes after phase 5
- [ ] `grep -rn` for each old name across `Cslib/` returns no matches (excluding comments where appropriate)
- [ ] No regression in `lake test` (CslibTests suite)

## Artifacts & Outputs

- `specs/210_lint_naming_conventions/plans/01_naming-plan.md` (this file)
- `specs/210_lint_naming_conventions/summaries/01_naming-summary.md` (after implementation)
- Modified Lean files across `Cslib/Logics/Bimodal/` and `Cslib/Logics/Temporal/` (24+ files)

## Rollback/Contingency

All renames are mechanical find-and-replace operations. If any phase breaks the build:
1. Use `git diff` to review the changes in the current phase
2. Revert with `git checkout -- <affected-files>` for the current phase only
3. Re-examine the failing rename for partial matches or missed reference sites
4. Re-apply more carefully with refined regex patterns

If the entire task needs rollback: `git revert` the commits from each completed phase in reverse order.
