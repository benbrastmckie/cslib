# Implementation Plan: Task #231

- **Task**: 231 - Fix countermodel_dense universe mismatch in ChronicleToCountermodelBasic
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/231_fix_countermodel_dense_universe/reports/01_universe-mismatch-analysis.md
- **Artifacts**: plans/01_universe-fix-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Five files in `Cslib/Logics/Bimodal/Metalogic/Algebraic/` declare `variable {Atom : Type}` (universe 0) instead of `variable {Atom : Type*}` (universe polymorphic). This artificial restriction prevents `countermodel_dense` from invoking `ParametricCanonicalTaskFrame` at the required universe level. The fix generalizes these 5 files to `Type*`, then fills the two sorry sites that the mismatch blocked: `countermodel_dense` and `completeness_dense`.

### Research Integration

Key findings from the research report:
- Root cause is a porting artifact: 5 Parametric files use `{Atom : Type}` while all upstream dependencies and sibling files already use `{Atom : Type*}`
- No `Denumerable`, `Countable`, or `Encodable` constraints force universe 0
- All 5 files are sorry-free, so the change is a pure generalization
- `ParametricCanonicalWorldState` also has an explicit `(Atom : Type)` parameter that must change
- `countermodel_dense` needs to construct a parametric canonical model on `Rat`
- `completeness_dense` needs to apply `countermodel_dense` and derive a contradiction with `validDense`

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation needed for this task.

## Goals & Non-Goals

**Goals**:
- Generalize 5 Algebraic Parametric files from `{Atom : Type}` to `{Atom : Type*}`
- Fill `countermodel_dense` sorry (ChronicleToCountermodelBasic.lean:825)
- Fill `completeness_dense` sorry (Dense.lean:122)
- Pass full CI pipeline (`lake build`, `lake test`, `checkInitImports`, `lint-style`)

**Non-Goals**:
- Filling any other sorry sites in the codebase
- Refactoring the Parametric files beyond the universe change
- Modifying `validDense` or other definitions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe elaboration failure in Parametric proofs | H | L | All upstream deps are already polymorphic; D is already Type*; proofs use standard tactics |
| countermodel_dense proof body more complex than expected | M | M | Research identified the exact construction: cantorBfmcsDense + restricted coherence + fully_restricted_parametric_completeness_from_neg_membership |
| completeness_dense universe mismatch on validDense's D quantifier | M | L | validDense uses D : Type (universe 0); countermodel uses D = Rat : Type 0; no mismatch on D |
| Downstream breakage in other files | M | L | No downstream callers exist outside the sorry-blocked theorems |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Universe Generalization [COMPLETED]

**Goal**: Change `{Atom : Type}` to `{Atom : Type*}` in 5 Algebraic Parametric files and verify they still compile.

**Tasks**:
- [ ] Edit `ParametricCanonical.lean:36`: change `variable {Atom : Type}` to `variable {Atom : Type*}`
- [ ] Edit `ParametricCanonical.lean:39`: change `def ParametricCanonicalWorldState (Atom : Type)` to `def ParametricCanonicalWorldState (Atom : Type*)`
- [ ] Edit `ParametricHistory.lean:37`: change `variable {Atom : Type}` to `variable {Atom : Type*}`
- [ ] Edit `ParametricTruthLemma.lean:39`: change `variable {Atom : Type}` to `variable {Atom : Type*}`
- [ ] Edit `ParametricCompleteness.lean:37`: change `variable {Atom : Type}` to `variable {Atom : Type*}`
- [ ] Edit `RestrictedParametricTruthLemma.lean:41`: change `variable {Atom : Type}` to `variable {Atom : Type*}`
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Algebraic.ParametricCanonical` to verify compilation
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Algebraic.RestrictedParametricTruthLemma` to verify the full chain compiles

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCanonical.lean` - line 36 variable, line 39 def parameter
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricHistory.lean` - line 37 variable
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean` - line 39 variable
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCompleteness.lean` - line 37 variable
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` - line 41 variable

**Verification**:
- All 5 files compile without errors via `lake build`
- `lean_verify` confirms no new sorry in any of the 5 files

---

### Phase 2: Fill countermodel_dense Sorry [IN PROGRESS]

**Goal**: Implement the proof body for `countermodel_dense` in ChronicleToCountermodelBasic.lean, replacing the sorry at line 825.

**Tasks**:
- [ ] Read the existing proof context using `lean_goal` at the sorry site (line 825)
- [ ] Construct the proof using:
  - `cantorBfmcsDense` to get a BFMCS on Rat
  - The three restricted coherence conditions (`cantor_bfmcs_dense_restricted_tc`, `cantor_bfmcs_dense_restricted_buc`, `cantor_bfmcs_dense_restricted_fuc`)
  - `fully_restricted_parametric_completeness_from_neg_membership` to derive the countermodel
- [ ] Replace the sorry with the proof body
- [ ] Verify with `lean_goal` that no goals remain
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodelBasic`

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` - replace sorry at line 825

**Verification**:
- `lean_verify` on `countermodel_dense` shows no sorry
- Module compiles cleanly

---

### Phase 3: Fill completeness_dense Sorry [NOT STARTED]

**Goal**: Implement the proof body for `completeness_dense` in Dense.lean, replacing the sorry at line 122.

**Tasks**:
- [ ] Read the goal state using `lean_goal` at the sorry site (line 122)
- [ ] Construct the proof:
  - Apply `countermodel_dense` with the MCS `M`, formula `phi`, and the hypothesis `h_box_dense`
  - Obtain the existential witnesses (D, AddCommGroup, LinearOrder, etc.)
  - Instantiate `h_valid_dense` with the countermodel's domain and model to get that phi holds
  - Derive contradiction: the model both satisfies (from validDense) and falsifies (from countermodel) phi
- [ ] Replace the sorry with the proof body
- [ ] Verify with `lean_goal` that no goals remain
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.BXCanonical.Completeness.Dense`

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` - replace sorry at line 122

**Verification**:
- `lean_verify` on `completeness_dense` shows no sorry
- Module compiles cleanly

---

### Phase 4: CI Verification [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline to confirm no regressions.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports` (verify Cslib.Init imports)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Verify total sorry count has decreased by 2 (countermodel_dense + completeness_dense)

**Timing**: 15 minutes

**Depends on**: 3

**Files to modify**: None (verification only)

**Verification**:
- All CI checks pass
- `grep -r "sorry" Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` shows no sorry on lines 825
- `grep -r "sorry" Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` shows no sorry on line 122

## Testing & Validation

- [ ] All 5 Parametric files compile after universe generalization
- [ ] `countermodel_dense` proof compiles without sorry
- [ ] `completeness_dense` proof compiles without sorry
- [ ] Full `lake build` succeeds
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No new sorry introduced in any file

## Artifacts & Outputs

- `specs/231_fix_countermodel_dense_universe/plans/01_universe-fix-plan.md` (this file)
- `specs/231_fix_countermodel_dense_universe/summaries/01_universe-fix-summary.md` (after implementation)

## Rollback/Contingency

If universe generalization causes unexpected elaboration failures:
1. Revert the 5 Parametric files to `{Atom : Type}`
2. Investigate which specific proof breaks with universe polymorphism
3. Consider a targeted `@[specialize]` or explicit universe annotation as alternative fix

If countermodel_dense or completeness_dense proofs are more complex than expected:
1. Leave the sorry with an updated comment explaining what was tried
2. Mark the phase [BLOCKED] with detailed goal state
3. Preserve the universe generalization (Phase 1) as it is independently valuable
