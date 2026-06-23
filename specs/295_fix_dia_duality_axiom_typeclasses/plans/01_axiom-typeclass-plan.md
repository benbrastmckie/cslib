# Implementation Plan: Add HasAxiomDiaDuality Typeclasses

- **Task**: 295 - fix_dia_duality_axiom_typeclasses
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_axiom-typeclass-research.md
- **Artifacts**: plans/01_axiom-typeclass-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add two missing `HasAxiomDiaDualityFwd` and `HasAxiomDiaDualityBack` typeclasses to `Cslib/Foundations/Logic/ProofSystem.lean`. Every other axiom abbreviation in `Axioms.lean` has a corresponding `HasAxiom*` typeclass in `ProofSystem.lean`, but the diamond duality pair is missing. The fix is purely additive: insert a new `DiaDualityAxiomClasses` section between the existing `ModalAxiomClasses` and `TemporalAxiomClasses` sections.

### Research Integration

Research report `01_axiom-typeclass-research.md` confirmed:
- The axioms `AxiomDiaDualityFwd` and `AxiomDiaDualityBack` are defined in `Axioms.lean` (lines 196-219) requiring `[HasBot F] [HasImp F] [HasBox F] [HasDia F]`.
- No existing section in `ProofSystem.lean` provides `[HasDia F]`, so a new section is needed.
- The insertion point is after line 204 (`end ModalAxiomClasses`) and before line 206 (`/-! ### Temporal Axiom Typeclasses -/`).
- The change has no downstream consumers and zero breakage risk.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation required for this task.

## Goals & Non-Goals

**Goals**:
- Add `HasAxiomDiaDualityFwd` typeclass following the existing pattern
- Add `HasAxiomDiaDualityBack` typeclass following the existing pattern
- Group both in a new `DiaDualityAxiomClasses` section with appropriate section variables
- Pass `lake build Cslib.Foundations.Logic.ProofSystem`

**Non-Goals**:
- Instantiating these typeclasses for any bundled proof system
- Adding downstream lemmas or theorems using these typeclasses
- Modifying `Axioms.lean` or any other file

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Incorrect section variables | L | L | Copy pattern from research; verify with `lean_goal` |
| Build failure from typo | L | L | Run `lake build Cslib.Foundations.Logic.ProofSystem` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add DiaDualityAxiomClasses Section [COMPLETED]

**Goal**: Insert the two typeclass declarations and verify the build.

**Tasks**:
- [ ] Read `ProofSystem.lean` lines 200-210 to confirm exact insertion point
- [ ] Insert new `DiaDualityAxiomClasses` section after `end ModalAxiomClasses` (line 204) and before the temporal section header (line 206)
- [ ] The section should contain:
  - `/-! ### Diamond Duality Axiom Typeclasses -/`
  - `section DiaDualityAxiomClasses`
  - `variable (S : Type*) [HasBot F] [HasImp F] [HasBox F] [HasDia F] [InferenceSystem S F]`
  - `HasAxiomDiaDualityFwd` class with field `diaDualityFwd {φ : F}`
  - `HasAxiomDiaDualityBack` class with field `diaDualityBack {φ : F}`
  - `end DiaDualityAxiomClasses`
- [ ] Run `lake build Cslib.Foundations.Logic.ProofSystem` to verify no errors
- [ ] Run `lake exe checkInitImports` to verify import correctness
- [ ] Run `lake exe lint-style` to verify style compliance

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` - Add new section between lines 204 and 206

**Verification**:
- `lake build Cslib.Foundations.Logic.ProofSystem` succeeds with no errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lean_hover_info` on the new classes shows correct types

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.ProofSystem` compiles without errors
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] New classes reference `Axioms.AxiomDiaDualityFwd` and `Axioms.AxiomDiaDualityBack` correctly

## Artifacts & Outputs

- `plans/01_axiom-typeclass-plan.md` (this file)
- Modified: `Cslib/Foundations/Logic/ProofSystem.lean`

## Rollback/Contingency

Revert the single Edit to `ProofSystem.lean` via `git checkout -- Cslib/Foundations/Logic/ProofSystem.lean`. No other files are modified.
