# Implementation Plan: Subformula Property for LK

- **Task**: 329 - Prove the subformula property as a corollary of cut elimination
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: 328 (cut elimination)
- **Research Inputs**: specs/329_cutelim_subformula_property/reports/01_subformula-property.md
- **Artifacts**: plans/01_subformula-property.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Create a new file `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean` that
proves the subformula property for LK as a corollary of cut elimination. The proof proceeds by
structural induction on the cut-free proof tree: for each rule, every formula in the proof tree
is shown to be a subformula of some formula in the conclusion sequent. The general case follows
by applying `LKProof.cutElim` to obtain a cut-free proof and then invoking the cut-free result.
The key infrastructure (`Proposition.subformulas`, `Proposition.IsSubformula`, and supporting
lemmas) already exists in `Normalization.lean` and will be imported, not redefined.

### Research Integration

Key findings from the research report (01_subformula-property.md):
- `Proposition.subformulas` and `Proposition.IsSubformula` already exist in `Normalization.lean` (lines 63-145) with lemmas `IsSubformula.refl`, `IsSubformula.trans`, `IsSubformula.and_left/right`, `IsSubformula.or_left/right`, `IsSubformula.imp_left/right`
- `LKProof.cutElim` returns `Nonempty (CutFreeLKProof seq)`, making the final theorem existential
- `CutElimination.lean` builds successfully despite the barrel file comment excluding it
- No circular dependency between CutElimination and Normalization imports
- The proof requires 11 cases (ax, botL, andL, andR, orL, orR, impL, impR, weakL, weakR, cut) with the cut case vacuously discharged by `CutFree`

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `LKProof.formulas`: recursive Finset-valued collector of all formulas in a proof tree
- Prove `CutFreeLKProof.subformula_property`: structural induction on cut-free proofs showing every formula is a subformula of the conclusion
- Prove `LKProof.subformula_property`: corollary via `cutElim` giving the existential version for arbitrary LK proofs
- Register the new file in the LK barrel file
- Pass full CI pipeline

**Non-Goals**:
- Factoring `Proposition.subformulas` out of `Normalization.lean` into a separate file (out of scope)
- Uncommenting/fixing the `CutElimination` barrel import (separate task; new file imports directly)
- Adding the subformula property for other proof systems (natural deduction and tableau already have theirs)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Pattern matching on LKProof with Finset quotient equations causes equation compiler issues | M | L | Use generic-sequent parameters with subset hypotheses, following CutElimination.lean patterns |
| Importing Normalization.lean is too heavy (brings Multiset.DershowitzManna) | L | L | Accept the import weight; factoring is out of scope and the dependency is clean |
| Finset membership bookkeeping is tedious across 11 cases | M | M | Each case follows the same pattern (IH + IsSubformula transitivity); extract helper lemmas if repetition is excessive |
| CutElimination barrel import stays commented out, making SubformulaProperty unreachable from barrel | L | H | Import CutElimination directly in SubformulaProperty.lean; add SubformulaProperty to barrel with a comment noting it also imports CutElimination |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Create SubformulaProperty.lean [COMPLETED]

**Goal**: Create the new file with all three declarations (`LKProof.formulas`, `CutFreeLKProof.subformula_property`, `LKProof.subformula_property`) and their complete proofs.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean` with copyright header and imports (`CutElimination`, `Normalization`)
- [ ] Define `LKProof.formulas` as a recursive function collecting all formulas in the proof tree into a `Finset (Proposition Atom)`
- [ ] Prove `CutFreeLKProof.subformula_property` by structural induction on the cut-free proof, handling all 11 LKProof constructors (cut case discharged by `CutFree` being `False`)
- [ ] Prove `LKProof.subformula_property` using `cutElim` to obtain a `CutFreeLKProof` and then applying the cut-free version
- [ ] Add docstrings to all three declarations
- [ ] Verify the file builds: `lake build Cslib.Logics.Propositional.SequentCalculus.LK.SubformulaProperty`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean` - new file with all declarations

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.SubformulaProperty` succeeds with no errors
- All three declarations have docstrings (docBlame compliance)
- `LKProof.formulas` uses `def`, `CutFreeLKProof.subformula_property` uses `lemma`, `LKProof.subformula_property` uses `theorem`

---

### Phase 2: Register in barrel file and run CI [COMPLETED]

**Goal**: Add SubformulaProperty to the LK barrel file and pass the full CI pipeline.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Propositional.SequentCalculus.LK.SubformulaProperty` to `Cslib/Logics/Propositional/SequentCalculus/LK.lean` (after Soundness, with a note that it imports CutElimination directly)
- [ ] Update `Cslib.lean` root barrel if SubformulaProperty needs explicit registration (check if LK barrel auto-propagates)
- [ ] Run `lake exe checkInitImports` to verify Cslib.Init import compliance
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake test` to run test suite
- [ ] Run `lake build` to verify full build

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` - add SubformulaProperty import
- `Cslib.lean` - add import if needed for barrel propagation

**Verification**:
- `lake build` succeeds with no errors or warnings
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LK.SubformulaProperty` compiles without errors
- [ ] `lake build` full build succeeds
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] All three declarations have docstrings
- [ ] `LKProof.formulas` returns `Finset (Proposition Atom)` and covers all 11 constructors
- [ ] `CutFreeLKProof.subformula_property` proves the universal statement for cut-free proofs
- [ ] `LKProof.subformula_property` derives the existential version via `cutElim`

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean` - new file with 3 declarations
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` - updated barrel file
- `specs/329_cutelim_subformula_property/plans/01_subformula-property.md` - this plan
- `specs/329_cutelim_subformula_property/summaries/01_subformula-property-summary.md` - execution summary (after implementation)

## Rollback/Contingency

- Delete `SubformulaProperty.lean` and revert barrel file change
- If `Normalization.lean` import causes issues, copy only the `subformulas` and `IsSubformula` definitions locally (minimal duplication)
- If structural induction on `LKProof` proves difficult with the equation compiler, use a `match`-based proof with explicit recursion instead of the `induction` tactic
