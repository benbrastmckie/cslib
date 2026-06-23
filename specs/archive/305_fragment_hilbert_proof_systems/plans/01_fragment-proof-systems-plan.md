# Implementation Plan: Fragment Hilbert Proof Systems

- **Task**: 305 - Fragment Hilbert Proof Systems
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: Task 302 (fragment predicates, completed)
- **Research Inputs**: specs/305_fragment_hilbert_proof_systems/reports/01_fragment-proof-systems-research.md
- **Artifacts**: plans/01_fragment-proof-systems-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Define two fragment-specific Hilbert axiom predicates (`ConjImpAxiom` with 5 constructors and
`ImpAxiom` with 2 constructors) in a new file `FragmentAxioms.lean`, along with subsumption
theorems linking them to the existing `MinPropAxiom` hierarchy, substitution closure theorems,
implication axiom witnesses, fragment predicate compatibility proofs, and deduction theorem
instances. Additionally, add two new tag types (`HilbertConjImp`, `HilbertImp`) to
`ProofSystem.lean` and register typeclass instances in a new `FragmentInstances.lean`. All
proofs are mechanical case-analysis or direct instantiation of existing parameterized
infrastructure.

### Research Integration

The research report confirmed:
- Both fragment predicates follow the exact pattern established by `PropositionalAxiom`,
  `IntPropAxiom`, and `MinPropAxiom` in `Axioms.lean`.
- The deduction theorem is already parameterized over arbitrary axiom predicates requiring only
  K and S witnesses; no new proof is needed, just witness instantiation.
- Substitution closure follows the `subst_preserves_*` pattern in `FromHilbert.lean`.
- Fragment predicate compatibility (`IsOrBotFree`, `IsImpTopOnly`) is provable by simple
  case analysis on the inductive constructors.
- Tag type and instance registration follows the `IntMinInstances.lean` pattern.
- Zero sorry risk; estimated 200-300 lines total across files.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly apply. This task advances the propositional algebraic semantics
pipeline (tasks 303-311) which is internal to `Logics/Propositional/`.

## Goals & Non-Goals

**Goals**:
- Define `ConjImpAxiom` (K, S, andI, andE1, andE2) and `ImpAxiom` (K, S) inductive predicates
- Prove subsumption: `ImpAxiom -> ConjImpAxiom -> MinPropAxiom`
- Prove substitution closure for both predicates
- Prove fragment predicate compatibility (`ConjImpAxiom.isOrBotFree`, `ImpAxiom.isImpTopOnly`)
- Instantiate deduction theorem for both fragments
- Add tag types `HilbertConjImp` and `HilbertImp` with typeclass instances
- Pass all CSLib CI checks (`lake build`, `checkInitImports`, `lint-style`, `lake test`)

**Non-Goals**:
- Define new bundled typeclasses (e.g., `ConjImpHilbert`); individual `HasAxiom*` instances suffice
- Prove Lindenbaum algebra properties for the fragments (tasks 306, 309)
- Prove conservative extension results (tasks 308, 311)
- Modify existing axiom predicates or derivation infrastructure

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `FragmentPredicates.lean` import pulls heavy transitive deps | L | M | Acceptable per research; fragment compat proofs genuinely need the predicate defs |
| `simp` fails on `IsOrBotFree`/`IsImpTopOnly` case analysis | L | L | Fall back to manual `Bool.and_eq_true` rewriting as done in existing `FragmentPredicates.lean` |
| Tag types in `ProofSystem.lean` cause import cycle | M | L | `ProofSystem.lean` is at Foundations level, no downstream imports from Propositional |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Complete Fragment Axiom Infrastructure [COMPLETED]

**Goal**: Create all fragment axiom definitions, theorems, tag types, and instances in a single phase. The task is simple enough (mechanical case-analysis proofs following established patterns) that splitting into multiple phases would add overhead without benefit.

**Tasks**:
- [ ] Add tag types `Propositional.HilbertConjImp` and `Propositional.HilbertImp` to `Cslib/Foundations/Logic/ProofSystem.lean` (2 `opaque` declarations with docstrings, following existing pattern at lines 491-497)
- [ ] Create `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`:
  - [ ] Module docstring explaining fragment axiom predicates and their role
  - [ ] `inductive ConjImpAxiom` with 5 constructors: `implyK`, `implyS`, `andI`, `andE1`, `andE2`
  - [ ] `inductive ImpAxiom` with 2 constructors: `implyK`, `implyS`
  - [ ] Subsumption: `ImpAxiom.toConjImpAxiom` and `ConjImpAxiom.toMinPropAxiom`
  - [ ] Implication witnesses: `ConjImpAxiom.mem_implyK`, `ConjImpAxiom.mem_implyS`, `ImpAxiom.mem_implyK`, `ImpAxiom.mem_implyS`
  - [ ] Substitution closure: `subst_preserves_conjImpAxiom` and `subst_preserves_impAxiom`
  - [ ] Fragment compatibility: `ConjImpAxiom.isOrBotFree` and `ImpAxiom.isImpTopOnly`
  - [ ] Deduction theorem instances: apply `hasDeductionTheorem` with `mem_implyK`/`mem_implyS` witnesses
- [ ] Create `Cslib/Logics/Propositional/ProofSystem/FragmentInstances.lean`:
  - [ ] `InferenceSystem` + `ModusPonens` for `HilbertConjImp` (using `DerivationTree ConjImpAxiom []`)
  - [ ] `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2` for `HilbertConjImp`
  - [ ] `MinimalHilbert HilbertConjImp` bundled instance
  - [ ] `InferenceSystem` + `ModusPonens` for `HilbertImp` (using `DerivationTree ImpAxiom []`)
  - [ ] `HasAxiomImplyK`, `HasAxiomImplyS` for `HilbertImp`
  - [ ] `MinimalHilbert HilbertImp` bundled instance
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Run `lake build` to verify compilation
- [ ] Run `lake exe checkInitImports` to verify imports
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake test` to verify test suite

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- add 2 opaque tag type declarations
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` -- new file, ~150-200 lines
- `Cslib/Logics/Propositional/ProofSystem/FragmentInstances.lean` -- new file, ~80-100 lines
- `Cslib.lean` -- updated by `mk_all` to include new modules

**Verification**:
- `lake build` succeeds with no errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- `#check @ConjImpAxiom` and `#check @ImpAxiom` resolve
- `#check @ConjImpAxiom.toMinPropAxiom` and `#check @ImpAxiom.toConjImpAxiom` resolve
- `#check (inferInstance : MinimalHilbert Propositional.HilbertConjImp (F := PL.Proposition Nat))` resolves
- `#check (inferInstance : MinimalHilbert Propositional.HilbertImp (F := PL.Proposition Nat))` resolves

## Testing & Validation

- [ ] `lake build` compiles all new files without errors or warnings
- [ ] `lake exe checkInitImports` confirms all files import `Cslib.Init`
- [ ] `lake exe lint-style` passes (docstrings on all declarations, correct naming)
- [ ] `lake test` passes (no regression)
- [ ] Subsumption chain type-checks: `ImpAxiom -> ConjImpAxiom -> MinPropAxiom -> IntPropAxiom -> PropositionalAxiom`
- [ ] Deduction theorem instances resolve for both fragment derivation systems
- [ ] Tag type instances provide `MinimalHilbert` for both `HilbertConjImp` and `HilbertImp`

## Artifacts & Outputs

- `specs/305_fragment_hilbert_proof_systems/plans/01_fragment-proof-systems-plan.md` (this plan)
- `Cslib/Foundations/Logic/ProofSystem.lean` (modified: 2 new tag types)
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` (new file)
- `Cslib/Logics/Propositional/ProofSystem/FragmentInstances.lean` (new file)
- `specs/305_fragment_hilbert_proof_systems/summaries/01_fragment-proof-systems-summary.md` (post-implementation)

## Rollback/Contingency

All changes are additive (new files and new declarations in existing file). Rollback is
straightforward:
1. Delete `FragmentAxioms.lean` and `FragmentInstances.lean`
2. Revert the 2 opaque declarations added to `ProofSystem.lean`
3. Re-run `lake exe mk_all --module` to update barrel import
4. Verify with `lake build`
