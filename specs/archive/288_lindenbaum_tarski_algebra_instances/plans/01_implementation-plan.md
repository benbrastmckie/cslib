# Implementation Plan: Lindenbaum-Tarski Algebra Instances

- **Task**: 288 - Export named Lindenbaum-Tarski algebra instances for MPL, IPL, and CPL
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: 266
- **Research Inputs**: specs/288_lindenbaum_tarski_algebra_instances/reports/01_research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Create a single new facade module `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` that exports named, standalone declarations making explicit that the Lindenbaum-Tarski algebra of MPL is a `GeneralizedHeytingAlgebra`, IPL is a `HeytingAlgebra`, and CPL (as `IPL union CPL`) is a `BooleanAlgebra`. The generic instances already exist in `Lindenbaum.lean` but are anonymous and parameterized over arbitrary theories; this module specializes and names them for direct use. The free Boolean algebra universal property for CPL is deferred to a separate task.

### Research Integration

Key findings from research report `01_research.md`:
- Two parallel Lindenbaum-Tarski constructions exist: ND-based (`LindenbaumAlgebra T` in `Lindenbaum.lean`) and Hilbert-based (`HilbertLindenbaumAlgebra Axioms` in `HilbertLindenbaum.lean`)
- All 6 target instances verified to resolve via `lean_run_code`
- `IsIntuitionistic` and `IsClassical` for `IPL union CPL` do NOT synthesize automatically -- `instIsIntuitionisticExtention` and `instIsClassicalExtention` are `theorem`s not `instance`s, so explicit instances for the union theory must be provided
- ND-level "classical propositional logic" is `IPL union CPL`, consistent with `HilbertConservativeGlivenko.lean` bridge theorems
- Implementation is a thin facade (~100-150 lines)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances propositional logic infrastructure in the Foundations/Logic layer. It does not directly correspond to a specific ROADMAP.md item but strengthens the algebraic semantics API used by downstream modal and temporal completeness work.

## Goals & Non-Goals

**Goals**:
- Create named type abbreviations `MPL.LindenbaumAlgebra`, `IPL.LindenbaumAlgebra`, `CPL.LindenbaumAlgebra` for the three logics
- Export named instance declarations: `MPL.instGHA`, `IPL.instHA`, `CPL.instBA`
- Provide explicit `IsIntuitionistic` and `IsClassical` instances for the union theory `IPL union CPL`
- Include characterization theorems as named standalone facts
- Pass full CSLib CI pipeline

**Non-Goals**:
- Free Boolean algebra universal property for CPL (deferred to separate task)
- Hilbert-based re-exports (the Hilbert construction already has named instances)
- Modifying existing `Lindenbaum.lean` or `HilbertLindenbaum.lean` files
- Nontriviality results (not part of core deliverable)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `inferInstance` fails for union theory instances | M | M | Research verified via `lean_run_code`; provide explicit proofs using `instIsIntuitionisticExtention Set.subset_union_left` if needed |
| `noncomputable` propagation from BooleanAlgebra instance | L | H | Expected behavior -- mark `CPL.instBA` as `noncomputable` per existing pattern in `Lindenbaum.lean` |
| Import cycle or missing dependency | L | L | Module only imports from `Lindenbaum.lean` which is well-tested |
| `lake exe checkInitImports` failure | L | M | Ensure `import Cslib.Init` is first import line |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Create LindenbaumInstances.lean module [COMPLETED]

**Goal**: Create the new facade module with all named abbreviations, instances, and characterization theorems.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` with CSLib copyright header
- [ ] Add imports: `import Cslib.Init` and `import Cslib.Logics.Propositional.Semantics.Algebra.Lindenbaum`
- [ ] Open the `Cslib.Logic.PL` and `Cslib.Logic.PL.Theory` namespaces
- [ ] Add universe and variable declarations: `variable {Atom : Type*} [DecidableEq Atom]`
- [ ] Define named type abbreviations:
  - `abbrev MPL.LindenbaumAlgebra (Atom) [DecidableEq Atom]` = `LindenbaumAlgebra (MPL : Theory Atom)`
  - `abbrev IPL.LindenbaumAlgebra (Atom) [DecidableEq Atom]` = `LindenbaumAlgebra (IPL : Theory Atom)`
  - `abbrev CPL.LindenbaumAlgebra (Atom) [DecidableEq Atom]` = `LindenbaumAlgebra (IPL ∪ CPL : Theory Atom)`
- [ ] Provide explicit typeclass instances for the union theory:
  - `instance : IsIntuitionistic (IPL ∪ CPL : Theory Atom)` using `instIsIntuitionisticExtention Set.subset_union_left`
  - `instance : IsClassical (IPL ∪ CPL : Theory Atom)` using `instIsClassicalExtention Set.subset_union_right`
- [ ] Define named instance declarations:
  - `instance MPL.instGHA : GeneralizedHeytingAlgebra (MPL.LindenbaumAlgebra Atom)` via `inferInstance`
  - `instance IPL.instHA : HeytingAlgebra (IPL.LindenbaumAlgebra Atom)` via `inferInstance`
  - `noncomputable instance CPL.instBA : BooleanAlgebra (CPL.LindenbaumAlgebra Atom)` via `inferInstance`
- [ ] Add characterization theorems:
  - `theorem MPL.lindenbaumIsGHA` stating `GeneralizedHeytingAlgebra (LindenbaumAlgebra (MPL : Theory Atom))`
  - `theorem IPL.lindenbaumIsHA` stating `HeytingAlgebra (LindenbaumAlgebra (IPL : Theory Atom))`
  - `theorem CPL.lindenbaumIsBA` stating `BooleanAlgebra (LindenbaumAlgebra (IPL ∪ CPL : Theory Atom))`
- [ ] Add module docstring documenting the relationship between logics and algebra structures
- [ ] Verify the file builds: `lake build Cslib.Logics.Propositional.Semantics.Algebra.LindenbaumInstances`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` - New file (create)

**Verification**:
- File compiles without errors or sorry
- All 3 named instances resolve
- All 3 characterization theorems type-check
- No axiom usage beyond what Lindenbaum.lean already uses

---

### Phase 2: CI pipeline and barrel import [COMPLETED]

**Goal**: Integrate the new module into the CSLib build system and pass the full CI pipeline.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Run `lake exe checkInitImports` to verify `Cslib.Init` import
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake build` for full project build verification
- [ ] Run `lake test` to verify no test regressions

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib.lean` - Updated by `mk_all` to include new module import

**Verification**:
- All CI commands pass without errors
- No test regressions
- `Cslib.lean` includes the new module

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.LindenbaumInstances` succeeds
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake build` (full project) succeeds
- [ ] `lake test` passes
- [ ] `lean_verify` on key declarations shows no unexpected axiom usage

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` - New facade module
- `Cslib.lean` - Updated barrel import
- `specs/288_lindenbaum_tarski_algebra_instances/plans/01_implementation-plan.md` - This plan

## Rollback/Contingency

Delete the new `LindenbaumInstances.lean` file and revert the `Cslib.lean` barrel import update. No existing files are modified by this task, so rollback is trivial.
