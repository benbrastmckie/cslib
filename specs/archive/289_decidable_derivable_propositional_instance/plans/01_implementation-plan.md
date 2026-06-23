# Implementation Plan: Decidable (Derivable PropositionalAxiom phi) Instance

- **Task**: 289 - Compose instDecidableTautology with prop_completeness_iff_tautology
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: 266 (completed)
- **Research Inputs**: reports/01_research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Register a `Decidable (Derivable PropositionalAxiom phi)` instance by composing the existing
`instDecidableTautology` (Bool.lean line 175) with `prop_completeness_iff_tautology`
(StrongCompleteness.lean line 558) via `decidable_of_iff`. This is a one-liner addition
placed inline in StrongCompleteness.lean immediately before the closing `end Cslib.Logic.PL`.
No new files or imports are needed.

### Research Integration

Research report (01_research.md) confirmed:
- Both components exist in the same namespace (`Cslib.Logic.PL`) and import chain
- The composition `decidable_of_iff (Tautology phi) prop_completeness_iff_tautology` compiles
  cleanly (verified via `lean_run_code`)
- Placement inline in StrongCompleteness.lean is preferred over a separate file
- All lint requirements (docBlame, defLemma, naming) are satisfied by the proposed code
- Task 266 dependency is satisfied (archived/completed)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly reference this task.

## Goals & Non-Goals

**Goals**:
- Register `instDecidableDerivablePropositionalAxiom` as a Lean instance so that
  `Decidable (Derivable PropositionalAxiom phi)` is automatically inferred for `[Fintype Atom] [DecidableEq Atom]`
- Pass all CSLib CI checks (build, lint, style, tests, imports)

**Non-Goals**:
- Creating a separate `Decidability.lean` file (disproportionate overhead for one instance)
- Extending decidability to other axiom systems beyond `PropositionalAxiom`
- Modifying `instDecidableTautology` or `prop_completeness_iff_tautology`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe unification failure | H | L | Already verified via lean_run_code; variable {Atom : Type*} unifies cleanly |
| Instance diamond/overlap | M | L | No other Decidable instance for Derivable PropositionalAxiom exists in CSLib |
| Upstream StrongCompleteness.lean changes | M | L | Insertion point is at end of file (line 560-562), minimal conflict surface |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add Decidable Instance and Verify [COMPLETED]

**Goal**: Add the `instDecidableDerivablePropositionalAxiom` instance to StrongCompleteness.lean
and verify it passes all CI checks.

**Tasks**:
- [ ] Insert the instance definition with docstring before `end Cslib.Logic.PL` (after line 560)
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness` to verify compilation
- [ ] Run `lean_verify` on `Cslib.Logic.PL.instDecidableDerivablePropositionalAxiom` to confirm no sorry/axiom issues
- [ ] Run `lake exe checkInitImports` to verify import compliance
- [ ] Run `lake exe lint-style` to verify style compliance

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - Add instance before `end Cslib.Logic.PL`

**Code to add** (insert between line 560 and `end Cslib.Logic.PL`):

```lean
/-- Derivability from `PropositionalAxiom` is decidable when `Atom` is a `Fintype` with
`DecidableEq`. The decision procedure reduces derivability to tautology-checking via
`prop_completeness_iff_tautology`, then uses `instDecidableTautology` to enumerate all
Boolean valuations. -/
instance instDecidableDerivablePropositionalAxiom [Fintype Atom] [DecidableEq Atom]
    (phi : PL.Proposition Atom) : Decidable (Derivable PropositionalAxiom phi) :=
  decidable_of_iff (Tautology phi) prop_completeness_iff_tautology
```

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness` succeeds with no errors
- `lean_verify` confirms no sorry or non-standard axioms
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

## Testing & Validation

- [ ] Module builds without errors (`lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness`)
- [ ] Instance is axiom-free and sorry-free (`lean_verify`)
- [ ] Import compliance (`lake exe checkInitImports`)
- [ ] Style compliance (`lake exe lint-style`)

## Artifacts & Outputs

- `plans/01_implementation-plan.md` (this file)
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` (modified)
- `summaries/01_execution-summary.md` (post-implementation)

## Rollback/Contingency

Remove the inserted instance definition (6 lines including docstring) from
StrongCompleteness.lean. The file reverts to its pre-task state with no other changes needed.
Alternatively, `git checkout -- Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`.
