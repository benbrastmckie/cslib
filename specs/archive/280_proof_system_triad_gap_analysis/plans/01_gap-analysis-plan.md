# Implementation Plan: Task #280

- **Task**: 280 - Proof System Triad Gap Analysis
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: 266 (effectively complete)
- **Research Inputs**: specs/280_proof_system_triad_gap_analysis/reports/01_team-research.md
- **Artifacts**: plans/01_gap-analysis-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: false

## Overview

This is a metatask whose deliverable is a set of new tasks in state.json, not code. The research identified six gap areas in CSLib's propositional proof system triad (Hilbert, Natural Deduction, Sequent Calculus). The Hilbert leg is fully closed (zero sorries, tasks 281-285 complete). The ND leg is strong combinatorially but lacks proof-theoretic metatheory (normalization, Curry-Howard). The SC leg is entirely absent (task 279, not started). Five new tasks will be created to fill the remaining gaps, plus task 279's dependency on 280 will be unblocked. Stone duality (P6 from research) is deferred as mathematical enrichment beyond the triad's metatheoretic purpose.

### Research Integration

Key findings from team research (4 teammates):
- Hilbert system: fully closed, no new tasks needed
- ND system: missing normalization theorem, subformula property, and Curry-Howard correspondence
- Sequent calculus: entirely absent (task 279 scope), with Critic's recommendation to phase cut elimination separately documented as context for 279's planning
- Algebraic semantics: comprehensive; only gap is named Lindenbaum-Tarski instances not exported
- Decidability: `Decidable (Tautology phi)` exists for CPL; `Decidable (Derivable PropositionalAxiom phi)` is a one-liner gap; IPL decidability requires LJ (blocked on 279)
- Task 266 status anomaly: shows "implementing" but is effectively complete (completion_summary present, all phases done, CI green)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

The ROADMAP.md focuses on the BimodalLogic-to-CSLib port (Foundations/Logic, Modal, Temporal, Bimodal). The propositional proof system triad underpins all of these logics through Foundations/Logic infrastructure. Specifically:
- ND normalization enables a subformula property usable across all logics
- Sequent calculus provides a cut-elimination backbone that generalizes to modal logics
- The three-way equivalence validates CSLib's proof system architecture for downstream consumers

## Goals & Non-Goals

**Goals**:
- Create 5 new implementation tasks covering all identified gaps in the proof system triad
- Establish correct dependency ordering among new tasks and existing tasks (266, 279)
- Unblock task 279 by completing 280's research-gate dependency
- Provide task descriptions scoped tightly enough for single-agent implementation

**Non-Goals**:
- Implementing any Lean code (this is a metatask: deliverable is tasks, not proofs)
- Modifying task 279's description or scope (that is for `/revise 279` if needed)
- Creating tasks for Stone duality (P6) -- deferred as enrichment beyond triad purpose
- Creating ND ProofSystem tag types (no concrete downstream consumer identified)
- Re-implementing any Hilbert-side work already completed in tasks 266/281-285

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task 266 status anomaly confuses dependency analysis | M | M | Note in task descriptions that 266 is effectively complete; recommend `/vet 266` |
| Curry-Howard scope creep (4 possible interpretations) | H | M | Scope to normalization-first (P1), then explicit isomorphism (P2) with reduced fragment option |
| Cut elimination difficulty underestimated in task 279 | H | M | Document phasing recommendation as context for 279's planning; not a new task from 280 |
| New tasks overlap with 266 deliverables | M | L | Explicit non-overlap checklist in each task description |
| Representation mismatch blocks Curry-Howard (Finset vs List contexts) | M | M | P2 scoped with reduced-fragment fallback ({arrow, and} only) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Independent Quick-Win Tasks [COMPLETED]

**Goal**: Create the two small, independent tasks that can start immediately without any blocking dependencies.

**Tasks**:
- [ ] Create task: "Named Lindenbaum-Tarski algebra instances for MPL/IPL/CPL" (cslib type)
  - Description: Export named `abbrev` or `instance` declarations making explicit that the Lindenbaum-Tarski algebra of MPL is a GeneralizedHeytingAlgebra, IPL is a HeytingAlgebra, and CPL is a BooleanAlgebra. These are currently implicit in algebraic completeness proofs but not exported as standalone usable facts. Optionally prove the free Boolean algebra universal property for CPL. Files: new module `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean`. Depends on 266.
  - Task type: cslib
  - Dependencies: [266]
  - Estimated effort: 4-8 hours
- [ ] Create task: "`Decidable (Derivable PropositionalAxiom phi)` instance" (cslib type)
  - Description: Compose `instDecidableTautology` with `prop_completeness_iff_tautology` to produce a `Decidable (Derivable PropositionalAxiom phi)` instance for `[Fintype Atom] [DecidableEq Atom]`. This is a one-liner composition gap: the bridge `Tautology phi <-> Derivable PropositionalAxiom phi` exists, and `Decidable (Tautology phi)` exists, but the composed `Decidable` instance is not registered. File: `Cslib/Logics/Propositional/Metalogic/Decidability.lean` or inline in `StrongCompleteness.lean`. Depends on 266.
  - Task type: cslib
  - Dependencies: [266]
  - Estimated effort: 1-2 hours

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `specs/state.json` - Add two new task entries
- `specs/TODO.md` - Regenerated from state.json

**Verification**:
- Both tasks appear in state.json with correct dependencies, type, and description
- TODO.md reflects the new tasks after regeneration

---

### Phase 2: Create ND Normalization Task [COMPLETED]

**Goal**: Create the medium-scope task for ND normalization, which is the critical prerequisite for the Curry-Howard correspondence.

**Tasks**:
- [ ] Create task: "Natural deduction normalization and subformula property for propositional logic" (cslib type)
  - Description: Formalize Prawitz-style normalization for CSLib's `Theory.Derivation` (propositional IPL and MPL). Define `Derivation.isNormal` predicate (no maximal formula -- i.e., no introduction rule immediately followed by the corresponding elimination on the same formula). Prove a normalization function `normalize` that transforms any derivation into a normal form. Derive the subformula property as a corollary: every formula in a normal derivation is a subformula of the conclusion or a hypothesis. The `Theory.Derivation` type is `Type u` (not `Prop`), enabling a computable normalization function. Reference: [Prawitz1965] Ch. IV-V. Consider starting with the implicational fragment ({arrow} only) as a milestone, then extending to full IPL connectives. Files: new module `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`. Depends on 266.
  - Task type: cslib
  - Dependencies: [266]
  - Estimated effort: 20-40 hours (medium-large; main challenge is the permutation reductions for disjunction)

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `specs/state.json` - Add one new task entry
- `specs/TODO.md` - Regenerated from state.json

**Verification**:
- Task appears in state.json with correct dependencies and description
- Description explicitly scopes the normalization theorem and subformula property
- Description mentions reduced-fragment milestone ({arrow} only) as a risk mitigation

---

### Phase 3: Create SC-Dependent Tasks (Blocked on 279) [COMPLETED]

**Goal**: Create the two tasks that are blocked on task 279 (sequent calculus) completing first.

**Tasks**:
- [ ] Create task: "Three-way proof system equivalence: Hilbert, ND, and sequent calculus" (cslib type)
  - Description: After task 279 delivers `hilbert_iff_lk` and `nd_iff_lk`, create a unifying module stating the three-way equivalence as `List.TFAE` theorems. For each of MPL, IPL, and CPL, prove that Hilbert derivability, ND derivability, and SC derivability are equivalent (e.g., `[Derivable PropositionalAxiom phi, DerivableIn CPL (empty turnstile phi), LKDerivable phi].TFAE` for CPL). The pairwise bridges are: Hilbert-ND from task 266, Hilbert-SC and ND-SC from task 279. This is purely compositional. File: `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`. Depends on 279.
  - Task type: cslib
  - Dependencies: [279]
  - Estimated effort: 4-6 hours
- [ ] Create task: "IPL decidability via cut-free LJ proof search" (cslib type)
  - Description: After task 279 delivers LJ with cut elimination, formalize the connection between cut-free proof search and decidability. Define a bounded backward proof search procedure over cut-free LJ: the search space is finite because all formulas in a cut-free proof are subformulas of the sequent. Prove termination via a well-founded measure (e.g., multiset of subformula sizes). Produce `Decidable (LJDerivable (Gamma turnstile A))` and lift via `nd_iff_lk` to `Decidable (DerivableIn IPL (Gamma turnstile A))`. This establishes IPL decidability constructively. File: `Cslib/Logics/Propositional/SequentCalculus/Decidability.lean`. Depends on 279.
  - Task type: cslib
  - Dependencies: [279]
  - Estimated effort: 15-25 hours

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `specs/state.json` - Add two new task entries
- `specs/TODO.md` - Regenerated from state.json

**Verification**:
- Both tasks appear in state.json with dependency on 279
- Descriptions are specific about what task 279 must deliver first

---

### Phase 4: Create Curry-Howard Task and Update Task 280 Status [COMPLETED]

**Goal**: Create the Curry-Howard correspondence task (depends on the normalization task from Phase 2), update task 280's status to planned, and write the orchestrator handoff.

**Tasks**:
- [ ] Create task: "Curry-Howard correspondence: propositional ND proofs and typed lambda terms" (cslib type)
  - Description: Establish the formal Curry-Howard isomorphism between `Theory.Derivation Gamma A` (propositional ND proofs) and well-typed lambda terms. Define a purpose-built simply-typed term language over `PL.Proposition` as the type language (to avoid representation mismatch with the existing locally-nameless STLC). Formalize: (1) `curry_howard_forward` extracting a well-typed term from a derivation, (2) `curry_howard_backward` extracting a derivation from a well-typed term, (3) roundtrip properties showing the maps are mutually inverse. Map ND constructors to term constructors: `impI` to lambda, `impE` to application, `andI` to pair, `andE1/2` to projections, `orI1/2` to injections, `orE` to case. As a reduced-scope fallback, the {arrow, and} fragment (omitting disjunction/sum types) is a self-contained milestone. Normal derivations correspond to beta-normal terms, connecting to the normalization task. References: [SorensenUrzyczyn2006]. Files: new directory `Cslib/Logics/Propositional/CurryHoward/`. Depends on ND normalization task.
  - Task type: cslib
  - Dependencies: [normalization task number from Phase 2]
  - Estimated effort: 30-50 hours (large; main challenge is the representation bridge)
- [ ] Update state.json: set task 280 status to "planned"
- [ ] Regenerate TODO.md
- [ ] Write orchestrator handoff to `.orchestrator-handoff.json`

**Timing**: 30 minutes

**Depends on**: 1, 2, 3

**Files to modify**:
- `specs/state.json` - Add Curry-Howard task, update task 280 status
- `specs/TODO.md` - Regenerated from state.json
- `specs/280_proof_system_triad_gap_analysis/.orchestrator-handoff.json` - Handoff metadata

**Verification**:
- All 5 new tasks present in state.json with correct dependencies
- Task 280 shows status "planned" in state.json
- TODO.md is regenerated and consistent
- Dependency graph: P5/P6(Lindenbaum + Decidable) independent; P1(normalization) independent; P2(Curry-Howard) depends on P1; P3(three-way equiv) depends on 279; P4(IPL decidability) depends on 279

## Testing & Validation

- [ ] All 5 new tasks present in state.json with non-empty descriptions
- [ ] Each task has correct `task_type: "cslib"` and appropriate dependencies
- [ ] No new task overlaps with tasks 266 or 279 deliverables
- [ ] Dependency graph is acyclic: independent tasks have no new-task dependencies; P2 depends on P1; P3 and P4 depend on 279
- [ ] TODO.md regenerated and consistent with state.json
- [ ] Task 280 status updated to "planned"

## Artifacts & Outputs

- `specs/280_proof_system_triad_gap_analysis/plans/01_gap-analysis-plan.md` (this file)
- 5 new tasks in `specs/state.json` (task numbers 288-292)
- `specs/280_proof_system_triad_gap_analysis/.orchestrator-handoff.json`

## Rollback/Contingency

If task creation fails partway:
1. Restore state.json from git (`git checkout -- specs/state.json`)
2. Regenerate TODO.md (`bash .claude/scripts/generate-todo.sh`)
3. Re-run `/implement 280` to retry

All new tasks are purely additive to state.json (no existing task modifications except 280's own status). Rollback is safe.

## Appendix: New Task Summary

| Task | Title | Type | Dependencies | Effort | Wave |
|------|-------|------|--------------|--------|------|
| T1 | Named Lindenbaum-Tarski algebra instances for MPL/IPL/CPL | cslib | 266 | 4-8h | Independent |
| T2 | `Decidable (Derivable PropositionalAxiom phi)` instance | cslib | 266 | 1-2h | Independent |
| T3 | ND normalization and subformula property for propositional logic | cslib | 266 | 20-40h | Independent |
| T4 | Three-way proof system equivalence (Hilbert/ND/SC) | cslib | 279 | 4-6h | After 279 |
| T5 | IPL decidability via cut-free LJ proof search | cslib | 279 | 15-25h | After 279 |
| T6 | Curry-Howard correspondence (propositional ND and typed terms) | cslib | T3 | 30-50h | After T3 |

**Deferred** (not created):
- Stone duality for CPL Lindenbaum algebra (mathematical enrichment, low confidence in Mathlib coverage)

**Not needed** (already complete):
- Hilbert algebraic completeness (done in 281-285)
- Hilbert-ND bridge (done in 266)
- `Decidable (Tautology phi)` (done in 266)
- Glivenko and conservative extension (done in HilbertConservativeGlivenko.lean)
- ND algebraic completeness (done in Algebra/Completeness.lean)

## Appendix: Dependency Graph

```
[266: Propositional improvements (effectively complete)]
    |
    +---> T1: Named Lindenbaum instances [SMALL, independent]
    |
    +---> T2: Decidable (Derivable) instance [TINY, independent]
    |
    +---> T3: ND normalization [MEDIUM, independent]
              |
              +---> T6: Curry-Howard [LARGE, needs T3]

[279: LK/LJ sequent calculus (not started, depends on 280)]
    |
    +---> T4: Three-way equivalence [SMALL, needs 279]
    |
    +---> T5: IPL decidability via LJ [MEDIUM, needs 279]
```

Critical path: 280 (this task) -> 279 -> T4/T5
Parallel path: T3 -> T6 (ND proof theory, independent of SC)
Quick wins: T1, T2 (small, independent, can start immediately)
