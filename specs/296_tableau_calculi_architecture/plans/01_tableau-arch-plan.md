# Implementation Plan: Task #296

- **Task**: 296 - Create Tableau Calculi Architecture Metatask
- **Status**: [IMPLEMENTING]
- **Effort**: 0.5 hours (metatask: plan is the deliverable)
- **Dependencies**: None (metatask -- child tasks have internal dependencies)
- **Research Inputs**: specs/296_tableau_calculi_architecture/reports/01_tableau-arch-research.md
- **Artifacts**: plans/01_tableau-arch-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: false

## Overview

This metatask produces precisely scoped implementation tasks covering the full tableau calculi pipeline for CSLib, from propositional through bimodal logics. The research report identified six tasks (A-F) organized in a layered dependency graph. This plan refines those into concrete task descriptions with file inventories, effort estimates, and a dependency DAG. The plan itself is the deliverable -- "implementing" this task means creating the child tasks in state.json.

### Research Integration

The research report (01_tableau-arch-research.md) provided:
- Complete codebase inventory of existing formula types, connective typeclasses, proof systems, and the bimodal decidability system (~7,400 lines)
- Analysis of the existing `PropositionalTableau.lean` (210 lines, unused) and how it relates to the bimodal `Sign`/`SignedFormula`/`TableauRule` infrastructure
- Detailed rule layering analysis: how modal rules (box/diamond) and temporal rules (G/H, F/P, U/S) extend propositional rules
- Label architecture analysis (none vs world vs time vs world+time)
- Recommendation to keep the bimodal system standalone and build new shared infrastructure validated through propositional/modal/temporal systems first
- Five identified risks with mitigations (native and/or complexity, label proliferation, S5 non-reusability, divergent termination arguments, bimodal regression risk)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following roadmap items:
- The tableau pipeline extends `Foundations/Logic/` with shared tableau infrastructure
- It creates new `Logics/Propositional/Tableau/`, `Logics/Modal/Tableau/`, and `Logics/Temporal/Tableau/` modules
- It complements the existing bimodal decidability system (`Logics/Bimodal/Metalogic/Decidability/`) already listed as completed
- It aligns with the broader project structure where each logic level adds its own metalogic capabilities

## Goals & Non-Goals

**Goals**:
- Define 5 precisely scoped implementation tasks with clear file inventories
- Establish a dependency graph that enables parallel work where possible
- Provide effort estimates calibrated against the known bimodal decidability codebase (~7,400 lines)
- Ensure each task is independently completable and verifiable
- Relate new tasks to existing tasks (279 sequent calculus, 291 three-way equivalence, 41 abstract completeness)

**Non-Goals**:
- Implementing any Lean code (this is a planning metatask)
- Refactoring the existing bimodal decidability system (deferred as optional future work)
- Creating a unified label type parameterized across all logics (research recommends against this)
- Building sequent calculus or natural deduction systems (those are separate task chains)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task scope underestimation for modal/temporal layers | H | M | Estimates calibrated against known bimodal system; buffer included in each task |
| Propositional native and/or adds unexpected complexity | M | M | Research identified this; PropositionalTableau.lean already handles decomposition parameterization |
| Modal K may need significant loop-checking infrastructure for S4 extension | M | L | S4/S5 extensions are a separate task from basic Modal K, isolating risk |
| Child tasks may reveal need for additional foundational infrastructure | M | M | Foundations task (Task A) is designed to be extended; later tasks can add to it |
| Temporal tableau complexity (until/since rules are unique to temporal logic) | H | M | Bimodal system already implements these rules; patterns can be studied and adapted |

## Implementation Phases

This metatask has a single phase: create the child tasks. The phases below describe what each child task will accomplish.

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Create Child Tasks [IN PROGRESS]

**Goal**: Create 5 implementation tasks in state.json with correct dependency relationships

**Tasks**:
- [ ] Create child task A: Foundations Tableau Infrastructure
- [ ] Create child task B: Propositional Tableau System
- [ ] Create child task C: Modal K Tableau
- [ ] Create child task D: Modal Extensions (T, S4, S5)
- [ ] Create child task E: Temporal Tableau

**Timing**: 0.5 hours

**Depends on**: none

**Verification**:
- All 5 tasks exist in state.json with correct descriptions
- Dependencies between tasks are correctly encoded
- TODO.md shows the dependency graph

---

## Child Task Specifications

### Child Task A: Foundations Tableau Infrastructure

**Title**: Build shared tableau infrastructure in Foundations/Logic/Tableau/

**Description**: Refactor and extend the existing `PropositionalTableau.lean` (210 lines) into a proper module directory at `Cslib/Foundations/Logic/Tableau/`. This provides the shared infrastructure consumed by all logic-specific tableau systems. Unify the `PropSign` type (from Foundations) with the bimodal `Sign` type into a single canonical sign type. Create generic signed formula, rule result, branch, and closure types parameterized to work across all logics. Preserve backward compatibility with the bimodal system by keeping its existing types until an explicit migration task.

**Task Type**: cslib

**Files to create**:
- `Cslib/Foundations/Logic/Tableau.lean` -- Module root (import hub)
- `Cslib/Foundations/Logic/Tableau/Sign.lean` -- Unified pos/neg sign type with decidable equality, simp lemmas
- `Cslib/Foundations/Logic/Tableau/SignedFormula.lean` -- Generic `SignedFormula (F : Type*) (L : Type*)` parameterized over formula type F and label type L (with `L = Unit` for propositional)
- `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean` -- 8 propositional rules refactored from current `PropositionalTableau.lean`, parameterized over decomposition functions (andOf?, orOf?, impOf?, negOf?)
- `Cslib/Foundations/Logic/Tableau/RuleResult.lean` -- Generic `RuleResult` with linear/branching/persistent/notApplicable variants (superset of current `PropRuleResult`)
- `Cslib/Foundations/Logic/Tableau/Branch.lean` -- `Branch F L := List (SignedFormula F L)` with membership, query helpers, and basic lemmas
- `Cslib/Foundations/Logic/Tableau/Closure.lean` -- Complementary pair detection: branch is closed iff it contains both T(phi) and F(phi) at the same label

**Files to modify**:
- `Cslib/Foundations/Logic.lean` -- Add `Tableau` import

**Dependencies**: None (leaf task)
**Estimated effort**: 4-6 hours (~600-800 lines)

**Verification**:
- `lake build Cslib.Foundations.Logic.Tableau` compiles
- All existing tests pass (no regression from moving PropositionalTableau content)
- Sign type has DecidableEq, BEq instances
- PropositionalRules.lean is parameterized and can be instantiated for different formula types

---

### Child Task B: Propositional Tableau System

**Title**: Implement complete propositional tableau with decidability

**Description**: Build a complete tableau decision procedure for propositional logic (`Cslib.Logic.PL.Proposition`) with soundness, completeness, and `Decidable (Valid phi)`. This is the first logic to consume the shared Foundations/Logic/Tableau/ infrastructure. The propositional formula type has native `and`/`or` constructors (unlike modal/temporal/bimodal which use Lukasiewicz encodings), so this task provides both native and encoded decomposition function sets. Use fuel-bounded expansion (following the bimodal `expandBranchWithFuel` pattern) with termination guaranteed by the subformula property. Extract valuations from open saturated branches for countermodels.

**Task Type**: cslib

**Files to create**:
- `Cslib/Logics/Propositional/Tableau.lean` -- Module root (import hub)
- `Cslib/Logics/Propositional/Tableau/Defs.lean` -- Propositional signed formula (`SignedFormula PL.Proposition Unit`), decomposition functions for native and/or/imp/neg
- `Cslib/Logics/Propositional/Tableau/Rules.lean` -- Instantiate `applyPropRule` for `PL.Proposition`, prove rule correctness lemmas
- `Cslib/Logics/Propositional/Tableau/Closure.lean` -- Branch closure specialized to propositional case, closed branch implies contradiction under any valuation
- `Cslib/Logics/Propositional/Tableau/Saturation.lean` -- Fuel-bounded expansion with applied-set tracking, termination argument via subformula closure finiteness
- `Cslib/Logics/Propositional/Tableau/Soundness.lean` -- Closed tableau implies formula is valid (bridge: closed branch -> unsatisfiable -> provable via Hilbert)
- `Cslib/Logics/Propositional/Tableau/Completeness.lean` -- Open saturated branch implies formula is satisfiable (extract valuation from Hintikka set)
- `Cslib/Logics/Propositional/Tableau/DecisionProcedure.lean` -- `DecisionResult` type (valid/invalid/timeout), `Decidable (Valid phi)` instance via tableau

**Files to modify**:
- `Cslib/Logics/Propositional.lean` -- Add `Tableau` import

**Dependencies**: Child Task A (Foundations infrastructure)
**Estimated effort**: 8-12 hours (~1,200-1,600 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau` compiles
- `Decidable (Valid phi)` instance for `PL.Proposition` is provable
- Soundness and completeness theorems are sorry-free
- Can decide simple formulas: `p -> p` is valid, `p -> q` is invalid

---

### Child Task C: Modal K Tableau

**Title**: Implement tableau system for basic modal logic K with world labels

**Description**: Build a tableau decision procedure for basic modal logic K, adding box/diamond rules on top of the propositional rules from the shared infrastructure. This introduces world labels (accessibility relation tracking) and the fundamental modal rule pattern: box-positive is universal/persistent (propagates to all accessible worlds), diamond-positive is existential (creates a fresh accessible world). Use the Lukasiewicz encoding for and/or (as modal formulas lack native constructors). Prove soundness against Kripke semantics and completeness by extracting finite Kripke countermodels from open saturated branches. The modal formula type is `Cslib.Logic.Modal.Formula` with `atom, bot, imp, box` primitives.

**Task Type**: cslib

**Files to create**:
- `Cslib/Logics/Modal/Tableau.lean` -- Module root (import hub)
- `Cslib/Logics/Modal/Tableau/Defs.lean` -- Modal signed formula with world labels (`SignedFormula Modal.Formula WorldIndex`), `WorldIndex := Nat`, decomposition functions using Lukasiewicz encodings
- `Cslib/Logics/Modal/Tableau/Rules.lean` -- 12 rules total: 8 propositional (via shared infrastructure) + 4 modal (boxPos, boxNeg, diamondPos, diamondNeg)
- `Cslib/Logics/Modal/Tableau/Branch.lean` -- World-aware branch with accessibility relation tracking (`AccessibilityInfo`), world creation counter, query helpers for "all worlds accessible from w"
- `Cslib/Logics/Modal/Tableau/Closure.lean` -- Modal closure: complementary signed formulas at the same world
- `Cslib/Logics/Modal/Tableau/Saturation.lean` -- Fuel-bounded expansion with world creation, applied-set tracking including world-rule pairs
- `Cslib/Logics/Modal/Tableau/Soundness.lean` -- Closed tableau implies K-valid (bridge to Kripke validity via `Cslib.Logics.Modal.Metalogic`)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` -- Open saturated branch yields finite Kripke model (worlds = world indices, R from accessibility info, valuation from positive atoms)

**Files to modify**:
- `Cslib/Logics/Modal.lean` -- Add `Tableau` import (if module root exists)

**Dependencies**: Child Task A (Foundations infrastructure), Child Task B (propositional rule reuse patterns, decomposition function patterns)
**Estimated effort**: 10-14 hours (~1,500-2,000 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau` compiles
- Soundness: closed tableau implies `KValid phi` (K-frame valid)
- Completeness: open branch yields a finite Kripke countermodel
- Can decide: `box(p -> q) -> box p -> box q` is K-valid (distribution axiom), `box p -> p` is not K-valid (reflexivity not assumed)

---

### Child Task D: Modal Extensions (T, S4, S5 Tableaux)

**Title**: Extend modal K tableau with frame-specific rules for T, S4, and S5

**Description**: Extend the basic Modal K tableau (Child Task C) with frame-condition-specific rules for reflexive (T), transitive (S4), and equivalence-relation (S5) frames. For T: add reflexivity rule (box phi at w implies phi at w). For S4: add transitivity-aware propagation with loop-checking to ensure termination. For S5: add equivalence-class simplification where all worlds are mutually accessible (matching the approach used in the existing bimodal decidability system). Each extension needs its own completeness proof showing the extracted countermodel satisfies the frame condition. Frame rules for B (symmetric) and 5 (Euclidean) should also be included to cover the full modal cube.

**Task Type**: cslib

**Files to create**:
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` -- Additional rules: reflexivity (T), transitivity propagation (4), symmetry (B), Euclidean (5)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` -- Loop detection for S4: recognize when expanding a world would duplicate an existing world's formula set (subset check), ensuring termination under transitive closure
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` -- S5-specific optimization: single equivalence class means box/diamond formulas propagate to all known worlds unconditionally (mirrors bimodal approach)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` -- Soundness for each frame condition: closed T-tableau implies T-valid, etc.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` -- Completeness for each system: open branch yields countermodel satisfying the frame condition

**Dependencies**: Child Task C (Modal K tableau)
**Estimated effort**: 8-12 hours (~1,200-1,800 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau` compiles (all extensions)
- T-tableau correctly validates `box p -> p` (which K-tableau rejects)
- S4-tableau terminates on formulas like `box(box p -> p)` (loop checking works)
- S5-tableau correctly validates `dia p -> box(dia p)`
- Each frame extension has soundness and completeness theorems

---

### Child Task E: Temporal Tableau

**Title**: Implement tableau system for temporal logic with until/since

**Description**: Build a tableau decision procedure for temporal logic (`Cslib.Logic.Temporal.Formula`) with until/since decomposition rules, time labels, and temporal ordering tracking. This is the most complex new tableau system because until/since rules have no modal analogue -- they require branching decomposition with event-witness and guard-continue alternatives. Adapt patterns from the bimodal decidability system (`TimeOrdering`, temporal rule structure, frame-class rules) but build fresh implementations consuming the shared Foundations infrastructure. Include frame-class-specific rules for density and discreteness. The temporal formula type has `atom, bot, imp, untl, snce` primitives using Lukasiewicz encoding for and/or.

**Task Type**: cslib

**Files to create**:
- `Cslib/Logics/Temporal/Tableau.lean` -- Module root (import hub)
- `Cslib/Logics/Temporal/Tableau/Defs.lean` -- Temporal signed formula with time labels (`SignedFormula Temporal.Formula TimeIndex`), `TimeIndex := Nat`, decomposition functions using Lukasiewicz encodings
- `Cslib/Logics/Temporal/Tableau/Rules.lean` -- Full rule set: 8 propositional + 8 G/H/F/P (universal/existential future/past) + 4 U/S (until/since decomposition with Reynolds co-decomposition) + frame-class rules
- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` -- Time ordering tracking between time indices (strict linear order constraints, before/after queries), analogous to bimodal `TimeOrdering`
- `Cslib/Logics/Temporal/Tableau/Branch.lean` -- Time-aware branch with temporal ordering, query helpers for "all known times after t" and "all known times before t"
- `Cslib/Logics/Temporal/Tableau/Closure.lean` -- Temporal closure including complementary pair and temporal-specific closure conditions (e.g., dense indicator closure T(U(top,bot)))
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` -- Fuel-bounded expansion with time creation and temporal ordering maintenance
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` -- Bridge to temporal Kripke semantics (`Cslib.Logics.Temporal.Semantics`)
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` -- Open branch yields temporal countermodel (linear order from time ordering, valuation from positive atoms)

**Files to modify**:
- `Cslib/Logics/Temporal.lean` or equivalent module root -- Add `Tableau` import

**Dependencies**: Child Task A (Foundations infrastructure), Child Task B (propositional decomposition patterns)
**Estimated effort**: 14-18 hours (~2,000-2,500 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau` compiles
- Soundness: closed tableau implies temporally valid
- Completeness: open branch yields temporal countermodel
- Can decide: `G(p) -> p` is valid, `p -> G(p)` is not valid, `F(p) -> F(F(p))` is valid (transitivity of time)
- Until decomposition works: `U(p,q) -> F(q)` is valid

---

## Dependency Graph

```
Child Task A: Foundations Tableau Infrastructure
    |
    +----------+----------+
    |          |          |
    v          v          v
Child Task B  Child Task E  (parallel: B and E are independent)
(Propositional)  (Temporal)
    |
    v
Child Task C
(Modal K)
    |
    v
Child Task D
(Modal Extensions: T, S4, S5)

External relationships:
- Task 279 (Sequent Calculus): independent, parallel path
- Task 291 (Three-way equivalence): depends on 279, no tableau dependency
- Task 41 (Abstract completeness): depends on temporal/bimodal completeness, may consume temporal tableau results
```

**Wave analysis for child task execution**:

| Wave | Tasks | Blocked by | Parallelism |
|------|-------|------------|-------------|
| 1 | A | -- | Single task |
| 2 | B, E | A | Two tasks in parallel |
| 3 | C | B | Single task |
| 4 | D | C | Single task |

**Critical path**: A -> B -> C -> D (4 waves, ~30-44 hours)
**Secondary path**: A -> E (2 waves, ~18-24 hours, runs parallel to B->C->D chain)

**Total estimated effort**: 44-62 hours across 5 tasks (~7,500-9,700 new lines of Lean 4)

### Deferred Work (Not a Child Task)

**Bimodal Integration (formerly Task F in research)**: Refactor the existing bimodal decidability system (~7,400 lines) to consume the shared Foundations/Logic/Tableau/ infrastructure. This is explicitly deferred because: (1) the bimodal system is working, sorry-free code, (2) refactoring risks regressions, (3) the shared infrastructure must first be validated through the propositional/modal/temporal systems. If pursued later, it would depend on all 5 child tasks being stable and would involve ~500-800 lines of refactoring (net zero or negative LOC change).

## Testing & Validation

- [ ] All 5 child tasks created in state.json with correct status (`not_started`)
- [ ] Dependencies correctly encoded in task descriptions
- [ ] Task type set to `cslib` for all child tasks
- [ ] TODO.md regenerated and shows all tasks
- [ ] No existing tasks disrupted by creation

## Artifacts & Outputs

- `specs/296_tableau_calculi_architecture/plans/01_tableau-arch-plan.md` (this file)
- 5 new tasks in state.json (created during implementation)

## Rollback/Contingency

Since this is a metatask that only creates tasks, rollback is straightforward: abandon the child tasks via `/task --abandon N` if the approach proves wrong. No code changes are made by this metatask itself.
