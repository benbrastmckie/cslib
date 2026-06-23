# Research Report: Task #296

**Task**: 296 - Create Tableau Calculi Architecture Metatask
**Started**: 2026-06-23
**Completed**: 2026-06-23
**Task Type**: formal
**Domains**: logic

## Executive Summary

- The existing bimodal decidability system (~7,400 lines across 11+7 files) contains a complete tableau pipeline (rules, closure, saturation, proof/countermodel extraction, decision procedure, correctness) but is hardcoded to bimodal `Formula Atom` with `{atom, bot, imp, box, untl, snce}` primitives.
- `Cslib.Foundations.Logic.PropositionalTableau` (210 lines) provides generic propositional rule infrastructure (`PropSign`, `PropSignedFormula`, `PropTableauRule`, `applyPropRule`) parameterized over abstract decomposition functions, but is not yet imported by any module.
- A unified tableau architecture should build from propositional through modal to temporal and bimodal, with each layer adding rules on top of the previous one, sharing branch/closure/saturation infrastructure.
- The bimodal tableau should eventually consume the shared infrastructure but can remain standalone during the transition to avoid disrupting the existing ~7,400 lines.
- Tableau completeness and MCS-based completeness are complementary: tableau gives decidability + finite countermodels; MCS gives strong completeness over infinite sets.

## Domain Analysis

This is primarily a logic domain task spanning proof theory (tableau methods), modal logic (Kripke semantics, box/diamond rules), and temporal logic (until/since decomposition). The architecture must also connect to the existing Hilbert and natural deduction proof systems.

## Findings

### 1. Existing Codebase Inventory

#### Formula Types Across Logics

| Logic | Namespace | Primitives | Location |
|-------|-----------|-----------|----------|
| Propositional | `Cslib.Logic.PL` | `atom, bot, imp, and, or` | `Logics/Propositional/Defs.lean` |
| Modal | `Cslib.Logic.Modal` | `atom, bot, imp, box` | `Logics/Modal/Basic.lean` |
| Temporal | `Cslib.Logic.Temporal` | `atom, bot, imp, untl, snce` | `Logics/Temporal/Syntax/Formula.lean` |
| Bimodal | `Cslib.Logic.Bimodal` | `atom, bot, imp, box, untl, snce` | `Logics/Bimodal/Syntax/Formula.lean` |

Key difference: Propositional has native `and`/`or` constructors; Modal/Temporal/Bimodal use Lukasiewicz encodings (`and phi psi := neg(phi -> neg psi)`, `or phi psi := neg phi -> psi`).

#### Connective Typeclass Hierarchy

```
HasBot, HasImp
    |
    v
PropositionalConnectives  (bot, imp)
    |           |
    v           v
ModalConnectives    FutureTemporalConnectives  (bot, imp, box)/(bot, imp, untl)
    |                   |            |
    |                   v            v
    |           LTLConnectives    TemporalConnectives  (bot, imp, untl, next)/(bot, imp, untl, snce)
    |                                   |
    +-----------------------------------+
    |
    v
BimodalConnectives  (bot, imp, box, untl, snce)
```

#### Existing Proof Systems (Non-Tableau)

| Logic | Hilbert | Natural Deduction | Sequent Calculus | MCS Completeness |
|-------|---------|-------------------|------------------|------------------|
| Propositional | Full (3 strengths: MPL/IPL/CPL) | Full (10 constructors) | NOT YET (task 279) | Full |
| Modal | Full (15 systems: K through S5) | Not yet | Not yet | Full (all 15 systems) |
| Temporal | Full (base, dense, discrete) | Not yet | Not yet | Full (base + dense) |
| Bimodal | Full (base, dense, discrete) | Not yet | Not yet | Full (base, in progress for dense/discrete) |

#### Existing Tableau Infrastructure

**Foundations layer** (`Cslib/Foundations/Logic/PropositionalTableau.lean`, 210 lines):
- `PropSign` -- pos/neg sign type (distinct from bimodal `Sign`)
- `PropSignedFormula F` -- formula + sign, parameterized over formula type
- `PropTableauRule` -- 8 propositional rules (andPos/Neg, orPos/Neg, impPos/Neg, negPos/Neg)
- `PropRuleResult F` -- linear/branching/notApplicable
- `applyPropRule` -- generic rule application parameterized over decomposition functions (`andOf?`, `orOf?`, `impOf?`, `negOf?`)
- NOT YET IMPORTED by any module

**Bimodal decidability** (`Cslib/Logics/Bimodal/Metalogic/Decidability/`, ~7,400 lines):
- `Sign` -- pos/neg (bimodal-specific, separate from `PropSign`)
- `SignedFormula Atom` -- formula + sign + `Label` (world index + time index)
- `TableauRule` -- 28 rules (8 propositional + 4 modal S5 + 1 modal-temporal bridge + 10 temporal + 5 frame-class-specific)
- `RuleResult Atom` -- linear/branching/persistent/notApplicable (adds `persistent` variant)
- `Branch Atom` -- `List (SignedFormula Atom)` with query helpers
- `TimeOrdering` -- tracks temporal ordering between time indices
- `ClosedBranch` / `ClosureReason` -- branch closure detection
- `ExpandedTableau` -- fully expanded tableau (allClosed/hasOpen)
- `expandBranchWithFuel` -- fuel-bounded expansion with applied-set tracking
- `ProofExtraction` / `CountermodelExtraction` -- extract proof terms or countermodels
- `DecisionProcedure` -- `DecisionResult` (valid/invalid/timeout)
- `Correctness` -- `decide_sound`, `validity_decidable`
- `FMP/` -- Finite Model Property via filtration (7 files, ~1,480 lines)
- `TraceCertificate` -- optional tracing instrumentation

### 2. Architectural Design Analysis

#### What Should Live in Foundations vs Logic-Specific Modules

**Foundations/Logic/Tableau/** (shared infrastructure):

| Component | Current Status | Proposed Location |
|-----------|---------------|-------------------|
| Sign type (pos/neg) | `PropSign` in Foundations, `Sign` in Bimodal | Unify into `Foundations/Logic/Tableau/Sign.lean` |
| Signed formula (no label) | `PropSignedFormula` in Foundations | `Foundations/Logic/Tableau/SignedFormula.lean` |
| Propositional rules (8) | `PropTableauRule` in Foundations | `Foundations/Logic/Tableau/PropositionalRules.lean` |
| Rule result type | `PropRuleResult` in Foundations | `Foundations/Logic/Tableau/RuleResult.lean` |
| Branch type (list of signed formulas) | Bimodal only | `Foundations/Logic/Tableau/Branch.lean` |
| Branch closure (complementary pair) | Bimodal only | `Foundations/Logic/Tableau/Closure.lean` |
| Saturation framework | Bimodal only | Deferred -- too logic-specific |
| Decision procedure skeleton | Bimodal only | Deferred -- too logic-specific |

**Logic-specific modules** (consuming Foundations):

| Logic | Tableau Module Location | Additions Over Foundations |
|-------|------------------------|--------------------------|
| Propositional | `Logics/Propositional/Tableau/` | Decidability via tableau, bridge to Hilbert |
| Modal K | `Logics/Modal/Tableau/` | Box/diamond rules, world labels |
| Modal S5 | `Logics/Modal/Tableau/` | S5-specific simplifications |
| Temporal | `Logics/Temporal/Tableau/` | Until/since rules, time labels |
| Bimodal | `Logics/Bimodal/Metalogic/Decidability/` (existing) | All of the above combined |

#### How Modal Rules Layer on Propositional Rules

The propositional tableau decomposes formulas using only the 8 rules in `PropTableauRule`. Modal tableaux add:

1. **Box rules** (for accessibility relation R):
   - `boxPos`: T(box phi) at world w -> T(phi) at all w' where R(w,w') (universal, persistent)
   - `boxNeg`: F(box phi) at world w -> create fresh w' with R(w,w'), add F(phi) at w' (existential, consumable)

2. **Diamond rules** (dual of box):
   - `diamondPos`: T(dia phi) at w -> create fresh w' with R(w,w'), add T(phi) at w' (existential)
   - `diamondNeg`: F(dia phi) at w -> F(phi) at all accessible w' (universal, persistent)

3. **Frame-specific rules** for different modal logics:
   - K: no additional frame constraints
   - T (reflexive): R is reflexive, so T(box phi) at w also gives T(phi) at w
   - S4 (reflexive + transitive): loop-checking needed to ensure termination
   - S5 (equivalence relation): all worlds mutually accessible, simplifies to single equivalence class

The bimodal system uses S5 specifically, which allows the simplification where `boxPos` propagates to ALL known worlds (not just accessible ones).

#### How Temporal Rules Layer on Modal Rules

Temporal rules add a time dimension orthogonal to the world dimension:

1. **G/H rules** (universal temporal, analogous to box):
   - `allFuturePos`: T(G phi) at time t -> T(phi) at all known future t' > t (persistent)
   - `allFutureNeg`: F(G phi) at t -> F(phi) at fresh future t' > t (existential)
   - `allPastPos` / `allPastNeg`: symmetric for H (historically)

2. **F/P rules** (existential temporal, analogous to diamond):
   - `someFuturePos`: T(F phi) at t -> T(phi) at fresh future t' > t (existential)
   - `someFutureNeg`: F(F phi) at t -> F(phi) at all known future t' > t (persistent)
   - `somePastPos` / `somePastNeg`: symmetric for P

3. **Until/Since rules** (no modal analogue -- unique to temporal):
   - `untlPos`: T(phi U psi) -> branch: event-witness at fresh future OR guard+continue
   - `untlNeg`: F(phi U psi) -> Reynolds co-decomposition at known future times
   - `sncePos` / `snceNeg`: symmetric for Since

4. **Frame-class rules** (density, discreteness):
   - `denseIndicatorClosure`: close branch on T(U(top,bot)) for dense frames
   - `densityRule`: introduce intermediate time points
   - `priorUZ` / `priorSZ`: discrete frame axiom rules
   - `z1Rule`: backward induction for discrete frames

#### The Label Architecture

A key design decision: what labels do signed formulas carry?

| Logic | Label Components | Label Type |
|-------|-----------------|-----------|
| Propositional | None needed | `Unit` or no label |
| Modal | World index | `WorldIndex := Nat` |
| Temporal | Time index | `TimeIndex := Nat` |
| Bimodal | World + time | `Label := { world : WorldIndex, time : TimeIndex }` |

The current bimodal `Label` type carries both dimensions. A generic approach would parameterize over the label type, but this adds complexity. The simpler approach: each logic defines its own `SignedFormula` extending the propositional `PropSignedFormula` with labels.

### 3. Bimodal Refactoring Analysis

**Should the bimodal tableau consume shared infrastructure?**

Arguments for refactoring:
- Eliminates code duplication (Sign, propositional rules, closure logic)
- Enables reuse of propositional tableau theorems in bimodal proofs
- Makes the architecture consistent

Arguments against refactoring now:
- The bimodal system is ~7,400 lines of working, sorry-free code
- Refactoring requires touching many files with tight interdependencies
- The bimodal Sign/SignedFormula includes Label which has no Foundations analogue
- `RuleResult` in bimodal has a `persistent` variant absent from `PropRuleResult`
- Risk of introducing regressions in the decidability system

**Recommendation**: Build the new shared infrastructure in Foundations and new logic-specific modules. Let the bimodal system remain standalone initially. Create an explicit migration task (optional, low priority) to refactor the bimodal system to consume shared infrastructure, with clear dependency on the shared infrastructure being stable and tested.

### 4. Dependency Chain Analysis

The proposed task dependency chain (bottom-up):

```
Layer 0: Foundations/Logic/Tableau/ (generic infrastructure)
    |
    +-- Propositional Tableau (complete system: rules, closure, termination, soundness, completeness, decision)
    |       |
    |       +-- Modal K Tableau (add box/diamond rules, world labels)
    |       |       |
    |       |       +-- Modal Extensions (T, S4, S5 -- frame-specific rules)
    |       |       |       |
    |       |       +-- Temporal Tableau (add until/since rules, time labels)
    |       |               |
    |       |               +-- Bimodal Integration (optional: refactor existing to consume shared)
    |       |
    |       +-- Propositional Sequent Calculus (task 279, independent but complementary)
    |               |
    |               +-- Three-way equivalence (task 291: Hilbert <-> ND <-> SC)
    |
    +-- Abstract Completeness Infrastructure (task 41, later)
```

### 5. Relationship to MCS-Based Completeness

The existing MCS-based completeness proofs (via canonical models) and the planned tableau completeness serve different purposes:

| Property | MCS Completeness | Tableau Completeness |
|----------|-----------------|---------------------|
| What it proves | Strong completeness: every valid formula is provable | Decidability: algorithm to determine validity |
| Construction | Infinite canonical model from maximal consistent sets | Finite search tree with termination guarantee |
| Strength | Works for infinite formula sets | Works only for individual formulas |
| Output | Existence proof (non-constructive) | Algorithm + finite countermodels |
| Status in CSLib | Complete for propositional, modal (15 systems), temporal, bimodal (partial) | Complete for bimodal only |

They relate via:
- Tableau soundness: closed tableau implies formula is provable (bridges to Hilbert system)
- Tableau completeness: open saturated branch yields finite countermodel
- MCS completeness + FMP implies tableau completeness (the FMP directory in bimodal)

### 6. Relationship to Sequent Calculus (Task 279)

Task 279 plans a Gentzen-style LK/LJ sequent calculus for propositional logic. Tableau and sequent calculus are related but distinct:

- **Shared concepts**: Structural decomposition of formulas, subformula property, cut-free proofs
- **Key difference**: Sequent calculus operates on sequents (Gamma |- Delta); tableau operates on signed formula branches
- **Bridge**: A closed tableau for F(phi) corresponds to a cut-free derivation of |- phi in sequent calculus
- **Independence**: They can be developed in parallel -- the tableau pipeline uses Hilbert-style proof terms, not sequent derivations

## Proposed Implementation Tasks

### Task A: Foundations Tableau Infrastructure (Foundations/Logic/Tableau/)

**Scope**: Refactor and extend `PropositionalTableau.lean` into a proper module directory.

Files to create:
1. `Sign.lean` -- Unified sign type (absorbing both `PropSign` and bimodal `Sign`)
2. `SignedFormula.lean` -- Generic signed formula, optionally labeled
3. `PropositionalRules.lean` -- The 8 propositional rules (refactored from current `PropositionalTableau.lean`)
4. `RuleResult.lean` -- Generic rule result type (linear/branching/persistent/notApplicable)
5. `Branch.lean` -- Branch type, closure detection, complementary pair check
6. `Expansion.lean` -- Generic single-step expansion, fuel-based saturation skeleton

**Dependencies**: None (leaf task).
**Estimated size**: ~600-800 lines.

### Task B: Propositional Tableau System (Logics/Propositional/Tableau/)

**Scope**: Complete propositional tableau system with decidability.

Files to create:
1. `Defs.lean` -- Propositional signed formula (no labels needed), decomposition functions for PL.Proposition (native and/or)
2. `Rules.lean` -- Instantiate `applyPropRule` for PL.Proposition
3. `Closure.lean` -- Branch closure for propositional case
4. `Saturation.lean` -- Fuel-bounded expansion, termination argument via subformula property
5. `Soundness.lean` -- Closed tableau implies valid (bridge to Bool semantics)
6. `Completeness.lean` -- Open branch implies satisfiable (extract valuation)
7. `DecisionProcedure.lean` -- `Decidable (Valid phi)` via tableau

**Dependencies**: Task A.
**Estimated size**: ~1,200-1,600 lines.

### Task C: Modal K Tableau (Logics/Modal/Tableau/)

**Scope**: Tableau system for basic modal logic K.

Files to create:
1. `Defs.lean` -- Modal signed formula with world labels, decomposition functions
2. `Rules.lean` -- 8 propositional + 4 modal (boxPos/Neg, diamondPos/Neg)
3. `Branch.lean` -- World-aware branch, accessibility tracking
4. `Closure.lean` -- Modal closure (complementary at same world)
5. `Saturation.lean` -- Fuel-bounded expansion with world creation
6. `Soundness.lean` -- Closed tableau implies K-valid (bridge to Kripke semantics)
7. `Completeness.lean` -- Open branch yields finite Kripke countermodel

**Dependencies**: Task A, Task B (for propositional rule reuse).
**Estimated size**: ~1,500-2,000 lines.

### Task D: Modal Extensions (T, S4, S5 Tableaux)

**Scope**: Extend modal K tableau for frame conditions.

Files to create (or extend Task C files):
1. `FrameRules.lean` -- Additional rules for T (reflexive), 4 (transitive), B (symmetric), 5 (Euclidean)
2. `S5Simplification.lean` -- S5-specific simplification (single equivalence class)
3. `LoopChecking.lean` -- Loop detection for S4 termination (transitive closure)
4. `FrameSpecificCompleteness.lean` -- Completeness for each system

**Dependencies**: Task C.
**Estimated size**: ~1,200-1,800 lines.

### Task E: Temporal Tableau (Logics/Temporal/Tableau/)

**Scope**: Tableau system for temporal logic with until/since.

Files to create:
1. `Defs.lean` -- Temporal signed formula with time labels, decomposition functions
2. `Rules.lean` -- Propositional + temporal (G/H, F/P, U/S) + frame-class rules
3. `TimeOrdering.lean` -- Time ordering tracking (reusable from bimodal or fresh)
4. `Branch.lean` -- Time-aware branch, temporal query helpers
5. `Closure.lean` -- Temporal closure
6. `Saturation.lean` -- Fuel-bounded expansion with time creation
7. `Soundness.lean` -- Bridge to temporal Kripke semantics
8. `Completeness.lean` -- Open branch yields temporal countermodel

**Dependencies**: Task A, Task B.
**Estimated size**: ~2,000-2,500 lines.

### Task F: Bimodal Integration (Optional)

**Scope**: Refactor existing bimodal Decidability/ to consume shared Foundations infrastructure.

Changes:
1. Replace bimodal `Sign` with shared `Sign` from Foundations
2. Factor propositional rule application through shared `applyPropRule`
3. Share `TimeOrdering` between temporal and bimodal
4. Possibly share closure/saturation patterns

**Dependencies**: Tasks A, C, D, E all stable.
**Estimated size**: ~500-800 lines of refactoring (net zero or negative LOC change).
**Risk**: High (touching working code), hence optional.

### Dependency Graph

```
Task A (Foundations Infrastructure)
    |
    +---+---+
    |       |
    v       v
Task B    Task E
(Prop)    (Temporal)
    |
    v
Task C
(Modal K)
    |
    v
Task D
(Modal Extensions)
    |
    +-- Task F (Bimodal Integration, optional)

Independent:
- Task 279 (Sequent Calculus) -- parallel path
- Task 291 (Three-way equivalence) -- depends on 279
- Task 41 (Abstract completeness) -- depends on temporal/bimodal completeness
```

**Critical path**: A -> B -> C -> D
**Secondary path**: A -> E (can run in parallel with B)
**Optional**: F (deferred indefinitely unless needed)

## Risks and Mitigations

### Risk 1: Propositional tableau complexity from native and/or
The propositional `PL.Proposition` has native `and` and `or` constructors, unlike modal/temporal/bimodal which encode them via Lukasiewicz convention. The tableau rules need both decomposition paths.

**Mitigation**: The `applyPropRule` in `PropositionalTableau.lean` is already parameterized over decomposition functions (`andOf?`, `orOf?`, `impOf?`, `negOf?`). Each logic provides its own decompositions. The propositional tableau provides two sets: native (`PL.Proposition.and`/`or`) and Lukasiewicz-encoded.

### Risk 2: Label type proliferation
Each logic needs different labels (none, world, time, world+time), creating type-level complexity.

**Mitigation**: Do NOT try to unify labels into a single parameterized type. Let each logic define its own `SignedFormula` extending the shared `Sign` and `RuleResult` types. Labels are logic-specific by nature.

### Risk 3: S5 simplification not reusable for K/T/S4
The bimodal system exploits S5's equivalence relation to simplify modal rules (all worlds accessible). This does not transfer to K, T, or S4.

**Mitigation**: Build the modal K tableau as the general case. S5 simplification is a separate optimization in Task D, not the default. The bimodal system's S5-specific approach can remain in its standalone code.

### Risk 4: Termination arguments differ by logic
Propositional: subformula property suffices. Modal K: subformula + finite branching. Modal S4: needs loop-checking. Temporal: needs eventuality tracking.

**Mitigation**: Use fuel-based termination uniformly (as the bimodal system does). Prove termination bounds per-logic using subformula closure cardinality. The `expandBranchWithFuel` pattern from the bimodal system is reusable.

### Risk 5: Bimodal refactoring disrupts working code
Touching the ~7,400 lines of bimodal decidability to consume shared infrastructure risks regressions.

**Mitigation**: Task F is explicitly optional and deferred. The bimodal system remains standalone. Shared infrastructure is validated through the new propositional/modal/temporal systems before any bimodal refactoring is attempted.

## Appendix: Line Count Summary

| Module | Current LOC | Status |
|--------|------------|--------|
| Foundations/Logic/PropositionalTableau.lean | 210 | Exists, unused |
| Bimodal/Metalogic/Decidability/ (core) | 5,945 | Complete |
| Bimodal/Metalogic/Decidability/FMP/ | 1,481 | Complete |
| **Total existing** | **7,636** | |
| | | |
| **Proposed new** | **Est. LOC** | |
| Task A: Foundations infrastructure | 600-800 | |
| Task B: Propositional tableau | 1,200-1,600 | |
| Task C: Modal K tableau | 1,500-2,000 | |
| Task D: Modal extensions | 1,200-1,800 | |
| Task E: Temporal tableau | 2,000-2,500 | |
| Task F: Bimodal integration | 500-800 (refactor) | |
| **Total proposed** | **7,000-9,500** | |
