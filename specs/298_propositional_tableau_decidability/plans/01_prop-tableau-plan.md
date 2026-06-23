# Implementation Plan: Task #298

- **Task**: 298 - Implement propositional tableau systems for all three propositional logics
- **Status**: [COMPLETED]
- **Effort**: 14 hours
- **Dependencies**: Task 297 (COMPLETE -- Foundations/Logic/Tableau/ infrastructure)
- **Research Inputs**: specs/298_propositional_tableau_decidability/reports/01_prop-tableau-research.md
- **Artifacts**: plans/01_prop-tableau-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Implement propositional tableau decision procedures for the three propositional logics in CSLib:
classical (PropositionalAxiom), intuitionistic (IntPropAxiom), and minimal (MinPropAxiom).
The classical tableau uses `L = Unit` with complementary closure and validates the Foundations
infrastructure. The intuitionistic tableau uses `L = Nat` with world-creating implication rules,
persistence propagation, and T(bot)-only closure. The minimal tableau reuses the intuitionistic
expansion with atom-only closure. Final deliverables are `Decidable (Tautology phi)` (alternative
to existing enumeration), `Decidable (IValid phi)` (NEW), and `Decidable (MValid phi)` (NEW),
with derivability instances via completeness bridges.

### Research Integration

The research report (01_prop-tableau-research.md) established:

1. **Infrastructure availability**: All Foundations/Logic/Tableau/ types are ready -- `Sign`,
   `SignedFormula F L`, `RuleResult F L` (with `persistent` variant), `Branch F L`,
   `ClosureCondition` typeclass, three namespaced closure instances, `PropTableauRule` enum,
   `applyPropRule` with decomposition functions, `tryAllPropRules`.

2. **Missing instances**: `Hashable (Proposition Atom)` and `IsAtomic (Proposition Atom)` are
   needed but not yet defined. These belong in a shared `Defs.lean` file alongside the
   decomposition functions (`propAndOf?`, `propOrOf?`, `propImpOf?`, `propNegOf?`).

3. **Code sharing**: Int/Min share ~95% of expansion code; only the `ClosureCondition` instance
   differs. The closure instances live in separate namespaces to avoid typeclass conflicts.

4. **Proof strategy**: Classical soundness/completeness via Boolean semantics bridge;
   intuitionistic/minimal via Kripke countermodel construction from open saturated branches.

5. **Line estimate**: 1,770-2,560 lines across 11 files.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly correspond to a specific ROADMAP.md item (the roadmap focuses on
porting BimodalLogic content). However, it extends the logic infrastructure at the Propositional
level, which is a shared sub-logic used by Modal, Temporal, and Bimodal. The tableau decidability
instances provide constructive decision procedures complementing the existing algebraic
completeness proofs.

## Goals & Non-Goals

**Goals**:
- Shared `Defs.lean` with Proposition-specific decomposers, `Hashable`, `IsAtomic`, complexity measure
- Classical tableau expansion loop with fuel-based termination (L = Unit)
- Classical tableau soundness: closed tableau implies `Tautology phi`
- Classical tableau completeness: open saturated branch yields Boolean countermodel
- Classical `Decidable (Tautology phi)` and `Decidable (Derivable PropositionalAxiom phi)` via tableau
- Intuitionistic world-creating implication rules and persistence propagation
- Intuitionistic tableau expansion loop with fuel-based termination (L = Nat)
- Intuitionistic tableau soundness: closed tableau implies `IValid phi`
- Intuitionistic tableau completeness: open saturated branch yields Kripke countermodel
- Intuitionistic `Decidable (IValid phi)` and `Decidable (Derivable IntPropAxiom phi)` via tableau
- Minimal `Decidable (MValid phi)` and `Decidable (Derivable MinPropAxiom phi)` reusing intuitionistic expansion with `MinimalClosure`

**Non-Goals**:
- Replacing the existing `instDecidableTautology` (Boolean enumeration remains; tableau is an alternative)
- Optimized SAT-style decision procedures (DPLL, etc.)
- First-order tableau systems
- Modal or temporal tableau (tasks 299-301)
- Performance benchmarks or computational complexity analysis

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Intuitionistic completeness proof complexity (countermodel from open branch) | H | M | Follow Fitting 1983 structure; prove truth lemma by induction on formula; break into helper lemmas |
| Persistence propagation correctness (too little breaks soundness, too much breaks termination) | H | M | Research report specifies exactly what to propagate (all T-formulas from predecessor world); validate with small examples via `#eval` |
| ClosureCondition instance conflicts between classical/intuitionistic/minimal | M | L | Use namespaced instances with explicit `letI`/`haveI` at call sites; expansion functions take closure condition as explicit parameter |
| Fuel bound too tight for intuitionistic/minimal (algorithm fails to saturate) | M | L | Use generous bound `2^(2 * complexity phi)`; can tighten later after correctness is established |
| `negOf?` vs `impOf?` overlap on `imp a .bot` | L | L | Research confirms both matches give equivalent results; use `tryAllPropRules` as-is for classical; custom rules for intuitionistic handle negation as implication |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 3 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Shared Definitions (Defs.lean) [COMPLETED]

**Goal**: Create the shared definitions file with Proposition-specific decomposition functions,
typeclass instances, and complexity measure required by all three tableau systems.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Defs.lean`
- [ ] Define `propAndOf?`, `propOrOf?`, `propImpOf?`, `propNegOf?` decomposition functions
- [ ] Define `Hashable (Proposition Atom)` instance (constructor-tag mixing: atom=0, bot=1, imp=2, and=3, or=4)
- [ ] Define `IsAtomic (Proposition Atom)` instance (`.atom _ => true`, `_ => false`)
- [ ] Define `Proposition.complexity` size measure for fuel computation
- [ ] Add convenience abbreviations for signed formula construction with `Proposition`
- [ ] Register `Cslib.Init` import
- [ ] Verify: `lake build Cslib.Logics.Propositional.Tableau.Defs`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Defs.lean` - NEW: decomposers, instances, complexity

**Verification**:
- File compiles with `lake build Cslib.Logics.Propositional.Tableau.Defs`
- `#check @propAndOf?`, `#check @propOrOf?`, etc. resolve correctly
- `#eval Proposition.complexity (.imp (.atom 0) (.and (.atom 1) (.atom 2)))` returns expected value

---

### Phase 2: Classical Tableau Expansion and Decision Procedure [COMPLETED]

**Goal**: Implement the classical propositional tableau with `L = Unit`, including the expansion
loop, fuel-based termination, and the `Decidable (Tautology phi)` instance.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean`
  - Define `ClassicalTableauResult` (closed/open with branch data)
  - Implement fuel-based expansion loop using `tryAllPropRules` with `propAndOf?` etc.
  - Use `ClassicalClosure` instance via `open ClassicalClosure in`
  - Termination via `fuel = complexity phi`; each rule strictly reduces formula complexity
  - Track expanded formulas to avoid re-expansion (applied set pattern)
- [ ] Create `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`
  - Define `branchSatisfiable` relating branch content to Boolean valuation
  - Prove each classical rule preserves satisfiability (contrapositive)
  - Prove classical closure implies unsatisfiability
  - Main theorem: `classicalTableau_sound : closed -> Tautology phi`
- [ ] Create `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
  - Define valuation extraction from open saturated branch (`v(p) := T(atom p) on branch`)
  - Prove truth lemma: T(alpha) on branch -> Evaluate v alpha; F(alpha) -> not (Evaluate v alpha)
  - Main theorem: `classicalTableau_complete : Tautology phi -> closed`
- [ ] Create `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean`
  - Combine soundness and completeness into iff: `classicalTableau_decides`
  - Define `Decidable (Tautology phi)` via tableau (alternative to `instDecidableTautology`)
  - Define `Decidable (Derivable PropositionalAxiom phi)` via `prop_completeness_iff_tautology`
- [ ] Verify: `lake build Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure`

**Timing**: 4 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean` - NEW: expansion loop
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - NEW: closed -> Tautology
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - NEW: Tautology -> closed
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` - NEW: Decidable instances

**Verification**:
- All four files compile with `lake build`
- `#eval` tests: `classicalTableau (.imp (.atom 0) (.atom 0))` returns closed; `classicalTableau (.atom 0)` returns open
- `lean_verify` on `Decidable (Tautology phi)` instance confirms no sorry

---

### Phase 3: Intuitionistic Tableau Rules and Expansion [COMPLETED]

**Goal**: Implement the intuitionistic-specific implication rules (world-creating `F(imp)`,
persistent `T(imp)`) and the full expansion loop with persistence propagation.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean`
  - Define `intImpNeg` rule: `F(phi -> psi)` at world w creates fresh world w' with `T(phi)` at w', `F(psi)` at w'
  - Define persistence propagation: when creating w' as successor of w, propagate all `T(alpha)` formulas from w to w' (atoms and implications for persistence)
  - Define `intImpPos` rule: `T(phi -> psi)` at world w triggers modus ponens for each w' >= w with `T(phi)` at w'
  - Define world counter / fresh world generation
  - Track accessibility relation (world creation order) for successor lookups
- [ ] Create `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
  - Define `IntTableauState` tracking: branch, next world counter, accessibility relation, persistent formulas
  - Implement fuel-based expansion loop: process formulas on branch, apply standard prop rules for and/or, custom rules for imp, re-check persistent `T(imp)` formulas after world creation
  - Use `IntuitionisticClosure` instance via explicit scoping
  - Fuel bound: `2^(2 * complexity phi)` to account for world creation bounded by finite model property
  - Return `closed` or `open` with saturated branch and accessibility data
- [ ] Verify: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion`

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` - NEW: world-creating imp rules, persistence
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - NEW: expansion loop with state

**Verification**:
- Both files compile
- `#eval` tests: intuitionistic tableau on `p -> p` returns closed; on `((p -> q) -> p) -> p` (Peirce's law) returns open (not intuitionistically valid)

---

### Phase 4: Intuitionistic Soundness and Completeness [COMPLETED]

**Goal**: Prove soundness and completeness of the intuitionistic tableau, establishing the
bridge between closed/open tableaux and `IValid`/`not IValid`.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
  - Define `branchSatisfied` for Kripke models: for all `T(alpha) at l` on branch, `IForces v bf w_l alpha`; for all `F(alpha) at l`, `not (IForces v bf w_l alpha)`
  - Prove each intuitionistic rule preserves Kripke satisfiability (using `iforces_persistence`, `IForces_imp` semantics)
  - Prove intuitionistic closure (T(bot) at some label) implies unsatisfiability (since `bf = fun _ => False`)
  - Main theorem: `intTableau_sound : closed -> IValid phi`
- [ ] Create `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
  - Construct finite Kripke model from open saturated branch: worlds = labels on branch, accessibility = reflexive-transitive closure of world creation, valuation `v(l, p) = T(atom p) at l on branch`
  - Prove upward-closure of valuation (follows from persistence propagation)
  - Prove truth lemma by induction on formula: T(alpha) at l -> IForces; F(alpha) at l -> not IForces
  - The implication case requires careful handling: T(phi -> psi) persistence ensures the universal quantifier over successors; F(phi -> psi) world creation provides the witness
  - Main theorem: `intTableau_complete : IValid phi -> closed`
- [ ] Verify: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness`

**Timing**: 4 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - NEW: Kripke soundness proof
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - NEW: countermodel construction + truth lemma

**Verification**:
- Both files compile
- `lean_verify` on soundness and completeness theorems confirms no sorry

---

### Phase 5: Intuitionistic and Minimal Decision Procedures [COMPLETED]

**Goal**: Deliver the final `Decidable` instances for intuitionistic and minimal validity and
derivability, completing the NEW decidability results.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean`
  - Combine soundness and completeness: `intTableau_decides : closed <-> IValid phi`
  - Define `Decidable (IValid phi)` via tableau result
  - Define `Decidable (Derivable IntPropAxiom phi)` via `int_soundness_completeness`
- [ ] Create `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
  - Reuse intuitionistic expansion loop with `MinimalClosure` instance instead of `IntuitionisticClosure`
  - Prove minimal soundness: closed (via atom contradiction) -> MValid phi
    - Key difference: `bot_forces` is an arbitrary upward-closed predicate; atom contradiction T(p)/F(p) at same label gives contradiction in any model
  - Prove minimal completeness: MValid phi -> closed
    - Countermodel uses `bot_forces w := T(.bot) at w on branch` (upward-closed by persistence)
  - Define `Decidable (MValid phi)` and `Decidable (Derivable MinPropAxiom phi)` via `min_soundness_completeness`
- [ ] Verify: `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure`

**Timing**: 2 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` - NEW: Decidable IValid, Decidable Derivable IntPropAxiom
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - NEW: reuse expansion + MinimalClosure -> Decidable MValid, Decidable Derivable MinPropAxiom

**Verification**:
- Both files compile
- `#eval` test: minimal tableau on `bot -> p` returns open (not minimally valid); intuitionistic tableau on same returns closed (intuitionistically valid)
- `lean_verify` on all four Decidable instances confirms no sorry

---

### Phase 6: Integration, Init Imports, and CI Verification [IN PROGRESS]

**Goal**: Wire up all files into the CSLib import structure, run the full CI verification
pipeline, and confirm clean compilation.

**Tasks**:
- [ ] Update `Cslib.lean` barrel import with `lake exe mk_all --module`
- [ ] Verify all new files import `Cslib.Init` (run `lake exe checkInitImports`)
- [ ] Run `lake exe lint-style` and fix any style violations
- [ ] Run `lake test` to confirm CslibTests suite passes
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for import minimization
- [ ] Run `lake build` for full project compilation
- [ ] Add module-level docstrings to all 11 files following CSLib conventions
- [ ] Verify `lean_verify` on all key theorems and Decidable instances (no sorry, no axiom abuse)

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- `Cslib.lean` - Update barrel import
- All 11 new files - Verify Init imports, docstrings, style compliance

**Verification**:
- `lake build` succeeds with zero errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- `lake shake` reports no unnecessary imports

## Testing & Validation

- [ ] Classical tableau correctly identifies tautologies: `p -> p`, `(p -> q) -> (q -> r) -> (p -> r)`, `((p -> q) -> p) -> p` (Peirce)
- [ ] Classical tableau correctly identifies non-tautologies: `p`, `p -> q`, `p or (not p)` is a tautology but `p or q` is not
- [ ] Intuitionistic tableau rejects Peirce's law: `((p -> q) -> p) -> p` returns open
- [ ] Intuitionistic tableau rejects excluded middle: `p or (not p)` returns open
- [ ] Intuitionistic tableau accepts: `p -> p`, `(p -> q) -> (not q -> not p)`, `not not not p -> not p`
- [ ] Minimal tableau rejects ex falso: `bot -> p` returns open
- [ ] Minimal tableau accepts: `p -> p`, `not not not p -> not p`
- [ ] All `Decidable` instances compile without sorry
- [ ] Full CI pipeline passes (checkInitImports, lint-style, test, shake)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Tableau/Defs.lean` - Shared decomposers, instances, complexity
- `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean` - Classical expansion loop
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - Classical soundness proof
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - Classical completeness proof
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` - Classical Decidable instances
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` - World-creating imp rules, persistence
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - Intuitionistic expansion loop
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - Intuitionistic Kripke soundness
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - Countermodel construction + truth lemma
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` - Intuitionistic Decidable instances
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - Minimal Decidable instances (reuses int expansion)

## Rollback/Contingency

All new files are in `Cslib/Logics/Propositional/Tableau/` -- a new directory with no modifications
to existing files. Rollback is clean: delete the `Tableau/` directory and revert `Cslib.lean`
barrel import. No existing functionality is modified or broken.

If the intuitionistic completeness proof proves too complex for a single dispatch:
1. Phase 4 can be split into separate Soundness and Completeness sub-phases
2. The truth lemma can use sorry as a placeholder, marked [PARTIAL], and completed in a follow-up
3. The Decidable instances in Phase 5 can still be defined with sorry-carrying completeness, allowing the architecture to be validated end-to-end before the hardest proof is completed
