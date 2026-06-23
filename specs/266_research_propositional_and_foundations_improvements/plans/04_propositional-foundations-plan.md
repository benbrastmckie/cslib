# Implementation Plan: Propositional and Foundations Improvements (v4)

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None (Tasks 281-285 completed Phase 1 and modal/temporal/bimodal ProofSystem instances)
- **Research Inputs**: reports/01_team-research.md, reports/02_team-research.md, reports/04_team-research.md
- **Artifacts**: plans/04_propositional-foundations-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: true

## Overview

This plan addresses the remaining actionable gaps in CSLib's Propositional/ and Foundations/Logic/ modules after tasks 281-285 delivered the Hilbert-primary architecture. Phase 1 (Hilbert-algebraic bridge with `HilbertCompleteness.lean`) and the modal/temporal/bimodal ProofSystem tag instances are complete and verified. The remaining work consists of: fixing two stale documentation sites plus a spurious import, adding the `HasDia` primitive, assembling a `Decidable (Tautology phi)` instance, extracting propositional tableau rules to Foundations/, scoping the GenericMCS bridge for modal logics, filling the `InferenceSystem.lean` empty module docstring, and adding propositional test coverage. Definition of done: all phases pass `lake build`, `lake test`, `lake exe checkInitImports`, and `lake exe lint-style`.

### Research Integration

- **reports/01_team-research.md** (Round 1): Initial 8-gap analysis. Identified the Hilbert-algebraic bridge (now complete), stale documentation, missing test coverage.
- **reports/02_team-research.md** (Round 2): Corrected 3 stale findings. Key: PL has no binders so ND capture-avoidance is a non-issue; abstract completeness extraction deferred until GenericMCS concretization.
- **reports/04_team-research.md** (Round 3): Post-281-285 audit confirming Phase 1 complete, partial Phase 2 remaining. Identified additional issues: `ProofSystem.lean` line 44-45 stale "will be" comment, `Conservative.lean` spurious `Mathlib.Tactic.ToAdditive` import, empty `InferenceSystem.lean` module docstring, `HasAxiomDNE` asymmetry needing documentation.

### Prior Plan Reference

The prior plan (03_propositional-foundations-plan.md, 7 phases, 7 hours) was partially executed by tasks 281-285 which completed Phase 1 (HilbertCompleteness.lean) and most of Phase 2 (ProofSystem documentation). Phases 3-7 remain untouched. Round 3 research confirmed two additional stale documentation sites not covered by the prior plan (ProofSystem.lean line 44-45, Conservative.lean spurious import) and an empty module docstring in InferenceSystem.lean. Effort calibration: Phase 1 took ~1.5h (matched estimate); Phase 5 (GenericMCS bridge) was correctly identified as highest-risk. This plan resequences remaining work to incorporate round 3 findings and adjusts dependency graph based on completed infrastructure.

### Roadmap Alignment

- **Abstract shared completeness infrastructure**: Phase 5 (GenericMCS concretization) is a prerequisite for this roadmap item
- **ProofSystem infrastructure**: Phase 1 documentation fixes support downstream completeness work

## Goals & Non-Goals

**Goals**:
- Fix all stale documentation: ProofSystem.lean line 44-45, NaturalDeduction/Basic.lean line 275, Conservative.lean spurious import
- Fill InferenceSystem.lean empty module docstring
- Add HasDia primitive to Foundations/Logic/ with scoped notation
- Create Decidable (Tautology phi) instance using BoolEvaluate and Fintype enumeration
- Extract propositional tableau rules from Bimodal/Decidability/Tableau.lean to Foundations/
- Scope and validate GenericMCS bridge for modal logic
- Add propositional test coverage via CslibTests/Propositional.lean

**Non-Goals**:
- Full ND substitution rewrite (PL has no binding operators; capture avoidance is not applicable)
- Propositional sequent calculus LK/LJ (split to task 279)
- Abstract completeness extraction to Foundations/ (deferred until GenericMCS concretization)
- CNF/DNF normal forms, Craig interpolation
- Refactoring all downstream logics to use GenericMCS (future task; this plan only proves the bridge for modal logic)
- Bundling And/Or axiom typeclasses into ClassicalHilbert (deferred to task 173)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| GenericMCS bridge proof infeasible for modal logic | M | M | Scope Phase 5 as proof-of-concept for one modal system only. If bridge is complex, document blockers and create follow-up task. Rest of plan unaffected. |
| HasDia changes interact unexpectedly with existing AxiomB/Axiom5/AxiomD encodings | M | L | HasDia is purely additive (new class, new notation). Do not modify existing classical axiom definitions. |
| Propositional tableau extraction breaks bimodal tableau imports | H | L | Extract as new definitions that bimodal module imports. Run full `lake build` to catch breakage. Fallback: create aliases instead of moving. |
| Decidable Tautology requires Fintype Atom constraint users may not expect | L | L | Expected and acceptable. Instance conditional on `[Fintype Atom] [DecidableEq Atom]`. Docstring explains constraint. |
| `lake shake` reveals additional unused imports beyond Conservative.lean | L | M | Run `lake shake` in Phase 1 and fix any findings. Low risk since CI already passes. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 5 | 1 |
| 3 | 6 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Fix Documentation, Stale Comments, and Spurious Import [COMPLETED]

**Goal**: Resolve all documentation gaps identified across three research rounds: fix stale "will be" comment in ProofSystem.lean, clarify/remove the capture-avoidance TODO in NaturalDeduction/Basic.lean, remove spurious ToAdditive import from Conservative.lean, fill InferenceSystem.lean empty module docstring, and add a docstring note to Axioms.lean about DNE being derived.

**Tasks**:
- [ ] Edit `Cslib/Foundations/Logic/ProofSystem.lean` lines 44-45: change "will be registered when derivation trees are defined" to "are registered in their respective `Instances.lean` files" with a note that modal/temporal/bimodal tags have full instances
- [ ] Edit `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` line 275: replace the capture-avoidance TODO in the `subs` docstring with a note that PL has no binding operators and capture avoidance does not apply
- [ ] Remove `import Mathlib.Tactic.ToAdditive` from `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` line 10 (zero usage confirmed by grep)
- [ ] Fill the empty module docstring `/-! -/` in `Cslib/Foundations/Logic/InferenceSystem.lean` line 11 with 10-15 lines explaining `InferenceSystem`, `Default`, `DerivableIn`, `Derivable`, and the notation `S=>a`
- [ ] Add a docstring note to `Cslib/Foundations/Logic/Axioms.lean` near line 94 explaining that `DNE` is defined as an axiom formula for completeness but is derived (not separately axiomatized) in `ClassicalHilbert`
- [ ] Run `lake build` and `lake exe lint-style` to verify

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` - fix stale comment at lines 44-45
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - clarify/remove TODO at line 275
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` - remove spurious import at line 10
- `Cslib/Foundations/Logic/InferenceSystem.lean` - fill empty module docstring at line 11
- `Cslib/Foundations/Logic/Axioms.lean` - add DNE docstring note near line 94

**Verification**:
- Comments accurately reflect the current codebase state
- No empty module docstrings remain in Foundations/Logic/
- `lake build` succeeds
- `lake exe lint-style` passes

---

### Phase 2: Add HasDia Primitive [COMPLETED]

**Goal**: Add a `HasDia` typeclass to Foundations/Logic/Connectives.lean providing a primitive diamond operator with scoped notation, enabling future non-classical modal logics where box and diamond are independent operators.

**Tasks**:
- [ ] Add `class HasDia (F : Type*) where dia : F -> F` to `Cslib/Foundations/Logic/Connectives.lean` (after the existing `HasBox` definition)
- [ ] Add scoped notation `◇` for `HasDia.dia`
- [ ] Update `Cslib/Foundations/Logic/Axioms.lean` comments at lines 152, 163, 175 to note that `HasDia` now exists as a primitive
- [ ] Add a `DiaDuality` axiom: define `AxiomDiaDuality` formula and `HasAxiomDiaDuality` typeclass (dia phi <-> neg box neg phi) in `Axioms.lean`
- [ ] Do NOT modify existing `AxiomB`, `Axiom5`, `AxiomD` definitions -- HasDia is additive
- [ ] Run `lake build` to verify no regressions

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - add `HasDia` class and notation
- `Cslib/Foundations/Logic/Axioms.lean` - update comments, add `DiaDuality` axiom

**Verification**:
- `HasDia` class and `DiaDuality` axiom compile
- Existing `lake build` succeeds with no regressions
- Forward-reference comments in Axioms.lean updated

---

### Phase 3: Add Decidable (Tautology phi) Instance [COMPLETED]

**Goal**: Assemble the existing `BoolEvaluate_eq_iff` infrastructure into a `Decidable (Tautology phi)` instance for `[Fintype Atom] [DecidableEq Atom]`.

**Tasks**:
- [ ] Read `Cslib/Logics/Propositional/Semantics/Bool.lean` to understand `BoolEvaluate_eq_iff`, `instDecidableBoolEvaluate`, and `Tautology`
- [ ] Prove bridge lemma: `Tautology phi <-> forall (v : BoolValuation Atom), BoolEvaluate v phi = true` using `BoolEvaluate_eq_iff`
- [ ] Use `Fintype.decidableForallFintype` (or equivalent) over `BoolValuation Atom` (= `Atom -> Bool`) with `[Fintype Atom]` to derive `Decidable (forall v, BoolEvaluate v phi = true)`
- [ ] Register `instance [Fintype Atom] [DecidableEq Atom] : Decidable (Tautology phi)` in `Bool.lean`
- [ ] Verify with `lake build`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - add bridge lemma and Decidable instance

**Verification**:
- `#eval decide (Tautology (p or neg p))` returns `true` for a concrete `Atom` type
- `lake build` succeeds
- No `sorry` in the new code

---

### Phase 4: Extract Propositional Tableau Rules to Foundations/ [COMPLETED]

**Goal**: Factor the 8 propositional tableau rules (andPos/Neg, orPos/Neg, impPos/Neg, negPos/Neg) from `Bimodal/Decidability/Tableau.lean` into `Foundations/Logic/PropositionalTableau.lean`, parameterized over general formula types to enable reuse.

**Tasks**:
- [ ] Read `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` lines 87-101 to identify the exact 8 propositional rule definitions and their dependencies
- [ ] Create `Cslib/Foundations/Logic/PropositionalTableau.lean` with the extracted propositional rules, parameterized over a general formula type with `[HasAnd F] [HasOr F] [HasImp F] [HasNeg F]`
- [ ] Update `Bimodal/Decidability/Tableau.lean` to import from the new module, replacing inline definitions with references (preserving backward compatibility)
- [ ] Register new file in the import hierarchy (`Cslib/Foundations/Logic.lean` barrel import)
- [ ] Run `lake build` to verify no regressions

**Timing**: 1.5 hours

**Depends on**: 1 (understanding Foundations/ module structure from Phase 1 documentation work)

**Files to modify**:
- `Cslib/Foundations/Logic/PropositionalTableau.lean` - new file with extracted propositional tableau rules
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` - update to import from Foundations
- `Cslib/Foundations/Logic.lean` - add import if barrel file exists

**Verification**:
- New module compiles independently
- `lake build` succeeds with no regressions in Bimodal/Decidability/
- Extracted rules are parameterized over general formula types, not specialized to bimodal formulas

---

### Phase 5: Scope GenericMCS Concretization for Modal Logic [COMPLETED]

**Goal**: Validate that `algebraicDerivationSystem` from GenericMCS can replace the custom `modalDerivationSystem` for at least one modal logic (HilbertK). This is the strategic unlock for cross-logic MCS reuse.

**Tasks**:
- [ ] Read `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` to understand `algebraicDerivationSystem` construction (parameterized on `MinimalHilbert S`)
- [ ] Read `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` to understand `modalDerivationSystem` construction
- [ ] Determine whether `algebraicDerivationSystem (S := Modal.HilbertK)` and `modalDerivationSystem ModalAxiom` produce equivalent derivation systems
- [ ] If equivalent: prove a bridging lemma `modal_algebraic_equiv` showing the two derivation systems agree on consistency and MCS properties
- [ ] If NOT equivalent: document the specific gap (likely related to how `modalDerivationSystem` handles the axiom predicate vs. how `algebraicDerivationSystem` uses the `MinimalHilbert` instance) and create a follow-up task
- [ ] If bridge proof succeeds: add a comment in `GenericMCS.lean` noting that modal logics can now use the algebraic path
- [ ] Run `lake build` to verify

**Timing**: 1.5 hours

**Depends on**: 1 (understanding the bridge theorem pattern from Phase 1 documentation; knowledge of the Hilbert-primary architecture)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - new file with bridge proof or gap documentation
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` - add comment if bridge succeeds

**Verification**:
- Bridge lemma compiles (if feasible) or blocker is documented with specific types and constraints
- `lake build` succeeds
- No `sorry` in the bridge proof

---

### Phase 6: Add Propositional Test Coverage [COMPLETED]

**Goal**: Create `CslibTests/Propositional.lean` with tests exercising BoolEvaluate, Tautology decidability, propositional derivability, and the Hilbert-algebraic bridge.

**Tasks**:
- [ ] Create `CslibTests/Propositional.lean` with test cases:
  - `#eval` tests for `BoolEvaluate` on concrete formulas (p and q, p or q, p imp q)
  - `decide` tests for `Tautology` using the Decidable instance from Phase 3
  - Derivability smoke tests: derive `p -> p`, `p -> q -> p` via `Derivable`
  - Non-tautology tests: verify `p` alone is not a tautology
  - Soundness round-trip: derived formulas are BoolEvaluate-valid
  - Hilbert-algebraic bridge: verify `hilbert_alg_complete` on concrete instances
- [ ] Register in `CslibTests.lean` (add import `CslibTests.Propositional`)
- [ ] Run `lake test` to confirm all tests pass
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`

**Timing**: 0.5 hours

**Depends on**: 3 (tests exercise the Decidable instance from Phase 3; optionally include GenericMCS bridge test if Phase 5 succeeds)

**Files to modify**:
- `CslibTests/Propositional.lean` - new test file
- `CslibTests.lean` - add import

**Verification**:
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

---

## Testing & Validation

- [ ] `lake build` succeeds after all phases
- [ ] `lake test` passes with new `CslibTests/Propositional.lean`
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No new `sorry` introduced (check with `grep -rn sorry` on modified files)
- [ ] ProofSystem.lean documentation accurately reflects registered instances
- [ ] `subs` TODO comment clarified or removed
- [ ] `HasDia` class and `DiaDuality` axiom compile without regressions
- [ ] `Decidable (Tautology phi)` instance works with `decide` tactic
- [ ] Propositional tableau rules extracted without breaking bimodal tableau
- [ ] `InferenceSystem.lean` has substantive module docstring
- [ ] Conservative.lean has no spurious imports

## Artifacts & Outputs

- `specs/266_research_propositional_and_foundations_improvements/plans/04_propositional-foundations-plan.md` (this file)
- `Cslib/Foundations/Logic/ProofSystem.lean` (modified, Phase 1)
- `Cslib/Foundations/Logic/InferenceSystem.lean` (modified, Phase 1)
- `Cslib/Foundations/Logic/Axioms.lean` (modified, Phases 1 and 2)
- `Cslib/Foundations/Logic/Connectives.lean` (modified, Phase 2)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (modified, Phase 1)
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` (modified, Phase 1)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` (modified, Phase 3)
- `Cslib/Foundations/Logic/PropositionalTableau.lean` (new, Phase 4)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` (modified, Phase 4)
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` (new, Phase 5)
- `CslibTests/Propositional.lean` (new, Phase 6)

## Rollback/Contingency

All changes are additive (new files) or localized edits (comment updates, new instances, new typeclasses). If any phase causes build failures:
1. Revert the specific phase's changes with `git checkout -- <file>`
2. Wave 1 phases (1-3) are fully independent and can each be reverted without affecting others
3. Phase 4 (tableau extraction) could break bimodal imports -- if so, keep rules in place and create aliases instead of moving definitions
4. Phase 5 (GenericMCS bridge) is the highest-risk phase -- if the bridge proof is infeasible, document the gap as a blocker and create a follow-up task; the rest of the plan proceeds unaffected
5. Phase 6 (tests) is purely additive with no regression risk
