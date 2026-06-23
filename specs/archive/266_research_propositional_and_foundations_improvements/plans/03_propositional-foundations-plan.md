# Implementation Plan: Propositional and Foundations Improvements

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Status**: [IMPLEMENTING]
- **Effort**: 7 hours
- **Dependencies**: None (Task 265 already resolved ipl_conservative_over_mpl sorry)
- **Research Inputs**: reports/01_team-research.md, reports/02_team-research.md
- **Artifacts**: plans/03_propositional-foundations-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: true

## Overview

This plan addresses actionable gaps in CSLib's Propositional/ and Foundations/Logic/ modules identified by two rounds of team research. The Propositional/ module is sorry-free and substantively complete across three logic tiers (MPL, IPL, CPL), but has concrete deficiencies: a missing algebraic-to-Hilbert completeness bridge, stale documentation, zero test coverage, no HasDia primitive, no Decidable Tautology instance, and propositional tableau rules trapped inside the bimodal module. The plan also scopes the GenericMCS concretization work needed to unlock MCS infrastructure reuse across downstream logics. Definition of done: all phases pass `lake build`, `lake test`, and `lake exe checkInitImports`.

### Research Integration

- **reports/01_team-research.md** (Round 1): Initial 8-gap analysis with 4 teammates. Identified the Hilbert-algebraic bridge as top priority, stale ProofSystem documentation, missing test coverage. Some findings were corrected in Round 2 (ipl_conservative_over_mpl sorry resolved by Task 265; Kripke completeness exists for IPL/MPL).
- **reports/02_team-research.md** (Round 2): Corrected 3 stale findings from Round 1. Key clarifications: ND capture-avoidance is a non-issue (PL has no binders, `subs` has zero call sites); abstract completeness extraction should be deferred until GenericMCS concretization is done; BimodalLogic Report 16 is irrelevant. Added new priorities: HasDia primitive, Decidable Tautology, propositional tableau extraction.

### Prior Plan Reference

The prior plan (01_propositional-foundations-plan.md, 6 phases, 8 hours) had two over-scoped phases: Phase 2 (fix ND substitution capture avoidance, 2 hours) was based on a round-1 finding that round-2 research corrected -- PL has no binders, so the full rewrite is unnecessary; the fix is to clarify/remove the TODO comment. Phase 5 (extract abstract completeness infrastructure, 2 hours) was premature -- round-2 research confirmed this depends on GenericMCS concretization for modal/temporal/bimodal logics being done first. The prior plan also omitted three items identified in round 2: HasDia, Decidable Tautology, and tableau extraction. Effort calibration from the prior plan was useful: Phase 1 (bridge, 1.5h) and Phase 4 (instance audit, 1.5h) had reasonable estimates.

### Roadmap Alignment

ROADMAP.md focuses on porting BimodalLogic to CSLib. This plan directly advances:
- **Abstract shared completeness infrastructure**: Phase 5 (GenericMCS concretization) is a prerequisite for this roadmap item
- **ProofSystem infrastructure**: Phase 2 (documentation fix) and Phase 5 (GenericMCS bridge) support downstream completeness work

## Goals & Non-Goals

**Goals**:
- Compose algebraic completeness with Hilbert-ND bridge for all three propositional logics
- Fix stale documentation in ProofSystem.lean and clarify/remove the `subs` capture-avoidance TODO
- Add test coverage for Propositional/ via CslibTests/Propositional.lean
- Add HasDia primitive to Foundations/Logic/ with duality axiom
- Create a Decidable (Tautology phi) instance using BoolEvaluate and Fintype enumeration
- Bridge GenericMCS algebraicDerivationSystem to modal/temporal/bimodal logics (scoping phase)
- Extract propositional tableau rules from Bimodal/Decidability/Tableau.lean to Foundations/

**Non-Goals**:
- Full ND substitution rewrite (non-issue: PL has no binding operators)
- Propositional sequent calculus LK/LJ (split to task 279)
- Abstract completeness extraction to Foundations/ (deferred until GenericMCS concretization is proven)
- CNF/DNF normal forms, Craig interpolation
- Refactoring all downstream logics to use GenericMCS (future task; this plan only proves the bridge)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Hilbert-ND bridge type mismatch with algebraic completeness | M | H | Research confirmed: `AxiomTheory Axioms` vs `∅`/`IPL` types differ. Need intermediate lemma connecting ND derivability under AxiomTheory to ND derivability under the empty/IPL theory. Investigate existing equivalence lemmas first. |
| HasDia changes break downstream AxiomB/Axiom5/AxiomD definitions | M | L | HasDia is additive (new class). Existing classical encodings remain; HasDia provides an alternative. Do not modify existing axiom definitions. |
| GenericMCS bridge requires nontrivial proof that algebraicDerivationSystem matches custom derivation systems | M | M | Scope Phase 5 as a proof-of-concept for modal logic only. If the bridge proof is complex, document blockers and create a follow-up task. |
| Propositional tableau extraction breaks bimodal tableau imports | H | L | Extract as new definitions that the bimodal module re-exports or aliases. Run `lake build` after extraction to catch import issues. |
| Decidable Tautology instance requires Fintype Atom constraint | L | L | This is expected and acceptable. The instance will be conditional on `[Fintype Atom] [DecidableEq Atom]`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5, 6 | 1, 2 |
| 3 | 7 | 1, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Bridge Algebraic Completeness to Hilbert [IN PROGRESS]

**Goal**: Compose the existing `alg_complete` theorems (ND-level) with the `hilbert_iff_nd` bridge to produce Hilbert-level algebraic completeness corollaries.

**Tasks**:
- [ ] Investigate the type gap between `hilbert_iff_nd_min` (uses `DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)`) and `MPL.alg_complete` (uses `DerivableIn (∅ : Theory Atom) φ`). Determine whether an existing equivalence lemma connects these or whether a new bridge lemma is needed.
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` with:
  - `MPL.hilbert_alg_complete : Derivable MinPropAxiom φ ↔ GHAValid φ` (or equivalent)
  - `IPL.hilbert_alg_complete : Derivable IntPropAxiom φ ↔ HAValid φ` (or equivalent)
  - `CPL.hilbert_alg_complete : Derivable PropositionalAxiom φ ↔ BAValid φ` (or equivalent)
- [ ] If bridge lemmas are needed, place them in the same file or in `NaturalDeduction/Equivalence.lean` as appropriate
- [ ] Register the new file in the import hierarchy (update `Algebra.lean` barrel import)
- [ ] Verify with `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` - new file with bridge theorems
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - add import (if barrel file exists)

**Verification**:
- `lake build` succeeds for the new module
- Bridge theorems correctly compose Hilbert derivability with algebraic validity
- No `sorry` in the new file

---

### Phase 2: Fix Stale Documentation and Clarify TODO Comments [NOT STARTED]

**Goal**: Update ProofSystem.lean line 49-50 to reflect that concrete instances already exist. Clarify or remove the `subs` capture-avoidance TODO in NaturalDeduction/Basic.lean.

**Tasks**:
- [ ] Edit `Cslib/Foundations/Logic/ProofSystem.lean` line 49-50: replace "Concrete instances require derivation trees (not yet ported) and are future work." with accurate description noting that propositional, modal, temporal, and bimodal instances are registered in their respective `Instances.lean` files
- [ ] Edit `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` lines 275-276: replace the TODO about capture avoidance with a note explaining that PL has no binding operators, so capture avoidance is not applicable; `subs` has zero external call sites
- [ ] Verify with `lake build`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` - update stale comment at line 49-50
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - clarify/remove TODO at lines 275-276

**Verification**:
- Comments accurately reflect the current codebase state
- `lake build` succeeds

---

### Phase 3: Add HasDia Primitive [NOT STARTED]

**Goal**: Add a `HasDia` typeclass to `Foundations/Logic/` providing a primitive diamond operator with a duality axiom, enabling future non-classical modal logics (intuitionistic modal logic).

**Tasks**:
- [ ] Create `class HasDia (F : Type*) where dia : F -> F` in `Cslib/Foundations/Logic/Connectives.lean` (or a new file `Cslib/Foundations/Logic/HasDia.lean` if Connectives.lean is not the right location)
- [ ] Add a `DiaDuality` axiom class: `class DiaDuality (S : Type*) [HasDia F] [HasBox F] [HasNeg F] [InferenceSystem S F] where dia_dual : DerivableIn S (dia φ ↔ ¬□¬φ)` (or appropriate formulation)
- [ ] Add notation `◇` for `HasDia.dia` (scoped)
- [ ] Do NOT modify existing `AxiomB`, `Axiom5`, `AxiomD` definitions -- those continue using the classical encoding; HasDia is additive
- [ ] Register any new files in the import hierarchy
- [ ] Verify with `lake build`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` or new `Cslib/Foundations/Logic/HasDia.lean` - new typeclass
- `Cslib/Foundations/Logic/Axioms.lean` - update comments referencing HasDia (lines 152, 163, 175)

**Verification**:
- `HasDia` class compiles
- Existing `lake build` succeeds (no regressions)
- Comments in Axioms.lean updated to note HasDia now exists

---

### Phase 4: Add Decidable (Tautology phi) Instance [NOT STARTED]

**Goal**: Assemble the existing `BoolEvaluate_eq_iff` infrastructure into a `Decidable (Tautology φ)` instance for `[Fintype Atom] [DecidableEq Atom]`.

**Tasks**:
- [ ] Read `Cslib/Logics/Propositional/Semantics/Bool.lean` to understand the existing `BoolEvaluate_eq_iff`, `instDecidableBoolEvaluate`, and `Tautology` definitions
- [ ] Create a bridge connecting `Tautology φ` (which uses `Prop`-valued `Valuation`) to `BoolEvaluate` (which uses `Bool`-valued `BoolValuation`)
- [ ] Prove: `Tautology φ ↔ ∀ (v : BoolValuation Atom), BoolEvaluate v φ = true` (using `BoolEvaluate_eq_iff`)
- [ ] Use `Fintype` enumeration over `BoolValuation Atom` (= `Atom → Bool`) to derive `Decidable (∀ v, BoolEvaluate v φ = true)`
- [ ] Register `instance [Fintype Atom] [DecidableEq Atom] : Decidable (Tautology φ)` in `Bool.lean` or a new companion file
- [ ] Verify with `lake build`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - add Decidable instance (or new companion file)

**Verification**:
- `#eval decide (Tautology (p ∨ ¬p))` returns `true` for a concrete `Atom` type
- `lake build` succeeds

---

### Phase 5: Scope GenericMCS Concretization for Modal Logic [NOT STARTED]

**Goal**: Prove that `algebraicDerivationSystem` from GenericMCS yields equivalent MCS properties to the custom `modalDerivationSystem` for modal logic. This validates the approach before refactoring downstream logics.

**Tasks**:
- [ ] Read `GenericMCS.lean` to understand `algebraicDerivationSystem` construction (parameterized on `MinimalHilbert S`)
- [ ] Read `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` to understand `modalDerivationSystem` construction
- [ ] Determine whether `algebraicDerivationSystem (S := Modal.HilbertK)` and `modalDerivationSystem ModalAxiom` produce equivalent derivation systems
- [ ] If equivalent: prove a bridging lemma `modal_algebraic_equiv` showing the two derivation systems agree on consistency and MCS properties
- [ ] If NOT equivalent: document the specific gap (likely related to how `modalDerivationSystem` handles the axiom predicate vs. how `algebraicDerivationSystem` uses the `MinimalHilbert` instance) and create a follow-up task
- [ ] If bridge proof succeeds: add a comment in `GenericMCS.lean` noting that modal logics can now use the algebraic path
- [ ] Verify with `lake build`

**Timing**: 1.5 hours

**Depends on**: 1, 2 (understanding the bridge theorem pattern from Phase 1 informs the approach; Phase 2 ensures documentation is accurate)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - new file with bridge proof (or documentation of the gap)
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` - add comment if bridge succeeds

**Verification**:
- Bridge lemma compiles (if feasible) or blocker is documented
- `lake build` succeeds

---

### Phase 6: Extract Propositional Tableau Rules to Foundations/ [NOT STARTED]

**Goal**: Factor the 8 propositional tableau rules (andPos/Neg, orPos/Neg, impPos/Neg, negPos/Neg) from `Bimodal/Decidability/Tableau.lean` into `Foundations/Logic/PropositionalTableau.lean`, enabling reuse for propositional decidability and templating modal tableau systems.

**Tasks**:
- [ ] Read `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` lines 86-100 to identify the exact 8 propositional rule definitions
- [ ] Create `Cslib/Foundations/Logic/PropositionalTableau.lean` with the extracted propositional rules, parameterized over a general formula type with `HasAnd`, `HasOr`, `HasImp`, `HasNeg`
- [ ] Update `Bimodal/Decidability/Tableau.lean` to import from the new module and alias the extracted definitions (preserving backward compatibility)
- [ ] Register new file in import hierarchy
- [ ] Verify with `lake build`

**Timing**: 1 hour

**Depends on**: 1, 2 (understanding the Foundations/ module structure from Phases 1-2)

**Files to modify**:
- `Cslib/Foundations/Logic/PropositionalTableau.lean` - new file with extracted propositional tableau rules
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` - update to import from Foundations
- `Cslib/Foundations/Logic.lean` - add import (if barrel file exists)

**Verification**:
- New module compiles independently
- `lake build` succeeds with no regressions in Bimodal/Decidability/
- Extracted rules are parameterized over general formula types

---

### Phase 7: Add Propositional Test Coverage [NOT STARTED]

**Goal**: Create `CslibTests/Propositional.lean` with tests exercising derivability, soundness, completeness, the Hilbert-algebraic bridge, and the new Decidable Tautology instance.

**Tasks**:
- [ ] Create `CslibTests/Propositional.lean` with test cases:
  - `#eval` tests for `BoolEvaluate` on concrete formulas
  - `decide` tests for `Tautology` using the new Decidable instance (from Phase 4)
  - Derivability smoke tests: derive `p -> p`, `p -> q -> p`
  - Soundness round-trip: verify that derived formulas are BoolEvaluate-valid
  - Hilbert-algebraic bridge: verify `hilbert_alg_complete` on concrete instances (from Phase 1)
  - Non-derivability: verify Peirce's law `((p -> q) -> p) -> p` is not derivable in IPL/MPL (if decidability allows)
- [ ] Register in `CslibTests.lean` (add import)
- [ ] Run `lake test` to confirm all tests pass
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`

**Timing**: 0.5 hours

**Depends on**: 1, 4, 5 (tests exercise the bridge theorems from Phase 1, Decidable instance from Phase 4, and GenericMCS validation from Phase 5)

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
- [ ] Bridge theorems correctly compose algebraic completeness with Hilbert-ND equivalence
- [ ] ProofSystem.lean documentation is accurate
- [ ] `subs` TODO comment clarified or removed
- [ ] HasDia class compiles and does not break existing axiom definitions
- [ ] `Decidable (Tautology φ)` instance works with `decide` tactic
- [ ] Propositional tableau rules extracted without breaking bimodal tableau

## Artifacts & Outputs

- `specs/266_research_propositional_and_foundations_improvements/plans/03_propositional-foundations-plan.md` (this file)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` (new, Phase 1)
- `Cslib/Foundations/Logic/ProofSystem.lean` (modified, Phase 2)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (modified, Phase 2)
- `Cslib/Foundations/Logic/Connectives.lean` or `HasDia.lean` (modified/new, Phase 3)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` (modified, Phase 4)
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` (new, Phase 5)
- `Cslib/Foundations/Logic/PropositionalTableau.lean` (new, Phase 6)
- `CslibTests/Propositional.lean` (new, Phase 7)

## Rollback/Contingency

All changes are additive (new files) or localized edits (comment updates, new instances). If any phase causes build failures:
1. Revert the specific phase's changes with `git checkout -- <file>`
2. Wave 1 phases (1-4) are fully independent and can each be reverted without affecting others
3. Phase 5 (GenericMCS bridge) is the highest-risk phase -- if the bridge proof is infeasible, document the gap as a blocker and create a follow-up task. The rest of the plan proceeds unaffected.
4. Phase 6 (tableau extraction) could break bimodal imports -- if so, keep rules in place and create aliases instead of moving definitions
5. Phase 7 (tests) is purely additive with no regression risk
