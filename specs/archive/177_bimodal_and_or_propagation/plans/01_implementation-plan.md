# Implementation Plan: Bimodal And/Or Propagation

- **Task**: 177 - Propagate the hybrid five-primitive design to the Bimodal layer
- **Status**: [NOT STARTED]
- **Effort**: 16 hours
- **Dependencies**: Task 175 (Modal and/or propagation), Task 176 (Temporal and/or propagation)
- **Research Inputs**: specs/177_bimodal_and_or_propagation/reports/01_bimodal-propagation-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Propagate the hybrid five-primitive design to the Bimodal layer by adding native `and` and `or`
constructors to `Bimodal.Formula`, changing it from 6 constructors `{atom, bot, imp, box, untl,
snce}` to 8 constructors `{atom, bot, imp, and, or, box, untl, snce}`. This requires adding 6
new axiom constructors (andI, andE1, andE2, orI1, orI2, orE), extending three separate truth
functions (truthAt, intTruth, ExtFormula operations), updating all pattern-matching functions
across ~50 files, and updating decidability helpers (asAnd?/asOr?) from Lukasiewicz decomposition
to direct constructor matching. Estimated ~1,860 lines changed/added. This is the largest
propagation in the five-primitive design series.

### Research Integration

Key findings from the research report (01_bimodal-propagation-research.md):
- **Three truth functions**: Unlike Modal (single `Satisfies`), Bimodal has `truthAt`
  (task-model), `intTruth` (integer temporal for separation), and `ExtFormula` operations
  (conservative extension). All three need and/or cases.
- **File impact analysis**: ~50-60 files need changes out of 127 total; ~60-70 files need
  NO changes (no formula pattern matching).
- **Change patterns identified**: 6 patterns (A-F) covering formula match extension, axiom
  extension, truth evaluation, subformula closure, decidability helpers, and abbrev-to-constructor
  transition.
- **Separation layer risk**: 10,263 lines across 17 files, most complex subsystem.
  The and/or cases should be structurally simple (propositionally definable, no temporal content).
- **Decidability tableau risk**: asAnd?/asOr? change from Lukasiewicz imp-pattern matching
  to direct constructor matching, which changes how the tableau decomposes formulas.
- **Embedding dependency**: Phase 8 embedding files depend on tasks 175/176 completing first.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the five-primitive Foundations Refactor design across:
- Bimodal syntax/semantics/proof system (already marked completed in ROADMAP.md but needs
  the and/or constructor extension)
- All Bimodal metalogic subsystems (Soundness, Completeness, Separation, Decidability,
  ConservativeExtension, Algebraic)

## Goals & Non-Goals

**Goals**:
- Add `and` and `or` as native constructors to `Bimodal.Formula`
- Add 6 and/or axiom constructors to the proof system
- Extend all truth functions (truthAt, intTruth, ExtFormula) with and/or structural clauses
- Update all pattern-matching functions and inductive proofs across the codebase
- Update decidability helpers to use direct constructor matching
- Maintain full CI (lake build, lake test, checkInitImports, lint-style) green throughout
- Update embedding files to map and/or constructors homomorphically

**Non-Goals**:
- Changing the derived connective definitions (neg, top, diamond, etc. remain derived)
- Refactoring the separation theorem proof structure
- Adding new theorems beyond what is needed for and/or
- Updating upstream PR branches (separate task)
- Addressing discrete/continuous completeness (separate blocked tasks)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Separation layer and/or induction complexity | H | M | and/or are propositionally definable, so separation induction cases should be straightforward recursive calls; follow existing imp pattern |
| Decidability tableau rule interaction | H | M | Test asAnd?/asOr? carefully; verify allFuturePosFormulas etc. don't accidentally match new constructors; run full test suite after changes |
| Tasks 175/176 not yet complete (embedding dependency) | M | H | Defer Phase 8 (Embeddings) to last; all other phases are independent of 175/176 |
| BimodalConnectives typeclass changes from Foundations | M | L | Verify if HasAnd/HasOr registration is needed in Formula.lean; check task 172/173 output |
| Build breakage mid-phase from cascading changes | M | M | Build after each phase boundary; phases ordered by dependency (syntax first, then proof system, then semantics, etc.) |
| Hierarchy induction files (HierarchyInduction.lean, 1455 lines) | M | M | The and/or cases in hierarchy induction are structurally identical to imp cases; follow the binary connective pattern |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 5 | 2 |
| 4 | 6, 7 | 3, 4, 5 |
| 5 | 8 | 6, 7 (and tasks 175, 176) |

Phases within the same wave can execute in parallel.

---

### Phase 1: Core Syntax Layer [COMPLETED]

**Goal**: Add `and` and `or` constructors to `Bimodal.Formula` and update all syntax-level
pattern-matching functions (swapTemporal, atoms, subformulas, closure, nesting depth).

**Tasks**:
- [ ] `Syntax/Formula.lean`: Add `.and` and `.or` constructors to the `Formula` inductive type,
  positioned after `imp` (maintaining `{atom, bot, imp, and, or, box, untl, snce}` order).
  Remove the `abbrev` definitions for `Formula.and` and `Formula.or` (they become constructors).
  Update `swapTemporal` (+2 cases: recurse on both subformulas), `swapTemporal_involution` (+2),
  `swapTemporal_neg`/`swapTemporal_diamond` (verify no change needed), `atoms` (+2 cases),
  `atoms_swapTemporal` (+2 cases). Register `HasAnd`/`HasOr` instances if typeclass requires
  (check Foundations task 172 output). Update `BimodalConnectives` instance if it gained
  `conj`/`disj` fields.
- [ ] `Syntax/Subformulas.lean`: Add and/or cases to `subformulas` function (+2 cases, binary
  connective pattern same as `imp`). Add `subformulas_and_left`/`_right` and
  `subformulas_or_left`/`_right` membership lemmas. Update `subformulas_trans` (+2 cases).
- [ ] `Syntax/SubformulaClosure.lean`: Add `closure_and_left`, `closure_and_right`,
  `closure_or_left`, `closure_or_right` lemmas following the existing `closure_imp_left/right`
  pattern.
- [ ] `Syntax/SubformulaClosure/NestingDepth.lean`: Add and/or cases to `fNestingDepth` (+2,
  both return 0), `pNestingDepth` (+2), `extractFutureInner`/`extractPastInner` (+2, return
  none). Add `IsFutureFormula`/`IsPastFormula` instance match arms (+2 each).
- [ ] `Syntax/SubformulaClosure/TemporalFormulas.lean`: Add and/or cases to
  `IsUntilFormula`/`IsSinceFormula` instances (+2 match arms each).
  `toUntilDeferral`/`toSinceDeferral` (+2 cases each, return bot). Add
  `f_nesting_depth_and`/`f_nesting_depth_or` simp lemmas.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - Add constructors, update swapTemporal/atoms
- `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` - Subformula cases + membership lemmas
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean` - Closure membership lemmas
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - Nesting depth functions
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` - Temporal predicate instances

**Verification**:
- `lake build Cslib.Logics.Bimodal.Syntax.SubformulaClosure.TemporalFormulas` compiles cleanly
- No sorry introduced
- All syntax-layer files build

---

### Phase 2: Proof System Layer [COMPLETED]

**Goal**: Add 6 new and/or axiom constructors and extend the proof system substitution
and instance registrations.

**Tasks**:
- [ ] `ProofSystem/Axioms.lean`: Add 6 new constructors to the `Axiom` inductive:
  `andI (phi psi)`, `andE1 (phi psi)`, `andE2 (phi psi)`, `orI1 (phi psi)`,
  `orI2 (phi psi)`, `orE (phi psi chi)`. Update `minFrameClass` with 6 new
  `| _ => .Base` catch-all cases (all and/or axioms are Base class).
- [ ] `ProofSystem/Substitution.lean`: Add 2 cases to `Formula.subst` for `.and`/`.or`.
  Update `subst_and`/`subst_or` simp lemmas to become direct (no longer Lukasiewicz
  expansion). Add 6 cases to `axiomSubst` for new axiom constructors. Add 2 cases to
  `swapTemporal_subst`. Add 2 cases to `subst_fresh_eq` and `subst_atoms`.
- [ ] `ProofSystem/Instances.lean`: Add 6 `HasAxiom` instances: `HasAxiomAndI`,
  `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE`.
  Verify `ClassicalHilbert` and `BimodalTMHilbert` instances auto-update.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` - 6 new axiom constructors + minFrameClass
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` - Formula.subst + axiomSubst extension
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` - 6 new HasAxiom instances

**Verification**:
- `lake build Cslib.Logics.Bimodal.ProofSystem.Instances` compiles cleanly
- No sorry introduced

---

### Phase 3: Semantics and Soundness [IN PROGRESS]

**Goal**: Extend the primary truth evaluation function and all soundness proofs with
and/or structural clauses and axiom validity theorems.

**Tasks**:
- [ ] `Semantics/Truth.lean`: Add 2 cases to `truthAt`:
  `| .and phi psi => truthAt M Omega tau t phi /\ truthAt M Omega tau t psi`
  `| .or phi psi => truthAt M Omega tau t phi \/ truthAt M Omega tau t psi`.
  Add 2 cases to `time_shift_preserves_truth` (and/or have no temporal content, so
  the proof is: apply constructor, recurse on both subformulas via inductive hypotheses).
  Add 2 cases to `truth_double_shift_cancel`.
- [ ] `Metalogic/Soundness/Core.lean`: Add 2 cases to `truth_at_swap_swap` for and/or
  (recurse on both subformulas).
- [ ] `Metalogic/Soundness/Soundness.lean`: Add 6 axiom validity theorems:
  `andI_valid`, `andE1_valid`, `andE2_valid`, `orI1_valid`, `orI2_valid`, `orE_valid`.
  Add 6 cases to `axiom_valid` match. Tactics: andI uses `And.intro`, andE1/E2 use
  `And.left`/`And.right`, orI1/I2 use `Or.inl`/`Or.inr`, orE uses `Or.elim`.
- [ ] `Metalogic/Soundness/FrameClassVariants.lean`: Add 6 cases each to
  `axiom_valid_dense` and `axiom_valid_discrete` (all delegate to base `axiom_valid`
  since and/or axioms are Base class).

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` - truthAt + time-shift preservation proofs
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Core.lean` - truth_at_swap_swap
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean` - 6 axiom validity + axiom_valid
- `Cslib/Logics/Bimodal/Metalogic/Soundness/FrameClassVariants.lean` - dense/discrete variants

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.FrameClassVariants` compiles cleanly
- No sorry introduced

---

### Phase 4: Core Metalogic and Completeness [NOT STARTED]

**Goal**: Extend MCS properties, truth lemmas across all completeness variants
(base Completeness, BXCanonical TruthLemma, Algebraic ParametricTruthLemma),
and restricted MCS with and/or membership and closure lemmas.

**Tasks**:
- [ ] `Metalogic/Core/MCSProperties.lean`: Add `and_iff_mcs` and `or_iff_mcs` lemmas
  for native constructors. `and_iff_mcs`: `phi.and psi in S <-> phi in S /\ psi in S`.
  `or_iff_mcs`: `phi.or psi in S <-> phi in S \/ psi in S`. These follow from the
  axioms andI/andE1/andE2 and orI1/orI2/orE via the MCS closure properties.
- [ ] `Metalogic/Core/RestrictedMCS.lean`: Add and/or closure lemmas for restricted MCS
  if needed (verify whether the existing MCS lemmas propagate through restriction).
- [ ] `Metalogic/Completeness.lean`: Add 2 cases to truth lemma induction for and/or.
  The `and` case uses `and_iff_mcs`, the `or` case uses `or_iff_mcs`.
- [ ] `Metalogic/BXCanonical/TruthLemma.lean`: Add 2 cases to truth lemma induction.
  Same pattern as base Completeness.
- [ ] `Metalogic/Algebraic/ParametricTruthLemma.lean`: Add 2 cases to truth lemma
  induction for and/or.
- [ ] `Metalogic/Algebraic/RestrictedParametricTruthLemma.lean`: Add 2 cases to truth
  lemma induction.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` - and/or MCS membership lemmas
- `Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean` - and/or closure lemmas
- `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` - truth lemma +2 cases
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/TruthLemma.lean` - truth lemma +2 cases
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean` - truth lemma +2 cases
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` - +2 cases

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Completeness` compiles cleanly
- `lake build Cslib.Logics.Bimodal.Metalogic.BXCanonical.TruthLemma` compiles cleanly
- No sorry introduced

---

### Phase 5: Conservative Extension [NOT STARTED]

**Goal**: Extend the `ExtFormula` parallel type with and/or constructors and update all
lifting, substitution, and derivation operations in the conservative extension module.

**Tasks**:
- [ ] `Metalogic/ConservativeExtension/ExtFormula.lean`: Add `.and` and `.or` constructors
  to the `ExtFormula` inductive type. Add 2 cases to `embedFormula`. Add 2 cases to
  `embedFormula_injective`. Add 2 cases to `fresh_not_in_embedFormula_atoms`.
  Update all structural lemmas for the new constructors.
- [ ] `Metalogic/ConservativeExtension/ExtDerivation.lean`: Add 6 cases to `extAxiomSubst`
  for new and/or axiom constructors (following the same pattern as existing axiom cases).
- [ ] `Metalogic/ConservativeExtension/Lifting.lean`: Add 2 cases each to `liftFormula`
  and `unliftFormula`. Update lifting preservation lemmas (+2 cases each).
- [ ] `Metalogic/ConservativeExtension/Substitution.lean`: Add 2 cases to
  `ExtFormula.subst`. Update substitution lemmas (+2 cases each).

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` - ExtFormula type + ops
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean` - +6 axiom cases
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` - lift/unlift +2 cases
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Substitution.lean` - subst +2 cases

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Lifting` compiles cleanly
- No sorry introduced

---

### Phase 6: Separation Layer [NOT STARTED]

**Goal**: Extend the separation theorem infrastructure with and/or cases across all
definition files, formula operations, duality, normal form, elimination files,
and the hierarchy induction. This is the most complex phase by file count.

**Tasks**:
- [ ] `Metalogic/Separation/Defs.lean`: Add 2 cases to `intTruth` (and = conjunction,
  or = disjunction). Add 2 cases each to `isUFree`, `isSFree` (and/or are U-free/S-free
  if components are). Add 2 cases to `isSyntacticallySeparated`. Add 2 cases each to
  `junctionDepth`, `U_depth_under_S`, `countUSubformulas`.
- [ ] `Metalogic/Separation/FormulaOps.lean`: Add 2 cases to `substFormula`.
  Add 2 cases to `subst_correctness` induction.
- [ ] `Metalogic/Separation/Duality.lean`: Add 2 cases to `swapTemporalInt`.
  Update duality lemmas (+2 cases each).
- [ ] `Metalogic/Separation/NegationEquiv.lean`: Add and/or negation equivalence cases
  if function matches on Formula.
- [ ] `Metalogic/Separation/Eliminations.lean`: Update formula decomposition functions
  with and/or cases where they match on Formula constructors.
- [ ] `Metalogic/Separation/DualEliminations.lean`: Similar decomposition updates.
- [ ] `Metalogic/Separation/Distributivity.lean`: Add and/or cases if matching on Formula.
- [ ] `Metalogic/Separation/NormalForm.lean`: Add 2 cases to `u_free_s_free_separated`
  induction (and/or with U-free/S-free components are trivially separated).
- [ ] `Metalogic/Separation/SeparationThm.lean`: Add 2 cases to main separation theorem
  induction.
- [ ] `Metalogic/Separation/TemporalClosure.lean`: Update closure operations with
  and/or cases where they match on Formula.
- [ ] `Metalogic/Separation/Hierarchy/HierarchyDefs.lean`: Add 2 cases to
  `hierJunctionDepth` and related hierarchy depth functions.
- [ ] `Metalogic/Separation/Hierarchy/HierarchyInduction.lean`: Add 2 cases to main
  hierarchy induction (and/or follow binary connective pattern).
- [ ] `Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean`: Add and/or cases if
  matching on Formula in case analysis.
- [ ] `Metalogic/Separation/Hierarchy/HierarchyCompletion.lean`: Add and/or cases if
  matching on Formula in completion argument.

**Timing**: 2 hours

**Depends on**: 3, 4, 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` - intTruth + all predicates
- `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` - substFormula + correctness
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` - swapTemporalInt + duality lemmas
- `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean` - negation equivalences
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` - formula decomposition
- `Cslib/Logics/Bimodal/Metalogic/Separation/DualEliminations.lean` - dual decomposition
- `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean` - distributivity cases
- `Cslib/Logics/Bimodal/Metalogic/Separation/NormalForm.lean` - normal form induction
- `Cslib/Logics/Bimodal/Metalogic/Separation/SeparationThm.lean` - main theorem induction
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean` - closure operations
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean` - depth functions
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean` - induction
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` - case analysis
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCompletion.lean` - completion

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Separation.SeparationThm` compiles cleanly
- `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCompletion` compiles
- No sorry introduced

---

### Phase 7: Decidability Layer [NOT STARTED]

**Goal**: Update decidability helpers (asAnd?/asOr?) to use direct constructor matching,
extend axiom matcher with 6 new patterns, and update hash/complexity functions.

**Tasks**:
- [ ] `Metalogic/Decidability/SignedFormula.lean`: Add 2 cases to `Formula.hashFormula`
  for and/or. Add 2 cases to `Formula.complexity`. Add 2 cases to `unexpandedComplexity`.
  Update `asAnd?` to match `.and phi psi => some (phi, psi)` directly (replacing
  Lukasiewicz pattern). Update `asOr?` similarly. Verify that `asNeg?` does NOT need
  changes (neg is still derived). Verify branch filter functions
  (allFuturePosFormulas, someFutureNegFormulas, etc.) do not accidentally match
  new constructors.
- [ ] `Metalogic/Decidability/Tableau.lean`: Update tableau rule implementations in
  `applyRule` for `andPos`/`andNeg`/`orPos`/`orNeg` to use native constructors
  instead of Lukasiewicz decomposition. This should simplify the rules.
- [ ] `Metalogic/Decidability/AxiomMatcher.lean`: Add 6 patterns to `matchAxiom` for
  andI, andE1, andE2, orI1, orI2, orE axiom matching.
- [ ] `Metalogic/Decidability/ProofExtraction.lean`: Update if proof extraction matches
  on formula structure for and/or (verify and add cases as needed).
- [ ] `Metalogic/Decidability/FMP/TruthPreservation.lean`: Add 2 cases to
  `truthPreserved` if it matches on Formula constructors (verify and add as needed).

**Timing**: 2 hours

**Depends on**: 3, 4, 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean` - hash, complexity, asAnd?/asOr?
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` - applyRule native and/or
- `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` - +6 axiom patterns
- `Cslib/Logics/Bimodal/Metalogic/Decidability/ProofExtraction.lean` - possible formula matching
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/TruthPreservation.lean` - possible +2 cases

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau` compiles cleanly
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.AxiomMatcher` compiles cleanly
- No sorry introduced

---

### Phase 8: Embeddings, Algebraic, and Final CI [NOT STARTED]

**Goal**: Update embedding files (depends on tasks 175/176), extend remaining algebraic
files, update propositional theorem files if needed, and run full CI verification.

**Tasks**:
- [ ] `Embedding/ModalEmbedding.lean`: Add 2 cases to `toBimodal` mapping `.and -> .and`
  and `.or -> .or`. Add 2 simp lemmas for the new cases. (Requires task 175 complete.)
- [ ] `Embedding/TemporalEmbedding.lean`: Add 2 cases to `toBimodal` mapping.
  Add 2 simp lemmas. (Requires task 176 complete.)
- [ ] `Embedding/PropositionalEmbedding.lean`: Update `.and`/`.or` cases from Lukasiewicz
  encoding to native constructor mapping. Commutation proofs simplify to `simp`.
  (Requires tasks 175 and 176 complete.)
- [ ] `Metalogic/Algebraic/LindenbaumQuotient.lean`: Add and/or characterization for
  `Derives` if it matches on formula structure.
- [ ] `Metalogic/Algebraic/BooleanStructure.lean`: Update `sup`/`inf` operations if
  they become direct with native and/or.
- [ ] `Metalogic/Algebraic/UltrafilterMCS.lean`: Add and/or membership lemmas if needed.
- [ ] `Theorems/Propositional/Core.lean`: Verify `lce`/`rce` work with native and/or
  constructors; update if encoding assumptions changed.
- [ ] Run full CI verification: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`.

**Timing**: 2 hours

**Depends on**: 6, 7 (and external: tasks 175, 176)

**Files to modify**:
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` - +2 cases + lemmas
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` - +2 cases + lemmas
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` - update encoding
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` - possible
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` - possible
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` - possible
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - possible

**Verification**:
- `lake build` (full project builds cleanly)
- `lake test` (all tests pass)
- `lake exe checkInitImports` (init imports correct)
- `lake exe lint-style` (style linting passes)
- No sorry introduced across entire Bimodal module

## Testing & Validation

- [ ] Each phase builds its target module cleanly before proceeding to next phase
- [ ] Full `lake build` passes after all phases complete
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] Zero new sorry introduced
- [ ] All 6 and/or axioms have validity proofs in Soundness
- [ ] All 3 truth functions (truthAt, intTruth, ExtFormula) have and/or structural clauses
- [ ] Decidability tableau correctly decomposes native and/or constructors
- [ ] Embedding files correctly map and/or from Modal/Temporal to Bimodal

## Artifacts & Outputs

- `specs/177_bimodal_and_or_propagation/plans/01_implementation-plan.md` (this file)
- `specs/177_bimodal_and_or_propagation/summaries/01_implementation-summary.md` (after completion)
- ~50-60 modified Lean files in `Cslib/Logics/Bimodal/`

## Rollback/Contingency

- All changes are additive (new constructors, new cases) so rollback is straightforward:
  revert the commit(s) to restore the 6-constructor Formula type.
- If Phase 8 (Embeddings) is blocked by tasks 175/176, mark it [BLOCKED] and complete
  phases 1-7 independently. The embedding files are small (~245 lines total) and can
  be done as a follow-up task.
- If the Separation layer (Phase 6) proves more complex than expected, it can be split
  into two sub-phases: 6a (Defs + FormulaOps + Duality + NormalForm + SeparationThm)
  and 6b (Eliminations + DualEliminations + Hierarchy files).
- Git commit after each phase for clean revert boundaries.
