# Implementation Plan: Task #183

- **Task**: 183 - Establish strong completeness for the minimal, intuitionistic, and classical propositional logics
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None (all prerequisite infrastructure exists)
- **Research Inputs**: specs/183_strong_completeness_propositional_logics/reports/01_team-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Establish strong completeness for the minimal, intuitionistic, and classical propositional logics in CSLib. Strong completeness states that if a formula is a semantic consequence of an arbitrary (possibly infinite) set of premises, then it is derivable from some finite subset of those premises. This is strictly stronger than the existing weak completeness results, which only handle derivability from the empty context. The implementation follows the direct MCS/Lindenbaum approach, reusing approximately 85-90% of the existing infrastructure (Lindenbaum lemmas, canonical models, truth lemmas). The deliverables are 4 new Lean files containing shared definitions, three strong completeness theorems, three strong soundness theorems, and three compactness corollaries.

### Research Integration

Team research (4 teammates, parallel) reached unanimous consensus on the direct MCS/Lindenbaum approach. Key findings integrated into this plan:

- **Gap analysis (Teammate C)**: CSLib has ~85-90% of needed infrastructure. Four categories of new code: `SetDerivable` definition, three semantic entailment definitions, three strong soundness theorems, three strong completeness theorems.
- **Proof architecture (Teammate A)**: All three proofs follow a uniform contrapositive pattern -- assume non-derivability, extend to MCS/prime DCCS/prime MinTheory, apply truth lemma to get countermodel, derive contradiction with semantic consequence.
- **Compactness analysis (Teammate B)**: Compactness route to strong completeness is circular for propositional logics. Compactness is a free corollary of strong completeness + strong soundness.
- **Algebraic approach (Teammate D)**: Deferred -- only works for classical, costs 5-10x more, lacks Heyting algebra support in Mathlib.
- **Implementation order**: Minimal first (no consistency side condition), then intuitionistic (EFQ case split), then classical (Peirce consistency argument).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items match this task directly.

## Goals & Non-Goals

**Goals**:
- Define `SetDerivable` (set-based syntactic derivability) parameterized over axiom predicates, with basic lemmas
- Define semantic entailment (`SemanticEntails`, `ISemanticEntails`, `MSemanticEntails`) for all three logics
- Prove strong soundness for all three logics
- Prove strong completeness for all three logics via the Lindenbaum/MCS approach
- Prove compactness as a corollary for all three logics
- Prove biconditional wrappers combining strong soundness and strong completeness

**Non-Goals**:
- Algebraic completeness via Lindenbaum-Tarski algebras (deferred to future task)
- Replacing existing weak completeness proofs with corollaries from strong completeness
- Stone duality or Esakia duality
- First-order extensions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Intuitionistic case split complexity (consistency of Gamma vs. EFQ trivial case) | M | L | Pattern is `rcases Classical.em (IntConsistent Gamma)` -- well-understood |
| Classical consistency argument (`Gamma union {neg phi}` consistent when phi not derivable) | L | L | Existing `prop_completeness` proof contains identical argument for empty Gamma -- direct generalization |
| Universe polymorphism mismatch in Kripke semantic consequence definitions | M | L | Follow universe parameters from `IntCompleteness.lean` and `MinCompleteness.lean` exactly |
| Set vs. List bridging in `SetDerivable` -- connecting deductive closures to `Deriv` | L | L | `intDeductiveClosure` and `minDeductiveClosure` already use the same List-based `Deriv` |
| `lake build` regressions from new imports | L | L | Scoped builds after each phase; `lake exe mk_all --module` after adding new files |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Shared Definitions (SemanticConsequence.lean) [NOT STARTED]

**Goal**: Create the shared definitions file containing `SetDerivable`, all three semantic entailment definitions, and basic lemmas. This is the foundation that all subsequent phases depend on.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` with module header, copyright, and `import Cslib.Init`
- [ ] Import `Cslib.Logics.Propositional.Semantics.Basic` (for `Evaluate`, `Valuation`) and `Cslib.Logics.Propositional.Semantics.Kripke` (for `IForces`)
- [ ] Import `Cslib.Logics.Propositional.ProofSystem.Derivation` (for `Deriv`, `Derivable`, `propDerivationSystem`)
- [ ] Define `SetDerivable Axioms (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop` as `exists (L : List (PL.Proposition Atom)), (forall x in L, x in Gamma) /\ Deriv Axioms L phi`
- [ ] Prove `SetDerivable_of_mem`: `phi in Gamma -> SetDerivable Axioms Gamma phi`
- [ ] Prove `SetDerivable_weakening`: `Gamma subset Delta -> SetDerivable Axioms Gamma phi -> SetDerivable Axioms Delta phi`
- [ ] Prove `SetDerivable_of_Derivable`: `Derivable Axioms phi -> SetDerivable Axioms Gamma phi`
- [ ] Prove `SetDerivable_empty_iff`: `SetDerivable Axioms {} phi <-> Derivable Axioms phi`
- [ ] Prove `SetDerivable_mp`: if `SetDerivable Axioms Gamma (phi -> psi)` and `SetDerivable Axioms Gamma phi` then `SetDerivable Axioms Gamma psi` (combine witness lists)
- [ ] Define `SemanticEntails (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop` -- classical bivalent semantic consequence
- [ ] Define `ISemanticEntails (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop` -- intuitionistic Kripke semantic consequence (quantifies over all Kripke models with `bot_forces = fun _ => False`)
- [ ] Define `MSemanticEntails (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop` -- minimal Kripke semantic consequence (quantifies over all minimal Kripke models with arbitrary upward-closed `bot_forces`)
- [ ] Prove `SemanticEntails_of_Tautology`: `Tautology phi -> SemanticEntails Gamma phi`
- [ ] Prove `ISemanticEntails_of_IValid`: `IValid phi -> ISemanticEntails Gamma phi`
- [ ] Prove `MSemanticEntails_of_MValid`: `MValid phi -> MSemanticEntails Gamma phi`
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.SemanticConsequence`
- [ ] Run `lake exe mk_all --module` to update barrel import

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` -- new file (~100-130 lines)
- `Cslib.lean` -- updated by `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.SemanticConsequence` succeeds
- All definitions and lemmas compile without sorry
- `lake exe checkInitImports` passes

---

### Phase 2: Minimal Strong Completeness (MinStrongCompleteness.lean) [NOT STARTED]

**Goal**: Prove minimal strong soundness, minimal strong completeness, the biconditional wrapper, and the compactness corollary. Minimal logic is the simplest case because `MinTheory` has no consistency requirement -- `minDeductiveClosure(Gamma)` is always a MinTheory.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` with module header
- [ ] Import `Cslib.Logics.Propositional.Semantics.SemanticConsequence`, `Cslib.Logics.Propositional.Metalogic.MinCompleteness`
- [ ] Prove `min_strong_soundness`: `SetDerivable MinPropAxiom Gamma phi -> MSemanticEntails Gamma phi`
  - Unfold `SetDerivable` to get witness list `L` and derivation `Deriv MinPropAxiom L phi`
  - Use existing `min_soundness` on `L` to show forcing at any world satisfying `L`
  - Since all elements of `L` are in `Gamma` and Gamma is satisfied, phi is forced
- [ ] Prove helper `minDeductiveClosure_iff_SetDerivable`: `phi in minDeductiveClosure(Gamma) <-> SetDerivable MinPropAxiom Gamma phi` (definitional unfolding)
- [ ] Prove `min_strong_completeness`: `MSemanticEntails Gamma phi -> SetDerivable MinPropAxiom Gamma phi`
  - Contrapositive: assume `phi` not set-derivable from `Gamma`
  - Then `phi not in minDeductiveClosure(Gamma)` (by the helper)
  - `minDeductiveClosure(Gamma)` is a MinTheory (no consistency needed)
  - Apply `min_prime_exclusion` to get prime MinTheory `T` containing `Gamma` but excluding `phi`
  - Build canonical world from `T` using `MinCanonicalWorld`
  - By `min_truth_lemma`: all of `Gamma` is forced at `T`, but `phi` is not forced
  - Instantiate `MSemanticEntails` with the canonical model to get contradiction
- [ ] Prove `min_strong_completeness_iff`: `MSemanticEntails Gamma phi <-> SetDerivable MinPropAxiom Gamma phi`
- [ ] Prove `min_compactness`: if every finite subset of `Gamma` is minimally satisfiable, then `Gamma` is minimally satisfiable (corollary of strong completeness + strong soundness)
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness`
- [ ] Run `lake exe mk_all --module`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` -- new file (~120-160 lines)
- `Cslib.lean` -- updated by `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness` succeeds
- No sorry in the file
- `lake exe checkInitImports` passes

---

### Phase 3: Intuitionistic Strong Completeness (IntStrongCompleteness.lean) [NOT STARTED]

**Goal**: Prove intuitionistic strong soundness, intuitionistic strong completeness (with the EFQ consistency case split), the biconditional wrapper, and the compactness corollary. This is more involved than the minimal case because `IntDCCS` has a consistency requirement, so a case split on `Gamma`'s Int-consistency is needed.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` with module header
- [ ] Import `Cslib.Logics.Propositional.Semantics.SemanticConsequence`, `Cslib.Logics.Propositional.Metalogic.IntCompleteness`
- [ ] Prove `int_strong_soundness`: `SetDerivable IntPropAxiom Gamma phi -> ISemanticEntails Gamma phi`
  - Same pattern as minimal: unfold `SetDerivable`, apply existing `int_soundness` on the witness list
- [ ] Prove helper `intDeductiveClosure_iff_SetDerivable`: `phi in intDeductiveClosure(Gamma) <-> SetDerivable IntPropAxiom Gamma phi`
- [ ] Prove `int_strong_completeness`: `ISemanticEntails Gamma phi -> SetDerivable IntPropAxiom Gamma phi`
  - Case split: `rcases Classical.em (IntConsistent intDeductiveClosure(Gamma))`
  - **Inconsistent case**: If `intDeductiveClosure(Gamma)` is inconsistent, then `bot` is set-derivable from `Gamma`. By EFQ (`IntPropAxiom` includes EFQ), `phi` is set-derivable from `Gamma`. Done.
  - **Consistent case**: `intDeductiveClosure(Gamma)` is an IntDCCS and `phi not in intDeductiveClosure(Gamma)` (otherwise phi is set-derivable). Apply `int_prime_exclusion` to get prime IntDCCS `T` containing `Gamma` but excluding `phi`. Build canonical world from `T` using `IntCanonicalWorld`. By `int_truth_lemma`: all of `Gamma` is forced at `T`, but `phi` is not forced. Instantiate `ISemanticEntails` with the canonical model to get contradiction.
- [ ] Prove `int_strong_completeness_iff`: `ISemanticEntails Gamma phi <-> SetDerivable IntPropAxiom Gamma phi`
- [ ] Prove `int_compactness`: if every finite subset of `Gamma` is intuitionistically satisfiable, then `Gamma` is intuitionistically satisfiable
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness`
- [ ] Run `lake exe mk_all --module`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` -- new file (~140-180 lines)
- `Cslib.lean` -- updated by `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness` succeeds
- No sorry in the file
- `lake exe checkInitImports` passes

---

### Phase 4: Classical Strong Completeness (StrongCompleteness.lean) [NOT STARTED]

**Goal**: Prove classical strong soundness, classical strong completeness (with the Peirce-based consistency argument), the biconditional wrapper, and the compactness corollary. The classical proof is conceptually the closest to the existing `prop_completeness` proof -- it extends from `{neg phi}` to `Gamma union {neg phi}`.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` with module header
- [ ] Import `Cslib.Logics.Propositional.Semantics.SemanticConsequence`, `Cslib.Logics.Propositional.Metalogic.Completeness`
- [ ] Prove `prop_strong_soundness`: `SetDerivable PropositionalAxiom Gamma phi -> SemanticEntails Gamma phi`
  - Unfold `SetDerivable`, apply existing `prop_soundness` on the witness list
- [ ] Prove helper `not_SetDerivable_imp_union_neg_consistent`: if `phi` is not set-derivable from `Gamma`, then `Gamma union {neg phi}` is `PropSetConsistent`
  - Contrapositive: if `Gamma union {neg phi}` is inconsistent, some finite list `L` from `Gamma union {neg phi}` derives `bot`
  - Separate `L` into `L_gamma` (from Gamma) and `neg phi` (from the singleton)
  - By deduction theorem: `L_gamma |- neg phi -> bot`, i.e. `L_gamma |- neg neg phi`
  - By Peirce's law / DNE (available in `PropositionalAxiom`): `L_gamma |- phi`
  - Therefore `phi` is set-derivable from `Gamma` -- contradiction
- [ ] Prove `prop_strong_completeness`: `SemanticEntails Gamma phi -> SetDerivable PropositionalAxiom Gamma phi`
  - Contrapositive: assume `phi` not set-derivable from `Gamma`
  - By helper: `Gamma union {neg phi}` is `PropSetConsistent`
  - Apply `prop_lindenbaum` to get MCS `M` containing `Gamma union {neg phi}`
  - By `prop_truth_lemma` with `canonicalValuation M`: all of `Gamma` is evaluated true, but `neg phi` is evaluated true, so `phi` is evaluated false
  - Instantiate `SemanticEntails` with `canonicalValuation M` to get contradiction
- [ ] Prove `prop_strong_completeness_iff`: `SemanticEntails Gamma phi <-> SetDerivable PropositionalAxiom Gamma phi`
- [ ] Prove `prop_compactness`: if every finite subset of `Gamma` is satisfiable, then `Gamma` is satisfiable
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness`
- [ ] Run `lake exe mk_all --module`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` -- new file (~120-160 lines)
- `Cslib.lean` -- updated by `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness` succeeds
- No sorry in the file
- `lake exe checkInitImports` passes

---

### Phase 5: Full CI Verification [NOT STARTED]

**Goal**: Run the complete CSLib CI verification pipeline to confirm all new files integrate cleanly with the existing codebase.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports` (verify all new files import Cslib.Init)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Verify no sorry remains: `grep -rn "sorry" Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean`
- [ ] Fix any lint or style issues identified

**Timing**: 0.5 hours

**Depends on**: 2, 3, 4

**Files to modify**:
- Potentially any of the 4 new files (lint/style fixes only)

**Verification**:
- All CI checks pass
- Zero sorry in new files
- `lake build` completes with no errors

## Testing & Validation

- [ ] `lake build` succeeds with all 4 new files
- [ ] `lake exe checkInitImports` passes for all new files
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] Zero sorry in any new file
- [ ] Weak completeness is recovered as special case: `SemanticEntails {} phi -> SetDerivable Axioms {} phi` reduces to existing `Tautology phi -> Derivable Axioms phi` via `SetDerivable_empty_iff`
- [ ] Compactness corollaries compile without additional axioms beyond what strong completeness already uses

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` -- shared definitions (~100-130 lines)
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` -- minimal strong completeness (~120-160 lines)
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` -- intuitionistic strong completeness (~140-180 lines)
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` -- classical strong completeness (~120-160 lines)
- Total estimated new code: 480-630 lines across 4 new files

## Rollback/Contingency

All changes are additive (4 new files, no modifications to existing files). Rollback is trivial: delete the 4 new files and revert `Cslib.lean` barrel import changes. No existing proofs are affected.

If any individual logic's strong completeness proof is blocked:
- Mark the specific phase [BLOCKED] with details
- The other logics' proofs are independent (Phases 2, 3, 4 can proceed in any order)
- The definitions phase (Phase 1) is never at risk since it contains only definitions and basic lemmas
