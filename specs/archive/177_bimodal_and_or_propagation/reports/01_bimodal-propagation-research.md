# Task 177: Bimodal And/Or Propagation -- Research Report

Session: sess_1781317385_e83d59_177

## 1. Executive Summary

This task propagates the hybrid five-primitive design to the Bimodal layer, adding native
`and` and `or` constructors to `Bimodal.Formula`. Currently the type has 6 constructors
`{atom, bot, imp, box, untl, snce}` with `and`/`or` as Lukasiewicz-derived `abbrev`s. The
target is 8 constructors `{atom, bot, imp, and, or, box, untl, snce}` with `neg`/`top`/
`diamond`/`someFuture`/`allFuture`/`somePast`/`allPast`/`always`/`sometimes` remaining derived.

The Bimodal layer spans **127 files** totaling ~51,200 lines across 12 subdirectories. This
is the largest propagation in the five-primitive design series (task 175 touched ~55 files,
task 176 ~37 files). The change is pervasive but structurally mechanical: every function or
proof that pattern-matches on `Formula Atom` constructors needs two new cases (`| .and`
and `| .or`), and every axiom/theorem constructor set needs 6 new entries.

### Key Structural Insight

Unlike Modal (task 175) where the `Satisfies` relation is the single truth function, Bimodal
has **three separate truth-evaluation functions** that need and/or cases:
1. `truthAt` in `Semantics/Truth.lean` (task-model semantics)
2. `intTruth` in `Metalogic/Separation/Defs.lean` (integer temporal semantics for separation)
3. `ExtFormula` operations in `Metalogic/ConservativeExtension/` (extended formula type with its own parallel constructors)

Additionally, the Decidability module has pattern-matching helpers (`asAnd?`, `asOr?`,
`asNeg?`) that currently decompose the Lukasiewicz encoding. With native constructors,
these become trivial direct matches, but the tableau rules that USE them need updating.

### Dependency on Tasks 175/176

The three Embedding files (`ModalEmbedding.lean`, `TemporalEmbedding.lean`,
`PropositionalEmbedding.lean`) depend on tasks 175 and 176 being completed first, since
they need to map the new `and`/`or` constructors from Modal/Temporal into Bimodal.
These files can be done last or in parallel with the rest.

## 2. Current Architecture

### 2.1 Formula Type (Syntax/Formula.lean, 210 lines)

```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi1 phi2 : Formula Atom)
  | box (phi : Formula Atom)
  | untl (phi1 phi2 : Formula Atom)
  | snce (phi1 phi2 : Formula Atom)
deriving DecidableEq, BEq
```

Derived connectives (abbrevs):
- `neg phi := .imp phi .bot`
- `top := .imp .bot .bot`
- `or phi1 phi2 := .imp (.imp phi1 .bot) phi2` (Lukasiewicz)
- `and phi1 phi2 := .imp (.imp phi1 (.imp phi2 .bot)) .bot` (Lukasiewicz)
- `diamond phi := .neg (.box (.neg phi))`
- `someFuture phi := .untl phi .top`
- `allFuture phi := .neg (.someFuture (.neg phi))`
- `somePast phi := .snce phi .top`
- `allPast phi := .neg (.somePast (.neg phi))`
- `always phi := .and (.allPast phi) (.and phi (.allFuture phi))`
- `sometimes phi := .neg (.always (.neg phi))`

Functions that match on Formula constructors in this file:
- `swapTemporal` (6 cases -> 8)
- `swapTemporal_involution` (6 cases -> 8)
- `swapTemporal_neg`, `swapTemporal_diamond` (trivial additions)
- `swapTemporal_someFuture/somePast/allFuture/allPast` (no change -- use derived)
- `atoms` (6 cases -> 8)
- `atoms_swapTemporal` (6 cases -> 8)
- `BimodalConnectives` instance (needs `conj`/`disj` fields if typeclass extended)

### 2.2 Axiom Type (ProofSystem/Axioms.lean, 314 lines)

Currently 42 constructors. Adding 6 new and/or axioms:
- `andI (phi psi)`: phi -> psi -> phi AND psi
- `andE1 (phi psi)`: phi AND psi -> phi
- `andE2 (phi psi)`: phi AND psi -> psi
- `orI1 (phi psi)`: phi -> phi OR psi
- `orI2 (phi psi)`: phi -> psi OR phi
- `orE (phi psi chi)`: (phi -> chi) -> (psi -> chi) -> phi OR psi -> chi

These follow the same pattern established by tasks 175 and 176.

`minFrameClass` needs 6 new `| _ => .Base` catch-all cases (and/or axioms are all Base).

### 2.3 Semantics -- Truth Evaluation (Semantics/Truth.lean, 651 lines)

`truthAt` currently has 6 cases. Adding:
```lean
| Formula.and phi psi => truthAt M Omega tau t phi /\ truthAt M Omega tau t psi
| Formula.or phi psi => truthAt M Omega tau t phi \/ truthAt M Omega tau t psi
```

The `time_shift_preserves_truth` theorem (lines 347-648) has 6 cases, each ~40-60 lines.
The and/or cases are straightforward (no temporal shifting involved for conjunctions).
`truth_double_shift_cancel` similarly needs 2 new cases.

### 2.4 Proof System Layer

| File | Lines | Changes Needed |
|------|-------|----------------|
| Derivation.lean | 168 | `height` function: +2 cases (but it doesn't match on formulas, only on DerivationTree constructors -- NO CHANGE needed) |
| Derivable.lean | 129 | NO CHANGE (wraps DerivationTree, doesn't match formulas) |
| Substitution.lean | 517 | `Formula.subst`: +2 cases. `subst_and`/`subst_or` simp lemmas become direct. `axiomSubst`: +6 cases. `swapTemporal_subst`: +2 cases. `derivationSubst`: NO CHANGE (matches on DerivationTree, not Formula). `subst_fresh_eq`: +2 cases. `subst_atoms`: +2 cases. |
| Instances.lean | 326 | +6 HasAxiom instances (AndI, AndE1, AndE2, OrI1, OrI2, OrE). ClassicalHilbert and BimodalTMHilbert instances auto-update. |
| LinearityDerivedFacts.lean | 78 | NO CHANGE (uses derived operators, no formula matching) |

### 2.5 Embedding Files

| File | Lines | Changes | Dependency |
|------|-------|---------|------------|
| ModalEmbedding.lean | 68 | `toBimodal`: +2 cases (`.and` -> `.and`, `.or` -> `.or`). +2 simp lemmas. | Task 175 |
| TemporalEmbedding.lean | 72 | `toBimodal`: +2 cases. +2 simp lemmas. | Task 176 |
| PropositionalEmbedding.lean | 105 | `toBimodal`: `.and`/`.or` cases change from Lukasiewicz to native. Commutation proofs become `simp`. | Tasks 175, 176 |

### 2.6 Syntax Layer

| File | Lines | Changes |
|------|-------|---------|
| Context.lean | 140 | NO CHANGE (uses List operations, no formula matching) |
| Subformulas.lean | 240 | `subformulas`: +2 cases. +2 membership lemmas per constructor. `subformulas_trans`: +2 cases. |
| SubformulaClosure.lean | 251 | `closure_and_left/right`, `closure_or_left/right`: +4 new closure lemmas. |
| SubformulaClosure/NestingDepth.lean | 134 | `fNestingDepth`: +2 cases (both return 0). `pNestingDepth`: +2 cases. `extractFutureInner`/`extractPastInner`: +2 cases (return none). `IsFutureFormula`/`IsPastFormula` instances: +2 match arms. |
| SubformulaClosure/TemporalFormulas.lean | 317 | `IsUntilFormula`/`IsSinceFormula` instances: +2 match arms each. `toUntilDeferral`/`toSinceDeferral`: +2 cases each (return bot). `f_nesting_depth_and/or`: +2 new simp lemmas. |

### 2.7 Semantics Layer (non-Truth)

| File | Lines | Changes |
|------|-------|---------|
| TaskFrame.lean | 192 | NO CHANGE (defines frame structure, no formula matching) |
| TaskModel.lean | 83 | NO CHANGE (defines model structure, no formula matching) |
| WorldHistory.lean | 309 | NO CHANGE (defines history structure, no formula matching) |
| Validity.lean | 275 | NO CHANGE (wraps truthAt, no formula matching) |

### 2.8 Theorems Layer

| File | Lines | Changes |
|------|-------|---------|
| Combinators.lean | 192 | NO CHANGE (uses derived operators via typeclass) |
| GeneralizedNecessitation.lean | 130 | NO CHANGE (no formula matching) |
| TemporalDerived.lean | 382 | NO CHANGE (no formula matching) |
| Perpetuity/Bridge.lean | 223 | NO CHANGE |
| Perpetuity/Helpers.lean | 134 | NO CHANGE |
| Perpetuity/Principles.lean | 204 | NO CHANGE |
| Propositional/Core.lean | 283 | `lce`/`rce` now use native and/or instead of Lukasiewicz encoding. May need adjustment but likely no change since `Formula.and` is still `abbrev` until conversion. |
| Propositional/Connectives.lean | 140 | NO CHANGE (delegates to Foundations via wrap/unwrap) |

### 2.9 FrameConditions Layer

| File | Lines | Changes |
|------|-------|---------|
| Compatibility.lean | 105 | NO CHANGE (no formula matching) |
| FrameClass.lean | 235 | NO CHANGE (defines frame class structures) |
| Soundness.lean | 116 | NO CHANGE (delegates to Metalogic.Soundness) |
| Validity.lean | 113 | NO CHANGE (wraps validity definitions) |

### 2.10 Metalogic/Core Layer

| File | Lines | Changes |
|------|-------|---------|
| Core.lean | 26 | NO CHANGE (barrel import) |
| DerivationTree.lean | 88 | NO CHANGE (wraps DerivationTree, no formula matching) |
| DeductionTheorem.lean | 233 | NO CHANGE (works with DerivationTree constructors, not Formula) |
| MaximalConsistent.lean | 218 | NO CHANGE (works with generic consistency, no formula matching) |
| MCSProperties.lean | 487 | May need `and_iff_mcs`/`or_iff_mcs` lemmas for native constructors. Currently these are proved via `imp_iff_mcs` since and/or are derived. With native constructors, new direct lemmas needed. |
| RestrictedMCS.lean | 436 | May need similar and/or closure lemmas. |

### 2.11 Metalogic/Soundness Layer

| File | Lines | Changes |
|------|-------|---------|
| Core.lean | 113 | `truth_at_swap_swap`: +2 cases (and/or trivial -- just recurse). |
| Soundness.lean | 839 | +6 axiom validity theorems (`andI_valid`, `andE1_valid`, `andE2_valid`, `orI1_valid`, `orI2_valid`, `orE_valid`). `axiom_valid` match: +6 cases. `soundness` theorem: NO CHANGE (induction on DerivationTree, not Formula). |
| FrameClassVariants.lean | 926 | `axiom_valid_dense`/`axiom_valid_discrete`: +6 cases each (delegate to base). |
| DenseValidity.lean | 1103 | NO CHANGE (proves density-specific axiom validity, independent of and/or). |
| DenseSoundness.lean | 35 | NO CHANGE. |
| DiscreteSoundness.lean | 31 | NO CHANGE. |

### 2.12 Metalogic/Completeness

| File | Lines | Changes |
|------|-------|---------|
| Completeness.lean | 482 | Truth lemma: +2 cases (and, or). These require `and_iff_mcs` and `or_iff_mcs` from MCSProperties. |

### 2.13 Metalogic/Bundle Layer

| File | Lines | Changes |
|------|-------|---------|
| Bundle.lean | 21 | NO CHANGE (barrel import) |
| BFMCS.lean | 130 | NO CHANGE (defines BFMCS, no formula matching) |
| CanonicalFrame.lean | 267 | NO CHANGE (defines canonical frame, no formula matching) |
| Construction.lean | 121 | NO CHANGE |
| FMCSDef.lean | 51 | NO CHANGE |
| FMCS.lean | 24 | NO CHANGE |
| ModalSaturation.lean | 200 | NO CHANGE (modal saturation, no formula matching) |
| SuccRelation.lean | 289 | NO CHANGE (successor relation, no formula matching) |
| TemporalCoherence.lean | 388 | NO CHANGE (temporal coherence, no formula matching) |
| TemporalContent.lean | 167 | NO CHANGE (temporal content, no formula matching) |
| UntilSinceCoherence.lean | 127 | NO CHANGE (USCoherence, no formula matching) |
| WitnessSeed.lean | 605 | NO CHANGE (witness seed construction) |

### 2.14 Metalogic/BXCanonical Layer

| File | Lines | Changes |
|------|-------|---------|
| BXCanonical.lean | 27 | NO CHANGE (barrel) |
| CanonicalChain.lean | 92 | NO CHANGE |
| CanonicalModel.lean | 768 | NO CHANGE (canonical model construction, no formula matching) |
| Frame.lean | 463 | NO CHANGE (frame construction, no formula matching) |
| OrderedSeedConsistency.lean | 150 | NO CHANGE |
| TruthLemma.lean | 222 | +2 cases in truth lemma induction (and, or). The and case uses MCS conjunction property, the or case uses MCS disjunction. |
| Completeness.lean | 24 | NO CHANGE (delegates to TruthLemma) |
| Completeness/Dense.lean | 132 | NO CHANGE |
| Filtration/DefectChain.lean | 99 | NO CHANGE |
| Chronicle/ChronicleTypes.lean | 385 | NO CHANGE (defines chronicle types) |
| Chronicle/ChronicleConstruction.lean | 1529 | NO CHANGE (chronicle construction, no formula matching) |
| Chronicle/ChronicleToCountermodelBasic.lean | 1174 | NO CHANGE |
| Chronicle/ChronicleToCountermodel.lean | 227 | NO CHANGE |
| Chronicle/CounterexampleElimination.lean | 3526 | NO CHANGE (elimination, no formula matching) |
| Chronicle/PointInsertion.lean | 3553 | NO CHANGE (point insertion, no formula matching) |
| Chronicle/RRelation.lean | 1692 | NO CHANGE |
| Quasimodel/Construction.lean | 665 | NO CHANGE |
| Quasimodel/HintikkaPoint.lean | 117 | NO CHANGE |
| Quasimodel/SubformulaClosure.lean | 98 | NO CHANGE |

### 2.15 Metalogic/Decidability Layer

| File | Lines | Changes |
|------|-------|---------|
| SignedFormula.lean | 849 | `Formula.hashFormula`: +2 cases. `Formula.complexity`: +2 cases. `unexpandedComplexity`: +2 cases. Branch filter functions that match on `.imp (.imp ...)` patterns for diamond/allFuture/allPast/someFuture/somePast: NO CHANGE (those match on derived operators which expand to imp/untl/snce). But `asAnd?`, `asOr?`: need updating to match native `.and`/`.or` constructors. |
| Tableau.lean | 1208 | `asAnd?`, `asOr?`, `asNeg?`: updated for native constructors. Tableau rules `andPos`/`andNeg`/`orPos`/`orNeg` already exist but need their `applyRule` implementations updated for native constructors. The `applyRule` function currently decomposes imp-based encodings; with native and/or, the rules become simpler. |
| AxiomMatcher.lean | 539 | `matchAxiom`: +6 patterns for new and/or axioms. |
| Closure.lean | 426 | NO CHANGE (uses Branch operations, no formula matching) |
| Correctness.lean | 148 | NO CHANGE |
| CountermodelExtraction.lean | 1082 | NO CHANGE (countermodel extraction, no formula matching) |
| DecisionProcedure.lean | 229 | NO CHANGE |
| ProofExtraction.lean | 371 | May need updates if proof extraction matches on formula structure. |
| Saturation.lean | 706 | NO CHANGE (saturation checks, uses Branch operations) |
| TraceCertificate.lean | 354 | NO CHANGE |
| FMP/ClosureMCS.lean | 295 | NO CHANGE |
| FMP/Filtration.lean | 302 | NO CHANGE (filtration, works with sets not formulas) |
| FMP/TruthPreservation.lean | 386 | `truthPreserved`: may need +2 cases if it matches on Formula. |
| FMP/FiniteModel.lean | 170 | NO CHANGE |
| FMP/FMP.lean | 187 | NO CHANGE |
| FMP/DenseFMP.lean | 73 | NO CHANGE |
| FMP/DiscreteFMP.lean | 73 | NO CHANGE |
| Decidability.lean (barrel) | 40 | NO CHANGE |
| FMP.lean (barrel) | 40 | NO CHANGE |

### 2.16 Metalogic/ConservativeExtension Layer

| File | Lines | Changes |
|------|-------|---------|
| ExtFormula.lean | 382 | `ExtFormula` inductive type: +2 constructors (`.and`, `.or`). `embedFormula`: +2 cases. `embedFormula_injective`: +2 cases. `fresh_not_in_embedFormula_atoms`: +2 cases. Various structural lemmas. |
| ExtDerivation.lean | 309 | `extAxiomSubst`: +6 cases for new axioms. `extDerivSubst`: likely NO CHANGE (matches on derivation tree). |
| Lifting.lean | 705 | `liftFormula`/`unliftFormula`: +2 cases each. Various lifting lemmas: +2 cases each. |
| Substitution.lean | 294 | `ExtFormula.subst`: +2 cases. Various subst lemmas: +2 cases. |

### 2.17 Metalogic/Separation Layer

| File | Lines | Changes |
|------|-------|---------|
| Defs.lean | 632 | `intTruth`: +2 cases (and, or). `isUFree`/`isSFree`: +2 cases each. `isSyntacticallySeparated`: +2 cases. `junctionDepth`/`U_depth_under_S`/`countUSubformulas`: +2 cases each. Various predicates matching on Formula: +2 cases. |
| FormulaOps.lean | 274 | `substFormula`: +2 cases. `subst_correctness`: +2 cases in induction. |
| Distributivity.lean | 174 | May need +2 cases if matching on Formula. |
| Eliminations.lean | 855 | Various formula decomposition functions. |
| DualEliminations.lean | 116 | Similar formula decomposition. |
| Duality.lean | 417 | `swapTemporalInt`: +2 cases. Duality lemmas: +2 cases. |
| NegationEquiv.lean | 179 | May need updates for and/or negation equivalences. |
| NormalForm.lean | 373 | `u_free_s_free_separated`: +2 cases in induction. |
| SeparationThm.lean | 391 | Main separation theorem induction: +2 cases. |
| TemporalClosure.lean | 525 | Various closure operations. |
| IntHelpers.lean | 172 | NO CHANGE (integer arithmetic helpers). |
| Separation.lean (barrel) | - | NO CHANGE. |
| DedekindZ/Cases.lean | 1660 | NO CHANGE (specific case analysis for DedekindZ). |
| DedekindZ/QLemma.lean | 440 | NO CHANGE. |
| Hierarchy/HierarchyDefs.lean | 988 | `hierJunctionDepth` and related: +2 cases. |
| Hierarchy/HierarchyInduction.lean | 1455 | Main induction: +2 cases. |
| Hierarchy/HierarchyCaseSep.lean | 613 | Specific case: possibly +2 cases. |
| Hierarchy/HierarchyCompletion.lean | 999 | Completion argument: possibly +2 cases. |

### 2.18 Metalogic/Algebraic Layer

| File | Lines | Changes |
|------|-------|---------|
| Algebraic.lean | 19 | NO CHANGE (barrel). |
| LindenbaumQuotient.lean | 290 | `Derives` may need and/or characterization. |
| BooleanStructure.lean | 341 | `sup`/`inf` operations: may become direct with native and/or. |
| InteriorOperators.lean | 177 | NO CHANGE (defines operators, no formula matching). |
| UltrafilterMCS.lean | 660 | May need and/or membership lemmas. |
| ParametricCanonical.lean | 155 | NO CHANGE. |
| ParametricCompleteness.lean | 144 | NO CHANGE. |
| ParametricHistory.lean | 116 | NO CHANGE. |
| ParametricTruthLemma.lean | 311 | +2 cases in truth lemma induction. |
| RestrictedParametricTruthLemma.lean | 322 | +2 cases in truth lemma induction. |

## 3. File Impact Classification

### 3.1 Files Requiring Changes (estimated 60-70 files)

**High Impact (core constructor changes, many new cases):**
1. `Syntax/Formula.lean` -- new constructors, swap, atoms
2. `ProofSystem/Axioms.lean` -- 6 new axiom constructors, minFrameClass
3. `ProofSystem/Substitution.lean` -- subst function + axiomSubst (48->54 cases)
4. `ProofSystem/Instances.lean` -- 6 new HasAxiom instances
5. `Semantics/Truth.lean` -- truthAt + all time-shift proofs (~300 lines added)
6. `Metalogic/Soundness/Soundness.lean` -- 6 axiom validity + axiom_valid match
7. `Metalogic/Soundness/FrameClassVariants.lean` -- +12 cases (2 frame classes x 6 axioms)
8. `Metalogic/Decidability/Tableau.lean` -- applyRule native and/or handling
9. `Metalogic/Decidability/AxiomMatcher.lean` -- +6 axiom patterns
10. `Metalogic/Decidability/SignedFormula.lean` -- hash, complexity, unexpanded
11. `Metalogic/Separation/Defs.lean` -- intTruth + all predicates
12. `Metalogic/ConservativeExtension/ExtFormula.lean` -- ExtFormula type + operations

**Medium Impact (2-8 new match cases):**
13. `Syntax/Subformulas.lean` -- subformulas + membership lemmas
14. `Syntax/SubformulaClosure.lean` -- closure lemmas
15. `Syntax/SubformulaClosure/NestingDepth.lean` -- nesting depth functions
16. `Syntax/SubformulaClosure/TemporalFormulas.lean` -- predicate instances
17. `Metalogic/Soundness/Core.lean` -- truth_at_swap_swap
18. `Metalogic/Core/MCSProperties.lean` -- and/or MCS lemmas
19. `Metalogic/Completeness.lean` -- truth lemma +2 cases
20. `Metalogic/BXCanonical/TruthLemma.lean` -- truth lemma +2 cases
21. `Metalogic/ConservativeExtension/Lifting.lean` -- lift/unlift +2 cases
22. `Metalogic/ConservativeExtension/ExtDerivation.lean` -- +6 axiom cases
23. `Metalogic/ConservativeExtension/Substitution.lean` -- +2 cases
24. `Metalogic/Separation/FormulaOps.lean` -- substFormula +2 cases
25. `Metalogic/Separation/Duality.lean` -- swapTemporalInt +2 cases
26. `Metalogic/Separation/NormalForm.lean` -- induction +2 cases
27. `Metalogic/Separation/SeparationThm.lean` -- main theorem +2 cases
28. `Metalogic/Separation/Hierarchy/HierarchyDefs.lean` -- depth functions
29. `Metalogic/Separation/Hierarchy/HierarchyInduction.lean` -- induction
30. `Metalogic/Algebraic/ParametricTruthLemma.lean` -- truth lemma +2 cases
31. `Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` -- +2 cases
32. `Embedding/ModalEmbedding.lean` -- +2 cases + lemmas
33. `Embedding/TemporalEmbedding.lean` -- +2 cases + lemmas
34. `Embedding/PropositionalEmbedding.lean` -- update encoding

**Low Impact (1-2 new match arms, or conditional):**
35. `Metalogic/Core/RestrictedMCS.lean` -- possible closure lemmas
36. `Metalogic/Separation/Eliminations.lean` -- possible formula decomposition
37. `Metalogic/Separation/DualEliminations.lean` -- possible
38. `Metalogic/Separation/NegationEquiv.lean` -- possible
39. `Metalogic/Separation/TemporalClosure.lean` -- possible
40. `Metalogic/Separation/Distributivity.lean` -- possible
41. `Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean` -- possible
42. `Metalogic/Separation/Hierarchy/HierarchyCompletion.lean` -- possible
43. `Metalogic/Algebraic/LindenbaumQuotient.lean` -- possible
44. `Metalogic/Algebraic/BooleanStructure.lean` -- possible
45. `Metalogic/Algebraic/UltrafilterMCS.lean` -- possible
46. `Metalogic/Decidability/ProofExtraction.lean` -- possible
47. `Metalogic/Decidability/FMP/TruthPreservation.lean` -- possible
48. `Theorems/Propositional/Core.lean` -- possible (lce/rce)

### 3.2 Files NOT Requiring Changes (estimated 57-67 files)

Files that do not pattern-match on Formula constructors, or only use derived
operators via the typeclass interface:
- All of `Metalogic/Bundle/` (12 files) -- works with MCS sets, not formula structure
- Most of `Metalogic/BXCanonical/Chronicle/` (7 files) -- chronicle construction
- Most of `Metalogic/BXCanonical/Quasimodel/` (3 files)
- `Metalogic/BXCanonical/CanonicalModel.lean`, `Frame.lean`, `OrderedSeedConsistency.lean`
- `Metalogic/Decidability/Closure.lean`, `Correctness.lean`, `CountermodelExtraction.lean`,
  `DecisionProcedure.lean`, `Saturation.lean`, `TraceCertificate.lean`
- Most `FMP/` files (6 files)
- All `FrameConditions/` files (4 files)
- `Semantics/TaskFrame.lean`, `TaskModel.lean`, `WorldHistory.lean`, `Validity.lean`
- `Syntax/Context.lean`
- `Theorems/` (7 files) -- use typeclass interface
- `ProofSystem/Derivation.lean`, `Derivable.lean`, `LinearityDerivedFacts.lean`
- `Metalogic/Core/DerivationTree.lean`, `DeductionTheorem.lean`, `MaximalConsistent.lean`
- `Metalogic/Core.lean`, `Metalogic/Separation.lean` (barrels)
- `Metalogic/Soundness/Dense*.lean`, `DiscreteSoundness.lean`
- `Metalogic/Separation/IntHelpers.lean`, `DedekindZ/` (2 files)

## 4. Change Patterns

### 4.1 Pattern A: Formula Match Extension

Every function/proof doing `induction phi with | atom | bot | imp | box | untl | snce`
needs two new cases:

```lean
-- New cases for and/or
| and phi psi ih_phi ih_psi =>
  -- typically: recurse on both subformulas
| or phi psi ih_phi ih_psi =>
  -- typically: recurse on both subformulas
```

For `and`, the pattern is always conjunction/pair of recursive results.
For `or`, the pattern is always disjunction/either of recursive results.

### 4.2 Pattern B: Axiom Extension

Add 6 new constructors to `Axiom`, 6 validity proofs in Soundness, 6 cases in
axiomSubst, 6 patterns in matchAxiom, 6 HasAxiom instances. All and/or axioms
are Base frame class.

### 4.3 Pattern C: Truth Evaluation Extension

`truthAt`, `intTruth` get direct structural clauses:
- `| .and phi psi => truthAt ... phi /\ truthAt ... psi`
- `| .or phi psi => truthAt ... phi \/ truthAt ... psi`

### 4.4 Pattern D: Subformula Closure Extension

`subformulas`, `subformulaClosure`, `closureWithNeg` gain and/or cases following
the same binary-connective pattern as `imp`:
```lean
| phi@(.and psi chi) => phi :: (subformulas psi ++ subformulas chi)
| phi@(.or psi chi) => phi :: (subformulas psi ++ subformulas chi)
```

### 4.5 Pattern E: Decidability Helpers

`asAnd?` and `asOr?` change from Lukasiewicz pattern matching to direct:
```lean
-- Before:
def asAnd? : Formula Atom -> Option (Formula Atom x Formula Atom)
  | .imp (.imp phi (.imp psi .bot)) .bot => some (phi, psi)
  | _ => none

-- After:
def asAnd? : Formula Atom -> Option (Formula Atom x Formula Atom)
  | .and phi psi => some (phi, psi)
  | _ => none
```

### 4.6 Pattern F: abbrev-to-Constructor Transition

`Formula.and` and `Formula.or` change from `abbrev` to being the actual constructors.
The old Lukasiewicz encoding becomes a derived equivalence theorem:
```lean
theorem and_eq_lukasiewicz : phi.and psi = .imp (.imp phi (.imp psi .bot)) .bot
```
This theorem is NOT needed if code is properly updated, but may help during transition.

## 5. Estimated Scale

| Category | Files Changed | Lines Added | Lines Modified |
|----------|--------------|-------------|----------------|
| Syntax | 6 | ~150 | ~60 |
| Semantics | 1 | ~100 | ~20 |
| ProofSystem | 3 | ~200 | ~80 |
| Embedding | 3 | ~40 | ~30 |
| Soundness | 3 | ~120 | ~40 |
| Completeness/TruthLemma | 3 | ~80 | ~20 |
| Core/MCS | 2 | ~60 | ~20 |
| Decidability | 4 | ~120 | ~100 |
| ConservativeExtension | 4 | ~160 | ~80 |
| Separation | 8-12 | ~200 | ~100 |
| Algebraic | 3 | ~60 | ~20 |
| **Total** | **~45-55** | **~1,290** | **~570** |

**Grand total change estimate**: ~1,860 lines changed/added across ~50 files.

Note: The initial task description estimated ~130 files, but careful analysis shows that
roughly 60-70 of the 127 files do NOT pattern-match on Formula constructors and need no
changes. The actual file count requiring changes is closer to 50-60.

## 6. Recommended Phase Structure

Given the scope (~50 files, ~1,860 lines), and that each phase should target ~100-500 lines
of output, I recommend **8 phases**:

### Phase 1: Core Formula + Syntax Layer (8 files, ~210 lines)
- `Syntax/Formula.lean` -- add constructors, update swapTemporal, atoms, BimodalConnectives
- `Syntax/Context.lean` -- verify no changes needed
- `Syntax/Subformulas.lean` -- add subformula cases + membership lemmas
- `Syntax/SubformulaClosure.lean` -- add closure membership lemmas
- `Syntax/SubformulaClosure/NestingDepth.lean` -- nesting depth cases
- `Syntax/SubformulaClosure/TemporalFormulas.lean` -- predicate instances, deferral cases
- Build verification: `lake build Cslib.Logics.Bimodal.Syntax.SubformulaClosure.TemporalFormulas`

### Phase 2: ProofSystem Layer (4 files, ~300 lines)
- `ProofSystem/Axioms.lean` -- 6 new axiom constructors + minFrameClass
- `ProofSystem/Substitution.lean` -- Formula.subst + axiomSubst (6 new cases) + derived lemmas
- `ProofSystem/Instances.lean` -- 6 new HasAxiom instances
- `ProofSystem/LinearityDerivedFacts.lean` -- verify no changes
- Build verification: `lake build Cslib.Logics.Bimodal.ProofSystem.Instances`

### Phase 3: Semantics + Soundness (4 files, ~320 lines)
- `Semantics/Truth.lean` -- truthAt cases + time-shift preservation proofs
- `Metalogic/Soundness/Core.lean` -- truth_at_swap_swap
- `Metalogic/Soundness/Soundness.lean` -- 6 axiom validity theorems + axiom_valid
- `Metalogic/Soundness/FrameClassVariants.lean` -- dense/discrete axiom_valid cases
- Build verification: `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness`

### Phase 4: Core Metalogic + Completeness (5 files, ~200 lines)
- `Metalogic/Core/MCSProperties.lean` -- and/or MCS lemmas
- `Metalogic/Core/RestrictedMCS.lean` -- and/or closure (if needed)
- `Metalogic/Completeness.lean` -- truth lemma and/or cases
- `Metalogic/BXCanonical/TruthLemma.lean` -- truth lemma and/or cases
- `Metalogic/Algebraic/ParametricTruthLemma.lean` -- and/or cases
- Build verification: `lake build Cslib.Logics.Bimodal.Metalogic.Completeness`

### Phase 5: ConservativeExtension (4 files, ~240 lines)
- `Metalogic/ConservativeExtension/ExtFormula.lean` -- ExtFormula +2 constructors + all ops
- `Metalogic/ConservativeExtension/ExtDerivation.lean` -- +6 axiom cases
- `Metalogic/ConservativeExtension/Lifting.lean` -- lift/unlift +2 cases each
- `Metalogic/ConservativeExtension/Substitution.lean` -- subst +2 cases
- Build verification: `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Lifting`

### Phase 6: Separation Layer (10-14 files, ~400 lines)
- `Metalogic/Separation/Defs.lean` -- intTruth + all predicates
- `Metalogic/Separation/FormulaOps.lean` -- substFormula + correctness
- `Metalogic/Separation/Duality.lean` -- swapTemporalInt
- `Metalogic/Separation/NegationEquiv.lean` -- negation cases
- `Metalogic/Separation/Eliminations.lean` -- formula decomposition
- `Metalogic/Separation/DualEliminations.lean`
- `Metalogic/Separation/Distributivity.lean`
- `Metalogic/Separation/NormalForm.lean`
- `Metalogic/Separation/SeparationThm.lean`
- `Metalogic/Separation/TemporalClosure.lean`
- `Metalogic/Separation/Hierarchy/HierarchyDefs.lean`
- `Metalogic/Separation/Hierarchy/HierarchyInduction.lean`
- `Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean`
- `Metalogic/Separation/Hierarchy/HierarchyCompletion.lean`
- Build verification: `lake build Cslib.Logics.Bimodal.Metalogic.Separation.SeparationThm`

### Phase 7: Decidability Layer (5 files, ~250 lines)
- `Metalogic/Decidability/SignedFormula.lean` -- hash, complexity, helpers
- `Metalogic/Decidability/Tableau.lean` -- asAnd?/asOr? + applyRule
- `Metalogic/Decidability/AxiomMatcher.lean` -- +6 axiom patterns
- `Metalogic/Decidability/ProofExtraction.lean` -- possible updates
- `Metalogic/Decidability/FMP/TruthPreservation.lean` -- possible +2 cases
- Build verification: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Closure`

### Phase 8: Embeddings + Algebraic + Final CI (8 files, ~200 lines)
- `Embedding/ModalEmbedding.lean` -- +2 cases + lemmas (DEPENDS ON TASK 175)
- `Embedding/TemporalEmbedding.lean` -- +2 cases + lemmas (DEPENDS ON TASK 176)
- `Embedding/PropositionalEmbedding.lean` -- update encoding (DEPENDS ON 175+176)
- `Metalogic/Algebraic/LindenbaumQuotient.lean` -- possible
- `Metalogic/Algebraic/BooleanStructure.lean` -- possible
- `Metalogic/Algebraic/UltrafilterMCS.lean` -- possible
- `Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` -- +2 cases
- Full CI: `lake build && lake test && lake exe checkInitImports && lake exe lint-style`

## 7. Risk Assessment

### 7.1 Low Risk
- Adding constructors and trivial match cases (Patterns A, C, D): purely mechanical
- Axiom extension (Pattern B): well-established pattern from tasks 175/176

### 7.2 Medium Risk
- **Separation layer (Phase 6)**: The separation proof is complex (10,263 lines across 17 files).
  The `isSyntacticallySeparated` predicate currently does NOT have and/or cases because
  and/or are not primitive. Adding native and/or means the separation induction must handle
  these cases. However, since and/or are propositionally definable from imp+bot, the
  separation induction should treat them as syntactic sugar that can be eliminated before
  the main induction. The `isUFree`/`isSFree` predicates need simple recursive cases
  (and/or are both U-free and S-free if their components are).

- **ConservativeExtension (Phase 5)**: The `ExtFormula` type mirrors `Formula` with its own
  parallel definitions. Adding and/or to both requires synchronized changes. Risk is moderate
  because the files are self-contained.

### 7.3 High Risk
- **Decidability tableau (Phase 7)**: The `asAnd?` and `asOr?` helpers currently pattern-match
  on the Lukasiewicz imp-encoding. Changing to native constructors fundamentally changes how
  the tableau decomposes formulas. The tableau rules `andPos`/`andNeg`/`orPos`/`orNeg` are
  already defined conceptually but their implementations in `applyRule` use the old encoding.
  Careful attention needed to ensure the `allFuturePosFormulas`, `someFutureNegFormulas` etc.
  don't accidentally match on the new constructors.

### 7.4 Embedding Dependency
Phase 8 (Embeddings) strictly depends on tasks 175 (Modal) and 176 (Temporal) being complete.
If either is incomplete, Phase 8 should be deferred. The embedding files are small (~245 lines
total) and can be done as a separate follow-up.

## 8. Tactic Survey Results

For the and/or cases being added, the following tactic patterns apply:

| Proof Pattern | Recommended Tactic |
|--------------|-------------------|
| truthAt and case | `constructor <;> exact ih ...` or `simp only [truthAt]; exact And.intro ...` |
| truthAt or case | `rcases h with h1 \| h2` / `exact Or.inl ...` or `exact Or.inr ...` |
| axiom validity (andI) | `intro h1 h2; exact And.intro h1 h2` |
| axiom validity (andE1) | `exact And.left` |
| axiom validity (orE) | Classical `by_contra` + `Or.elim` |
| subformulas membership | `simp [subformulas, List.mem_cons, List.mem_append]` |
| swapTemporal | `simp only [swapTemporal, ih1, ih2]` |
| time_shift_preserves_truth | Follow imp case pattern: `constructor <;> intro ...` |

## 9. Reuse Check Results

### 9.1 BimodalConnectives Typeclass

The `BimodalConnectives` instance (Formula.lean:106-111) currently registers:
```lean
instance : BimodalConnectives (Formula Atom) where
  bot := .bot; imp := .imp; box := .box; untl := .untl; snce := .snce
```

If `BimodalConnectives` gains `conj`/`disj` fields (from Foundation changes), the instance
needs extension. Check if this was done in the Foundations for task 173.

### 9.2 Existing and/or Infrastructure

The existing `Formula.and` and `Formula.or` `abbrev`s (lines 53-59) will be REPLACED by
the new constructors. All `simp` lemmas, theorems, and notation that reference these abbrevs
will automatically resolve to the constructors instead.

### 9.3 Foundations HasAxiom Typeclasses

The `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`,
`HasAxiomOrE` typeclasses need to exist in `Cslib.Foundations.Logic.ProofSystem` before
the Bimodal Instances file can register them. Verify these were added by task 173/174.
