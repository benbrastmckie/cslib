---
next_project_number: 191
---

# TODO

## Task Order

*Updated 2026-06-14. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,179,180 | -- | Bimodal Porting |
| 2 | 39,40,181 | 36,37,179,180 | Temporal Logic |
| 3 | 41 | 39,40 | Foundations |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Temporal Logic

39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Uncategorized

179 [NOT STARTED] — Add diamond (dia) as a primitive constructor to Modal.Proposition
  └─ 181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 
180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
  └─ 181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors  (see above)

## Tasks

### 190. Review propositional pr readiness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional PRs
- **Dependencies**: None
- **Research**: [190_review_propositional_pr_readiness/reports/01_team-research.md]
- **Plan**: [190_review_propositional_pr_readiness/plans/01_pr-readiness-fixes.md]
- **Summary**: [190_review_propositional_pr_readiness/summaries/01_pr-readiness-summary.md]

---

### 189. Rename completeness to canonical model
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [189_rename_completeness_to_canonical_model/reports/01_team-research.md]
- **Plan**: [189_rename_completeness_to_canonical_model/plans/01_implementation-plan.md]

**Description**: Reorganize the completeness file structure by eliminating the three legacy weak completeness files entirely. Move the canonical model infrastructure (canonicalValuation, prop_truth_lemma, IntCanonicalWorld, int_truth_lemma, MinCanonicalWorld, min_truth_lemma) into the corresponding strong completeness files (StrongCompleteness.lean, IntStrongCompleteness.lean, MinStrongCompleteness.lean) so each logic has a single self-contained completeness file containing: canonical model construction, truth lemma, strong soundness, strong completeness, weak completeness corollary, and compactness corollary. Delete Completeness.lean, IntCompleteness.lean, and MinCompleteness.lean after merging. Update all imports across the project (including Modal/Temporal/Bimodal conservative extension files), update Cslib.lean barrel file, and ensure lake build passes.

---

### 188. First propositional upstream pr
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [188_first_propositional_upstream_pr/reports/01_team-research.md]
- **Plan**: [188_first_propositional_upstream_pr/plans/01_implementation-plan.md]
- **Summary**: [188_first_propositional_upstream_pr/summaries/01_execution-summary.md]

**Description**: Design and prepare a first upstream PR (~300 LOC) contributing propositional logic foundations to CSLib. Study what upstream CSLib currently includes to identify gaps. The PR should set the foundation for eventually contributing: (1) completeness results for all three propositional Hilbert systems (minimal, intuitionistic, classical), and (2) the extensional equivalence between Hilbert and natural deduction systems. Select a self-contained ~300 LOC slice from Foundations/ and Propositional/ that gives reviewers something easy to take in — likely the core Proposition type, axiom schemata, derivation tree, and basic metatheorems — while building towards the larger contribution. Must study upstream repo structure, existing PRs, and reviewer expectations to scope appropriately.

---

### 187. Propositional foundations quality fixes
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 185
- **Research**: [187_propositional_foundations_quality_fixes/reports/01_fix-verification.md]
- **Plan**: [187_propositional_foundations_quality_fixes/plans/01_implementation-plan.md]

**Description**: Fix all issues identified in the task 185 quality audit. Prioritized list: HIGH: (1) Remove unused public import Std.Tactic.BVDecide.Normalize from DerivedRules.lean and SemanticConsequence.lean; (2) Fix 14 files using bare CZ abbreviation — replace with proper [ChagrovZakharyaschev1997] BibKey format for doc-gen cross-linking; (3) Add literature citations to Lindenbaum lemma (set_lindenbaum) and deduction theorem (deductionTheorem); (4) Fix lake shake import hygiene — move IntSoundness/MinSoundness imports from Completeness to StrongCompleteness files. MEDIUM: (5) Decompose 241-line prop_truth_lemma in Completeness.lean into 6 helper lemmas (one per connective direction); (6) Add van Dalen 2013 and Fitting 1969 to references.bib; (7) Add References sections to 5 files lacking them (MCS.lean, Axioms.lean, Derivation.lean, Consistency.lean, DeductionHelpers.lean); (8) Fix naming convention violations — rename soundness_tautology to prop_soundness_tautology, completeness_iff_tautology to prop_completeness_iff_tautology; (9) Extract duplicated private h_implyK/h_implyS helpers from 4 files into ProofSystem/Axioms.lean; (10) Change public import Cslib.Init to private import in Defs.lean. LOW: (11) Rename misleading lem theorem; (12) Replace 3 instances of bare simp with simp only; (13) Add missing @[simp] attributes where appropriate; (14) Fix stale docstring axiom count.

---

### 186. Hilbert nd equivalence refactor
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 185
- **Research**: [186_hilbert_nd_equivalence_refactor/reports/01_nd-equivalence-research.md]
- **Plan**: [186_hilbert_nd_equivalence_refactor/plans/01_implementation-plan.md]
- **Summary**: [186_hilbert_nd_equivalence_refactor/summaries/01_execution-summary.md]

**Description**: Refactor the Hilbert / natural deduction extensional equivalence in Cslib/Logics/Propositional/NaturalDeduction/ to the highest standards of quality and elegance. Current gaps: (1) no minimal logic instantiation (hilbert_iff_nd_min) — the generic theorem requires EFQ which MinPropAxiom lacks, so either a separate EFQ-free version or an adapted ND system is needed; (2) equivalence is only for closed derivability (empty context Derivable ↔ DerivableIn ∅) — extend to full context-based equivalence (Deriv Axioms Γ φ ↔ NDDeriv Theory Γ φ) for the stronger result; (3) review proof style in ndToHilbert and hilbertToND for clarity and decomposition; (4) ensure all three systems (minimal, intuitionistic, classical) have clean corollary instantiations; (5) add proper literature references for the equivalence result (Prawitz 1965, Troelstra & van Dalen 1988); (6) review naming conventions and docstrings against Mathlib standards.

---

### 185. Propositional foundations quality audit
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 183, Task 184
- **Research**:
  - [185_propositional_foundations_quality_audit/reports/01_team-research.md]
  - [185_propositional_foundations_quality_audit/reports/01_teammate-a-findings.md]
  - [185_propositional_foundations_quality_audit/reports/01_teammate-b-findings.md]
  - [185_propositional_foundations_quality_audit/reports/01_teammate-c-findings.md]
- **Plan**: [185_propositional_foundations_quality_audit/plans/01_implementation-plan.md]
- **Summary**: [185_propositional_foundations_quality_audit/summaries/01_execution-summary.md]

**Description**: Rigorous quality audit of Cslib/Logics/Propositional/ and its Cslib/Foundations/Logic/ dependencies. Survey architecture, organization, proof quality, literature references, docstrings, notation, and naming conventions against CSLib contribution standards and mathematical best practices. Identify improvements to: (1) file organization and module structure, (2) proof style and tactic usage (prefer term-mode where natural, eliminate unnecessary classical reasoning in constructive proofs), (3) BibTeX references in references.bib for all key theorems citing standard sources (CZ, Blackburn et al., Chagrov & Zakharyaschev, etc.), (4) module-level docstrings following Mathlib conventions, (5) notation consistency (scoped notation, typeclass-backed operators), (6) naming conventions (Mathlib snake_case, descriptive theorem names), (7) import hygiene (minimal imports, no transitive leakage), (8) redundant or duplicated lemmas across files. Produce a prioritized improvement plan with concrete file-level recommendations, ensuring long-term maintainability and contribution readiness.

---

### 181. Bimodal primitive dia always historically
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: Task 179, Task 180
- **Research**: [181_bimodal_primitive_dia_always_historically/reports/01_bimodal-primitive-expansion-research.md]

**Description**: Propagate primitive diamond, allFuture, and allPast constructors to the Bimodal layer, giving {atom, bot, imp, and, or, box, dia, untl, snce, allFuture, allPast} (11 primitives). This is the union of Modal (task 179) and Temporal (task 180) primitive sets. Scope: (1) Syntax/Formula.lean: add .dia/.allFuture/.allPast constructors, update all match cases. (2) Semantics/Truth.lean: structural truthAt clauses. (3) ProofSystem: axiom constructors for diamond duality and G/H axioms. (4) Embedding: extend ModalEmbedding (.dia), TemporalEmbedding (.allFuture/.allPast). (5) Metalogic: propagate through ~50 files (Core, Soundness, Completeness, BXCanonical, ConservativeExtension, Separation, Decidability, Algebraic). Follow task 177 playbook. (6) Classical equivalences become theorems. Verify full CI. Estimated ~50 files, ~2000 lines, similar scope to task 177.

---

### 180. Temporal primitive always historically
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: Task 176
- **Research**: [180_temporal_primitive_always_historically/reports/01_primitive-always-historically-research.md]

**Description**: Add allFuture (G) and allPast (H) as primitive constructors to Temporal.Formula, giving {atom, bot, imp, and, or, untl, snce, allFuture, allPast}. Currently G is derived as neg(someFuture(neg phi)) and H as neg(somePast(neg phi)), which are only valid classically. Making them primitive enables intuitionistic temporal logics. Note: someFuture (F) and somePast (P) remain derivable without negation (F = top U phi, P = top S phi). Scope: (1) Syntax/Formula.lean: add .allFuture/.allPast constructors, update complexity, subst, atoms, encodeNat, temporalDepth, swapTemporal. (2) Semantics: structural clauses for universal future/past quantification. (3) ProofSystem: temporal axioms referencing G/H now use primitive constructors. (4) Metalogic: cases in Soundness, Chronicle/TruthLemma, MCS, Completeness. (5) Classical equivalences become theorems. Verify full CI. Reference: Boudou et al. for intuitionistic temporal logic.

---

### 179. Modal primitive diamond
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: Task 175
- **Research**: [179_modal_primitive_diamond/reports/01_primitive-diamond-research.md]

**Description**: Add diamond (dia) as a primitive constructor to Modal.Proposition, giving {atom, bot, imp, and, or, box, dia}. Currently diamond is derived as neg(box(neg phi)), which is only valid classically. Making it primitive enables intuitionistic and minimal modal logics where box and diamond are independent operators. Scope: (1) Basic.lean: add .dia constructor, structural Satisfies clause, keep notation. (2) Denotation, LogicalEquivalence, Cube: .dia cases. (3) ProofSystem/Instances: diamond-related axiom constructors and dual axioms. (4) Metalogic: .dia cases in DerivationTree, truth lemmas, all 15 soundness/completeness files. (5) Classical equivalence dia(A) iff neg(box(neg(A))) becomes a theorem. Verify full CI. Reference: upstream CSLib uses diamond as primitive; Fischer Servi 1984, Simpson 1994 for intuitionistic modal logic.

---

### 171. Research connective basis min int classical
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [171_research_connective_basis_min_int_classical/reports/01_team-research.md]
- **Plan**: [171_research_connective_basis_min_int_classical/plans/01_implementation-plan.md]
- **Summary**: [171_research_connective_basis_min_int_classical/summaries/01_execution-summary.md]

**Description**: Research connective-basis design for minimal, intuitionistic, and classical propositional logic in CSLib: rigorously ground in literature (Gentzen 1935, Prawitz 1965, Troelstra & van Dalen 1988, Heyting 1930, Church 1956, Chagrov & Zakharyaschev 1997, Johansson 1937) whether {imp, bot} primitives with derived neg/top/and/or is adequate — addressing ctchou's objection on PR #635 that {imp, bot} is functionally complete only classically (intuitionistically, and/or are NOT definable), and his challenge that Gentzen/Prawitz/T&vD do not actually use this basis or the 10-to-5 natural deduction rule reduction. Determine the truth of these claims and design a formula type + proof system architecture that supports minimal, intuitionistic, and classical logics naturally and elegantly (e.g., full primitive connective set {bot, atom, imp, and, or} with logics distinguished by inference rules: minimal = no ex falso, intuitionistic = + ex falso, classical = + DNE/Peirce). Also reconcile with maintainer fmontesi's competing PR #607 typeclass approach (Operators/ files, notation-level classes over unchanged primitive constructors) and eric-wieser's suggestion to co-opt Mathlib's Bot/HImp classes. Verify all citations against references.bib and primary sources.

---

### 41. Abstract completeness infrastructure
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Foundations
- **Dependencies**: Task 38, Task 39, Task 40

**Description**: Abstract shared completeness infrastructure between temporal and bimodal logic once concrete completeness proofs are finished for both.

The temporal (tasks 31, 38, 39) and bimodal (tasks 34, 35) completeness proofs share structural patterns that can be factored into a generic completeness scaffold in Cslib/Foundations/Logic/Metalogic/, extending the existing generic MCS framework (Task 29).

Candidate abstractions (to be confirmed once concrete implementations exist):
1. Generic neg_consistent_of_not_derivable: if φ is not derivable then {¬φ} is consistent — identical structure in both logics, parameterized over DerivationSystem
2. Generic completeness contrapositive skeleton: not derivable → consistent → Lindenbaum → MCS → canonical model → countermodel — the overall proof shape is shared
3. Dense/discrete case split pattern: the three-way case split on □(F'T) / □(U(T,⊥)) / mixed is structurally similar (temporal uses G/H instead of □)
4. Canonical order construction patterns: both define canonical_lt via G-sets (temporal) or box-sets (bimodal); the linearity/irreflexivity/transitivity proofs follow parallel structures
5. Dense indicator elimination: both dense completeness proofs eliminate the non-dense branch by showing the dense indicator axiom is a theorem — identical pattern

Scope: Identify which abstractions yield genuine code savings vs. premature generalization, implement those that do, and refactor both temporal and bimodal completeness to use the shared infrastructure.

Target: Cslib/Foundations/Logic/Metalogic/Completeness.lean (or similar)
Depends on: Tasks 35 (dense bimodal), 38 (dense temporal), 39 (discrete temporal) — transitively includes 31 (base temporal) and 34 (base bimodal MCS)

---

### 40. Temporal continuous completeness
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 37

**Description**: Continuous temporal completeness: completeness for temporal logic over Dedekind-complete (continuous) linear orders, e.g. the reals.

Scope: Define a Continuous frame class extending Dense, add any required axioms (e.g., Dedekind completeness schema or equivalent), prove soundness over conditionally complete linear orders, prove completeness via canonical model on Real or equivalent.

Blocked: The continuous case has not been developed for either the temporal or bimodal logic upstream. Requires foundational research into which additional axioms (if any) are needed beyond density to characterize continuous time. The standard result (Burgess 1982) is that the Until/Since temporal logic over the reals has the same theorems as over the rationals (density suffices), which would make this task trivial — but this equivalence itself needs to be formalized.

Target: Cslib/Logics/Temporal/Metalogic/ContinuousCompleteness.lean
Blocker: Research needed on whether continuous frames require additional axioms beyond density

---

### 39. Temporal discrete completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 36

**Description**: Discrete temporal completeness: prove that every formula valid on all discrete serial linear orders is derivable in the Discrete temporal proof system.

Scope:
1. Add discrete-specific axioms to Temporal.Axiom: `prior_UZ` (F(φ) → U(φ,¬φ)), `prior_SZ` (P(φ) → S(φ,¬φ)), `z1` (G(Gφ→φ) → (F(Gφ)→Gφ)), and discrete uniformity axioms (discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd), gated to FrameClass.Discrete via minFrameClass.
2. Prove discrete soundness: each discrete axiom valid on SuccOrder+PredOrder+IsSuccArchimedean.
3. Prove discrete completeness via contrapositive + MCS + canonical model on Int. The non-discrete branch is eliminated by deriving U(⊤,⊥) as a Discrete theorem.

New development (not a port). The canonical model specializes the base temporal canonical order to Int. The discrete uniformity axioms (minus discrete_box_necessity which is bimodal-only) ensure U(⊤,⊥) propagates uniformly.

Target: Cslib/Logics/Temporal/Metalogic/DiscreteCompleteness.lean + axiom additions to Axioms.lean
Estimated scope: ~500-700 lines (new axioms + discrete soundness + discrete completeness)

---

### 37. Port continuous completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task BimodalLogic:continuous_extension

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic. This task is blocked pending upstream development of continuous frame completeness.

**Source**: Not yet developed in BimodalLogic
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic continuous extension development
**Parent task**: 8 (expanded)

---

### 36. Port discrete completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task BimodalLogic:discrete_sorry_elimination

**Description**: Port discrete completeness (completeness_discrete theorem) and WeakCanonical/IntegerModel/ infrastructure (~6 files). The discrete branch constructs countermodels on Int via the Reynolds pipeline. Currently blocked: upstream BimodalLogic has sorryAx tracing through chronicle_gap_contradiction → succ_cofinal → limitDomSubtype_isSuccArchimedean → succ_embed_surjective. Port after upstream sorry elimination completes.

**Source**: BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/IntegerModel/ (~6 files), discrete branch of BXCanonical/Completeness.lean
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic discrete completeness sorry elimination (36 sorries across IntegerModel/)
**Parent task**: 8 (expanded)
