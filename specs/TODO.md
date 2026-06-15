---
next_project_number: 208
---

# TODO

## Task Order

*Updated 2026-06-15. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,188,192,195,197,202,207 | -- | Bimodal Porting, Propositional Logic, Propositional PRs, ... |
| 2 | 39,40,181 | 36,37,180 | Bimodal Porting, Temporal Logic |
| 3 | 41 | 39,40 | Foundations |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
195 [NOT STARTED] — Fix 30+ linter warnings in Cslib/Logics/Bimodal/Metalogic/Soundne
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

188 [NOT STARTED] — Design and prepare a first upstream PR (~300 LOC) contributing pr
202 [RESEARCHED] — Comprehensive review of cslib PR #648 (https://github.com/leanpro

### Propositional PRs

192 [PLANNED] — Draw on sources in specs/literature/ to verify and improve citati

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
207 [RESEARCHED] — Research refactoring Temporal/ and Modal/ implementations based o
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Pr

197 [PR READY] — Review the ambition to contribute Modal/ to upstream, identifying

## Tasks

### 207. Research temporal modal refactor pr649
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**:
  - [207_research_temporal_modal_refactor_pr649/reports/01_team-research.md]
  - [207_research_temporal_modal_refactor_pr649/reports/02_reviewer-directed-research.md]

**Description**: Research refactoring Temporal/ and Modal/ implementations based on PR #649 review feedback on Tense Logic, drawing on Isabelle Propositional_Logic_Class formalization for a dependent type system approach in Lean 4

---

### 206. Fix --wfail CI warnings across Bimodal, Temporal, and Modal files
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Project Management
- **Dependencies**: None

**Description**: Fix all --wfail CI warnings across Bimodal/, Temporal/, and Modal/ files (push_neg deprecation, unused simp args, show tactic misuse, empty lines in commands, unscoped options, module docstring placement, flexible simp, open Classical)

---

### 205. Review pr649 quality conventions
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [205_review_pr649_quality_conventions/reports/01_pr649-quality-review.md]
- **Plan**: [205_review_pr649_quality_conventions/plans/01_pr649-quality-fixes.md]
- **Summary**: [205_review_pr649_quality_conventions/summaries/01_execution-summary.md]

**Description**: Review PR #649 (Temporal/Syntax/Formula.lean and Connectives.lean extensions) for proof quality, comment style, naming conventions, and docstring standards against existing CSLib modules as a baseline. Compare against established patterns in Propositional/, Modal/, and Foundations/ to ensure consistency before upstream review

---

### 204. Polish pr 648 propositional
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Polish PR #648: remove Aesop.BuiltinRules import, trim Architecture section from Defs.lean docstring (references non-existent upstream files), fix inconsistent context variable naming (G vs Γ) in NaturalDeduction/Basic.lean constructors, fix copyright header format. Then squash and force-push to feat/propositional-v2

---

### 203. First temporal pr classical propositional
- **Status**: [COMPLETED]
- **Task Type**: pr
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Pr-description**: [203_first_temporal_pr_classical_propositional/pr-description.md]
- **Summary**: [203_first_temporal_pr_classical_propositional/summaries/01_execution-summary.md]

**Description**: Create first ~300 LOC PR for Temporal/ extending classical propositional logic, establishing foundations for full temporal logic development (follows PR #648)

---

### 202. Review hilbert classes vs pr648
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [202_review_hilbert_classes_vs_pr648/reports/01_hilbert-classes-comparison.md]
  - [202_review_hilbert_classes_vs_pr648/reports/02_team-research.md]

**Description**: Comprehensive review of cslib PR #648 (https://github.com/leanprover/cslib/pull/648). This task serves as the central tracking point for all review dimensions: upstream reviewer feedback, architectural concerns, API design decisions, compatibility with existing Propositional/ and Hilbert/ developments, naming conventions, and any requested changes. Initial research compared the thomaskwaring/cslib_SKI Hilbert branch approach against the PR's Hilbert system design; further research rounds should address additional review concerns as they arise, including code quality, proof style, module organization, and alignment with cslib contribution standards.

---

### 201. Review modal pr citations
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [201_review_modal_pr_citations/reports/01_modal-citation-review.md]
- **Plan**: [201_review_modal_pr_citations/plans/01_modal-citation-fixes.md]
- **Summary**: [201_review_modal_pr_citations/summaries/01_modal-citation-fixes-summary.md]

**Description**: Review citations in Modal PR changes for accuracy and completeness, covering the Basic.lean and Denotation.lean files in scope for the initial Modal/ upstream PR (task 197). Verify literature references (Blackburn2001, ChagrovZakharyaschev1997, Bentzen2023, Trufas2024, Johansson1937), check BibTeX entries in references.bib, and ensure pr-description.md citations are accurate and properly grounded in primary sources

---

### 197. Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [PR READY]
- **Task Type**: pr
- **Topic**: pr
- **Dependencies**: None
- **Research**: [197_modal_upstream_initial_pr/reports/06_modal-pr-landscape.md]
- **Plan**: [197_modal_upstream_initial_pr/plans/08_modal-upstream-pr-plan.md]
- **Pr_description**: [197_modal_upstream_initial_pr/pr-description.md]

**Description**: Review the ambition to contribute Modal/ to upstream, identifying an appropriate ~300 LOC initial PR to submit that builds on the first PR described in specs/188_first_propositional_upstream_pr/pr-description.md for the Foundations/ and Propositional/ logic while making this PR maintain independence wherever possible

---

### 195. Fix dense validity linter warnings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: None

**Description**: Fix 30+ linter warnings in Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean: remove ~20 unused simp arguments and replace 6 deprecated push_neg calls with push Not.

---

### 192. Research verify literature refs pr 188
- **Status**: [PLANNED]
- **Task Type**: general
- **Topic**: Propositional PRs
- **Dependencies**: None
- **Research**:
  - [192_research_verify_literature_refs_pr_188/reports/01_team-research.md]
  - [192_research_verify_literature_refs_pr_188/reports/02_team-research.md]

**Description**: Draw on sources in specs/literature/ to verify and improve citations throughout the files within scope of the task 188 PR, update references.bib following CONTRIBUTING.md conventions, and improve literature claims in specs/archive/188_first_propositional_upstream_pr/pr-description.md while maintaining a clear and concise style for reviewers

---

### 188. First propositional upstream pr
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [188_first_propositional_upstream_pr/reports/01_team-research.md]
- **Plan**: [188_first_propositional_upstream_pr/plans/01_implementation-plan.md]
- **Summary**: [188_first_propositional_upstream_pr/summaries/01_execution-summary.md]

**Description**: Design and prepare a first upstream PR (~300 LOC) contributing propositional logic foundations to CSLib.

---

### 181. Bimodal primitive dia always historically
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: Task 180
- **Research**: [181_bimodal_primitive_dia_always_historically/reports/01_bimodal-primitive-expansion-research.md]

**Description**: Propagate primitive diamond, allFuture, and allPast constructors to the Bimodal layer, giving {atom, bot, imp, and, or, box, dia, untl, snce, allFuture, allPast} (11 primitives). This is the union of Modal (task 179) and Temporal (task 180) primitive sets. Scope: (1) Syntax/Formula.lean: add .dia/.allFuture/.allPast constructors, update all match cases. (2) Semantics/Truth.lean: structural truthAt clauses. (3) ProofSystem: axiom constructors for diamond duality and G/H axioms. (4) Embedding: extend ModalEmbedding (.dia), TemporalEmbedding (.allFuture/.allPast). (5) Metalogic: propagate through ~50 files (Core, Soundness, Completeness, BXCanonical, ConservativeExtension, Separation, Decidability, Algebraic). Follow task 177 playbook. (6) Classical equivalences become theorems. Verify full CI. Estimated ~50 files, ~2000 lines, similar scope to task 177.

---

### 180. Temporal primitive always historically
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [180_temporal_primitive_always_historically/reports/01_primitive-always-historically-research.md]

**Description**: Add allFuture (G) and allPast (H) as primitive constructors to Temporal.Formula, giving {atom, bot, imp, and, or, untl, snce, allFuture, allPast}. Currently G is derived as neg(someFuture(neg phi)) and H as neg(somePast(neg phi)), which are only valid classically. Making them primitive enables intuitionistic temporal logics. Note: someFuture (F) and somePast (P) remain derivable without negation (F = top U phi, P = top S phi). Scope: (1) Syntax/Formula.lean: add .allFuture/.allPast constructors, update complexity, subst, atoms, encodeNat, temporalDepth, swapTemporal. (2) Semantics: structural clauses for universal future/past quantification. (3) ProofSystem: temporal axioms referencing G/H now use primitive constructors. (4) Metalogic: cases in Soundness, Chronicle/TruthLemma, MCS, Completeness. (5) Classical equivalences become theorems. Verify full CI. Reference: Boudou et al. for intuitionistic temporal logic.

---

### 41. Abstract completeness infrastructure
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Foundations
- **Dependencies**: Task 39, Task 40

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
