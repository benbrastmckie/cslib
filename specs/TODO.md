---
next_project_number: 202
---

# TODO

## Task Order

*Updated 2026-06-14. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,188,192,195,197,198,201 | -- | Bimodal Porting, Modal Logic, Propositional Logic, ... |
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

### Modal Logic

197 [PLANNED] — Review the ambition to contribute Modal/ to upstream, identifying
201 [NOT STARTED] — Review citations in Modal PR changes for accuracy and completenes

### Propositional Logic

188 [NOT STARTED] — Design and prepare a first upstream PR (~300 LOC) contributing pr
198 [PR READY] — Submit first propositional logic upstream PR (~300 LOC) to CSLib 

### Propositional PRs

192 [PLANNED] — Draw on sources in specs/literature/ to verify and improve citati

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

## Tasks

### 201. Review modal pr citations
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Review citations in Modal PR changes for accuracy and completeness, covering the Basic.lean and Denotation.lean files in scope for the initial Modal/ upstream PR (task 197). Verify literature references (Blackburn2001, ChagrovZakharyaschev1997, Bentzen2023, Trufas2024, Johansson1937), check BibTeX entries in references.bib, and ensure pr-description.md citations are accurate and properly grounded in primary sources

---

### 200. Fix literature directory quality
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: Project Management
- **Dependencies**: None

**Description**: Fix literature directory quality: complete incomplete book splits (blackburn_2001 only has 3 of 7+ chapters, mendelson_2016 and church_1956 have content loss), remove redundant monolithic .md files after verifying split completeness, audit index.json entries for accuracy (token counts, paths, keywords), ensure all chapter files are within the 4000-token budget for --lit injection, and verify the 3 scholarly reconstruction files (burgess_1984, gabbay_1994_ch10, reynolds_1992) have adequate content for research use. Goal: make specs/literature/ fully functional for --lit flag during /research, /plan, and /implement phases

---

### 199. Review pr citations
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [199_review_pr_citations/reports/01_pr-citation-review.md]
- **Plan**: [199_review_pr_citations/plans/01_pr-citation-plan.md]
- **Summary**: [199_review_pr_citations/summaries/01_pr-citation-summary.md]

**Description**: Review citations in PR changes for accuracy and completeness

---

### 198. Submit first propositional logic upstream PR (~300 LOC)
- **Status**: [PR READY]
- **Task Type**: pr
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Submit first propositional logic upstream PR (~300 LOC) to CSLib contributing Foundations/Logic/Connectives.lean and Propositional/ changes. Create a new feature branch from upstream/main, cherry-pick the appropriate changes from main while maintaining the scope defined in pr-description.md, then push and submit PR. The pr-description.md from task 188 has been copied into this task directory as the authoritative PR description.

---

### 197. Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [PLANNED]
- **Task Type**: pr
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Review the ambition to contribute Modal/ to upstream, identifying an appropriate ~300 LOC initial PR to submit that builds on the first PR described in specs/188_first_propositional_upstream_pr/pr-description.md for the Foundations/ and Propositional/ logic while making this PR maintain independence wherever possible

---

### 196. Refactor connectives mathlib bot
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional PRs
- **Dependencies**: None
- **Research**: [196_refactor_connectives_mathlib_bot/reports/01_mathlib-section-research.md]
- **Plan**: [196_refactor_connectives_mathlib_bot/plans/02_implementation-plan.md]
- **Summary**: [196_refactor_connectives_mathlib_bot/summaries/02_verification-summary.md]

**Description**: Keep HasBot/HasImp/HasAnd/HasOr as custom CSLib classes for naming symmetry and to match the Has* convention used across ProofSystem.lean, Axioms.lean, Consistency.lean, and BigConj.lean. No bridge instance needed — concrete formula types already provide direct Bot instances for ⊥ notation, and generic code intentionally uses HasBot.bot. Update pr-description.md Mathlib section to accurately explain the design choice: uniform Has* naming, concrete types get ⊥ via direct Bot instances, HImp notation mismatch prevents HasImp replacement. Scope: pr-description.md (Mathlib section rewrite)

---

### 195. Fix dense validity linter warnings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: None

**Description**: Fix 30+ linter warnings in Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean: remove ~20 unused simp arguments and replace 6 deprecated push_neg calls with push Not.

---

### 194. Curate zotero pdfs for literature
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: Project Management
- **Dependencies**: None
- **Research**: [194_curate_zotero_pdfs_for_literature/reports/02_literature-organization-practices.md]
- **Plan**: [194_curate_zotero_pdfs_for_literature/plans/02_literature-curation-plan.md]
- **Summary**: [194_curate_zotero_pdfs_for_literature/summaries/02_literature-curation-summary.md]

---

### 193. Clean up modal deduction theorem naming
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

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

### 191. Clean up propositional deduction theorem naming
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

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

### 179. Modal primitive diamond
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [179_modal_primitive_diamond/reports/01_primitive-diamond-research.md]
  - [179_modal_primitive_diamond/reports/02_team-research.md]
  - [179_modal_primitive_diamond/reports/02_team-research.md]
  - [179_modal_primitive_diamond/reports/03_upstream-study.md]
  - [179_modal_primitive_diamond/reports/05_team-research.md]
- **Plan**: [179_modal_primitive_diamond/plans/05_documentation-plan.md]
- **Summary**: [179_modal_primitive_diamond/summaries/05_documentation-summary.md]

**Description**: Document why box is primitive in classical modal logic; add docstrings citing Blackburn2001 and ChagrovZakharyaschev1997

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
