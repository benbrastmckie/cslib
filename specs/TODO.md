---
next_project_number: 237
---

# TODO

## Task Order

*Updated 2026-06-19. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,209,226,232,234,235,236 | -- | Bimodal Porting, Modal Logic, Project Management, ... |
| 2 | 39,40,181,215 | 36,37,180 | Bimodal Porting, Temporal Logic |
| 3 | 41 | 39,40 | Foundations |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Modal Logic

235 [PR READY] — Upgrade weak completeness to strong completeness for all 15 modal

### Project Management

209 [IMPLEMENTING] — Fix 298 namespace lint errors: 239 declarations not properly name

### Propositional Logic

226 [RESEARCHED] — Prepare a follow-up upstream PR (~400-500 LOC) stacked on PR #648

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
234 [IMPLEMENTING] — Revise main branch to use standard LTL convention for untl and sn
236 [PLANNED] — Complete follow-up PRs from PR #649 for Büchi automata and closur
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Pr

232 [IMPLEMENTING] — Rebase PR #649 (feat/temporal-formula-propositional) onto PR #648

## Tasks

### 236. Follow up prs buchi omega regular
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Complete follow-up PRs from PR #649 for Büchi automata and closure of omega-regular languages under boolean operations

---

### 235. Strong completeness modal cube
- **Status**: [PR READY]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [235_strong_completeness_modal_cube/reports/01_strong-completeness-research.md]
- **Plan**: [235_strong_completeness_modal_cube/plans/01_strong-completeness-plan.md]

**Description**: Upgrade weak completeness to strong completeness for all 15 modal cube systems (K, T, B, D, S4, S5, K4, K5, K45, KB5, D4, D5, D45, DB, TB). The existing weak completeness results prove that validity implies derivability from the empty context. Strong completeness should prove that semantic entailment from a set of premises Γ implies syntactic entailment: Γ ⊨ φ → Γ ⊢ φ, matching the existing strong soundness signature Γ ⊢ φ → Γ ⊨ φ. Include clear documentation distinguishing strong vs weak versions and careful organization of parameterized and per-system files

---

### 234. Revise untl snce convention
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [234_revise_untl_snce_convention/reports/01_untl-snce-convention.md]
- **Plan**: [234_revise_untl_snce_convention/plans/01_untl-snce-convention.md]

**Description**: Revise main branch to use standard LTL convention for untl and snce: first argument is the guard (holds at intermediate points), second argument is the event (eventually holds at the witness point). Update all Lean code, docstrings, and comments that reference the Burgess convention to align with the standard temporal logic convention

---

### 233. Revise pr649 ltl only
- **Status**: [COMPLETED]
- **Task Type**: pr
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Revise PR #649 on branch feat/temporal-formula-propositional to include LTL only per reviewer comment (pullrequestreview-4528240645), add LTL semantics if space permits (~300LOC), and update pr-description accordingly

---

### 232. Rebase pr649 onto pr648
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: pr
- **Dependencies**: None
- **Research**: [232_rebase_pr649_onto_pr648/reports/01_rebase-research.md]
- **Plan**: [232_rebase_pr649_onto_pr648/plans/01_rebase-plan.md]

**Description**: Rebase PR #649 (feat/temporal-formula-propositional) onto PR #648 base branch (feat/propositional-v2) and remove unrelated file changes per reviewer ctchou's request. Currently the branch is a single commit on main with many unrelated changes (HasFresh, LTS/Notation, CCS/Semantics, LambdaCalculus files, Modal logic files, Propositional/Defs.lean). Cherry-pick only the temporal-specific changes (Temporal/Syntax/Formula.lean, LTL/Syntax/Formula.lean, Connectives.lean temporal additions, Cslib.lean imports, references.bib) onto feat/propositional-v2 as the new base

---

### 226. Propositional semantics upstream pr
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [226_propositional_semantics_upstream_pr/reports/01_upstream-pr-research.md]
  - [226_propositional_semantics_upstream_pr/reports/02_three-way-comparison.md]

**Description**: Prepare a follow-up upstream PR (~400-500 LOC) stacked on PR #648, contributing propositional semantics to CSLib. Scope: (1) Semantics/Algebra.lean — GHA evaluation with bot_val parameter for minimal/intuitionistic/classical logic, following Thomas Waring's GeneralizedHeytingAlgebra direction from the Zulip thread. (2) Semantics/Bool.lean — BoolEvaluate with bridge lemma to AlgEvaluate for computable procedures (DPLL/SAT). (3) Semantics/SemanticConsequence.lean — semantic consequence and tautology definitions. (4) Possibly Semantics/Kripke.lean — Kripke semantics with botForces for minimal logic if LOC budget permits. Soundness proofs deferred to a subsequent Hilbert systems + metalogic PR. Ensure lake build, lake test, lake exe checkInitImports, lake exe lint-style, and lake shake all pass. Write PR description referencing the Zulip Propositional Logic thread discussion with Thomas Waring and Matthew Doty on GHA semantics and bot_val design.

---

### 215. Fill sorry declarations in Bimodal BXCanonical and Bundle files
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: Task 36, Task 37

**Description**: Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal/Metalogic/:
- Bundle/SuccRelation.lean: 7 sorries (lines 253, 258, 263, 269, 275, 281, 285)
- BXCanonical/Chronicle/ChronicleToCountermodel.lean: 10 sorries (lines 66, 143, 144, 147, 153, 157, 163, 171, 172, 177)
- Bundle/UntilSinceCoherence.lean: 2 sorries (lines 37, 41)
- BXCanonical/Frame.lean: 1 sorry (line 159)

Note: countermodel_dense (ChronicleToCountermodelBasic.lean:825) and completeness_dense (Dense.lean:122) carved off to task 231.

9 sorries blocked on task 37 (strict Until/Since semantics gap: BX8/BX9/temporal-T axioms removed as unsound). 11 sorries blocked on task 36 (discrete completeness pipeline requires unported GoodStructuresModelSurgery infrastructure).

---

### 209. Fix namespace lint errors (not namespaced + duplicate namespace)
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Project Management
- **Dependencies**: None
- **Research**: [209_lint_namespace_fixes/reports/01_namespace-research.md]
- **Plan**: [209_lint_namespace_fixes/plans/01_namespace-plan.md]

**Description**: Fix 298 namespace lint errors: 239 declarations not properly namespaced and 59 duplicate namespace components (Chronicle, Temporal, Bimodal repeated in names). Requires moving declarations into correct namespaces or renaming.

---

### 197. Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [COMPLETED]
- **Task Type**: pr
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [197_modal_upstream_initial_pr/reports/06_modal-pr-landscape.md]
  - [197_modal_upstream_initial_pr/reports/09_team-research.md]
  - [197_modal_upstream_initial_pr/reports/10_plan-review.md]
- **Pr_description**: [197_modal_upstream_initial_pr/pr-description.md]
- **Plan**: [197_modal_upstream_initial_pr/plans/10_modal-pr-revision.md]

**Description**: Review the ambition to contribute Modal/ to upstream, identifying an appropriate ~300 LOC initial PR to submit that builds on the first PR described in specs/188_first_propositional_upstream_pr/pr-description.md for the Foundations/ and Propositional/ logic while making this PR maintain independence wherever possible

---

### 192. Research verify literature refs pr 188
- **Status**: [ABANDONED]
- **Task Type**: general
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [192_research_verify_literature_refs_pr_188/reports/01_team-research.md]
  - [192_research_verify_literature_refs_pr_188/reports/02_team-research.md]

**Description**: Draw on sources in specs/literature/ to verify and improve citations throughout the files within scope of the task 188 PR, update references.bib following CONTRIBUTING.md conventions, and improve literature claims in specs/archive/188_first_propositional_upstream_pr/pr-description.md while maintaining a clear and concise style for reviewers

---

### 188. First propositional upstream pr
- **Status**: [COMPLETED]
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
