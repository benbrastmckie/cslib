---
next_project_number: 221
---

# TODO

## Task Order

*Updated 2026-06-16. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,188,192,195,197,209,214,215,219,220 | -- | Bimodal Porting, Project Management, Propositional Logic, ... |
| 2 | 39,40,181 | 36,37,180 | Bimodal Porting, Temporal Logic |
| 3 | 41 | 39,40 | Foundations |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
195 [NOT STARTED] — Fix 30+ linter warnings in Cslib/Logics/Bimodal/Metalogic/Soundne
214 [NOT STARTED] — Fix 4 tactic goal-count warnings in Cslib/Logics/Bimodal/Metalogi
215 [NOT STARTED] — Fill 22 sorry declarations across 5 files: Bundle/SuccRelation.le
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Project Management

209 [IMPLEMENTING] — Fix 298 namespace lint errors: 239 declarations not properly name

### Propositional Logic

188 [NOT STARTED] — Design and prepare a first upstream PR (~300 LOC) contributing pr
219 [RESEARCHED] — Address PR #648 review from ctchou: merge Semantics/Basic.lean an

### Propositional PRs

192 [PLANNED] — Draw on sources in specs/literature/ to verify and improve citati

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
220 [NOT STARTED] — Refactor PR #649: trim completeness-only content, add FutureTempo
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Pr

197 [PR READY] — Review the ambition to contribute Modal/ to upstream, identifying

## Tasks

### 220. Refactor pr649 typeclass split ltl formula
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Refactor PR #649: trim completeness-only content, add FutureTemporalConnectives typeclass layer, and LTL.Formula type. Remove Encodable/Countable/Infinite/Denumerable and BEq instances from PR scope (save for completeness PR). Split TemporalConnectives into FutureTemporalConnectives + TemporalConnectives in Connectives.lean. Add HasNext typeclass and LTLConnectives bundle. Create Cslib/Logics/LTL/Syntax/Formula.lean with {atom, bot, imp, next, untl} and derived connectives. Create LTL.Formula.toTemporal embedding. Add basic LTL satisfaction over omega-words. Addresses PR #649 review (ctchou) and Zulip LTL/Büchi discussion. References: Kamp (1968), Burgess (1982), Vardi & Wolper (1986)

---

### 219. Address pr648 merge semantics files
- **Status**: [RESEARCHED]
- **Task Type**: pr
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [219_address_pr648_merge_semantics_files/reports/01_pr648-review-analysis.md]
  - [219_address_pr648_merge_semantics_files/reports/02_team-research.md]

**Description**: Address PR #648 review from ctchou: merge Semantics/Basic.lean and Bool.lean into a single file, update references to Avigad, and coordinate with PRs #536, #587, #607. PR: https://github.com/leanprover/cslib/pull/648 Zulip: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/603538889

---

### 218. Push bib entries minor fixes pr649
- **Status**: [COMPLETED]
- **Task Type**: pr
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Push missing bib entries and minor fixes to PR #649: add 7 missing references.bib entries (Church1956, Gentzen1935, Johansson1937, McKinsey1939, Prawitz1965, TroelstraVanDalen1988, Wajsberg1938) referenced by Connectives.lean, Defs.lean, and NaturalDeduction/Basic.lean; include Defs.lean architecture docstring, NaturalDeduction/Basic.lean Γ→G rename, and copyright date updates

---

### 215. Fill sorry declarations in Bimodal BXCanonical and Bundle files
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: None

**Description**: Fill 22 sorry declarations across 5 files: Bundle/SuccRelation.lean (7), BXCanonical/Chronicle/ChronicleToCountermodel.lean (10), Bundle/UntilSinceCoherence.lean (2), BXCanonical/Completeness/Dense.lean (1), BXCanonical/Frame.lean (1). These are incomplete proofs in the bimodal temporal logic development.

---

### 214. Fix tactic goal-count warnings in DedekindZ/Cases.lean
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: None

**Description**: Fix 4 tactic goal-count warnings in Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean where apply chains create unfocused goals. Restructure the proof to properly focus each subgoal.

---

### 209. Fix namespace lint errors (not namespaced + duplicate namespace)
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Project Management
- **Dependencies**: None

**Description**: Fix 298 namespace lint errors: 239 declarations not properly namespaced and 59 duplicate namespace components (Chronicle, Temporal, Bimodal repeated in names). Requires moving declarations into correct namespaces or renaming.

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
