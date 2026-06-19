---
next_project_number: 247
---

# TODO

## Task Order

*Updated 2026-06-19. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,236,241,242,243,244,245,246 | -- | Bimodal Porting, Modal Logic, Propositional Logic, ... |
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

246 [NOT STARTED] — Clean up scratch-work inline comments inside Modal/ proof bodies,

### Propositional Logic

226 [RESEARCHED] — Prepare a follow-up upstream PR (~400-500 LOC) stacked on PR #648

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
236 [PLANNED] — Complete follow-up PRs from PR #649 for Büchi automata and closur
241 [NOT STARTED] — Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller)
242 [NOT STARTED] — Implement full Vardi-Wolper tableau construction for LTL-to-NBA t
243 [NOT STARTED] — Implement deterministic Büchi automata constructions and related 
244 [NOT STARTED] — Optimize NBA state space constructions prioritizing correctness o
245 [NOT STARTED] — Add Encodable, Countable, and Denumerable instances for LTL Formu
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

## Tasks

### 246. Modal comment cleanup pr description
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Clean up scratch-work inline comments inside Modal/ proof bodies, revise specs/archive/197_modal_upstream_initial_pr/pr-description.md to link exact line numbers for strong soundness and completeness results across all 15 systems, then update the description on GitHub PR #662 (leanprover/cslib)

---

### 245. Formula encodable countable instances
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Add Encodable, Countable, and Denumerable instances for LTL Formula type (deferred to completeness PRs)

---

### 244. Optimize nba state space
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Optimize NBA state space constructions prioritizing correctness over minimality

---

### 243. Deterministic buchi automata
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Implement deterministic Büchi automata constructions and related results

---

### 242. Vardi wolper tableau construction
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Implement full Vardi-Wolper tableau construction for LTL-to-NBA translation using direct NBA construction approach

---

### 241. Mcnaughton theorem
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller) establishing equivalence between omega-regular languages and deterministic Muller automata

---

### 240. Modal metalogic naming and barrel fixes
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 238
- **Research**: [240_modal_metalogic_naming_and_barrel_fixes/reports/01_naming-barrel-fixes.md]
- **Plan**: [240_modal_metalogic_naming_and_barrel_fixes/plans/01_naming-barrel-fixes.md]
- **Summary**: [240_modal_metalogic_naming_and_barrel_fixes/summaries/01_naming-barrel-fixes-summary.md]

**Description**: Fix naming inconsistencies and barrel file issues in Modal/Metalogic. (1) Add missing 'public import Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension' to Metalogic.lean barrel file. (2) Normalize barrel import ordering so StrongCompleteness block follows the same system order as Soundness/Completeness block (K, T, D, S4, K4, B, K45, K5, D4, KB5, TB, D45, D5, DB, S5). (3) Rename S5/Soundness.lean theorem 'axiom_sound' to 's5_axiom_sound' for consistency with all other 14 systems. (4) Rename D/Completeness.lean theorems from suffix to prefix convention: 'derive_box_from_inconsistency_d' → 'd_derive_box_from_inconsistency', 'mcs_box_witness_d' → 'd_mcs_box_witness', 'canonical_serial' → 'd_canonical_serial', 'truth_lemma_d' → 'd_truth_lemma'. Verify no downstream consumers break (grep for old names in the codebase). (5) Reword K/Completeness.lean:111 comment from 'K-SPECIFIC FIX' to 'K-SPECIFIC CASE' to avoid triggering lint scanners. (6) Evaluate S5 alias 'alias completeness := s5_completeness' — if no downstream consumers use the bare 'completeness' name, remove it; otherwise add a deprecation docstring.

---

### 239. Modal metalogic citation standardization
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [239_modal_metalogic_citation_standardization/reports/01_citation-standardization.md]
- **Plan**: [239_modal_metalogic_citation_standardization/plans/01_citation-standardization.md]
- **Summary**: [239_modal_metalogic_citation_standardization/summaries/01_citation-standardization-summary.md]

**Description**: Standardize all citations in Modal/Metalogic to use Lean4Doc bib link format. (1) Convert ~20 Soundness.lean and Completeness.lean module docstrings from plain-text style ('Blackburn, de Rijke, Venema, "Modal Logic" (2002)') to the Lean4Doc link format ('* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]') matching the StrongCompleteness.lean standard. (2) Replace undefined 'BRV' abbreviation in module docstrings with either spelled-out author names or bib key references; inline code comments may keep 'BRV' if the abbreviation is defined in the file's docstring. (3) Replace internal file references in Soundness.lean's References section ('* Cslib/Logics/Modal/Basic.lean') with proper bib citations or remove if no literature source applies. (4) Remove or convert cross-repo references to BimodalLogic/ project in DeductionTheorem.lean, MCS.lean, and DerivationTree.lean docstrings — replace with bib citations where a literature source exists, otherwise remove the stale path.

---

### 238. Modal metalogic stale docstrings
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [238_modal_metalogic_stale_docstrings/reports/01_stale-docstrings.md]
- **Plan**: [238_modal_metalogic_stale_docstrings/plans/01_stale-docstrings.md]
- **Summary**: [238_modal_metalogic_stale_docstrings/summaries/01_stale-docstrings-summary.md]

**Description**: Fix stale module docstrings in Modal/Metalogic after task 237 theorem migration. (1) Core Completeness.lean: update /-! docstring to remove moved `completeness` theorem from Main Results, update description to reflect the file now provides generic completeness infrastructure (truth lemma, canonical model) but not the system-specific completeness theorems. (2) 8 empty-body Completeness.lean files (K4, K5, K45, KB5, D4, D5, D45, DB): replace stale 'This module proves completeness...' docstrings with short infrastructure docstrings matching the B/S4/S5 pattern — state the file exists for import chain stability and cross-reference StrongCompleteness.lean for the actual theorems. (3) K5/Completeness.lean has a contradictory hybrid docstring that both says 'proves completeness' and 'provides import infrastructure' — pick one (infrastructure).

---

### 236. Follow up prs buchi omega regular
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Plan**: [236_follow_up_prs_buchi_omega_regular/plans/05_gnba-correctness-plan.md]

**Description**: Complete follow-up PRs from PR #649 for Büchi automata and closure of omega-regular languages under boolean operations

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
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Project Management
- **Dependencies**: None
- **Research**: [209_lint_namespace_fixes/reports/01_namespace-research.md]
- **Plan**: [209_lint_namespace_fixes/plans/01_namespace-plan.md]
- **Summary**: [209_lint_namespace_fixes/summaries/01_namespace-summary.md]

**Description**: Fix 298 namespace lint errors: 239 declarations not properly namespaced and 59 duplicate namespace components (Chronicle, Temporal, Bimodal repeated in names). Requires moving declarations into correct namespaces or renaming.

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
