---
next_project_number: 286
---

# TODO

## Task Order

*Updated 2026-06-23. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,241,245,252,266,269,278,279,280,285 | -- | Bimodal Porting, Foundations, Propositional Logic, ... |
| 2 | 39,40,181,215 | 36,37,180 | Bimodal Porting, Temporal Logic |
| 3 | 41,275 | 39,40 | Foundations |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

269 [PLANNED] — Build generic bounded proof-search tactic for InferenceSystem. Cr
278 [NOT STARTED] — Simplify proofs using new simp/grind normalization tags. After ta
41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
266 [IMPLEMENTING] — Research improvements to Propositional/ and Foundations/Logic/ in
279 [NOT STARTED] — Implement a two-sided Gentzen-style sequent calculus (LK for clas
280 [NOT STARTED] — Research the current state of propositional proof systems in CSLi
285 [NOT STARTED] — Refactor the ND metalogical API so that all ND-level results (alg

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
241 [NOT STARTED] — Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller)
245 [NOT STARTED] — Add Encodable, Countable, and Denumerable instances for LTL Formu
252 [NOT STARTED] — Formalize Rabin and parity acceptance conditions alongside the ex
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
  └─ 275 [BLOCKED] — Prove that Bimodal TM is conservative over Temporal BX for tempor
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Uncategorized

## Tasks

### 285. Nd metalogic as hilbert corollaries
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 283, Task 284

**Description**: Refactor the ND metalogical API so that all ND-level results (algebraic completeness, conservative extension, Glivenko) are derived as corollaries of the Hilbert-primary versions via the hilbert_iff_nd bridge theorems. Remove the old ND-primary proofs (or move to a Legacy/ module if needed for transition). Ensure all downstream imports and dependent modules (modal, temporal, bimodal) still compile. Update ProofSystem.lean documentation to reflect the Hilbert-primary architecture. Run full CI pipeline (lake build, lake test, lake lint, lake exe checkInitImports).

---

### 284. Hilbert primary conservative glivenko
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 283

**Description**: Restate ipl_conservative_over_mpl and glivenko as Hilbert-primary using the Hilbert algebraic completeness from task 283. Conservative extension becomes: Derivable IntPropAxiom φ → Derivable MinPropAxiom φ (for bot-free φ), routed through Hilbert alg_complete and the GHA/HA embedding. Glivenko becomes: Derivable PropositionalAxiom φ → Derivable IntPropAxiom (¬¬φ), routed through Hilbert alg_complete and the Heyting.Regular subalgebra argument. Derive ND versions as corollaries via the bridge.

---

### 283. Hilbert primary algebraic completeness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 282

**Description**: Restate algebraic completeness as Hilbert-primary using the Hilbert Lindenbaum algebra from task 282. Replace MPL.alg_complete, IPL.alg_complete, and Theory.alg_complete with versions stated for Derivable/SetDerivable (Hilbert) rather than DerivableIn (ND). The algebraic soundness theorems (min_alg_soundness_derivable etc.) are already Hilbert-primary and can be kept. The completeness direction uses the new Hilbert Lindenbaum algebra directly. Derive ND versions as corollaries via the hilbert_iff_nd bridge.

---

### 282. Lindenbaum algebra over hilbert
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 281

**Description**: Rebuild the Lindenbaum algebra construction over Hilbert derivations instead of ND. Currently Lindenbaum.lean defines the quotient ordering via DerivableIn T ({A} ⊢ B) (ND) and builds GHA/HA/BA instances using ND structural rules. Redefine using Hilbert SetDerivable/Deriv with the derived structural rules from task 281. The lattice operations (sup, inf, himp, compl) and their GHA/HA/BA instances must all be restated and proven using Hilbert derivations. The existing ND Lindenbaum can be kept temporarily as internal machinery but the new Hilbert version becomes primary.

---

### 281. Hilbert derived structural rules
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Complete the set of Hilbert derived structural rules needed for the Lindenbaum algebra construction. HilbertDerivedRules.lean already has some derived rules; extend it to include all ND structural rules as Hilbert-derived theorems for each tier (MPL/IPL/CPL): andI, andE1, andE2, orI1, orI2, orE, impI, impE, botE (IPL+CPL), dne (CPL). Each rule must be stated as a Hilbert DerivationTree derivation using only ax, assumption, modus_ponens, and weakening. This is the prerequisite for rebuilding the Lindenbaum algebra over Hilbert.

---

### 280. Proof system triad gap analysis
- **Status**: [NOT STARTED]
- **Task Type**: formal
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Research the current state of propositional proof systems in CSLib and create tasks to fill all gaps needed to provide: (1) Hilbert systems for algebraic completeness and MCS, (2) natural deduction for the Curry-Howard correspondence, (3) sequent calculus for cut elimination and decidability. Audit what exists (Hilbert + ND + algebraic semantics + Kripke semantics + equivalence bridges), identify what is missing for each proof system to fully serve its metatheoretic purpose (e.g., Hilbert-algebraic bridge corollaries, ND normalization/Curry-Howard, LK/LJ cut elimination, decidability instances, proof-system equivalence bridges), and create appropriately scoped implementation tasks with dependencies. Account for existing tasks 266 and 279 to avoid overlap. This is a metatask: the deliverable is a set of new tasks, not implementation.

---

### 279. Propositional sequent calculus lk lj
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Implement a two-sided Gentzen-style sequent calculus (LK for classical, LJ for intuitionistic) for propositional logic with cut elimination. Use Finset-based contexts on both sides, following the CLL sequent calculus in Cslib/Logics/LinearLogic/CLL/Basic.lean as a template. Prove soundness, completeness, cut elimination (Hauptsatz), and equivalence bridges to the existing Hilbert and natural deduction systems (hilbert_iff_lk, nd_iff_lk). This completes the proof-system triad (Hilbert + ND + SC) for propositional logic and would be the first LK/LJ formalization in Lean 4.

---

### 278. Simplify proofs with normalization tags
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None

**Description**: Simplify proofs using new simp/grind normalization tags. After task 268 adds @[simp, scoped grind =] tags to Hilbert system definitional lemmas, audit all proofs in Propositional/, Modal/, Temporal/, and Bimodal/ that use manual `simp only [listImp_nil, listImp_cons, bigconj_nil, ...]` or verbose tactic chains involving these normalization lemmas. Replace with `grind` or `simp` where the new tags make the explicit lemma lists redundant. Also check Foundations/Logic/ proofs. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake

---

### 275. Bimodal tm conservative over temporal bx
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: Task 36, Task 39
- **Research**:
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/02_team-research.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/03_team-research.md]

**Description**: Prove that Bimodal TM is conservative over Temporal BX for temporal formulas (those using only until/since, no box). The Temporal.Formula.toBimodal embedding exists. The lift_derivation_qfree infrastructure in Bimodal/Metalogic/ConservativeExtension/ partially supports this. Requires verifying the lifting extends to temporal connectives.

---

### 269. Hilbert search tactic
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 268
- **Research**: [269_hilbert_search_tactic/reports/01_team-research.md]
- **Plan**: [269_hilbert_search_tactic/plans/02_hilbert-search-plan.md]

**Description**: Build generic bounded proof-search tactic for InferenceSystem. Create a bounded DFS proof-search tactic (e.g., hilbert_search) that works generically over the InferenceSystem typeclass. Inspired by BimodalLogic modal_search (~700 lines) but adapted to cslib polymorphic architecture. Search strategies: axiom matching, assumption lookup, modus ponens decomposition, necessitation + K rules, temporal rules. Must handle the InferenceSystem S α typeclass generically (not hardcoded to a specific DerivationTree). Configurable search depth. Should work across Propositional, Modal, Temporal, and Bimodal systems. Depends on task 268 (normalization tags help the tactic work on clean goals). Needs Zulip discussion before PR since this is novel cross-cutting infrastructure for cslib. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake

---

### 268. Simp grind normalization tags
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [268_simp_grind_normalization_tags/reports/01_team-research.md]
- **Plan**: [268_simp_grind_normalization_tags/plans/02_normalization-tags-plan.md]
- **Summary**: [268_simp_grind_normalization_tags/summaries/02_normalization-tags-summary.md]

**Description**: Add @[simp, scoped grind =] normalization tags to Hilbert system definitional lemmas. Add tags to the normalization/definitional layer across Propositional/, Modal/, Temporal/, and Bimodal/ Hilbert systems. Target: derived connective unfoldings, context manipulation lemmas, listImp equalities, and similar structural/characterization lemmas. Do NOT tag derivability constructors (Derivable.ax, Derivable.mp, etc.) — those are for the proof-search tactic. Follow cslib existing co-tagging convention. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake

---

### 266. Research propositional and foundations improvements
- **Status**: [IMPLEMENTING]
- **Task Type**: formal
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [266_research_propositional_and_foundations_improvements/reports/01_team-research.md]
  - [266_research_propositional_and_foundations_improvements/reports/02_team-research.md]
- **Plan**: [266_research_propositional_and_foundations_improvements/plans/03_propositional-foundations-plan.md]

**Description**: Research improvements to Propositional/ and Foundations/Logic/ in this repo: compose the Hilbert-ND bridge with algebraic completeness for Hilbert-tier corollaries, fix stale ProofSystem.lean documentation, add propositional test coverage, concretize modal/temporal/bimodal ProofSystem tag instances to unlock GenericMCS reuse, extract propositional tableau rules from the bimodal tableau to Foundations/, add HasDia primitive, and assemble a Decidable (Tautology φ) instance. Excludes sequent calculus (split to task 279).

---

### 252. Acceptance conditions zoo
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [252_acceptance_conditions_zoo/reports/01_acceptance-conditions-seed.md]

**Description**: Formalize Rabin and parity acceptance conditions alongside the existing Muller acceptance (DMA) and Büchi acceptance (DBA) in CSLib, and prove the classical conversions between them. Build on the existing infOcc predicate (Cslib/Foundations/Data/OmegaSequence/InfOcc.lean) which already provides the "infinitely often" foundation. Scope: (1) Rabin acceptance — pairs of (Eᵢ, Fᵢ) sets. (2) Parity acceptance — priority coloring. (3) Muller↔Rabin conversion. (4) Rabin↔parity conversion (Piterman 2007). Target: Cslib/Computability/Automata/DA/Rabin.lean, Parity.lean, Conversions.lean

---

### 245. Formula encodable countable instances
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Add Encodable, Countable, and Denumerable instances for LTL Formula type (deferred to completeness PRs)

---

### 241. Mcnaughton theorem
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [241_mcnaughton_theorem/reports/01_ctchou-coordination-seed.md]

**Description**: Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller) establishing equivalence between omega-regular languages and deterministic Muller automata. Research phase should evaluate ctchou/AutomataTheory (independent Lean 4 project that claims McNaughton already proved) for architectural compatibility, portability, and licensing before deciding whether to port, adapt, or develop independently.

---

### 226. Propositional semantics upstream pr
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [226_propositional_semantics_upstream_pr/reports/01_upstream-pr-research.md]
  - [226_propositional_semantics_upstream_pr/reports/02_three-way-comparison.md]

**Description**: Cherry-pick propositional semantics from the local codebase into a <500 LOC follow-up PR stacked on PR #648. PR #648 contributes the formula type and natural deduction; this follow-up adds the semantics layer. Scope: (1) Semantics/Algebra.lean — GHA evaluation with bot_val parameter for minimal/intuitionistic/classical logic. (2) Semantics/Bool.lean — BoolEvaluate with bridge to AlgEvaluate. (3) Semantics/SemanticConsequence.lean — semantic consequence and tautology definitions. (4) Semantics/Kripke.lean — Kripke semantics with botForces for minimal logic (include if LOC budget permits). All four files already exist locally with full implementations. Task is to select, trim, and package for upstream submission. Ensure lake build, lake test, lake exe checkInitImports, lake exe lint-style, and lake shake all pass on the PR branch. Write PR description referencing the Zulip Propositional Logic thread.

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
