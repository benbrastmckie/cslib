---
next_project_number: 261
---

# TODO

## Task Order

*Updated 2026-06-21. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,241,243,245,250,251,252,255,256,259 | -- | Bimodal Porting, Propositional Logic, Temporal Logic |
| 2 | 39,40,181,215,257,260 | 36,37,180,255,256 | Bimodal Porting, Temporal Logic |
| 3 | 41,258 | 39,40,257 | Foundations, Temporal Logic |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Prepare a follow-up upstream PR (~400-500 LOC) stacked on PR #648

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
241 [NOT STARTED] — Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller)
243 [NOT STARTED] — Implement deterministic Büchi automata constructions and related 
245 [NOT STARTED] — Add Encodable, Countable, and Denumerable instances for LTL Formu
250 [RESEARCHING] — Implement NBA complementation: given an NBA A, construct an NBA a
251 [RESEARCHING] — Implement the synchronous product construction of an LTS (using e
252 [NOT STARTED] — Formalize Rabin and parity acceptance conditions alongside the ex
255 [PLANNED] — Fix stale docstrings and comments left over from the task-254 LTL
  └─ 260 [NOT STARTED] — Add module-level documentation contrasting the LTL and Temporal c
256 [PLANNED] — Add @[simp] unfold lemmas for LTL.Satisfies to match the pattern 
  └─ 257 [NOT STARTED] — Fix style issues in GNBA.lean: (1) Break 7 lines exceeding 100 ch
    └─ 258 [NOT STARTED] — Refactor duplicated proof patterns in GNBA.lean. Currently subfor
259 [PLANNED] — Narrow file-wide linter suppressions in Temporal/Metalogic/ to de
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

## Tasks

### 260. Add ltl temporal convention contrast docs
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 255

**Description**: Add module-level documentation contrasting the LTL and Temporal convention differences. (1) In the LTL module docstring (Formula.lean or a new LTL.lean barrel file header), add a note explaining that LTL uses standard convention (guard U event, notation ◯/𝓤/◇/□) while Temporal uses Burgess convention (event U guard, notation X/U/𝐅/𝐆), and that Embedding.lean bridges the two via reflexiveUntl. (2) In Temporal/Syntax/Formula.lean module docstring, add a cross-reference noting the convention difference from LTL. (3) In Connectives.lean, add a brief note that HasSince/TemporalConnectives/BimodalConnectives serve Temporal and Bimodal modules while HasUntil/HasNext/FutureTemporalConnectives/LTLConnectives serve LTL.

---

### 259. Narrow temporal metalogic linter suppressions
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Narrow file-wide linter suppressions in Temporal/Metalogic/ to declaration-level scope. Currently 13 file-wide set_option linter.* suppressions exist across 4 files: CompletenessHelpers.lean (3: style.setOption, unusedSimpArgs, flexible), DenseCompleteness.lean (4: unusedSectionVars, unusedSimpArgs, style.setOption, dupNamespace), GeneralizedNecessitation.lean (4: unusedSimpArgs, style.setOption, flexible, style.emptyLine), TemporalContent.lean (2: style.emptyLine, style.longLine). For each suppression: (a) try removing it and see which declarations fail, (b) move the set_option to just those declarations using `set_option ... in`, (c) where possible, fix the underlying issue (remove unused simp args, fix empty lines, break long lines) instead of suppressing. Goal: zero file-wide suppressions, or document why any remaining ones are unavoidable.

---

### 258. Refactor gnba duplicated subformula proofs
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 257

**Description**: Refactor duplicated proof patterns in GNBA.lean. Currently subformulas_untl_left, subformulas_untl_right, subformulas_imp_left, subformulas_imp_right (lines ~236-333) are four near-identical inductive proofs. Similarly untl_left_mem_closure, untl_right_mem_closure, imp_left_mem_closure, imp_right_mem_closure, subformulas_subset_closure (lines ~358-396) follow the same pattern. Refactor each group into a single parameterized lemma with a case dispatch or a shared helper, reducing code duplication while preserving all downstream usage sites. Ensure lake build passes.

---

### 257. Fix gnba long lines and style
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 256

**Description**: Fix style issues in GNBA.lean: (1) Break 7 lines exceeding 100 characters (lines 912, 929, 1023, 1352, 1421, 1427, 1435) — these involve deeply nested gnbaAcceptSet expressions that can be split with let bindings or intermediate names. (2) Rename instInhabitedSetAtom in OmegaRegular.lean:142 to follow Mathlib instance naming conventions (anonymous instance or Set.instInhabited pattern). Ensure lake build passes after all changes.

---

### 256. Add ltl satisfies simp lemmas
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Add @[simp] unfold lemmas for LTL.Satisfies to match the pattern in Temporal/Semantics/Satisfies.lean. Currently LTL's Satisfies is a bare def with no simp lemmas, while Temporal has atom_iff, imp_iff, bot_iff, etc. Add analogous @[simp] lemmas for each constructor: atom, bot, imp, next, untl, plus derived operators someFuture, allFuture, and the leadsto abbreviation. This improves proof automation so downstream files (GNBA, OmegaRegular) can use `simp [Satisfies]` more effectively.

---

### 255. Fix stale ltl docstrings post task254
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Fix stale docstrings and comments left over from the task-254 LTL convention revision. (1) Embedding.lean:15 — module docstring says "Burgess-temporal counterparts"; rewrite to explain that LTL uses standard convention while Temporal uses Burgess, and the embedding bridges the two. (2) Formula.lean:75 — next constructor docstring says "Xφ holds at t"; change to "◯φ holds at t". (3) Embedding.lean:49 — parameter names ψ/φ in the untl match arm are swapped relative to LTL's standard convention (guard=φ₁, event=φ₂); rename for clarity or add an inline comment explaining the swap is intentional due to Temporal's Burgess order. (4) OmegaRegular.lean:310 — docstring says "matches the original proof_wanted"; the proof is now complete, so remove or rephrase the reference.

---

### 252. Acceptance conditions zoo
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [252_acceptance_conditions_zoo/reports/01_acceptance-conditions-seed.md]

**Description**: Formalize Rabin and parity acceptance conditions alongside the existing Muller acceptance (DMA) and Büchi acceptance (DBA) in CSLib, and prove the classical conversions between them. Build on the existing infOcc predicate (Cslib/Foundations/Data/OmegaSequence/InfOcc.lean) which already provides the "infinitely often" foundation. Scope: (1) Rabin acceptance — pairs of (Eᵢ, Fᵢ) sets. (2) Parity acceptance — priority coloring. (3) Muller↔Rabin conversion. (4) Rabin↔parity conversion (Piterman 2007). Target: Cslib/Computability/Automata/DA/Rabin.lean, Parity.lean, Conversions.lean

---

### 251. Product construction model checking
- **Status**: [RESEARCHING]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 248
- **Research**:
  - [251_product_construction_model_checking/reports/01_product-model-checking-seed.md]
  - [251_product_construction_model_checking/reports/02_literature-sources.md]

**Description**: Implement the synchronous product construction of an LTS (using existing Cslib/Foundations/Semantics/LTS/ infrastructure) with an NBA, and prove the model checking reduction: an LTS M satisfies an LTL property φ iff the product of M with the NBA for ¬φ has an empty language. The existing OmegaExecution type and SatisfiesExec bridge (Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean) already connect LTL satisfaction to LTS runs via a labeling function State → (Atom → Prop). The main new work is: (1) the system × NBA product construction (distinct from the existing automaton × automaton products in NA/Prod.lean), (2) the correctness proof linking product acceptance to LTL satisfaction. Target: Cslib/Computability/Automata/NA/LTSProduct.lean and Cslib/Logics/LTL/ModelChecking.lean

---

### 250. Nba complementation
- **Status**: [RESEARCHING]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**:
  - [250_nba_complementation/reports/01_nba-complementation-seed.md]
  - [250_nba_complementation/reports/02_literature-sources.md]

**Description**: Implement NBA complementation: given an NBA A, construct an NBA accepting the complement language Σ^ω \ L(A). Two main approaches: (1) determinization-based — determinize via McNaughton/Safra then complement the deterministic automaton (depends on task 241), (2) direct rank-based construction (Kupferman-Vardi 2001, Schewe 2009) avoiding full determinization. CSLib already has ω-regular complementation at the language-theoretic level via Büchi congruence; this task provides the automata-level construction needed for algorithmic applications (language inclusion, model checking). Target: Cslib/Computability/Automata/NA/Complement.lean

---

### 248. Nba emptiness checking
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [248_nba_emptiness_checking/reports/01_nba-emptiness-seed.md]
- **Plan**: [248_nba_emptiness_checking/plans/01_emptiness-plan.md]

**Description**: Implement NBA emptiness checking: decide whether a nondeterministic Büchi automaton accepts any ω-word. Two approaches: (1) nested DFS (Courcoubetis-Vardi-Wolper-Yannakakis 1992) finding a reachable accepting cycle, or (2) SCC-based algorithm checking for accepting SCCs reachable from the initial state. The existing infOcc predicate (Cslib/Foundations/Data/OmegaSequence/InfOcc.lean) and NBA Büchi acceptance (NA/Basic.lean using Filter.Frequently/atTop) provide the acceptance-condition foundation. This is the key building block connecting LTL-to-NBA translation to model checking. Target: Cslib/Computability/Automata/NA/Emptiness.lean

---

### 245. Formula encodable countable instances
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Add Encodable, Countable, and Denumerable instances for LTL Formula type (deferred to completeness PRs)

---

### 243. Deterministic buchi automata
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Implement deterministic Büchi automata constructions and related results

---

### 242. Vardi wolper tableau construction
- **Status**: [COMPLETED]
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
