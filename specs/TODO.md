---
next_project_number: 334
---

# TODO

## Task Order

*Updated 2026-06-24. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,241,245,278,290,299,301,316,321,329 | -- | Bimodal Porting, Foundations, Propositional Logic, ... |
| 2 | 39,40,181,215,300,317,332 | 36,37,180,290,299,316 | Bimodal Porting, Propositional Logic, Temporal Logic, ... |
| 3 | 41,275,333 | 39,40,332 | Foundations |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

278 [NOT STARTED] — Simplify proofs using new simp/grind normalization tags. After ta
41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
290 [PARTIAL] — Formalize Prawitz-style normalization for CSLib Theory.Derivation
  └─ 332 [IMPLEMENTING] — Prove the normalization termination theorem for CSLib Theory.Deri
    └─ 333 [NOT STARTED] — Refactor and split the 1099-line Normalization.lean into well-org
316 [IMPLEMENTING] — Fill the 6 sorry instances in propositional tableau soundness pro
  └─ 317 [BLOCKED] — Fill the 8 sorry instances in propositional tableau completeness 
329 [NOT STARTED] — Prove the subformula property as a corollary of cut elimination: 

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
241 [NOT STARTED] — Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller)
245 [NOT STARTED] — Add Encodable, Countable, and Denumerable instances for LTL Formu
301 [NOT STARTED] — Implement tableau decision procedure for temporal logic (Cslib.Lo
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
  └─ 275 [BLOCKED] — Prove that Bimodal TM is conservative over Temporal BX for tempor
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Code Hygiene

321 [NOT STARTED] — Review file size and structure throughout Logics/ and Foundations

### Modal

299 [NOT STARTED] — Implement tableau decision procedure for basic modal logic K with
  └─ 300 [NOT STARTED] — Extend modal K tableau (task 299) with frame-specific rules for r

### Uncategorized

## Tasks

### 333. Normalization module refactor
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: Task 332

**Description**: Refactor and split the 1099-line Normalization.lean into well-organized submodules following CSLib conventions. Proposed split: (1) Cslib/Logics/Propositional/NaturalDeduction/Normalization/Basic.lean — isNormal, isStronglyNormal predicates, SubformulaProperty; (2) Normalization/Reduction.lean — reduceRoot, normalizeAux, normalize; (3) Normalization/Termination.lean — redexWeight, sn_redexWeight_zero, redexWeight_zero_sn, normalizeAux_fixpoint, normalize_isStronglyNormal; (4) Normalization/SubformulaProperty.lean — subformula_property_of_isStronglyNormal, subformula_property. Clean up API: review private vs public visibility, ensure naming follows CSLib NOTATION.md and CONTRIBUTING.md conventions. Depends on 332.

---

### 332. Normalization termination proof
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Dependencies**: Task 290

**Description**: Prove the normalization termination theorem for CSLib Theory.Derivation: d.normalize.redexWeight = 0 (the 1 sorry remaining in Normalization.lean line 1083). The proof requires well-founded induction on a (cutrank, total_cut_length) lexicographic measure following Prawitz 1965, Ch. III-IV. Key obstacle: subsOne can increase derivation height, breaking fuel-sufficiency arguments. Needs ~200-300 lines of infrastructure: cutrank definition, cut_length measure, strict decrease lemma for reduceRoot, and the main induction. File: Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean. Depends on 290.

---

### 331. Completed tasks code polish
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Quality
- **Dependencies**: None

**Description**: Polish code from recently completed tasks (310, 312, 322). Three items: (1) Add cross-reference docstrings between ConservativeExtensionChain.lean and MplConservativeChain.lean — the IPL-routed proofs (hilbertMplConservativeOverConjImp, hilbertMplConservativeOverImp) and their direct-algebraic counterparts (_direct variants in MplConservativeChain) prove the same statements via different paths but neither file mentions the other. Add See also references in both directions. (2) Evaluate the thin alias hilbertConjImpConservativeOverImp_direct in ConservativeExtensionChain.lean — it is literally hilbertConjImpConservativeOverImp hITO h with no independent content; add a docstring noting it exists for API symmetry, or inline it. (3) Remove the unused _hφ parameter from hilbertEmbeddingLemma in DiegoEmbedding.lean, or if it is needed for API stability, document why it is retained.

---

### 330. Lj cut admissibility sorry
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Fill the sorry in LJ cutAdmissibility (Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean:103). This is the only sorry in the LJ sequent calculus module (task 315) and it voids the cutElim theorem that depends on it. The proof requires showing that cuts on any formula can be eliminated from cut-free LJ proofs — the standard approach is double induction on cut-formula complexity and proof height, mirroring the LK cut elimination strategy in LK/CutElimination.lean but restricted to the intuitionistic single-succedent constraint. Once filled, LJProof.cutElim becomes fully proven and the LJ subformula property becomes available.

---

### 329. Cutelim subformula property
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 328

**Description**: Prove the subformula property as a corollary of cut elimination: every formula appearing in a cut-free LK proof is a subformula of some formula in the conclusion sequent. Define Proposition.isSubformula, prove CutFreeLKProof.subformula_property, and derive LKProof.subformula_property via cutElim. Place in a new file Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean. This is a standard textbook result that follows directly from the Hauptsatz

---

### 328. Cutelim refactor heartbeats
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 327

**Description**: Refactor CutElimination.lean to reduce or eliminate the maxHeartbeats 800000 override. Extract shared Finset subset-proof helpers (insert membership transport, multi-level weakening combinators) to reduce elaboration cost in the mutual block. Consider splitting the 902-line file: move the four cutAdm_right_* helpers into a CutAdmRight.lean module and keep cutAdmissibility + cutElim in CutElimination.lean. Target: default heartbeats (200000) or at most 400000. Ensure the public API (cutAdmissibility, LKProof.cutElim, CutFreeLKProof.mono) remains unchanged

---

### 327. Cutelim lint ci fixes
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [327_cutelim_lint_ci_fixes/reports/01_lint-ci-fixes.md]
- **Plan**: [327_cutelim_lint_ci_fixes/plans/01_lint-ci-fixes.md]

**Description**: Fix CI lint warnings in CutElimination.lean: add required comment to maxHeartbeats 800000 override, fix 8 long-line warnings (>100 chars), remove unused variable hB. All mechanical fixes required for CI to pass

---

### 326. Tableau lint cleanup
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 324, Task 325

**Description**: Fix ~35 linter warnings across the propositional tableau soundness and completeness modules. By file: (1) Classical/Soundness.lean (~20 warnings): 14 unused section variables ([DecidableEq Atom] and/or [Hashable Atom] on private lemmas and classicalRule_preserves_sat) — add omit annotations; 1 deprecated push_neg at line 639 — replace with push Not; 3 show tactic misuses at lines 207/210/334/336; 3 flexible simp calls at line 468 — replace with simp only. (2) Classical/Completeness.lean (~13 warnings): 8 unused simp arguments at lines 110/111/160/254/326/343/366/387 — remove; 3 dead tactic blocks at lines 468-479 — remove; 2 unused section variables on mem_extendMany_of_mem and hintikka_inv_mono — add omit. (3) Intuitionistic/Soundness.lean (4 warnings): 2 unused section variables on intRule_preserves_sat and intClosed_unsatisfiable — add omit; 2 long lines at 207/281 — break. (4) Minimal/Soundness.lean (1 warning): unused [Hashable Atom] on minClosed_unsatisfiable — add omit. All fixes are mechanical and should not change proof semantics.

---

### 325. Tableau dedup dead code cleanup
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 324

**Description**: Deduplicate identical definitions across minimal/intuitionistic tableau modules and remove dead code from the MinimalClosure bug fix. (A) Deduplication: (1) Delete minBranchSatisfied from Minimal/Soundness.lean:71-78 — it is character-for-character identical to intBranchSatisfied in Intuitionistic/Soundness.lean:55-62 (the docstring even says so). Use intBranchSatisfied everywhere since the botForces parameter already distinguishes minimal from intuitionistic semantics. (2) Delete minExtractValuation from Minimal/Completeness.lean:72-73 — verbatim copy of intExtractValuation in Intuitionistic/Completeness.lean:57-58. Valuation extraction is logic-independent. (3) Standardize naming: extractValuation (classical) has no prefix while int/min versions do. After dedup, only classical extractValuation and intExtractValuation remain, which is consistent enough. (B) Dead code removal: (4) Remove MinimalClosure instance from ClosureCondition.lean:124-134 — isMinimallyClosed now uses Branch.hasContradiction, making this instance dead code. (5) Check if IsAtomic typeclass (ClosureCondition.lean:76-78) and instIsAtomicProposition (Tableau/Defs.lean:113-117) are used anywhere besides MinimalClosure. If not, remove both. (6) Check if atomContradiction constructor in ClosureReason (Closure.lean:60) is used anywhere besides MinimalClosure. If not, remove. Verify no downstream consumers before removing.

---

### 324. Lawfulbeq proposition signedformula
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [324_lawfulbeq_proposition_signedformula/reports/01_lawfulbeq-research.md]
- **Plan**: [324_lawfulbeq_proposition_signedformula/plans/01_lawfulbeq-plan.md]
- **Summary**: [324_lawfulbeq_proposition_signedformula/summaries/01_lawfulbeq-summary.md]

**Description**: Add LawfulBEq instances for Proposition Atom and SignedFormula F L, then remove workaround lemmas. Currently Proposition derives BEq independently from DecidableEq (Defs.lean:92), so the derived BEq uses structural matching rather than decide (a = b). This means eq_of_beq, beq_iff_eq, and all standard BEq<->Eq lemmas fail, forcing custom workaround lemmas: prop_beq_eq (Classical/Soundness.lean:128, private, ~30 lines) and proposition_beq_eq (Minimal/Soundness.lean:87, public, ~30 lines). Fix: (1) In Defs.lean, either derive BEq from DecidableEq via instBEq or keep the derived BEq and prove a LawfulBEq instance. (2) Add conditional LawfulBEq instance for SignedFormula F L when F and L have LawfulBEq. (3) Delete prop_beq_eq from Classical/Soundness.lean and proposition_beq_eq from Minimal/Soundness.lean. (4) Replace all call sites with eq_of_beq or beq_iff_eq: Classical/Soundness.lean callers, Minimal/Completeness.lean:111-113 (currently uses full qualification Cslib.Logic.PL.proposition_beq_eq). (5) Optionally add Repr to Proposition deriving clause for debugging. Eliminates ~60 lines of workaround code across 3 files.

---

### 323. Fix intuitionistic tableau bugs
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [323_fix_intuitionistic_tableau_bugs/reports/01_bug-analysis.md]
- **Plan**: [323_fix_intuitionistic_tableau_bugs/plans/01_bug-fix-plan.md]
- **Summary**: [323_fix_intuitionistic_tableau_bugs/summaries/01_bug-fix-summary.md]

**Description**: Fix two intuitionistic tableau implementation bugs: (1) isIntuitionisticallyClosed missing complementary-pair closure check — only checks T(⊥) but should also check Branch.hasContradiction, causing valid formulas like p→p to return .openBranch; (2) intTImpRule uses Nat ordering (· ≥ w) as Kripke accessibility proxy, but this fires at sibling worlds that are NOT accessible, causing invalid formula ((p→⊥)→q)∨(p→r) to incorrectly close. Fix requires: (a) add || Branch.hasContradiction b to isIntuitionisticallyClosed in Expansion.lean:67, (b) track parent-child accessibility in expansion state and restrict intTImpRule in Rules.lean:129 to fire only along actual accessibility paths. Both bugs verified by #eval. See specs/316_propositional_tableau_soundness/reports/04_b4-hard-research.md and .orchestrator-handoff.json for detailed analysis and counterexamples

---

### 322. Mpl conservative extension chain
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 311, Task 312
- **Research**: [322_mpl_conservative_extension_chain/reports/01_mpl-chain-research.md]
- **Plan**: [322_mpl_conservative_extension_chain/plans/01_mpl-chain-plan.md]
- **Summary**: [322_mpl_conservative_extension_chain/summaries/01_mpl-chain-summary.md]

**Description**: Establish the MPL conservative extension chain as standalone results and organize the relationship between the IPL and MPL chains. Specifically: (1) Prove MPL → ConjImp conservativity for or-free formulas (GHAValid → BrouwerianValid, requiring a free join/distributive lattice completion of BrouwerianSemilattices to GHAs). (2) Prove MPL → Imp conservativity for imp-top-only formulas as a composition. (3) Organize the full algebraic picture: state the MPL chain (ImpAxiom ⊂ ConjImpAxiom ⊂ MinPropAxiom) with its own conservativity results independent of IPL, and relate it to the IPL chain via the IPL → MPL conservativity bridge. File: Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean

---

### 321. Code hygiene logics foundations
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Review file size and structure throughout Logics/ and Foundations/ to identify and refactor files that are too long or poorly structured. Abstract and expose all and only what should be abstracted/exposed, maintaining the highest standards for code hygiene. Survey file lengths, identify candidates over ~400 lines, check for proper module boundaries, unnecessary public exports, missing abstraction barriers, and violations of single-responsibility principle. Produce a refactoring plan with prioritized actions

---

### 320. Remove nd metalogic cleanup
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Remove ND-level metalogic that has been superseded by Hilbert-primary results. The Hilbert systems now prove deduction theorem, strong completeness, compactness, decidability, and the algebraic conservativity/Glivenko chain directly. ND should keep soundness and the extensional equivalence to Hilbert, but no longer needs standalone completeness theorems or the duplicate Lindenbaum infrastructure used only to derive them. Clean up: (1) Deprecate or remove `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`, and `alg_complete_classical` in `Semantics/Algebra/Completeness.lean`; replace downstream uses with the Hilbert-primary theorems (`MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete`) composed through `hilbert_iff_nd_ctx` equivalences. (2) Simplify or remove `HilbertConservativeGlivenko.lean` algebraic bridges if they are no longer needed for ND corollaries; keep only the equivalences required by other modules. (3) Remove or consolidate duplicate ND Lindenbaum algebra material that is only used for ND completeness. (4) Update module docstrings in `Semantics/Algebra.lean`, `Semantics/Algebra/Completeness.lean`, and related files to state that Hilbert is the primary proof system and ND inherits results via equivalence. (5) Fix imports and barrel files affected by deletions. (6) Ensure the build is `sorry`-free and all downstream modules (sequent calculus, tableau, modal/temporal embeddings) still compile.

---

### 319. Minimal tableau infrastructure
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 316, Task 317
- **Research**: [319_minimal_tableau_infrastructure/reports/01_minimal-tableau-research.md]
- **Plan**: [319_minimal_tableau_infrastructure/plans/02_implementation-plan.md]
- **Summary**: [319_minimal_tableau_infrastructure/summaries/03_implementation-summary.md]

**Description**: Build dedicated Soundness and Completeness modules for the minimal propositional tableau, matching the structure of the classical and intuitionistic systems. Currently the minimal system has only DecisionProcedure.lean (135 lines) with sorry-marked theorems, while classical has 4 modules (795 lines) and intuitionistic has 5 modules (908 lines). The minimal tableau shares the intuitionistic rules and expansion loop (intExpandBranches with isMinimallyClosed), so no separate Rules.lean or Expansion.lean is needed. Create: (1) Minimal/Soundness.lean — define minRule_preserves_sat (each rule preserves branch satisfiability in any Kripke model with arbitrary botForces, not just fun _ => False), minClosed_unsatisfiable (MinimalClosure T(p)/F(p) contradiction is unsatisfiable since val w p ↔ ¬val w p), and prove minimalTableau_sound. Key difference from intuitionistic: closure is on complementary atoms only, and botForces is unconstrained. (2) Minimal/Completeness.lean — construct countermodel from open saturated branch with botForces w = (T(⊥) at w on branch), prove truth lemma by formula induction, and prove minimalTableau_complete. Key difference from intuitionistic: the countermodel allows bot to be forced at some worlds. (3) Refactor DecisionProcedure.lean to import the new modules, keeping only the Decidable instances and the minimalTableau_decides bridge theorem. (4) Update Cslib.lean barrel imports via lake exe mk_all.

---

### 317. Propositional tableau completeness
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 316, Task 323

**Description**: Fill the 8 sorry instances in propositional tableau completeness proofs across all three logics. Classical (Classical/Completeness.lean): prove classicalOpenBranch_countermodel (open saturated branch yields a Boolean valuation falsifying phi) and classicalTableau_complete (if phi is not a Tautology then the tableau has an open branch), plus one helper — by constructing a valuation from the positive atoms in the saturated branch and proving a truth lemma by formula induction. Intuitionistic (Intuitionistic/Completeness.lean): prove intuitionisticOpenBranch_countermodel (open saturated branch yields a finite Kripke model refuting phi) and intuitionisticTableau_complete — by constructing worlds from the branch world indices, accessibility from the expansion record, valuation from positive atoms, and proving a truth lemma showing forced/not-forced matches signed formulas at each world. Minimal (Minimal/DecisionProcedure.lean): prove minimalTableau_complete (if phi is not MValid then the tableau has an open branch) — adapts intuitionistic proof with MinimalClosure and botForces=false. Core technique: Hintikka-set argument — saturated branches satisfy Hintikka conditions, from which countermodels are extracted.

---

### 316. Propositional tableau soundness
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 323
- **Research**:
  - [316_propositional_tableau_soundness/reports/01_soundness-research.md]
  - [316_propositional_tableau_soundness/reports/02_blockers-resolution.md]
- **Plan**: [316_propositional_tableau_soundness/plans/01_soundness-plan.md]

**Description**: Fill the 6 sorry instances in propositional tableau soundness proofs across all three logics. Classical (Classical/Soundness.lean): prove classically_closed_unsatisfiable (closed branch is unsatisfiable under any Boolean valuation) and classicalTableau_sound (closed tableau implies Tautology phi), plus one helper lemma — by induction on rule applications showing each propositional rule preserves satisfiability. Intuitionistic (Intuitionistic/Soundness.lean): prove intuitionisticTableau_sound (closed tableau implies IValid phi) plus two helper lemmas — by showing each rule (including world-creating F(imp) and persistent T(imp)) preserves forcing at Kripke worlds. Minimal (Minimal/DecisionProcedure.lean): prove minimalTableau_sound (closed tableau implies MValid phi) — adapts intuitionistic proof with MinimalClosure (complementary atoms only, no ex falso). Core technique: induction on expansion steps showing each rule application preserves the semantic invariant for the respective logic.

---

### 315. Lj intuitionistic sequent calculus
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 314

**Description**: Implement the intuitionistic sequent calculus LJ for propositional logic.

---

### 314. Lk classical sequent calculus
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [314_lk_classical_sequent_calculus/reports/01_lk-research.md]
  - [314_lk_classical_sequent_calculus/reports/02_cutelim-rewrite-research.md]
- **Plan**: [314_lk_classical_sequent_calculus/plans/01_lk-plan.md]

**Description**: Implement the classical sequent calculus LK for propositional logic. Create shared definitions (Defs.lean with LKSequent type, scoped notation), LK proof inductive with all-additive Finset-based presentation (LK/Basic.lean), structural admissibility lemmas (weakening, monotone contexts), soundness (LK/Soundness.lean), cut elimination / Hauptsatz (LK/CutElimination.lean) via lexicographic induction on (formula complexity, height sum), and equivalence bridges hilbert_iff_lk and nd_iff_lk composed through existing ND bridge. Completeness follows as corollary via Hilbert bridge. File layout: Cslib/Logics/Propositional/SequentCalculus/{Defs,LK/Basic,LK/Soundness,LK/CutElimination,LK/Completeness}.lean. Reuse Proposition type, Proposition.complexity, InferenceSystem typeclass, and existing hilbert_iff_nd_ctx bridge. Parent task: 279.

Literature sources:
- specs/literature/sources/negri_von_plato_2001/section04_ch3-classical-sequent-calculus.md — G3cp rules, admissibility of structural rules, completeness (primary reference for LK design)
- specs/literature/sources/troelstra_schwichtenberg_2000/section04_ch3-gentzen-systems.md — LK/LJ definitions, G3-style systems, structural rules
- specs/literature/sources/troelstra_schwichtenberg_2000/section05_ch4-cut-elimination.md — Hauptsatz proof structure, subformula property, termination argument
- specs/literature/sources/negri_von_plato_2001/section06_ch5-variant-sequent-calculi.md — Alternative calculus designs, independent contexts
- specs/literature/sources/negri_von_plato_2001/section07_ch6-8-extensions-translations.md — ND-SC translations for bridge proofs
- specs/literature/sources/gentzen_1935/gentzen_1935_sec03.md — Original LK/LJ definitions and Hauptsatz

---

### 312. Unified conservative extension chain
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 311

**Description**: Consolidate the full conservative extension chain into a unified module: IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ MPL ⊂ IPL ⊂ CPL, where each ⊂ denotes conservative extension for the smaller fragments language. State the chain theorem and derive inter-fragment conservativity as corollaries — e.g., IPL⟨∧,→,⊤⟩ conservative over IPL⟨→,⊤⟩ by composing the two embeddings through IPL. Include the algebraic validity subsumption chain: HilbertAlgValid → BrouwerianValid → GHAValid → HAValid → BAValid. Provide the full picture connecting all five levels of algebraic semantics (Hilbert algebras, Brouwerian semilattices, GHAs, HAs, BAs) to their proof systems (ImpAxiom, ConjImpAxiom, MinPropAxiom, IntPropAxiom, PropositionalAxiom). This is the capstone module demonstrating the algebraic method for propositional logic — each connective extension is genuinely conservative, each algebra class has sound and complete proof theory, and each completion construction provides the bridge. File: Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean.

---

### 311. Ipl conservative over imp
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 309, Task 310
- **Research**:
  - [311_ipl_conservative_over_imp/reports/01_conservative-extension-research.md]
  - [311_ipl_conservative_over_imp/reports/02_dual-ordering-research.md]
  - [311_ipl_conservative_over_imp/reports/03_blocker-unblock-research.md]
- **Plan**: [311_ipl_conservative_over_imp/plans/01_conservative-imp-plan.md]

**Description**: Prove the conservative extension theorem: IPL is conservative over IPL⟨→,⊤⟩ for imp-top-only formulas. Statement: if Derivable IntPropAxiom φ and φ.IsImpTopOnly = true, then Derivable ImpAxiom φ. Proof route: (1) IPL.hilbert_alg_complete.mp converts to HA-validity, (2) for any HilbertAlgebra H and valuation v, instantiate HA-validity at the Diego embedding HA(H), (3) the Diego embedding lemma rewrites back to HilbertEvaluate v φ = ⊤ in H, (4) Hilbert algebra completeness converts back to Derivable ImpAxiom φ. Derive the ND corollary. This is the deepest result in the chain, showing that conjunction, disjunction, and falsum are all independent of the pure implication fragment. Connects to typed SKI combinators: the derivable imp-top-only formulas are exactly the types inhabited by typed combinatory terms. File: Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean.

---

### 310. Diego embedding
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 304
- **Research**: [310_diego_embedding/reports/01_diego-embedding-research.md]
- **Plan**: [310_diego_embedding/plans/01_diego-embedding-plan.md]

**Description**: Formalize the Diego embedding theorem (Diego 1966): every Hilbert algebra embeds into a Heyting algebra preserving the implication operation and top element. Given a HilbertAlgebra H, construct a HeytingAlgebra HA(H) and an order-embedding ι : H → HA(H) such that ι(a ⇨ b) = ι(a) ⇨ ι(b) and ι(⊤) = ⊤. The classical construction uses the lattice of filters of H: a filter F ⊆ H is a non-empty upward-closed set closed under ⇨-detachment (a ∈ F and a ⇨ b ∈ F implies b ∈ F). The filter lattice ordered by inclusion forms a Heyting algebra, and ι(a) = {F | a ∈ F} is the embedding. Prove: (1) the filter lattice is a HeytingAlgebra, (2) ι preserves ⇨ and ⊤, (3) ι is injective (order-embedding), (4) the embedding lemma: for imp-top-only formulas, HilbertEvaluate v φ = ⊤ ↔ AlgEvaluate (ι ∘ v) ⊥ φ = ⊤. This is the most technically demanding algebraic construction in the chain. References: Diego (1966), Köhler (1981), Celani-Jansana (2012). File: Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean.

---

### 301. Temporal tableau
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Implement tableau decision procedure for temporal logic (Cslib.Logic.Temporal.Formula) with until/since decomposition rules, time labels, and temporal ordering tracking. Most complex new tableau: until/since rules have no modal analogue, requiring branching decomposition with event-witness and guard-continue alternatives. Adapt patterns from bimodal decidability system (TimeOrdering, temporal rule structure, frame-class rules) but build fresh implementations on shared Foundations infrastructure. Include density and discreteness frame-class rules. Formula type has atom, bot, imp, untl, snce primitives using Lukasiewicz encoding. Files under Cslib/Logics/Temporal/Tableau/: Defs.lean, Rules.lean, TimeOrdering.lean, Branch.lean, Closure.lean, Saturation.lean, Soundness.lean, Completeness.lean. Estimated: 2,000-2,500 lines.

---

### 300. Modal extensions t s4 s5
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal
- **Dependencies**: Task 299

**Description**: Extend modal K tableau (task 299) with frame-specific rules for reflexive (T), transitive (S4), and equivalence-relation (S5) frames. T: reflexivity rule (box phi at w implies phi at w). S4: transitivity-aware propagation with loop-checking for termination. S5: equivalence-class simplification (mirrors bimodal approach). Include rules for B (symmetric) and 5 (Euclidean) to cover full modal cube. Each extension needs own completeness proof showing extracted countermodel satisfies frame condition. Files: FrameRules.lean, LoopChecking.lean, S5Simplification.lean, FrameSoundness.lean, FrameCompleteness.lean. Estimated: 1,200-1,800 lines.

---

### 299. Modal k tableau
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal
- **Dependencies**: None

**Description**: Implement tableau decision procedure for basic modal logic K with world labels, box/diamond rules on top of propositional rules from shared infrastructure. Introduces world labels (accessibility relation tracking) and fundamental modal rule pattern: box-positive is universal/persistent, diamond-positive is existential (fresh accessible world). Use Lukasiewicz encoding for and/or. Prove soundness against Kripke semantics and completeness by extracting finite Kripke countermodels. Modal formula type: Cslib.Logic.Modal.Formula with atom, bot, imp, box primitives. Files under Cslib/Logics/Modal/Tableau/: Defs.lean, Rules.lean, Branch.lean, Closure.lean, Saturation.lean, Soundness.lean, Completeness.lean. Estimated: 1,500-2,000 lines.

---

### 296. Tableau calculi architecture
- **Status**: [EXPANDED]
- **Task Type**: formal
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [296_tableau_calculi_architecture/reports/01_tableau-arch-research.md]
- **Plan**: [296_tableau_calculi_architecture/plans/01_tableau-arch-plan.md]

**Description**: Research and design a unified tableau calculi architecture for CSLib spanning propositional, modal, temporal, and bimodal logics. The existing PropositionalTableau.lean provides generic rule infrastructure (PropSign, PropSignedFormula, PropTableauRule, applyPropRule) already consumed by the bimodal decidability system (~5,900 lines). The goal is to determine how to build a complete propositional tableau system (branch construction, closure, termination, soundness, completeness, decision procedure) that naturally extends to modal and temporal tableau systems, sharing resources with and relating cleanly to the existing bimodal tableau. Investigate: (1) what generic tableau infrastructure should live in Foundations/ vs logic-specific modules, (2) how modal tableau rules (box/diamond) and temporal rules (until/since) layer on top of propositional rules, (3) whether the bimodal tableau can be refactored to consume shared infrastructure or whether it should remain standalone, (4) what the dependency chain should be between propositional, modal, temporal tableau tasks, (5) how tableau completeness relates to the existing MCS-based completeness proofs and the planned sequent calculus (task 279). Output: a set of precisely scoped implementation tasks with dependency graph covering the full tableau pipeline from propositional through bimodal.

---

### 293. Curry howard nd typed lambda
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 290
- **Summary**: [293_curry_howard_nd_typed_lambda/summaries/01_curry-howard-summary.md]

**Description**: Establish the formal Curry-Howard isomorphism between Theory.Derivation Gamma A (propositional ND proofs) and well-typed lambda terms. Define a purpose-built simply-typed term language over PL.Proposition as the type language. Formalize: (1) curry_howard_forward extracting a well-typed term from a derivation, (2) curry_howard_backward extracting a derivation from a well-typed term, (3) roundtrip properties showing the maps are mutually inverse. Map ND constructors to term constructors: impI to lambda, impE to application, andI to pair, andE1/2 to projections, orI1/2 to injections, orE to case. As a reduced-scope fallback, the {arrow, and} fragment is a self-contained milestone. Normal derivations correspond to beta-normal terms. Files: new directory Cslib/Logics/Propositional/CurryHoward/. Depends on the normalization task (290).

---

### 292. Ipl decidability cutfree lj
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 315
- **Research**: [292_ipl_decidability_cutfree_lj/reports/01_decidability-research.md]
- **Plan**: [292_ipl_decidability_cutfree_lj/plans/01_decidability-plan.md]

**Description**: After task 279 delivers LJ with cut elimination, formalize the connection between cut-free proof search and decidability. Define a bounded backward proof search procedure over cut-free LJ: the search space is finite because all formulas in a cut-free proof are subformulas of the sequent. Prove termination via a well-founded measure. Produce Decidable (LJDerivable (Gamma |- A)) and lift via nd_iff_lk to Decidable (DerivableIn IPL (Gamma |- A)). File: Cslib/Logics/Propositional/SequentCalculus/Decidability.lean. Depends on 279.

---

### 291. Three way proof system equivalence
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 314, Task 315

**Description**: Three-way proof system equivalence as TFAE theorems for CPL, IPL, and MPL.

---

### 290. Nd normalization subformula property
- **Status**: [PARTIAL]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Summary**: [290_nd_normalization_subformula_property/summaries/01_nd-normalization-summary.md]
- **Lean**: [Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean]
- **Research**: [290_nd_normalization_subformula_property/reports/03_termination-measure-research.md]
- **Plan**: [290_nd_normalization_subformula_property/plans/04_nd-normalization-plan-v3.md]

**Description**: Formalize Prawitz-style normalization for CSLib Theory.Derivation (propositional IPL and MPL). Define Derivation.isNormal predicate (no maximal formula -- i.e., no introduction rule immediately followed by the corresponding elimination on the same formula). Prove a normalization function normalize that transforms any derivation into a normal form. Derive the subformula property as a corollary: every formula in a normal derivation is a subformula of the conclusion or a hypothesis. The Theory.Derivation type is Type u (not Prop), enabling a computable normalization function. Reference: [Prawitz1965] Ch. IV-V. Consider starting with the implicational fragment ({arrow} only) as a milestone, then extending to full IPL connectives. Files: new module Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean. Depends on 266.

---

### 279. Propositional sequent calculus lk lj
- **Status**: [EXPANDED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-a-findings.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_team-research.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-b-findings.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-c-findings.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-d-findings.md]
- **Plan**: [279_propositional_sequent_calculus_lk_lj/plans/02_sequent-calculus-plan.md]

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
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/01_tm-over-bx-conservativity.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/02_teammate-a-findings.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/02_teammate-b-findings.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/02_teammate-c-findings.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/02_teammate-d-findings.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/03_teammate-a-findings.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/03_teammate-b-findings.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/03_teammate-c-findings.md]
  - [275_bimodal_tm_conservative_over_temporal_bx/reports/03_teammate-d-findings.md]
- **Plan**: [275_bimodal_tm_conservative_over_temporal_bx/plans/01_tm-over-bx-plan.md]

**Description**: Prove that Bimodal TM is conservative over Temporal BX for temporal formulas (those using only until/since, no box). The Temporal.Formula.toBimodal embedding exists. The lift_derivation_qfree infrastructure in Bimodal/Metalogic/ConservativeExtension/ partially supports this. Requires verifying the lifting extends to temporal connectives.

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
- **Research**: [215_fill_bimodal_sorries/reports/01_sorry-analysis.md]

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
