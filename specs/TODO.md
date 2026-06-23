---
next_project_number: 313
---

# TODO

## Task Order

*Updated 2026-06-23. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,241,245,278,279,290,297,302,303,304 | -- | Bimodal Porting, Foundations, Propositional Logic, ... |
| 2 | 39,40,181,215,291,292,293,298,305,307,310 | 36,37,180,279,290,297,302,303,304 | Bimodal Porting, Propositional Logic, Temporal Logic, ... |
| 3 | 41,275,299,301,306,309 | 39,40,298,303,304,305 | Foundations, Temporal, Modal, ... |
| 4 | 300,308,311 | 299,306,307,309,310 | Modal, Algebraic Semantics |
| 5 | 312 | 308,311 | Algebraic Semantics |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

278 [NOT STARTED] — Simplify proofs using new simp/grind normalization tags. After ta
297 [IMPLEMENTING] — Build shared tableau infrastructure in Foundations/Logic/Tableau/
41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
279 [NOT STARTED] — Implement a two-sided Gentzen-style sequent calculus (LK for clas
  └─ 291 [NOT STARTED] — After task 279 delivers hilbert_iff_lk and nd_iff_lk, create a un
  └─ 292 [NOT STARTED] — After task 279 delivers LJ with cut elimination, formalize the co
290 [NOT STARTED] — Formalize Prawitz-style normalization for CSLib Theory.Derivation
  └─ 293 [NOT STARTED] — Establish the formal Curry-Howard isomorphism between Theory.Deri

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
241 [NOT STARTED] — Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller)
245 [NOT STARTED] — Add Encodable, Countable, and Denumerable instances for LTL Formu
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
  └─ 275 [BLOCKED] — Prove that Bimodal TM is conservative over Temporal BX for tempor
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Propositional

298 [NOT STARTED] — Implement propositional tableau systems for all three proposition

### Modal

299 [NOT STARTED] — Implement tableau decision procedure for basic modal logic K with
  └─ 300 [NOT STARTED] — Extend modal K tableau (task 299) with frame-specific rules for r

### Temporal

301 [NOT STARTED] — Implement tableau decision procedure for temporal logic (Cslib.Lo

### Algebraic Semantics

302 [NOT STARTED] — Define syntactic fragment predicates on Proposition analogous to 
  └─ 305 [NOT STARTED] — Define fragment-specific Hilbert axiom predicates for the two sub
    └─ 306 [NOT STARTED] — Prove soundness and completeness of IPL⟨∧,→,⊤⟩ w.r.t. Brouwerian 
      └─ 308 [NOT STARTED] — Prove the conservative extension theorem: IPL is conservative ove
        └─ 312 [NOT STARTED] — Consolidate the full conservative extension chain into a unified 
    └─ 309 [NOT STARTED] — Prove soundness and completeness of IPL⟨→,⊤⟩ w.r.t. Hilbert algeb
      └─ 311 [NOT STARTED] — Prove the conservative extension theorem: IPL is conservative ove
        └─ 312 [NOT STARTED] — Consolidate the full conservative extension chain into a unified  (see above)
  └─ 307 [NOT STARTED] — Construct a HeytingAlgebra from any BrouwerianSemilattice via a f
    └─ 308 [NOT STARTED] — Prove the conservative extension theorem: IPL is conservative ove (see above)
303 [NOT STARTED] — Define the BrouwerianSemilattice typeclass: SemilatticeInf + Orde
  └─ 306 [NOT STARTED] — Prove soundness and completeness of IPL⟨∧,→,⊤⟩ w.r.t. Brouwerian  (see above)
  └─ 307 [NOT STARTED] — Construct a HeytingAlgebra from any BrouwerianSemilattice via a f (see above)
304 [NOT STARTED] — Define the HilbertAlgebra typeclass: a structure (H, ⇨, ⊤) satisf
  └─ 309 [NOT STARTED] — Prove soundness and completeness of IPL⟨→,⊤⟩ w.r.t. Hilbert algeb (see above)
  └─ 310 [NOT STARTED] — Formalize the Diego embedding theorem (Diego 1966): every Hilbert
    └─ 311 [NOT STARTED] — Prove the conservative extension theorem: IPL is conservative ove (see above)

### Uncategorized

## Tasks

### 312. Unified conservative extension chain
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 308, Task 311

**Description**: Consolidate the full conservative extension chain into a unified module: IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ MPL ⊂ IPL ⊂ CPL, where each ⊂ denotes conservative extension for the smaller fragments language. State the chain theorem and derive inter-fragment conservativity as corollaries — e.g., IPL⟨∧,→,⊤⟩ conservative over IPL⟨→,⊤⟩ by composing the two embeddings through IPL. Include the algebraic validity subsumption chain: HilbertAlgValid → BrouwerianValid → GHAValid → HAValid → BAValid. Provide the full picture connecting all five levels of algebraic semantics (Hilbert algebras, Brouwerian semilattices, GHAs, HAs, BAs) to their proof systems (ImpAxiom, ConjImpAxiom, MinPropAxiom, IntPropAxiom, PropositionalAxiom). This is the capstone module demonstrating the algebraic method for propositional logic — each connective extension is genuinely conservative, each algebra class has sound and complete proof theory, and each completion construction provides the bridge. File: Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean.

---

### 311. Ipl conservative over imp
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 309, Task 310

**Description**: Prove the conservative extension theorem: IPL is conservative over IPL⟨→,⊤⟩ for imp-top-only formulas. Statement: if Derivable IntPropAxiom φ and φ.IsImpTopOnly = true, then Derivable ImpAxiom φ. Proof route: (1) IPL.hilbert_alg_complete.mp converts to HA-validity, (2) for any HilbertAlgebra H and valuation v, instantiate HA-validity at the Diego embedding HA(H), (3) the Diego embedding lemma rewrites back to HilbertEvaluate v φ = ⊤ in H, (4) Hilbert algebra completeness converts back to Derivable ImpAxiom φ. Derive the ND corollary. This is the deepest result in the chain, showing that conjunction, disjunction, and falsum are all independent of the pure implication fragment. Connects to typed SKI combinators: the derivable imp-top-only formulas are exactly the types inhabited by typed combinatory terms. File: Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean.

---

### 310. Diego embedding
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 304

**Description**: Formalize the Diego embedding theorem (Diego 1966): every Hilbert algebra embeds into a Heyting algebra preserving the implication operation and top element. Given a HilbertAlgebra H, construct a HeytingAlgebra HA(H) and an order-embedding ι : H → HA(H) such that ι(a ⇨ b) = ι(a) ⇨ ι(b) and ι(⊤) = ⊤. The classical construction uses the lattice of filters of H: a filter F ⊆ H is a non-empty upward-closed set closed under ⇨-detachment (a ∈ F and a ⇨ b ∈ F implies b ∈ F). The filter lattice ordered by inclusion forms a Heyting algebra, and ι(a) = {F | a ∈ F} is the embedding. Prove: (1) the filter lattice is a HeytingAlgebra, (2) ι preserves ⇨ and ⊤, (3) ι is injective (order-embedding), (4) the embedding lemma: for imp-top-only formulas, HilbertEvaluate v φ = ⊤ ↔ AlgEvaluate (ι ∘ v) ⊥ φ = ⊤. This is the most technically demanding algebraic construction in the chain. References: Diego (1966), Köhler (1981), Celani-Jansana (2012). File: Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean.

---

### 309. Hilbert algebra soundness completeness
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 302, Task 304, Task 305

**Description**: Prove soundness and completeness of IPL⟨→,⊤⟩ w.r.t. Hilbert algebras. Soundness: if Derivable ImpAxiom φ then HilbertEvaluate v φ = ⊤ in every HilbertAlgebra. Completeness via the Lindenbaum-Tarski algebra: the quotient Proposition Atom / ≈ where φ ≈ ψ iff Derivable ImpAxiom (φ → ψ) and Derivable ImpAxiom (ψ → φ). Define [φ] ⇨ [ψ] := [φ → ψ] and show this is well-defined and satisfies the Hilbert algebra axioms K, S, and antisymmetry. Prove the truth lemma: HilbertEvaluate [·] φ = ⊤ ↔ Derivable ImpAxiom φ. This is the simplest Lindenbaum construction in the chain — no lattice operations needed, just the implication operation on equivalence classes. Reference: Diego (1966) Chapter 2, Rasiowa (1974) Chapter V. File: Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean.

---

### 308. Ipl conservative over conj imp
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 306, Task 307

**Description**: Prove the conservative extension theorem: IPL is conservative over IPL⟨∧,→,⊤⟩ for or-bot-free formulas. Statement: if Derivable IntPropAxiom φ and φ.IsOrBotFree = true, then Derivable ConjImpAxiom φ. Proof route: (1) IPL.hilbert_alg_complete.mp converts to HA-validity, (2) for any BrouwerianSemilattice B and valuation v, instantiate HA-validity at the free join completion of B, (3) the embedding lemma from FreeJoinCompletion.lean rewrites back to BrouwerianEvaluate v φ = ⊤ in B, (4) Brouwerian completeness converts back to Derivable ConjImpAxiom φ. Derive the ND corollary via algebraic bridges. This shows that disjunction and falsum are genuinely independent extensions — no theorem in the ∧-→-⊤ language gains a new proof by adding ∨ and ⊥. File: Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean.

---

### 307. Free join completion
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 302, Task 303

**Description**: Construct a HeytingAlgebra from any BrouwerianSemilattice via a free join completion, and prove the embedding lemma for or-bot-free formulas. The construction adjoins formal joins (and a bottom element) to a BrouwerianSemilattice while preserving meets and Heyting implication. Candidate construction: the lattice of downward-closed subsets (downsets/order ideals) of B ordered by inclusion, which forms a complete Heyting algebra with an order-embedding ι : B → Downsets(B) via principal downsets ι(b) = ↓b. Prove: (1) Downsets(B) is a HeytingAlgebra, (2) ι preserves ⊓ (ι(a ⊓ b) = ι(a) ⊓ ι(b)), (3) ι preserves ⇨ (ι(a ⇨ b) = ι(a) ⇨ ι(b)), (4) ι preserves ⊤, (5) the embedding lemma: for or-bot-free formulas, BrouwerianEvaluate v φ = ⊤ ↔ AlgEvaluate (ι ∘ v) ⊥ φ = ⊤. This is the algebraic bridge for the ∧→⊤ conservative extension, analogous to WithBot for MPL→IPL. File: Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean.

---

### 306. Brouwerian soundness completeness
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 302, Task 303, Task 305

**Description**: Prove soundness and completeness of IPL⟨∧,→,⊤⟩ w.r.t. Brouwerian semilattices. Soundness: if Derivable ConjImpAxiom φ then BrouwerianEvaluate v φ = ⊤ in every BrouwerianSemilattice. Completeness via the Lindenbaum-Tarski algebra: construct the quotient Proposition Atom / ≈ where φ ≈ ψ iff Derivable ConjImpAxiom (φ ↔ ψ), show it is a BrouwerianSemilattice, and prove the truth lemma (BrouwerianEvaluate [φ] = ⊤ ↔ Derivable ConjImpAxiom φ). The Lindenbaum construction parallels HilbertLindenbaumGHA but quotients by ConjImpAxiom-derivability; the key difference is that the quotient need not have joins (⊔). Reference: Rasiowa (1974) Chapters IV-V for the general algebraic completeness pattern. File: Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean.

---

### 305. Fragment hilbert proof systems
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 302

**Description**: Define fragment-specific Hilbert axiom predicates for the two sub-IPL proof systems: (1) ConjImpAxiom for IPL⟨∧,→,⊤⟩ — the implicational and conjunctive axiom schemes from IntPropAxiom restricted to or-bot-free formulas: K (φ → ψ → φ), S ((φ → ψ → χ) → (φ → ψ) → φ → χ), conjunction intro (φ → ψ → φ ∧ ψ), conjunction elim left/right (φ ∧ ψ → φ, φ ∧ ψ → ψ). No efq, no disjunction axioms. (2) ImpAxiom for IPL⟨→,⊤⟩ — only K and S with modus ponens. Prove for each: substitution closure (subst_preserves_conjImpAxiom, subst_preserves_impAxiom), that modus ponens is the sole rule, and the deduction theorem for each fragment. These axiom predicates are the proof-theoretic counterparts to BrouwerianSemilattice and HilbertAlgebra. File: Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean.

---

### 304. Hilbert algebra typeclass
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: None

**Description**: Define the HilbertAlgebra typeclass: a structure (H, ⇨, ⊤) satisfying (K) a ⇨ (b ⇨ a) = ⊤, (S) (a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤, and antisymmetry (a ⇨ b = ⊤ ∧ b ⇨ a = ⊤ → a = b). Derive the induced partial order a ≤ b ↔ a ⇨ b = ⊤ and prove it is a PartialOrder. Provide forgetful instances from BrouwerianSemilattice and GeneralizedHeytingAlgebra. Define HilbertEvaluate mapping imp-top-only Propositions to elements of a HilbertAlgebra using only ⇨. This captures the algebraic semantics of IPL⟨→,⊤⟩ — the pure implication fragment corresponding to typed SKI combinators via Curry-Howard. Mathlib has no such class. References: Diego (1966), Monteiro (1955), Rasiowa (1974) Ch. V. File: Cslib/Foundations/Order/HilbertAlgebra.lean.

---

### 303. Brouwerian semilattice typeclass
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: None

**Description**: Define the BrouwerianSemilattice typeclass: SemilatticeInf + OrderTop + HImp with the adjunction a ≤ b ⇨ c ↔ a ⊓ b ≤ c. This is the algebraic semantics for IPL⟨∧,→,⊤⟩ — the conjunction-implication-verum fragment of intuitionistic logic. Mathlib has no such class; this fills the gap between SemilatticeInf and GeneralizedHeytingAlgebra (which additionally requires SemilatticeSup). Provide the forgetful instance from GeneralizedHeytingAlgebra. Define BrouwerianEvaluate mapping or-bot-free Propositions to elements of a BrouwerianSemilattice using only ⊓ and ⇨ (no ⊔ or ⊥). Prove basic algebraic identities (e.g., a ⇨ a = ⊤, monotonicity of ⇨ in the second argument). Reference: Rasiowa (1974), Köhler (1981). File: Cslib/Foundations/Order/BrouwerianSemilattice.lean.

---

### 302. Fragment syntactic predicates
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: None

**Description**: Define syntactic fragment predicates on Proposition analogous to the existing IsBotFree: (1) IsOrFree — no disjunction, (2) IsOrBotFree — no disjunction or falsum, (3) IsImpTopOnly — only implication and atoms (no conjunction, disjunction, or falsum). Prove AlgEvaluate independence lemmas for each: or-free evaluation is independent of the join operation, imp-top-only evaluation is independent of join, meet, and bot_val. These predicates and lemmas form the syntactic foundation for all fragment conservative extension results. Also prove closure properties (conjunction/substitution preservation) needed by downstream proof system tasks. File: Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean. Extends the pattern established by IsBotFree in Conservative.lean.

---

### 301. Temporal tableau
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal
- **Dependencies**: Task 297, Task 298

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
- **Dependencies**: Task 297, Task 298

**Description**: Implement tableau decision procedure for basic modal logic K with world labels, box/diamond rules on top of propositional rules from shared infrastructure. Introduces world labels (accessibility relation tracking) and fundamental modal rule pattern: box-positive is universal/persistent, diamond-positive is existential (fresh accessible world). Use Lukasiewicz encoding for and/or. Prove soundness against Kripke semantics and completeness by extracting finite Kripke countermodels. Modal formula type: Cslib.Logic.Modal.Formula with atom, bot, imp, box primitives. Files under Cslib/Logics/Modal/Tableau/: Defs.lean, Rules.lean, Branch.lean, Closure.lean, Saturation.lean, Soundness.lean, Completeness.lean. Estimated: 1,500-2,000 lines.

---

### 298. Propositional tableau decidability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional
- **Dependencies**: Task 297

**Description**: Implement propositional tableau systems for all three propositional logics in CSLib: classical (PropositionalAxiom), intuitionistic (IntPropAxiom), and minimal (MinPropAxiom). Build on the logic-neutral Foundations/Logic/Tableau/ infrastructure from task 297. Classical tableau: two-sided signed (T/F), complementary closure, all rules invertible, L = Unit — delivers Decidable (BValid phi) via Boolean semantics. Intuitionistic tableau: Kripke-style worlds even at propositional level (L = WorldIndex), restricted T(φ→ψ) rule creating successor worlds, closure only on F(⊥) — delivers Decidable (IValid phi) via propositional Kripke semantics. Minimal tableau: like intuitionistic but closure restricted to complementary atoms T(p)/F(p) only (no ex falso) — delivers Decidable (MValid phi) via MValid/Kripke semantics with botForces = false. Build classical first (simplest, validates infrastructure), then intuitionistic (adds world-labeled branches), then minimal (restricts closure further). Handle native and/or constructors for PL.Proposition. Use fuel-bounded expansion with termination via subformula property (classical) and finite model property (intuitionistic/minimal). Soundness and completeness proved against respective semantics. Files under Cslib/Logics/Propositional/Tableau/: Defs.lean, Rules.lean, Classical/Closure.lean, Classical/Saturation.lean, Classical/Soundness.lean, Classical/Completeness.lean, Classical/DecisionProcedure.lean, Intuitionistic/Closure.lean, Intuitionistic/Saturation.lean, Intuitionistic/Soundness.lean, Intuitionistic/Completeness.lean, Intuitionistic/DecisionProcedure.lean, Minimal/Closure.lean, Minimal/DecisionProcedure.lean. Estimated: 2,000-2,800 lines.

---

### 297. Foundations tableau infrastructure
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [297_foundations_tableau_infrastructure/reports/01_foundations-tableau-research.md]
- **Plan**: [297_foundations_tableau_infrastructure/plans/01_foundations-tableau-plan.md]

**Description**: Build shared tableau infrastructure in Foundations/Logic/Tableau/. Refactor and extend the existing PropositionalTableau.lean (210 lines) into a proper module directory. Unify the PropSign type (from Foundations) with the bimodal Sign type into a single canonical sign type. Create generic signed formula (parameterized over formula type F and label type L), rule result, and branch types. Crucially, the foundation must be logic-neutral to support classical, intuitionistic, and minimal tableaux: (1) Closure must be parameterized via a ClosureCondition typeclass — classical uses complementary signed pairs at the same label, intuitionistic uses only F(⊥), minimal uses only complementary atoms T(p)/F(p). (2) Rule application must be configurable via a RuleConfig or LogicKind parameter — the T(φ→ψ) rule behaves differently in classical (branch into F(φ) or T(ψ)) vs intuitionistic (create successor world w' with T(φ), F(ψ)) vs minimal (same as intuitionistic). (3) Branch needs world-awareness even at propositional level (L = Unit for classical, L = WorldIndex for intuitionistic/minimal). CSLib already has Kripke semantics for propositional logic with IValid (intuitionistic) and MValid (minimal) via botForces parameterization, and algebraic semantics via GeneralizedHeytingAlgebra/HeytingAlgebra/BooleanAlgebra. Files to create: Sign.lean, SignedFormula.lean, PropositionalRules.lean, RuleResult.lean, Branch.lean, Closure.lean, ClosureCondition.lean under Cslib/Foundations/Logic/Tableau/. Estimated: 800-1,100 lines.

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

### 295. Fix dia duality axiom typeclasses
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None
- **Plan**: [295_fix_dia_duality_axiom_typeclasses/plans/01_axiom-typeclass-plan.md]

**Description**: Add HasAxiomDiaDualityFwd and HasAxiomDiaDualityBack typeclasses to Cslib/Foundations/Logic/ProofSystem.lean to complete the axiom-typeclass pairing pattern. AxiomDiaDualityFwd and AxiomDiaDualityBack are defined in Axioms.lean but lack corresponding Has* typeclasses in ProofSystem.lean, unlike every other axiom. Add two class declarations in a new DiaDualityAxiomClasses section following the existing pattern.

---

### 294. Fix missing docstrings nd inference
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None
- **Research**: [294_fix_missing_docstrings_nd_inference/reports/01_docstring-research.md]
- **Plan**: [294_fix_missing_docstrings_nd_inference/plans/01_docstring-fix-plan.md]

**Description**: Add missing docstrings to 6 declarations identified by /vet 266: two anonymous Coe instances in Cslib/Foundations/Logic/InferenceSystem.lean (lines 74, 81), and four declarations in Cslib/Logics/Propositional/NaturalDeduction/Basic.lean (emptySequent_eq line 158, iff_derivableIn_empty line 160, derivableIn_top line 335, equiv.refl line 361). Follow CONTRIBUTING.md docstring conventions for consistency with surrounding code.

---

### 293. Curry howard nd typed lambda
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 290

**Description**: Establish the formal Curry-Howard isomorphism between Theory.Derivation Gamma A (propositional ND proofs) and well-typed lambda terms. Define a purpose-built simply-typed term language over PL.Proposition as the type language. Formalize: (1) curry_howard_forward extracting a well-typed term from a derivation, (2) curry_howard_backward extracting a derivation from a well-typed term, (3) roundtrip properties showing the maps are mutually inverse. Map ND constructors to term constructors: impI to lambda, impE to application, andI to pair, andE1/2 to projections, orI1/2 to injections, orE to case. As a reduced-scope fallback, the {arrow, and} fragment is a self-contained milestone. Normal derivations correspond to beta-normal terms. Files: new directory Cslib/Logics/Propositional/CurryHoward/. Depends on the normalization task (290).

---

### 292. Ipl decidability cutfree lj
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 279

**Description**: After task 279 delivers LJ with cut elimination, formalize the connection between cut-free proof search and decidability. Define a bounded backward proof search procedure over cut-free LJ: the search space is finite because all formulas in a cut-free proof are subformulas of the sequent. Prove termination via a well-founded measure. Produce Decidable (LJDerivable (Gamma |- A)) and lift via nd_iff_lk to Decidable (DerivableIn IPL (Gamma |- A)). File: Cslib/Logics/Propositional/SequentCalculus/Decidability.lean. Depends on 279.

---

### 291. Three way proof system equivalence
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 279

**Description**: After task 279 delivers hilbert_iff_lk and nd_iff_lk, create a unifying module stating the three-way equivalence as List.TFAE theorems. For each of MPL, IPL, and CPL, prove that Hilbert derivability, ND derivability, and SC derivability are equivalent. The pairwise bridges are: Hilbert-ND from task 266, Hilbert-SC and ND-SC from task 279. This is purely compositional. File: Cslib/Logics/Propositional/ProofSystemEquivalence.lean. Depends on 279.

---

### 290. Nd normalization subformula property
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 266

**Description**: Formalize Prawitz-style normalization for CSLib Theory.Derivation (propositional IPL and MPL). Define Derivation.isNormal predicate (no maximal formula -- i.e., no introduction rule immediately followed by the corresponding elimination on the same formula). Prove a normalization function normalize that transforms any derivation into a normal form. Derive the subformula property as a corollary: every formula in a normal derivation is a subformula of the conclusion or a hypothesis. The Theory.Derivation type is Type u (not Prop), enabling a computable normalization function. Reference: [Prawitz1965] Ch. IV-V. Consider starting with the implicational fragment ({arrow} only) as a milestone, then extending to full IPL connectives. Files: new module Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean. Depends on 266.

---

### 289. Decidable derivable propositional instance
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 266

**Description**: Compose instDecidableTautology with prop_completeness_iff_tautology to produce a Decidable (Derivable PropositionalAxiom phi) instance for [Fintype Atom] [DecidableEq Atom]. This is a one-liner composition gap: the bridge Tautology phi <-> Derivable PropositionalAxiom phi exists, and Decidable (Tautology phi) exists, but the composed Decidable instance is not registered. File: Cslib/Logics/Propositional/Metalogic/Decidability.lean or inline in StrongCompleteness.lean. Depends on 266.

---

### 288. Lindenbaum tarski algebra instances
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 266

**Description**: Export named abbrev or instance declarations making explicit that the Lindenbaum-Tarski algebra of MPL is a GeneralizedHeytingAlgebra, IPL is a HeytingAlgebra, and CPL is a BooleanAlgebra. These are currently implicit in algebraic completeness proofs but not exported as standalone usable facts. Optionally prove the free Boolean algebra universal property for CPL. Files: new module Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean. Depends on 266.

---

### 279. Propositional sequent calculus lk lj
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 280

**Description**: Implement a two-sided Gentzen-style sequent calculus (LK for classical, LJ for intuitionistic) for propositional logic with cut elimination. Use Finset-based contexts on both sides, following the CLL sequent calculus in Cslib/Logics/LinearLogic/CLL/Basic.lean as a template. Prove soundness, completeness, cut elimination (Hauptsatz), and equivalence bridges to the existing Hilbert and natural deduction systems (hilbert_iff_lk, nd_iff_lk). This completes the proof-system triad (Hilbert + ND + SC) for propositional logic and would be the first LK/LJ formalization in Lean 4.

---

### 278. Simplify proofs with normalization tags
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 266

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

### 252. Acceptance conditions zoo
- **Status**: [COMPLETED]
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
