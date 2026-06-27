---
next_project_number: 380
---

# TODO

## Task Order

*Updated 2026-06-27. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,241,278,290,299,301,321,342,355,364,367,368,370,371,372,376,377 | -- | Bimodal Porting, Foundations, Modal Logic, ... |
| 2 | 39,40,181,215,300,332,363,366,374,378 | 36,37,180,290,299,355,371,376,377 | Bimodal Porting, Foundations, Modal Logic, ... |
| 3 | 41,275,360,369,373,379 | 39,40,332,363,364,378 | Foundations, Propositional Logic, Algebraic Semantics |
| 4 | 317 | 369 | Propositional Logic |
| 5 | 375 | 317 | Propositional Logic |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

278 [NOT STARTED] — Simplify proofs using new simp/grind normalization tags. After ta
355 [NOT STARTED] — Consolidate the Modal and Propositional deductionTheorem through 
  └─ 366 [NOT STARTED] — Capstone audit ensuring the deduction theorem is correctly abstra
41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Modal Logic

299 [IMPLEMENTING] — Implement tableau decision procedure for basic modal logic K with
  └─ 300 [NOT STARTED] — Extend modal K tableau (task 299) with frame-specific rules for r
364 [RESEARCHED] — Repair the pre-existing Mathlib/toolchain-drift build failure in 
  └─ 360 [BLOCKED] — The repo-wide 'lake build' currently fails (unrelated to vetted t

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
290 [PARTIAL] — Formalize Prawitz-style normalization for CSLib Theory.Derivation
  └─ 332 [IMPLEMENTING] — Close the two remaining normalization-termination sorries for CSL
    └─ 373 [NOT STARTED] — Extend the Curry-Howard layer from a structural isomorphism to a 
368 [NOT STARTED] — Deduplicate the prime-exclusion machinery shared by the intuition
370 [NOT STARTED] — Close the decidability asymmetry in the metalogic layer: classica
371 [NOT STARTED] — Symmetrize the LK/LJ sequent-calculus metatheory and add the miss
  └─ 374 [NOT STARTED] — Add Craig interpolation for the propositional sequent calculi, a 
372 [NOT STARTED] — Complete the propositional fragment lattice by adding the disjunc
317 [BLOCKED] — Fill the propositional tableau completeness sorries (7 real sorri
  └─ 375 [NOT STARTED] — Complete the cross-system equivalence story by folding the tablea
369 [NOT STARTED] — Parameterize the intuitionistic and minimal tableau developments 
  └─ 317 [BLOCKED] — Fill the propositional tableau completeness sorries (7 real sorri (see above)

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
241 [IMPLEMENTING] — Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller)
301 [IMPLEMENTING] — Implement tableau decision procedure for temporal logic (Cslib.Lo
342 [NOT STARTED] — Migrate the Burgess argument-order convention to the Pnueli conve
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
  └─ 275 [BLOCKED] — Prove that Bimodal TM is conservative over Temporal BX for tempor
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Code Hygiene

321 [NOT STARTED] — Review file size and structure throughout Logics/ and Foundations

### Algebraic Semantics

367 [PLANNED] — Collapse the three near-identical Brouwerian completeness develop
377 [PLANNED] — Create the classical conjunction-implication fragment axiom syste
  └─ 378 [PLANNED] — Prove CPL is conservative over its classical conjunction-implicat
    └─ 379 [PLANNED] — Prove CPL is conservative over its classical conjunction-implicat

### Uncategorized

376 [RESEARCHED] — Prove the fuel-sufficiency lemma needed to discharge the sorry at
  └─ 363 [BLOCKED] — Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean fa
    └─ 360 [BLOCKED] — The repo-wide 'lake build' currently fails (unrelated to vetted t (see above)
    └─ 369 [NOT STARTED] — (Propositional Logic: Parameterize the intuitionistic and mini) (see above)

## Tasks

### 379. Cpl conservative over classical conjimpbot
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 378
- **Plan**: [379_cpl_conservative_over_classical_conjimpbot/plans/01_classical-conjimpbot-conservativity.md]

**Description**: Prove CPL is conservative over its classical conjunction-implication-falsum fragment CPL⟨∧,→,⊥,⊤⟩, completing the classical column to 4-for-4 (symmetric with the minimal and intuitionistic towers). Deliver classicalConjImpBot_completeness : IsOrFree φ → Tautology φ → Derivable ClassicalConjImpBotAxiom φ by adding a ⊥ case to the ∧-extended Kalmár truth lemma from task 378 (⊥ is always false under any Boolean assignment, so the surrogate handling is direct), plus the conservativity edge cpl_conservative_over_classicalConjImpBot and classicalConjImpBot_iff_chain. RISK: reuses the ∧-extended Kalmár machinery from 378; the ⊥ case should be the easy increment, but keep zero-debt — [BLOCKED] with goal state rather than sorry if stuck. Mirrors tasks 352/378. After this lands the classical conservativity column is complete and the MPL/IPL/CPL towers are structurally symmetric. Files: Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean (new). Depends on task 378 (reuses the ∧-extended Kalmár lemma).

---

### 378. Cpl conservative over classical conjimp
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 377
- **Plan**: [378_cpl_conservative_over_classical_conjimp/plans/01_classical-conjimp-conservativity.md]

**Description**: Prove CPL is conservative over its classical conjunction-implication fragment CPL⟨∧,→,⊤⟩, the next rung above the implicational result (task 352). Deliver classicalConjImp_completeness : IsOrBotFree φ → Tautology φ → Derivable ClassicalConjImpAxiom φ, proved by EXTENDING the Kalmár / Tarski–Bernays truth-assignment lemma classicalImp_kalmar (Metalogic/ClassicalImpCompleteness.lean) with a conjunction (∧) case (the falsum-surrogate double-negation form carries over; add the ∧ truth-table subcases). Then derive the conservativity edge cpl_conservative_over_classicalConjImp (compose with CPL soundness via ClassicalConjImpAxiom.toPropAxiom, mirroring cpl_conservative_over_imp) and the classicalConjImp_iff_chain biconditional. RISK: the ∧-extended Kalmár induction is the genuine difficulty (medium-high) — must use the truth-assignment method, NOT an algebraic free-completion route (classical fragments are not Heyting-complete; Peirce is invalid in free Heyting completions). If the ∧ induction is intractable, mark [BLOCKED] with the exact goal state, no sorry. Mirrors task 352. Files: Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean (new), ProofSystem/FragmentAxioms.lean. Depends on the ClassicalConjImpAxiom system (task 377).

---

### 377. Classical conjunction fragment axioms
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 352
- **Plan**: [377_classical_conjunction_fragment_axioms/plans/01_classical-conjimp-axioms.md]

**Description**: Create the classical conjunction-implication fragment axiom systems to fill the missing classical middle of the propositional conservativity chain (the classical column is currently 2-for-4: only Glivenko at top + the implicational fragment at bottom from task 352). Deliver: (1) inductive ClassicalConjImpAxiom for CPL⟨∧,→,⊤⟩ = {implyK, implyS, peirce, andI, andE1, andE2} (mirror ConjImpAxiom ∪ the peirce constructor of ClassicalImpAxiom in ProofSystem/FragmentAxioms.lean); (2) inductive ClassicalConjImpBotAxiom for CPL⟨∧,→,⊥,⊤⟩ = above + efq; (3) subsumption (toX) maps: ConjImpAxiom.toClassicalConjImpAxiom, ClassicalImpAxiom.toClassicalConjImpAxiom, ClassicalConjImpAxiom.toClassicalConjImpBotAxiom, ClassicalConjImpAxiom.toPropAxiom, ClassicalConjImpBotAxiom.toPropAxiom; (4) supporting infra mirroring siblings: mem_implyK/mem_implyS witnesses, subst_preserves_* closure lemmas, the *_hasDeductionTheorem instance, and IsOrBotFree/IsOrFree fragment-predicate compatibility lemmas. Pure syntactic mirror of FragmentAxioms.lean blocks; no new semantics. Zero-debt, CI green. Files: Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean (+ Axioms.lean if needed).

---

### 376. Prove fuel sufficiency lemma for classical tableau completeness
- **Effort**: 3-5 hours
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Dependencies**: None
- **Research**: [363_repair_classical_tableau_completeness/reports/01_spawn-analysis.md]

**Description**: Prove the fuel-sufficiency lemma needed to discharge the sorry at line 492 of Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean. The sorry is the body of `classicalExpandBranches_hintikka`, which proves that any open branch produced by `classicalExpandBranches` satisfies the Hintikka condition. The induction on fuel is blocked because the fuel=0 base case is unprovable with the current invariant: when `classicalExpandBranches branches expandedSets 0 = .openBranch b`, the invariant covers only `sf ∈ expandedSets[j]`, leaving `sf ∈ b \ expandedSets[j]` without any Hintikka guarantee.

The recommended approach (Path A) is to prove a helper lemma — call it `classicalExpandBranches_fuel_sufficient` or similar — establishing that when `classicalExpandBranches` is called with `fuel = 4*(φ.complexity+1)+1` (the bound used by `classicalTableau`), it NEVER returns `.openBranch` via the fuel=0 degenerate path. That is, every open branch is found saturated via `classicalStepBranch b e = none` before fuel reaches 0. This makes the fuel=0 case of `classicalExpandBranches_hintikka` vacuously true. The proof is a termination/measure argument: each step strictly decreases the number of unexpanded applicable formulas on open branches, and the fuel bound 4*(φ.complexity+1)+1 exceeds this measure. The companion lemma `classicalExpandBranches_openBranch_initial_mem` (already proved) establishes membership preservation and can be used to bound the applicable set.

Fallback paths if Path A proves intractable: (B) restate `classicalExpandBranches_hintikka` using well-founded recursion on the pair (unexpanded-applicable-formula count, fuel) rather than fuel alone — avoids the fuel=0 issue at the cost of restructuring the recursion scheme; (C) prove `classicalTableau_hintikka` directly without using `classicalExpandBranches_hintikka` as an intermediate general lemma, using structural induction on (pending_size, fuel). Paths B and C are fully documented in specs/363_repair_classical_tableau_completeness/.orchestrator-handoff.json.

Deliverable: a complete, sorry-free proof of `classicalExpandBranches_hintikka` (and any helper lemmas required by Path A/B/C) in Completeness.lean, with the file building green under `lake build` and `lake test`. The zero-debt green build of task 363 depends directly on this lemma being closed.

---

### 375. Proof system equivalence tableau sequent edges
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317, Task 363

**Description**: Complete the cross-system equivalence story by folding the tableau (and remaining sequent) decision systems into the proof-system TFAE. Cslib/Logics/Propositional/ProofSystemEquivalence.lean currently proves Hilbert<->ND<->LK for CPL (cplProofSystemsTfae) and Hilbert<->ND<->LJ for IPL (iplProofSystemsTfae), plus the MPL Hilbert<->ND two-way. Add the missing edges so the equivalence is genuinely complete across all proof systems: classical Tautology <-> LK provability <-> closed classical tableau, and intuitionistic validity <-> LJ provability <-> closed intuitionistic tableau, extending the TFAE lists accordingly. Requires the tableau soundness+completeness to be green (task 316 done for soundness; task 317 for completeness) and the classical tableau build repaired (task 363). No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 317, 363.

---

### 374. Sequent calculus interpolation
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 371

**Description**: Add Craig interpolation for the propositional sequent calculi, a foundational metatheorem currently absent for LK and LJ. Implement Maehara's method: for a cut-free LK proof of Gamma1, Gamma2 turnstile Delta1, Delta2, construct an interpolant I in the shared vocabulary with Gamma1 turnstile Delta1, I and I, Gamma2 turnstile Delta2, by induction on the cut-free derivation (using LK cut-elimination + subformula property as the foundation), then derive Craig interpolation for implications as the standard corollary; provide the intuitionistic (LJ) analogue. This is a larger new piece (estimate several hundred lines) and the highest-effort item in the propositional backlog -- schedule after the LK/LJ coverage is symmetrized (task 371 supplies the LJ subformula property the LJ case needs). Consider whether to also state the algebraic interpolation corollary over the Lindenbaum/Heyting substrate. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake).

---

### 373. Curry howard reduction correspondence
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 332

**Description**: Extend the Curry-Howard layer from a structural isomorphism to a genuine computational correspondence. Cslib/Logics/Propositional/CurryHoward/{Defs,Isomorphism.lean} currently provide only a constructor-renaming bijection between Theory.Derivation and the intrinsically-typed lambda calculus Theory.Term (curryHowardForward/Backward, roundtrip = rfl). Add: (1) the reduction correspondence -- prove that ND root reduction (NaturalDeduction/Normalization/Reduction.lean reduceRoot: the 5 beta-redexes + 3 commuting conversions) corresponds to beta/eta reduction on Theory.Term, i.e. d reduceRoot d' implies curryHowardForward d reduces to curryHowardForward d' (and a congruence/compatibility lemma); (2) term-level strong normalization -- transport derivation-level SN (normalize_isStronglyNormal) across the isomorphism to obtain SN for well-typed Terms. Depends on task 332 (the normalization termination proof must be sorry-free first). No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 332.

---

### 372. Or imp disjunctive implicational fragment
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 345

**Description**: Complete the propositional fragment lattice by adding the disjunctive-implicational fragment IPL<or,->,top>, the one missing vertex. Current fragments (ProofSystem/FragmentAxioms.lean): ImpAxiom (K,S), ConjImpAxiom (+andI/andE1/andE2), ConjImpBotAxiom/ConjImpBotMinAxiom (+efq), ClassicalImpAxiom (+Peirce) -- none covers or-with-implication. Add OrImpAxiom : Proposition Atom -> Prop with constructors K, S, orI1, orI2, orE; the subsumption OrImpAxiom -> MinPropAxiom; the mem_implyK/mem_implyS witnesses and substitution-closure + fragment-predicate-compatibility lemmas mirroring the existing fragments; the deduction-theorem instance; a tag type Propositional.HilbertOrImp with its InferenceSystem/MinimalHilbert instances (ProofSystem/{Instances,FragmentInstances}.lean); and, if natural, its conservativity step into the chain. Land it on the cleaned-up strength substrate from task 345 (IsMinimal + MinimalAxioms<->inclusion bridge) so the fragment/strength story stays coherent. Like task 352 this is an optional lattice-completion extension -- confirm desirability before heavy investment in the conservativity step; the axioms + instances + deduction theorem are the core deliverable. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 345.

---

### 371. Symmetrize sequent calculus coverage
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Symmetrize the LK/LJ sequent-calculus metatheory and add the missing cut-elimination corollaries; all three items are near-mechanical consequences of results already proved. (1) LJ subformula property: LK has Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean but LJ has none despite having cut-elimination (LJ/CutElimination.lean) -- add LJ/SubformulaProperty.lean mirroring the LK proof, adapted to single-conclusion sequents. (2) LK decidability: LJ has decidability (LJ/Decidability.lean, via tableau) but LK does not -- add an LK decision procedure, either by cut-free proof search (using LK cut-elimination + subformula property to bound the search) or by reduction to the existing classical tautology checker, and prove it correct. (3) Cut-free completeness as a named theorem: LK has the CutFreeLKProof subtype and LKProof.cutElim but no standalone statement -- add lk_cut_free_completeness : Tautology phi -> Nonempty (CutFreeLKProof (emptyset turnstile {phi})) as a corollary of cutElim composed with lk_iff_tautology. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake).

---

### 370. Int min metalogic decidability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Close the decidability asymmetry in the metalogic layer: classical propositional logic has a decision procedure (instDecidableDerivablePropositionalAxiom via tautology enumeration, Metalogic/StrongCompleteness.lean:566), but intuitionistic (IntPropAxiom) and minimal (MinPropAxiom) logics have none. Establish Decidable (Derivable IntPropAxiom phi) and Decidable (Derivable MinPropAxiom phi) via the finite model property: bound the canonical Kripke models (prime DCCS / MinTheory worlds) by the subformulas of phi, give a terminating decision procedure over the finite model space, and prove it correct against the existing int/min strong-completeness theorems (IntStrongCompleteness.lean, MinStrongCompleteness.lean). Independent of the tableau decision procedures (which currently rest on unproved completeness witnesses). Note: the LJ sequent calculus already has a tableau-backed decidability instance (SequentCalculus/LJ/Decidability.lean) -- assess whether the FMP route or a bridge to LJ decidability is the cleaner source for the IPL instance before implementing. No new axioms (Classical.choice / Decidable.decide acceptable on noncomputable defs); CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake).

---

### 369. Parameterize int min tableau
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 363

**Description**: Parameterize the intuitionistic and minimal tableau developments over their two points of difference to remove ~400 lines of duplication and set up task 317 to discharge ONE truth lemma instead of two. The two logics already share intExpandBranches, the rule set, the Nat-labelled Kripke world scheme, and the accessibility-edge mechanism; they diverge only in (a) the closure predicate (isIntuitionisticallyClosed, which fires on T(bot) at any world, vs isMinimallyClosed, contradiction-only) and (b) the extracted countermodel's botForces (intuitionistic: fun _ => False; minimal: botForces w = T(bot) present on the branch at w). Refactor the shared Soundness and Completeness scaffolding (Cslib/Logics/Propositional/Tableau/{Intuitionistic,Minimal}/{Soundness,Completeness,DecisionProcedure}.lean) to abstract over (closurePred, modelBot) so both logics instantiate a single parametric development, leveraging the generic Foundations/Logic/Tableau ClosureCondition typeclass where natural. Constraints: keep all three Soundness modules green and sorry-free (task 316); preserve the still-open completeness obligations as a SINGLE parametric truth-lemma/countermodel pair (do not introduce new sorries beyond the existing ones being unified). Must run after the classical tableau build is repaired (task 363) so the suite is green. CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 363.

---

### 368. Lift prime exclusion generic lemma
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Deduplicate the prime-exclusion machinery shared by the intuitionistic and minimal Lindenbaum constructions by lifting it to a single generic Foundations lemma. Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean:258-438 (int_prime_exclusion, int_maximal_is_prime, int_excluding_chain_union, int_excluding_base_mem) and Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean:353-369 (min_* counterparts) repeat ~70% identical Zorn's-lemma + orE-axiom + chain-union-closure logic, differing only in that the intuitionistic case threads an extra EFQ consistency check (IntLindenbaum:328-382). Extract a generic prime-exclusion / maximal-is-prime lemma into Cslib/Foundations/Logic/Metalogic (parameterized over the deriv_imp_of_union witness and an optional consistency predicate, defaulting to the trivial predicate for the minimal case), then re-derive both int_prime_exclusion and min_prime_exclusion from it. ~150-line reduction. No new axioms; both StrongCompleteness proofs remain sorry-free; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake).

---

### 367. Unify brouwerian completeness triplication
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: Task 348, Task 354

**Description**: Collapse the three near-identical Brouwerian completeness developments into one parametric module; this is a NET SIMPLIFICATION (~1000-line reduction), not added abstraction. Cslib/Logics/Propositional/Semantics/Algebra/{BrouwerianCompleteness.lean (~528), PointedBrouwerianCompleteness.lean (~561), MplPointedConservative.lean (~658)} are ~80% copy-paste: identical soundness, Lindenbaum-quotient order lemmas (mk_le_mk/inf_mk/himp_mk/le_antisymm/...), canonicalV_spec truth lemma, and completeness/iff skeletons. They differ ONLY in bot semantics: ConjImp maps bot to top, ConjImpBot maps bot to the OrderBot least element (ex falso), ConjImpBotMin uses a free bot_val parameter (the free-vs-least split already landed in task 354). Refactor to a single development over the AlgEvaluate v bot_val / AlgTValid substrate (Semantics/Algebra.lean), with bot interpretation as the one varying parameter guarded by [OrderBot H] only where the least-element semantics is intended; recover the three tier results (Brouwerian / pointed-Brouwerian / free-bot Brouwerian completeness) as corollaries with their existing names preserved for downstream consumers. Build on the theory-parametric substrate from task 348. No new axioms; every existing theorem preserved (as a corollary or alias); CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 348, 354.

---

### 366. Deduction theorem threading documentation audit
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 355

**Description**: Capstone audit ensuring the deduction theorem is correctly abstracted, uniformly threaded, and thoroughly documented across all four logics, after task 355 routes Modal/Propositional through the generic algebraic deduction-theorem layer (algebraic_has_deduction_theorem in Cslib/Foundations/Logic/Metalogic/GenericMCS.lean, built on list_deduction_theorem in ListDeduction.lean). Work: (1) Verify end-to-end that NO logic retains a hand WF-recursion deduction-theorem body or a bespoke deductionWithMem helper -- Propositional (Metalogic/DeductionTheorem.lean), Modal, Temporal, Bimodal all reach the theorem through the single generic seam via their GenericMCSBridge. (2) Verify every downstream consumer (MCS, Lindenbaum, StrongCompleteness, TruthLemma, ProofSystemEquivalence, and the ~25 raw DerivationTree call sites) is threaded through the consolidated HasDeductionTheorem instance with no signature drift and stays sorry-free. (3) Documentation: add a single authoritative architecture docstring (in GenericMCS.lean or a short Foundations doc) explaining the predicate->type HilbertOf bridge and how the four structural logics inherit one deduction theorem; add/curate module docstrings on Propositional/Metalogic/DeductionTheorem.lean and the new Propositional GenericMCSBridge.lean narrating the routing; ensure cross-references resolve. This is the user's explicit priority ('correctly abstracted, threaded, and documented'). Zero behavioral change beyond docs and any thin re-routing 355 missed. CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 355.

---

### 365. Propositional docstring sorry note hygiene
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Docstring/comment-only hygiene pass over the Propositional metatheory; zero code or proof changes. (1) Fix stale 'Notes on sorry' docstrings that no longer match the code after task 316 closed the tableau soundness sorries: Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean lines ~34-39 claim the key lemmas (classicalRule_preserves_sat, classically_closed_unsatisfiable, classicalTableau_sound) are 'marked sorry' but they are fully proved; Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean lines ~41-44 say it 'inherits sorry from Intuitionistic.Soundness' but both are now sorry-free. Audit every 'Notes on sorry' section across the Tableau tree (Classical/Intuitionistic/Minimal Soundness + DecisionProcedure) and rewrite each to accurately describe current status (soundness sorry-free; the remaining sorries live only in the three Completeness modules and the Decidable instances rest on those witnesses). (2) Remove internal development task-number leaks from committed docstrings, replacing them with named-theorem references per CONTRIBUTING.md (same class as the vet finding behind task 356): Semantics/Algebra/Brouwerian.lean:41 references 'task 308' (now completed) -> reference the named bridge lemma brouwerianEmbeddingLemma in FreeJoinCompletion.lean instead; NaturalDeduction/Normalization/Termination.lean:22 and the inline comment at ~1325 reference 'task 332' -> reword to name the open obligation (reduceRootSubSN h_8 case / normalize_isStronglyNormal) rather than a tracker number. Files: the Tableau Soundness/DecisionProcedure docstrings, Brouwerian.lean, Termination.lean. CI green (lake build, lake exe lint-style); no behavioral change. Do FIRST -- trivial, zero-risk, and a prerequisite for 'everything in perfect order'.

---

### 364. Modal tableau soundness drift repair
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [364_modal_tableau_soundness_drift_repair/reports/01_drift-diagnosis.md]
  - [364_modal_tableau_soundness_drift_repair/reports/02_refactor-strategy.md]

**Description**: Repair the pre-existing Mathlib/toolchain-drift build failure in Cslib/Logics/Modal/Tableau/Soundness.lean (947 lines, ~77 errors under leanprover/lean4:v4.31.0). The file is sorry-free but broke under a Lean/Mathlib bump; it was the only module not fixed during the 2026-06-26 CI-failure sweep (all other ~10 originally-failing modules were repaired). Three single-pass agents overflowed their context on it because lean_goal returns very large hypothesis contexts here, so this MUST be done in chunks with incremental commits, never calling lean_diagnostic_messages (hangs in this repo). A full root-cause diagnosis with concrete fix idioms is in reports/01_drift-diagnosis.md. The 77 errors reduce to ~4 fix-families: (1) cases X.sign no longer substitutes the isPos hypothesis (use cases h : X.sign <;> simp_all [Sign.isPos]); (2) simp only [Satisfies] ordering/no-op (reorder after rw, or use Satisfies.neg_iff/diamond_iff / Proposition.neg_def); (3) simp [tryAllPropRules,...] at hsf no longer normalizes to the shape the obtain pattern expects, causing ~60 Unknown identifier hnewBs cascades in modalStepBranch_preserves_sat (re-derive the post-simp shape via lean_goal and fix the obtain/simp set across the 5 parallel rule-cases); (4) LawfulBEq.eq_of_beq instance-synth/type mismatch. Zero sorry, zero new axioms, preserve all statements. CI: lake build (scoped + full), lake exe lint-style. Created as a follow-up of the CI-failure fix sweep.

---

### 363. Repair Classical/Tableau/Completeness.lean proof gaps and bad lemma ref
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: Task 376

**Description**: Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean fails to build with `unsolved goals` (lines ~110, 111) and a reference to a non-existent Mathlib lemma `List.findSome?_of_mem` (line ~117), left mid-refactor. Replace the bad lemma reference with a valid one (or a local proof) and close the remaining goals so the module builds green. Zero-debt: no sorry/axiom. Source: task 360 build-repair (blocked WIP).

---

### 362. Repair Modal/Tableau/Soundness.lean mid-refactor proof gaps
- **Status**: [ABANDONED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Cslib/Logics/Modal/Tableau/Soundness.lean fails to build with multiple `unsolved goals` and `simp made no progress` errors (lines ~99, 100, 124, and more), left mid-refactor by commit df974743 (vague "update") with dangling hypotheses. Reconstruct the intended proofs so the module builds green. Zero-debt: no sorry/axiom. Source: task 360 build-repair (blocked WIP).

---

### 361. Repair Intuitionistic/Minimal Tableau Soundness build (task-316 WIP)
- **Status**: [ABANDONED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean fails to build (error ~line 1383: `simp made no progress` on List.getElem_zip/List.getElem_map), which transitively breaks Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean. This file is active WIP for task 316 (specs/316_propositional_tableau_soundness/). Repair the proof at the failing site (and any sibling simp-progress failures) so both modules build green. A Cluster C call-site fix to Minimal/Soundness.lean from task 360 is staged in the working tree and should be validated/kept once the upstream is green. Zero-debt: no sorry/axiom. Source: task 360 build-repair (blocked WIP).

---

### 360. Repair 11 pre-existing broken modules failing repo-wide lake build
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: Task 363, Task 364

**Description**: The repo-wide 'lake build' currently fails (unrelated to vetted tasks 343/344/350/351/353/354, whose files build clean in isolation). Failing modules: Cslib.Logics.Modal.Denotation (simp made no progress, Denotation.lean:60), Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth (unsolved goals, multiple lines), Cslib.Logics.Temporal.ConservativeExtension (ambiguous term, lines 54/59/69), Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles (type mismatch, lines 84/164/176), Cslib.Logics.Temporal.Metalogic.DenseCompleteness (unsolved goals, line 166), Cslib.Logics.Propositional.SequentCalculus (duplicate _proof_1 environment clash between LJ and LK CutElimination), Cslib.Logics.Bimodal.Metalogic.Separation.Defs (many simp made no progress), Cslib.Logics.Propositional.Tableau.Minimal.Soundness, Cslib.Logics.Bimodal.ProofSystem.Substitution, Cslib.Logics.Modal.Tableau.Soundness, Cslib.Logics.Propositional.Tableau.Classical.Completeness. checkInitImports/shake also fail downstream due to missing oleans. Restore a green repo-wide build. Source: /vet CI run 2026-06-26.

---

### 359. Remove internal task numbers and Zulip-only citation from public docstrings
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Four docstrings embed internal development task numbers: HilbertStrongCompleteness.lean (lines 31, 114, 118 reference 'task 341') and MplConservativeChain.lean (line 229 references 'task 353'). Replace these with references to the named theorems/lemmas directly. Additionally, DeductionCharacterization.lean (line 36) cites only a CSLib Zulip thread as its reference; replace or supplement with a published source for the deduction-theorem characterization (e.g. Troelstra & Schwichtenberg, Basic Proof Theory). Source: /vet of tasks 344, 351, 354.

---

### 358. Rewrite Modal/GenericMCSBridge.lean to remove contradictory gap analysis
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean is a documentation-only file whose CORRECTION NOTICE (lines 14-32) states the original gap analysis was OUTDATED, but the old (incorrect) Component 1/2/3 analysis (lines 34-160) remains in place, making the file self-contradictory. Rewrite the module docstring to reflect the corrected understanding (the bridge IS buildable but requires a HilbertOf wrapper type) and remove or clearly archive the obsolete analysis. Source: /vet of task 350.

---

### 357. Replace global linter suppressions with targeted nolint in task-350 files
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Five task-350 files suppress linters globally via set_option linter.* directives. Bimodal/Metalogic/Core/DeductionTheorem.lean disables linter.style.show, linter.style.emptyLine, and linter.flexible (lines 43-46). Bimodal/Metalogic/Core/GenericMCSBridge.lean (line 64) and Temporal/Metalogic/GenericMCSBridge.lean (line 54) disable linter.dupNamespace globally. Temporal/Metalogic/DenseMCS.lean (line 43) disables linter.flexible globally. Fix the underlying style/naming issue and remove each suppression, or use per-declaration @[nolint <category>] as DenseMCS.lean already does for dupNamespace on Temporal.DerivFc. Fix all linter issues accurately rather than blanket-suppressing. Source: /vet of task 350.

---

### 356. Add missing docstrings to six theorems in Temporal/DenseMCS.lean
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Six public theorems in Cslib/Logics/Temporal/Metalogic/DenseMCS.lean lack /-- -/ docstrings: mp_deriv_fc (line 72), weakening_deriv_fc (line 80), assumption_deriv_fc (line 87), mcs_bot_not_mem_fc (line 324), mcs_neg_of_not_mem_fc (line 334), mcs_not_mem_of_neg_fc (line 342). Add a brief /-- ... -/ docstring immediately before each declaration to clear docBlame lint warnings. Source: /vet of task 350.

---

### 355. Modal propositional deduction theorem consolidation
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 350

**Description**: Consolidate the Modal and Propositional deductionTheorem through the generic algebraic deduction-theorem layer, completing the consolidation begun in task 350 (which handled Temporal and Bimodal). Task 350 deferred Modal/Propositional because their deductionTheorem defs are polymorphic over an Axioms : Proposition -> Prop predicate, whereas the generic algebraicDerivationSystem (Cslib/Foundations/Logic/Metalogic/GenericMCS.lean) and MinimalHilbert (Cslib/Foundations/Logic/ProofSystem.lean) are keyed on a TYPE S with [InferenceSystem S] [MinimalHilbert S]. Bridging requires new predicate->InferenceSystem infrastructure: introduce a HilbertOf Axioms wrapper type (predicate -> type) carrying [InferenceSystem] and [MinimalHilbert] instances, then build temporal-style bridges (deriv_iff_algebraic) for Modal (HilbertK at Modal/Metalogic/GenericMCSBridge.lean, whose current content is documentation-only) and Propositional (no bridge exists). Re-implement Modal hasDeductionTheorem (Modal/Metalogic/DeductionTheorem.lean) and Propositional hasDeductionTheorem (Propositional/Metalogic/DeductionTheorem.lean) signature-preserving (do NOT delete: ~25 raw DerivationTree call sites consume them directly), routing through the new bridge + algebraic_has_deduction_theorem, and remove the hand WF-recursion bodies + deductionWithMem helpers. Preserve any logic-specific witnesses. Files: Modal/Metalogic/{DeductionTheorem,GenericMCSBridge}.lean, Propositional/Metalogic/DeductionTheorem.lean (+ a new Propositional GenericMCSBridge.lean), Cslib/Foundations/Logic/Metalogic/GenericMCS.lean. Zero technical debt (no new sorry, no new axioms; Classical.choice on already-noncomputable defs acceptable). CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake --add-public --keep-implied --keep-prefix); all downstream consumers (MCS, Completeness, TruthLemma) still compile sorry-free. Surfaced as a follow-up by task 350; implements the same Zulip CSLib Temporal Logic suggestion by Matthew Doty (prove the deduction theorem once via an axiom class and inherit it across the structural logics): https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Temporal.20Logic/near/606511638

---

### 354. Mpl arbitrary point brouwerian completeness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 353

**Description**: Close the fourth conservativity step of the MPL fragment tower so it parallels the IPL chain step-for-step. Build algebraic completeness for MPL⟨∧,→,⊥,⊤⟩ (ConjImpBotMinAxiom from task 353) against Brouwerian semilattices with an ARBITRARY distinguished element (a free bot_val : H) — NOT the OrderBot least-element semantics of PointedBrouwerian.lean (PointedBrouwerian.lean:22,67), which encodes ex falso. Generalise PointedBrouwerianEvaluate / PointedBrouwerianCompleteness by dropping the [OrderBot H] requirement and interpreting ⊥ as a parametric bot_val — exactly the AlgEvaluate v bot_val that GHAValid already quantifies over (Semantics/Algebra.lean:93). Then prove hilbertMplConservativeOverConjImpBot_direct (MPL conservative over ConjImpBotMin for or-free formulas, analogous to hilbertMplConservativeOverConjImp_direct in MplConservativeChain.lean) plus the biconditional mplAxiom_iff_conjImpBotMinAxiom. Reuse the GHA→Brouwerian bridge GHAValid_implies_BrouwerianValid_direct, generalised to carry bot_val. Result: MPL⟨→,⊤⟩ ⊂ MPL⟨∧,→,⊤⟩ ⊂ MPL⟨∧,→,⊥,⊤⟩ ⊂ MPL mirrors IPL's Hilbert → Brouwerian → pointed-Brouwerian → GHA, the sole divergence being free vs. least ⊥. Depends on 353. CI green.

---

### 353. Mpl conjimpbot fragment axiom
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Create the MPL-flavoured ⟨∧,→,⊥,⊤⟩ fragment axiom system ConjImpBotMinAxiom — identical to the existing ConjImpBotAxiom (ProofSystem/FragmentAxioms.lean:259) but WITHOUT the ex-falso constructor Proposition.bot.imp φ (line 277). This is the fourth element MPL⟨∧,→,⊥,⊤⟩ of the MPL fragment tower, sitting between ConjImpAxiom and MinPropAxiom, and is the point where the MPL chain genuinely diverges from IPL (free ⊥ vs. least ⊥). Deliver: (1) inductive ConjImpBotMinAxiom with the 5 non-exfalso constructors (implyK, implyS, andIntro, andElimL, andElimR); (2) subsumptions ConjImpAxiom.toConjImpBotMinAxiom and ConjImpBotMinAxiom.toMinPropAxiom (deliberately NOT toIntPropAxiom — staying inside minimal logic is the whole point); (3) substitution closure, fragment-predicate compatibility, and the HasDeductionTheorem instance, mirroring the existing ConjImpBotAxiom blocks (FragmentAxioms.lean:282-394). Leave ConjImpBotAxiom untouched. CI green (lake build, checkInitImports, lint-style, shake).

---

### 352. Cpl conservative over classical implicational fragment
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Algebraic Semantics
- **Dependencies**: None
- **Research**: [352_cpl_conservative_over_classical_implicational_fragment/reports/01_cpl-conservative-classical-implicational.md]
- **Plan**: [352_cpl_conservative_over_classical_implicational_fragment/plans/03_classical-imp-conservativity-v3.md]

**Description**: Prove CPL is conservative over its classical implicational fragment CPL⟨→,⊤⟩, extending the propositional conservativity chain to the classical side, as raised in the Zulip CSLib Propositional Logic thread by Matthew Doty (2026-06-25): "There's also CPL⟨→, ⊤⟩ ... Is it worth proving CPL is conservative over that?" (https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/606508446). The classical implicational fragment Hilbert system is K (φ → ψ → φ), S, and a classical implicational axiom (e.g. Peirce's law ((φ → ψ) → φ) → φ; the research phase must pin down the exact axiomatization — Matthew's thread message lists candidate schemata that should be verified). The existing chain (completed tasks 310/311/312/322) closes the intuitionistic and minimal sides — IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ IPL⟨∧,→,⊥,⊤⟩ ⊂ IPL and the MPL chain — via Hilbert-algebra / Brouwerian routes in Cslib/Logics/Propositional/Semantics/Algebra/{ImpConservative,ConjImpConservative,ConservativeChain,MplConservativeChain,Hilbert}.lean, with fragment axioms in ProofSystem/FragmentAxioms.lean (ImpAxiom, ConjImpAxiom, ConjImpBotAxiom). For the classical implicational fragment the natural algebraic semantics are implication algebras / Tarski algebras; Matthew noted these are obscure and suggested traditional truth-assignment semantics may be the more natural route here ("I'm not about using algebraic semantics here, rather than traditional truth assignments") — the research/plan phase should evaluate both routes and pick the cleaner one. Deliver a cpl_conservative_over_imp (classical) conservativity theorem analogous to the intuitionistic ipl_conservative_over_imp, adding the classical implicational fragment axiom set to FragmentAxioms.lean and extending the derivability subsumption chain. NOTE: Matthew himself flagged this as lower-interest ("not as interesting in terms of Curry-Howard or Category theory or anything"), so this is an optional/exploratory extension — confirm desirability before heavy investment. Files: Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean, a new Semantics/Algebra/ClassicalImpConservative.lean (or a truth-assignment-based module), ConservativeChain.lean. CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake); existing chain preserved.

---

### 351. Deduction theorem weakest logic converse
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 350
- **Plan**: [351_deduction_theorem_weakest_logic_converse/plans/01_deduction-theorem-weakest-logic-converse.md]
- **Summary**: [351_deduction_theorem_weakest_logic_converse/summaries/01_deduction-theorem-weakest-logic-converse-summary.md]

**Description**: Formalize the weakest-logic characterization of the deduction theorem: prove the converse direction that no current Cslib result provides. Introduce an axiom class bundling Modus Ponens with the Deduction Theorem property (the HasDeductionTheorem-style hypothesis Γ ⊢ A → B ↔ A :: Γ ⊢ B, plus reflection/assumption) and prove it instances the implicational Hilbert core MinimalHilbert (= K, S, MP; Cslib/Foundations/Logic/ProofSystem.lean:342) by DERIVING the K axiom A → B → A and the S axiom (A → B → C) → (A → B) → A → C from DT + MP alone. Composed with the existing forward direction (MinimalHilbert ⇒ deduction theorem via list_deduction_theorem), this yields the equivalence characterizing IPL⟨→,⊤⟩ as the weakest logic admitting the deduction theorem, as proposed in the Zulip CSLib Temporal Logic thread by Matthew Doty (2026-06-25): "make another axiom class for the deduction theorem and modus ponens, and show that it instances the IPL⟨→,⊤⟩ class, since IPL⟨→,⊤⟩ is the weakest logic that proves the deduction theorem." (https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Temporal.20Logic/near/606511638). Currently NO converse result exists: every deductionTheorem/hasDeductionTheorem consumes the K and S axioms (h_implyK, h_implyS) as inputs to prove deduction; none derives them. Additionally, decouple the deduction-theorem machinery from [HasBot F]: the generic DerivationSystem/HasDeductionTheorem layer (Cslib/Foundations/Logic/Metalogic/Consistency.lean) lives under a [HasBot F] variable block although its content is purely implicational, so introduce or generalize to a ⊥-free implicational class (cf. existing ⊥-free classes ImpAxiom in Propositional/ProofSystem/FragmentAxioms.lean:84 and HasHilbertTree in Foundations/Logic/Metalogic/DeductionHelpers.lean:61) so purely-implicational systems inherit the deduction theorem without a spurious ⊥. Files: Cslib/Foundations/Logic/ProofSystem.lean, Cslib/Foundations/Logic/Metalogic/{Consistency,ListDeduction,DeductionHelpers}.lean, possibly a new Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean. CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Related to task 345 (MinimalAxioms/IsMinimal reconcile) and best done after or alongside task 350 (generic deduction-theorem consolidation).

---

### 350. Generic deduction theorem lindenbaum consolidation
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [350_generic_deduction_theorem_lindenbaum_consolidation/reports/01_generic-dt-lindenbaum-consolidation.md]
- **Plan**: [350_generic_deduction_theorem_lindenbaum_consolidation/plans/01_deduction-theorem-consolidation.md]
- **Summary**: [350_generic_deduction_theorem_lindenbaum_consolidation/summaries/01_deduction-theorem-consolidation-summary.md]

**Description**: Discharge the deduction theorem and Lindenbaum extension generically across all four logics (Propositional, Modal, Temporal, Bimodal), eliminating the 4x-duplicated hand proofs. The Foundations generic layer already provides a once-and-for-all deduction theorem (list_deduction_theorem in Cslib/Foundations/Logic/Metalogic/ListDeduction.lean:55, exposed as algebraic_has_deduction_theorem in GenericMCS.lean:65) requiring only [MinimalHilbert S] (= K, S, MP), a generic set_lindenbaum (Consistency.lean), and the MinimalHilbert-parametrized MCS-property quartet (MCSProperties.lean). The MCS quartet is already inherited generically, but the deduction theorem is still proved by hand four times and merely wrapped as the HasDeductionTheorem predicate: Propositional hasDeductionTheorem (Propositional/Metalogic/DeductionTheorem.lean:198), Modal hasDeductionTheorem (Modal/Metalogic/DeductionTheorem.lean:177), temporal_has_deduction_theorem (Temporal/Metalogic/DeductionTheorem.lean:167 plus DenseMCS.lean:266), and Bimodal deductionTheorem/bimodalHasDeductionTheorem (Bimodal/Metalogic/Core/DeductionTheorem.lean:161/225). Lindenbaum (prop_lindenbaum, modal_lindenbaum, temporal_lindenbaum, bimodal_lindenbaum) is likewise re-proved per logic via Zorn. Work: route each logic's HasDeductionTheorem instance through the generic algebraic_has_deduction_theorem (using the existing GenericMCSBridge.lean seams in Modal and Temporal, and adding equivalent bridges for Propositional and Bimodal), then delete the four hand proofs of the deduction theorem; likewise discharge each *_lindenbaum from the generic set_lindenbaum where the logic carries no extra structure. Preserve temporal/bimodal-specific witnesses (g_witness, h_witness, allFuture/allPast closure). Completes the consolidation begun in task 338 (which covered only MCS boilerplate for Propositional and Temporal), extending it to the deduction theorem and to Bimodal. Files: the four DeductionTheorem.lean files, the GenericMCSBridge.lean files, Cslib/Foundations/Logic/Metalogic/{ListDeduction,GenericMCS,Consistency}.lean. CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake); all downstream consumers (MCS, Completeness, Chronicle, TruthLemma) still compile sorry-free. Implements the Zulip CSLib Temporal Logic suggestion by Matthew Doty (prove the deduction theorem once via an axiom class and inherit it across all structural logics that extend the implicational core): https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Temporal.20Logic/near/606511638

---

### 348. Glivenko conservativity theory parametric
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 343, Task 345
- **Research**: [348_glivenko_conservativity_theory_parametric/reports/01_parametric-conservativity-spine.md]
- **Plan**: [348_glivenko_conservativity_theory_parametric/plans/01_parametric-conservativity-spine.md]

**Description**: Restate Glivenko and conservativity theory-parametrically against v ⊨ T on the algebraic substrate, using Heyting-homomorphism machinery (GeneralizedHeytingHom.map_interpret and Extension-style homs, cf. Waring's Heyting.lean) over the HilbertLindenbaumAlgebra / Lindenbaum quotient. Generalise the existing Glivenko.lean and *Conservative*.lean family (Conservative, ConservativeChain, ConjImpConservative, ConjImpBotConservative, ImpConservative, MplConservativeChain) so they read as theory-parametric statements with the tier results as corollaries; reuse the IsIntuitionistic/IsClassical/IsMinimal inclusion typeclasses (345). All completeness/soundness remains Hilbert-based. CI green; existing results preserved.

---

### 345. Reconcile logic encodings isminimal
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 341, Task 344
- **Research**: [345_reconcile_logic_encodings_isminimal/reports/01_team-research.md]
- **Plan**: [345_reconcile_logic_encodings_isminimal/plans/01_isminimal-reconciliation.md]

**Description**: Reconcile the two strength encodings on the Hilbert substrate and add the missing inclusion view. Waring's Defs.lean characterises strength by INCLUSION (IsIntuitionistic T ↔ IPL ⊆ T, IsClassical T ↔ CPL ⊆ T, with monotone propagation), while the Hilbert machinery uses the witness-bundle typeclass MinimalAxioms (NaturalDeduction/Equivalence.lean: 8 schema witnesses K, S, ∧I, ∧E1, ∧E2, ∨I1, ∨I2, ∨E). MinimalAxioms STAYS — it is genuinely needed for Hilbert completeness, because the Hilbert system encodes the connectives as axioms. Work: (1) add IsMinimal T ↔ minimal ⊆ T mirroring IsIntuitionistic/IsClassical; (2) add a bridge MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms so the inclusion idiom (monotone, free propagation) and the witness bundle are interchangeable; (3) optionally monotone-extension propagation. Gives Waring-style strength-axis scalability WITHOUT abandoning the Hilbert witness bundle. Files: Defs.lean, NaturalDeduction/Equivalence.lean, ProofSystem/Axioms.lean. CI green.

---

### 344. Algebraic strong completeness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 343

**Description**: Add algebraic STRONG (context/theory) completeness for the HILBERT system, extending 341's weak completeness and factored through v ⊨ T. 341 gives Derivable Axioms φ ↔ validity (theorems only); the only strong completeness today (Γ ⊢ φ ↔ Γ ⊨ φ) is Kripke-based in Metalogic/*StrongCompleteness.lean, not algebraic. Goal: SetDerivable Axioms Γ φ ↔ (algebraic Γ-consequence) — every GHA model (v, bot_val) with v ⊨ AxiomTheory Axioms and v⟦ψ⟧ = ⊤ for all ψ ∈ Γ satisfies v⟦φ⟧ = ⊤ (equivalently the SValid/≤ form v⟦Γ⟧ ≤ v⟦φ⟧). Stay on HILBERT: reuse SetDerivable (Semantics/SemanticConsequence.lean), the HilbertLindenbaumAlgebra + canonicalV/canonicalBotVal scaffolding (Semantics/Algebra/HilbertLindenbaum.lean), and [MinimalAxioms Axioms]. Recover the weak theorem (341) as the Γ = ∅ case. CI green.

---

### 343. Rewire validity through satisfies
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 341
- **Research**: [343_rewire_validity_through_satisfies/reports/01_canonical-satisfies-predicate.md]
- **Plan**: [343_rewire_validity_through_satisfies/plans/01_rewire-validity-satisfies.md]

**Description**: Establish the canonical theory-satisfaction predicate v ⊨ T for propositional logic on the HILBERT/algebraic substrate, adopting the SHAPE of Waring's TValid (Semantics/Heyting.lean) while keeping cslib's PRIMITIVE .bot language and the bot_val parameter — the faithful minimal-logic semantics, since GHAValid quantifying ∀ bot_val means 'valid under every interpretation of ⊥' (Johansson/GHA algebras do not pin a bottom). Define v ⊨ T generically over the ALREADY-applied evaluator: SatisfiesTheory (eval : Proposition Atom → β) (T : Theory Atom) := ∀ A ∈ T, eval A = ⊤, notation v ⊨ T; with AlgTValid T v bot_val := SatisfiesTheory (AlgEvaluate v bot_val) T (DEFINITIONALLY EQUAL, so 341's Hilbert proofs are untouched). bot_val rides inside the evaluator, never in the predicate signature. Keep it generic over the eval FUNCTION, not a bundled Model (defeq). Generality boundary: factor Evaluate (Prop), BoolEvaluate (Bool), AlgEvaluate (GHA), Kripke forcing; EXCLUDE cross-logic (Modal/Temporal/LTL). Adopt uniform v ⊨ A / v ⊨ S / v ⊨ T notation; deprecate/alias v ⊨[bot_val] T. Rewire GHAValid/HAValid/BAValid (Algebra.lean) and SemanticEntails/ISemanticEntails/MSemanticEntails (SemanticConsequence.lean) to factor through it. This underpins the Hilbert completeness theorems (341 weak, 344 strong). CI green; 341 unchanged (defeq).

---

### 342. Temporal burgess to pnueli convention
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Migrate the Burgess argument-order convention to the Pnueli convention for untl and snce throughout Cslib/Logics/Temporal. Temporal currently uses the Burgess order (untl event guard, snce event guard) where the event holds at the witness point and the guard holds at intermediate points, with derived operators someFuture = untl _ top and somePast = snce _ top. Swap to the standard Pnueli order (untl guard event, snce guard event) used in Cslib/Logics/LTL so the two logics agree. Scope: Syntax/Formula.lean constructors, notation, and the convention docstring; Semantics (Satisfies, Validity); the BX axiom schemata in ProofSystem/Axioms.lean; all derived-operator definitions (someFuture, somePast, allFuture, allPast, always, sometimes); every downstream proof in Metalogic (Soundness, Completeness, DenseSoundness, DenseCompleteness, MCS, DeductionTheorem, Chronicle/* including TruthLemma, ConservativeExtension); and the LTL Embedding (Cslib/Logics/LTL/Embedding.lean, Formula.toTemporal) which currently bridges the convention swap. Verify the whole tree builds sorry-free via lake build and the CSLib CI pipeline. Large mechanical-but-pervasive refactor across the entire Temporal subtree.

---

### 341. Theory parametric completeness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Restate propositional algebraic completeness theory-parametrically over AlgTValid, adopting Thomas Waring's v ⊨ T formulation as the canonical statement. Currently the three tier completeness theorems MPL.hilbert_alg_complete (Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean:57), IPL.hilbert_alg_complete (:80), and CPL.hilbert_alg_complete (:105) fold each logic's axioms into the algebra class (GHAValid/HAValid/BAValid) rather than carrying a v ⊨ T hypothesis. Introduce a single theory-parametric completeness theorem of the form: Derivable Axioms φ ↔ ∀ (H) [GeneralizedHeytingAlgebra H] (v) (bot_val), AlgTValid (AxiomTheory Axioms) v bot_val → AlgEvaluate v bot_val φ = ⊤, for any Axioms with [MinimalAxioms Axioms], and recover the three existing tier theorems as corollaries. The AlgTValid predicate already exists (Cslib/Logics/Propositional/Semantics/Algebra.lean:149) but is currently unused; the Lindenbaum scaffolding (HilbertLindenbaumAlgebra, canonicalV, canonicalBotVal, canonicalV_spec, hilbertLindenbaumMk_eq_top_iff in Semantics/Algebra/HilbertLindenbaum.lean) is already parametric in the axiom set with [MinimalAxioms Axioms], so the machinery largely exists. Work needed: (1) soundness direction must discharge axioms from the AlgTValid hypothesis instead of the per-tier *_alg_axiom_sound lemmas (Semantics/Algebra/Soundness.lean); (2) a new lemma that the canonical/Lindenbaum valuation satisfies AlgTValid (AxiomTheory Axioms); (3) the corollary bridges showing v ⊨ IntPropAxiom / PropositionalAxiom force the Heyting/Boolean (bot_val = ⊥) specializations to recover HAValid/BAValid. This matches the shape of Thomas Waring's Theory.complete. Verify the full CI pipeline stays green and existing tier theorems remain (as corollaries).

---

### 340. Derived connective defaults
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 334
- **Research**: [340_derived_connective_defaults/reports/01_derived-connective-defaults.md]

**Description**: Investigate and consolidate derived connective definitions (neg, top, conj/and, disj/or, iff) that use the same Lukasiewicz encoding across Modal, Temporal, Bimodal, and LTL formula types. All four use identical encodings: neg phi := phi imp bot, top := neg bot, and phi psi := neg(phi imp neg psi), or phi psi := neg phi imp psi, iff phi psi := and (phi imp psi) (psi imp phi). Determine whether Foundations/Logic/Connectives.lean can provide default implementations via the existing HasBot/HasImp typeclasses (e.g., a class DerivedNeg extending HasBot+HasImp with a default neg field), so that formula types automatically get these derived connectives by registering PropositionalConnectives. If feasible, migrate Modal/Basic.lean, Temporal/Syntax/Formula.lean, Bimodal/Syntax/Formula.lean, and LTL/Syntax/Formula.lean to use the defaults. Must verify that simp lemmas, pattern matching, and reducibility are preserved — the current definitions may rely on being definitionally equal to specific terms. Files: Cslib/Foundations/Logic/Connectives.lean, plus the 4 formula files. Target: ~80 lines reduced, improved consistency guarantee that all logics share the same encodings.

---

### 339. Unify swap temporal
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [339_unify_swap_temporal/reports/01_swap-temporal-unification.md]

**Description**: Unify the swapTemporal function and its associated theorems between Temporal/Syntax/Formula.lean (lines 335-452, ~117 lines) and Bimodal/Syntax/Formula.lean (lines 124-205, ~81 lines). The shared core (definition, involution, neg distribution, someFuture/somePast exchange, allFuture/allPast exchange, atoms preservation) is near-verbatim duplicated. Bimodal adds a box/diamond case and swapTemporal_diamond. Temporal has additional theorems for next/prev and strongRelease/strongTrigger that Bimodal lacks (those constructors are not in bimodal syntax). The cleanest approach is likely: Bimodal.Formula.swapTemporal delegates to or mirrors Temporal.Formula.swapTemporal for the shared constructors, with Bimodal adding only the box case. Alternatively, a shared typeclass in Foundations/Logic/ could define swapTemporal generically for any type with HasUntil+HasSince. Must preserve all downstream consumers in Metalogic/Separation/ and Metalogic/Decidability/. Files: Cslib/Logics/Temporal/Syntax/Formula.lean, Cslib/Logics/Bimodal/Syntax/Formula.lean. Target: ~70 lines of exact duplication eliminated.

---

### 338. Mcs generic migration
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [338_mcs_generic_migration/reports/01_mcs-generic-migration.md]

**Description**: Migrate Propositional/Metalogic/MCS.lean and Temporal/Metalogic/MCS.lean to use Foundations/Logic/Metalogic/GenericMCS.lean, following the pattern established by Modal/Metalogic/GenericMCSBridge.lean. Currently Propositional and Temporal each maintain ~80 lines of MCS wrapper boilerplate that re-abbreviates generic Metalogic.SetConsistent/SetMaximalConsistent and re-invokes set_lindenbaum/closed_under_derivation. GenericMCS.lean already provides algebraicDerivationSystem for any MinimalHilbert, giving free deduction theorem and all MCS properties. Modal adopted this via GenericMCSBridge.lean. Temporal/Metalogic/MCS.lean has additional temporal-specific properties (g_witness, h_witness, temporal content) that must be preserved — only the generic boilerplate should be replaced. Files: Cslib/Logics/Propositional/Metalogic/MCS.lean, Cslib/Logics/Temporal/Metalogic/MCS.lean, potentially Cslib/Foundations/Logic/Metalogic/GenericMCS.lean (if the interface needs minor extension). Target: ~160 lines of boilerplate eliminated while preserving all downstream API.

---

### 337. Parametric modal conservative extension
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 335

**Description**: Extract a single parametric conservative extension theorem taking frame condition hypotheses and a universal model constructor as parameters, replacing 15 near-identical Systems/*/ConservativeExtension.lean files. Currently 15 files (55-61 lines each, 896 total) that all compose: soundness -> toModal_valid_implies_tautology -> CPL completeness, differing only in which frame conditions (reflexivity, transitivity, symmetry, seriality, euclideanness) are discharged and which model is constructed. A parametric theorem in Modal/Metalogic/ would let each system instantiate in ~5 lines. Files: new theorem in Cslib/Logics/Modal/Metalogic/ (possibly ConservativeExtension.lean), all 15 Systems/*/ConservativeExtension.lean. Target: ~400 lines reduced. Depends on task 335 (to avoid conflicting edits in the same system directories).

---

### 336. Parametric modal completeness cascade
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 335

**Description**: Extract parametric completeness cascade theorems (strong_soundness, strong_completeness, strong_completeness_iff, compactness, weak completeness) in Modal/Metalogic/Completeness.lean, parameterized by truth lemma variant and frame conditions. Refactor the per-system completeness files to use the parametric cascade. The 15 Systems/*/Completeness.lean files total 3,205 lines. The cascade pattern (strong_soundness via unfold+soundness, strong_completeness via contrapositive+Lindenbaum+truth-lemma, then iff/compactness/weak wrappers) is mechanically identical across systems, differing only in: (a) which truth lemma variant is used (K-family, T-family, D-family), (b) which frame condition hypotheses are stated. K (367 lines) and D (468 lines) have unique truth lemma infrastructure; the remaining 13 systems (159-205 lines each) are near-identical. Files: Cslib/Logics/Modal/Metalogic/Completeness.lean (add parametric cascade), all 15 Systems/*/Completeness.lean. Target: ~1,200-1,500 lines reduced. Depends on task 335 (soundness refactor must land first since strong_soundness wraps per-system soundness).

---

### 335. Parametric modal soundness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [335_parametric_modal_soundness/reports/01_parametric-modal-soundness.md]

**Description**: Extract a shared propositional axiom soundness lemma in Modal/Metalogic/Soundness.lean handling the 5 cases identical across all 15 modal systems (implyK, implyS, efq, peirce, modalK). Then refactor all 15 Systems/*/Soundness.lean files to call the shared lemma, keeping only system-specific modal axiom cases (modalT, modalFour, modalB, modal5, modalD). Currently 15 files totaling 1,291 lines with ~40 lines of identical propositional case-splits in each. Files: Cslib/Logics/Modal/Metalogic/Soundness.lean (add shared lemma), Cslib/Logics/Modal/Metalogic/Systems/{K,T,B,D,S4,S5,K4,K5,K45,KB5,DB,D4,D5,D45,TB}/Soundness.lean (refactor to use it). Target: ~600 lines reduced.

---

### 334. Propositional refactoring audit
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Codebase refactoring audit for the LK sequent calculus module: (1) Extract shared Proposition.IsSubformula/subformulas definitions from Normalization.lean into a standalone Cslib/Logics/Propositional/Subformula.lean module, eliminating the duplicate LKIsSubformula/lkSubformulas in SubformulaProperty.lean and the Proposition.complexity name collision that caused it. (2) Audit all files under Cslib/Logics/Propositional/ for similar issues: duplicate definitions across modules, transitive import collisions, definitions that belong in shared utility files, overly large files that should be split, missing abstractions that would reduce code duplication, and namespace hygiene problems. (3) Propose and implement refactoring to produce a clean, minimal dependency graph consistent with CSLib CONTRIBUTING.md, ORGANISATION.md, and NOTATION.md standards. The subformula extraction is the concrete exemplar; the broader audit should cover the full propositional logic subtree

---

### 333. Normalization module refactor
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 332

**Description**: Refactor and split the 1099-line Normalization.lean into well-organized submodules following CSLib conventions. Proposed split: (1) Cslib/Logics/Propositional/NaturalDeduction/Normalization/Basic.lean — isNormal, isStronglyNormal predicates, SubformulaProperty; (2) Normalization/Reduction.lean — reduceRoot, normalizeAux, normalize; (3) Normalization/Termination.lean — redexWeight, sn_redexWeight_zero, redexWeight_zero_sn, normalizeAux_fixpoint, normalize_isStronglyNormal; (4) Normalization/SubformulaProperty.lean — subformula_property_of_isStronglyNormal, subformula_property. Clean up API: review private vs public visibility, ensure naming follows CSLib NOTATION.md and CONTRIBUTING.md conventions. Depends on 332.

---

### 332. Normalization termination proof
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Dependencies**: Task 290
- **Research**: [332_normalization_termination_proof/reports/03_commuting-and-wf-bridge.md]
- **Plan**: [332_normalization_termination_proof/plans/05_termination-plan-v5.md]

**Description**: Close the two remaining normalization-termination sorries for CSLib Theory.Derivation in Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean (the proof was split out of the former monolithic Normalization.lean). (1) reduceRootSubSN case h_8 at line ~1333 -- the impE(orE ...) commuting-conversion decrease; the mathematics is settled (commutingSum_sn_eq_zero is proved, and reduceRootSubSN's hA forces the major premise strongly normal so Ecc.maximalFormulas = empty and Ecc.commutingSum = 0), the blocker is a ~250-branch simp_all whnf blowup, fixed by proving the E-SN side facts as standalone bounded `have`s before a single `cases Dcc` (red attempt preserved in handoffs/termination-h8-Esn-attempt-red.lean.bak). (2) normalize_isStronglyNormal at line ~1349 -- the fuel-bound argument that `normalize` with 2^height fuel drives redexWeight to 0 (depends on (1)). Following Prawitz 1965 Ch. III-IV. Once both close, the subformula-property corollary (Normalization/SubformulaProperty.lean) and parent task 290 are fully discharged. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 290.

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
- **Status**: [COMPLETED]
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
- **Dependencies**: Task 316, Task 323, Task 363, Task 369

**Description**: Fill the propositional tableau completeness sorries (7 real sorries; soundness is already sorry-free after task 316). The open obligations are the truth-lemma / countermodel-extraction proofs in the three Completeness modules. Classical (Tableau/Classical/Completeness.lean): classicalExpandBranches_hintikka (line ~462) -- note the module's separate build break (bad Mathlib lemma ref + unsolved goals) is repaired first under task 363. Intuitionistic (Tableau/Intuitionistic/Completeness.lean): intTruthLemma (line ~89), intuitionisticOpenBranch_countermodel (~98), intuitionisticTableau_complete (~112). Minimal (Tableau/Minimal/Completeness.lean): minTruthLemma (~168), minOpenBranch_countermodel (~179), minimalTableau_complete (~190). Core technique: Hintikka-set argument -- a saturated open branch satisfies Hintikka conditions, from which a countermodel is extracted (a Boolean valuation for classical; a finite Kripke model for intuitionistic/minimal) and a truth lemma by formula induction matches forced/not-forced to the signed formulas at each world. Because task 369 parameterizes the intuitionistic and minimal tableau over (closurePred, modelBot), the int and min cases should be discharged ONCE as a single parametric truth-lemma/countermodel pair rather than duplicated. The tableau Decidable instances become genuinely sorry-free once these land. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 316, 323, 363, 369.

---

### 316. Propositional tableau soundness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 323
- **Research**:
  - [316_propositional_tableau_soundness/reports/01_soundness-research.md]
  - [316_propositional_tableau_soundness/reports/02_blockers-resolution.md]
- **Plan**: [316_propositional_tableau_soundness/plans/08_soundness-plan-revised.md]

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
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [301_temporal_tableau/reports/01_temporal-tableau-decision-procedure.md]
- **Plan**: [301_temporal_tableau/plans/01_temporal-tableau-decision-procedure.md]

**Description**: Implement tableau decision procedure for temporal logic (Cslib.Logic.Temporal.Formula) with until/since decomposition rules, time labels, and temporal ordering tracking. Most complex new tableau: until/since rules have no modal analogue, requiring branching decomposition with event-witness and guard-continue alternatives. Adapt patterns from bimodal decidability system (TimeOrdering, temporal rule structure, frame-class rules) but build fresh implementations on shared Foundations infrastructure. Include density and discreteness frame-class rules. Formula type has atom, bot, imp, untl, snce primitives using Lukasiewicz encoding. Files under Cslib/Logics/Temporal/Tableau/: Defs.lean, Rules.lean, TimeOrdering.lean, Branch.lean, Closure.lean, Saturation.lean, Soundness.lean, Completeness.lean. Estimated: 2,000-2,500 lines.

---

### 300. Modal extensions t s4 s5
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 299

**Description**: Extend modal K tableau (task 299) with frame-specific rules for reflexive (T), transitive (S4), and equivalence-relation (S5) frames. T: reflexivity rule (box phi at w implies phi at w). S4: transitivity-aware propagation with loop-checking for termination. S5: equivalence-class simplification (mirrors bimodal approach). Include rules for B (symmetric) and 5 (Euclidean) to cover full modal cube. Each extension needs own completeness proof showing extracted countermodel satisfies frame condition. Files: FrameRules.lean, LoopChecking.lean, S5Simplification.lean, FrameSoundness.lean, FrameCompleteness.lean. Estimated: 1,200-1,800 lines.

---

### 299. Modal k tableau
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [299_modal_k_tableau/reports/01_modal-k-tableau-research.md]
- **Plan**: [299_modal_k_tableau/plans/01_modal-k-tableau-plan.md]

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
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [245_formula_encodable_countable_instances/reports/01_encodable-countable-denumerable-instances.md]
- **Plan**: [245_formula_encodable_countable_instances/plans/01_encodable-countable-denumerable-instances.md]
- **Summary**: [245_formula_encodable_countable_instances/summaries/01_encodable-countable-denumerable-instances-summary.md]

**Description**: Add Encodable, Countable, and Denumerable instances for LTL Formula type (deferred to completeness PRs)

---

### 241. Mcnaughton theorem
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**:
  - [241_mcnaughton_theorem/reports/01_ctchou-coordination-seed.md]
  - [241_mcnaughton_theorem/reports/02_mcnaughton-ctchou-port-path.md]
- **Plan**: [241_mcnaughton_theorem/plans/01_mcnaughton-da-muller.md]
- **Summary**: [241_mcnaughton_theorem/summaries/01_mcnaughton-da-muller-summary.md]

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
