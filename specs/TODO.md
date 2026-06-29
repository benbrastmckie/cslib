---
next_project_number: 411
---

# TODO

## Task Order

*Updated 2026-06-29. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,241,278,299,301,317,321,370,385,386,387,388,396,400,401,403,404,406,407 | -- | Bimodal Porting, Foundations, Modal Logic, ... |
| 2 | 39,40,181,215,300,375,389,390,405,408,409,410 | 36,37,180,299,317,387,404,407 | Bimodal Porting, Modal Logic, Propositional Logic, ... |
| 3 | 41,275,391,392 | 39,40,386,387,389 | Bimodal Porting, Foundations, Propositional Logic |
| 4 | 393 | 386,391 | Propositional Logic |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 
275 [BLOCKED] — Prove that Bimodal TM is conservative over Temporal BX for tempor

### Foundations

278 [NOT STARTED] — Simplify proofs using new simp/grind normalization tags. After ta
41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Modal Logic

299 [PLANNED] — Implement tableau decision procedure for basic modal logic K with
  └─ 300 [NOT STARTED] — Extend modal K tableau (task 299) with frame-specific rules for r
396 [NOT STARTED] — Evaluate and salvage the architecture-independent proof-engineeri
404 [NOT STARTED] — Replace the local private re-proofs of List.Forall2 lemmas in Csl
  └─ 405 [NOT STARTED] — Simplify the proof machinery in the task-402 modal tableau soundn

### Project Management

403 [NOT STARTED] — Rename specs/384_modal_tableau_soundness_gap_redesign/ to specs/4

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
317 [PLANNED] — Fill the propositional tableau completeness sorries (7 real sorri
  └─ 375 [NOT STARTED] — Complete the cross-system equivalence story by folding the tablea
  └─ 389 [NOT STARTED] — [Reconciled by task 395.] Tier-2. (a) Foundations/Order/HilbertAl
    └─ 391 [NOT STARTED] — [Reconciled by task 395.] Tier-3. Remove internal task/process ja
      └─ 393 [NOT STARTED] — Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING befo
    └─ 392 [NOT STARTED] — [Reconciled by task 395.] Tier-3. Delete grep-verified dead decls
370 [PLANNED] — Close the decidability asymmetry in the metalogic layer: classica
385 [NOT STARTED] — [Reconciled by task 395, post-merge.] Tier-1. LK/Interpolation su
386 [NOT STARTED] — [Refreshed by post-merge vet sess_1782671052_6af6a1; supersedes t
  └─ 392 [NOT STARTED] — [Reconciled by task 395.] Tier-3. Delete grep-verified dead decls (see above)
  └─ 393 [NOT STARTED] — Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING befo (see above)
387 [NOT STARTED] — [Refreshed post-merge vet.] DECISION REQUIRES UPSTREAM AGREEMENT.
  └─ 390 [NOT STARTED] — [Refreshed post-merge vet.] The Propositional section (~ORGANISAT
  └─ 392 [NOT STARTED] — [Reconciled by task 395.] Tier-3. Delete grep-verified dead decls (see above)
388 [NOT STARTED] — [Reconciled by task 395, post-merge.] Tier-2. NaturalDeduction/No
400 [IMPLEMENTING] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
401 [NOT STARTED] — From Matthew Doty's Atom->Bool vs Atom->Prop concern (DPLL portab
407 [IMPLEMENTING] — DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat
  └─ 408 [NOT STARTED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 5. Lar
  └─ 409 [NOT STARTED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
  └─ 410 [NOT STARTED] — Research and formalize the per-fragment algebraic completeness ne

### Temporal Logic

180 [NOT STARTED] — Add allFuture (G) and allPast (H) as primitive constructors to Te
241 [IMPLEMENTING] — Prove McNaughton's theorem (proof_wanted IsRegular.iff_da_muller)
301 [IMPLEMENTING] — Implement tableau decision procedure for temporal logic (Cslib.Lo
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Code Hygiene

321 [NOT STARTED] — Review file size and structure throughout Logics/ and Foundations
406 [NOT STARTED] — NEW from post-merge vet (sess_1782671052_6af6a1). Fix 33 pre-exis

## Tasks

### 410. Fragment-generic algebraic completeness for MPL-base derivability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 407

**Description**: Research and formalize the per-fragment algebraic completeness needed to instantiate the fully-generic Derivable P-logic framework. Current residual from task 407 (phase 7 S3 spike): FragmentGeneric.lean delivers AlgEvalIndependent + generic_gha_implies_ha + ghaValid_of_botFree (the GHAValid <-> HAValid equivalence for bot-free formulas). The remaining step -- HAValid phi -> Derivable X-logic phi for a specific sub-logic X -- requires per-fragment algebraic completeness, which is not currently generic in P. Each fragment has its own canonical algebra model: IsBotFree routes through WithBot G + Heyting completeness; IsOrBotFree routes through LowerSet B + Brouwerian completeness; IsImpTopOnly routes through the Rasiowa free algebra. A fully generic Derivable P-logic phi <- HAValid phi parameterized by P is open research. Research goal: (1) identify what algebraic completeness property a fragment P needs to satisfy so that the generic framework closes; (2) state and prove a typeclass or predicate CanAlgComplete P such that (CanAlgComplete P, AlgEvalIndependent P) implies generic Derivable P-logic phi <-> GHAValid phi; (3) instantiate for at least IsBotFree and IsOrBotFree; (4) determine whether IsImpTopOnly can be recovered. See Cslib/Logics/Propositional/Semantics/Algebra/FragmentGeneric.lean lines 40-53 for the open residual. References: Rasiowa1974 (algebraic approach), task 407 reports 01-03. Task type: cslib. Depends on 407 (delivers FragmentGeneric.lean).

---

### 409. Literal ⊥-rule-free base ND inductive (option B): split MinDerivation + Explosion; re-cut Curry-Howard & normalization
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 407

**Description**: SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- OPTIONAL / advanced. Task 407 adopts option C (re-frame the task-398 gated efq constructor as the explosion property module; the base relation is ⊥-rule-free UP TO the IsIntuitionistic gate). Option B is the LITERAL structure-first ND: split Theory.Derivation into a genuinely ⊥-rule-free base inductive MinDerivation (no efq constructor) plus an Explosion extension, prove all structural metatheory once on the base, and recover IPL-ND by adjoining efq. TRIGGER CONDITION: only pursue if a concrete downstream consumer needs a physically ⊥-free derivation object (e.g. a minimal-ND normalization theorem, or a lambda-calculus without an abort/efq combinator). COST/RISK: re-opens the single genuinely hard point from task 398 -- the subformula property under efq -- and forces re-cutting Curry-Howard (Theory.Term mirror) and Prawitz normalization (Basic/Reduction/Termination/SubformulaProperty) against the split. Reuse the task-398 decided strategy (atomic restriction + permutation conversions); treat any non-green proof as [BLOCKED], never sorry. HIGH effort -- use --hard. Depends on 407 (and ideally 408). Source: task 407 report 01 §5 option B / §7 W6, report 02 §5. ALIGNMENT NOTE: this two-inductive split is the Design-B-flavored route that the universal-algebra approach (task 407 option C) deliberately AVOIDS, because it duplicates derivation structure (exclude-then-add at the derivation level). Default remains task 407 option C: ONE derivation type with explosion as a property module. Pursue 409 ONLY if the trigger condition above fires.

---

### 408. Sequent calculus: property-gated botL (single calculus, MPL/IPL one inductive; cut/subformula proved once)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 407

**Description**: SPAWNED from task 407 (MPL structure-first redesign), Wave 5. Largest structural gap (report 01 §3.4/§7.1): LJProof/LKProof HARD-CODE the botL/explosion rule (SequentCalculus/LJ/Basic.lean:91-92, LK/Basic.lean:76-77) and there is NO minimal sequent calculus; cut elimination/subformula/decidability/interpolation are proved per-system, not once at a base. PRIMARY DESIGN (universal-algebra approach, aligned with task 407 option C): a SINGLE sequent calculus over the full signature (incl. primitive ⊥) with a PROPERTY-GATED botL constructor -- gate botL by [IsIntuitionistic T] (mirroring task 407's gated efq in ND), so MPL and IPL are the SAME inductive at different property strengths and the structural metatheory (cut elimination, subformula property) is proved ONCE generically over the gate. MPL = the strength WITHOUT the IsIntuitionistic instance; IPL = WITH it. This avoids the exclude-then-add / two-inductive duplication cost and keeps the sequent layer consistent with the ND layer. SCOPE: cleanly unifies MPL/IPL (single-conclusion); LK (classical, multiple-conclusion) is a different structural shape and stays its own calculus, related via its own module rather than folded in. FALLBACK (only if property-gating cut-elimination proves infeasible): define a separate minimal LMProof inductive (LJ rules minus botL), prove structural results once on LM, recover LJ = LM + botL by composition/re-export. Preserve all existing LJ/LK results (soundness, hilbert_iff_lj/lk, LJProof.cutElim/LKProof.cutElim) -- no weakening. HIGH effort -- use --hard. Depends on 407 (gated-rule design + property modules) and green main. Files: SequentCalculus/Defs.lean, LJ/* (gated botL + generic cut/subformula), LK/* (relate). Honor Zulip AI policy (human-authored prose). Source: task 407 report 01 §3.4/§7 W5, report 02 §6.

---

### 407. Research & design: make MPL the structure-first base logic (⊥ as nullary connective; explosion/leastness/initiality as independent property modules)
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 398
- **Research**:
  - [407_mpl_base_structure_first_redesign/reports/01_mpl-base-structure-first.md]
  - [407_mpl_base_structure_first_redesign/reports/02_mpl-base-with-vs-without-bot.md]
  - [407_mpl_base_structure_first_redesign/reports/03_design-verification-plan-readiness.md]
- **Plan**: [407_mpl_base_structure_first_redesign/plans/04_mpl-base-waves-1-4-v2.md]
- **Summary**: [407_mpl_base_structure_first_redesign/summaries/04_mpl-base-waves-1-4-v2-summary.md]

**Description**: DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat.md) + codebase synthesis. Adopt the STRUCTURE-FIRST account: one fixed language ⟨Atom,⊥,∧,∨,→⟩; ⊥ is a primitive NULLARY connective whose meaning is intentionally underdetermined (a Johansson 'designated constant' supplied by every model, no intrinsic proof rule). MPL is the BASE proof theory (no rule/axiom mentions ⊥; ¬A:=A→⊥; A,A→⊥⊢⊥ is just impE). IPL = MPL + explosion (⊥/A) as an INDEPENDENT module; CPL = IPL + classical principles. Semantically, leastness (⊥≤a), initiality (universal property 0→A), and explosion-soundness are INDEPENDENT properties added by conservative strengthening, not changes to syntax or recursive clauses. Modularity organized around PROPERTIES (typeclasses/mixins), not connectives, so structural metatheory (weakening, substitution, admissibility, cut) is proved ONCE at MPL. RELATION TO 398: this is the deeper redesign 398 postponed (398 report §5). 398 took the OPPOSITE commitment (IPL-as-base via a gated ND efq constructor). Recommendation (report §5) is option (C): re-frame 398's gate as the explosion PROPERTY MODULE rather than revert it. FINDINGS (report 01): codebase is already ~70-80% structure-first. ALIGNED: algebraic semantics (AlgEvaluate with arbitrary bot_val; BrouwerianBot vs PointedBrouwerian; IsBotFree; conservativity chains) and Hilbert axioms (MinPropAxiom→IntPropAxiom+efq→PropositionalAxiom+peirce; IsIntuitionistic/MinimalAxioms typeclasses). GAPS: (1) ND inverted by 398 (gated efq = IPL-base); (2) sequent calculus LARGE gap (LJ/LK hard-code botL; no minimal LM; structural results per-system); (3) metalogic ~50% Min*/Int* duplication, Lindenbaum hard-wires EFQ; (4) semantic leastness/initiality/explosion present only implicitly (OrderBot + per-axiom proofs), not as a NAMED property hierarchy. SCOPE: research+design done (report 01). Plan should cover the cheap additive waves first: W1 design canonicalization+ND re-framing (C), W2 named semantic property hierarchy, W3 metalogic genericization, W4 tableau unification; and SPAWN W5 (minimal sequent calculus LM) and optional W6 (literal ⊥-rule-free ND, option B) as separate --hard tasks. Preserve ALL MPL/conservativity assets (do not revert 398). --hard recommended for planning. Honor Zulip AI policy. See OPEN QUESTIONS in report §9 (ND reconciliation C vs B; task scope; categorical/initiality timing; property naming; relation to task 400).

---

### 406. Fix cross-cutting lake lint across Modal/Temporal/Bimodal/Foundations (33)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: NEW from post-merge vet (sess_1782671052_6af6a1). Fix 33 pre-existing lake lint violations (not introduced by the merges but blocking CI globally -> hard repo push gate). Same pattern as the PL GenericMCSBridge/DeductionTheorem fixes (task 386). Modal: Metalogic/GenericMCSBridge.lean defLemma x1 + defsWithUnderscore x3 (deriv_tree_to_list, unfold_listImp_in_tree, list_deriv_to_tree), Tableau/Saturation.lean docBlame x1 (modalExpandBranches.processNext), Metalogic/DeductionTheorem.lean unusedArguments x1 (deductionWithMem arg9). Temporal: Metalogic/GenericMCSBridge.lean defLemma x2 + defsWithUnderscore x5, Tableau/Saturation.lean docBlame x1, Metalogic/DenseMCS.lean unusedArguments x1. Bimodal: Metalogic/Core/GenericMCSBridge.lean defLemma x2 + defsWithUnderscore x6, Metalogic/Core/DeductionTheorem.lean unusedArguments x1. Foundations: HilbertAlgebra/FreeMeetExtension.lean docBlame x7 (fld, fmeLe, fmeEquiv, fmeSetoid, FreeMeetExtension, mk, freeMeetEmbed), Logic/Metalogic/DeductionCharacterization.lean:109 defsWithUnderscore x1 (dt_inference_system). Rename underscores->lowerCamelCase, def->lemma, @[nolint unusedArguments]+comments, add docstrings. ABSORBS stale task 394 (foundations_logic_cleanup). Best coordinated with task 386's GenericMCSBridge renames. Verify `lake lint` green. Source: vet findings.

---

### 405. Proof style cleanup modal soundness
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 404

**Description**: Simplify the proof machinery in the task-402 modal tableau soundness redesign before any upstream PR. Targets in Cslib/Logics/Modal/Tableau/Soundness.lean: modalApplyOne_fresh (uses unfold + extract_lets + `repeat first | Or.inl rfl | Or.inr ... | split` plus an apply_ite/ite_self cleanup) and the modalExpandBranches_closed_unsat per-branch accs/Forall2 reformulation. Improve readability/robustness without changing statements. Verify scoped + full lake build green, zero sorry, lint-style pass. Touches the same file as task 404 (sequence after it); overlaps code-hygiene task 321.

---

### 404. Forall2 mathlib cleanup soundness
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Replace the local private re-proofs of List.Forall2 lemmas in Cslib/Logics/Modal/Tableau/Soundness.lean (forall2_append_aux, forall2_drop_aux, forall2_take_aux, forall2_of_zip_mem) with canonical Mathlib lemmas. These were added during task 402 because Mathlib.Data.List.Forall2 is not transitively imported by Cslib.Init. Either add the Mathlib import and switch call sites to library lemmas (List.Forall2.append/length_eq/etc.), or document why the local helpers are kept. Verify scoped + full lake build green, zero sorry, lint-style pass. Low-priority polish; helpers are correct as-is.

---

### 403. Rename specs 384 to 402
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Project Management
- **Dependencies**: None

**Description**: Rename specs/384_modal_tableau_soundness_gap_redesign/ to specs/402_modal_tableau_soundness_gap_redesign/ to match task 402 (the soundness-gap redesign was renumbered 384->402 during the task-364 merge to avoid colliding with main task 384 tableau_completeness_sorries). git mv the directory and update task 402 artifact paths in specs/state.json (reports/01_soundness-gap-redesign.md, plans/01_per-branch-accessibility.md). Grep for any remaining 384_modal_tableau references. Bookkeeping only; no code changes.

---

### 401. Expose polymorphic AlgEvaluate at Bool/Prop as the canonical computable evaluator (DPLL)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: From Matthew Doty's Atom->Bool vs Atom->Prop concern (DPLL portability) and Waring's GeneralizedHeytingAlgebra-polymorphic evaluator suggestion in the Zulip thread. Surface the algebraic `AlgEvaluate` specialized at `Bool` (computable) and `Prop` as the canonical evaluation path, and reconcile with Semantics/Bool.lean (BoolEvaluate + bridge lemma + Decidable instance) so there is ONE documented story: Prop-valued `Evaluate` for uniformity with Kripke semantics; Bool/AlgEvaluate for decision procedures (DPLL/SAT). Keep `Valuation` = Atom->Prop (canonical model construction needs it). Confirm the bridge to prop_strong_soundness. Coordinate with Matthew's DPLL/Tseitin development. Lower priority; independent of the IPL-base work. Source: Zulip thread (msgs 603367168, 603520169, 603572691, 603755068, 603877853 on HasInterp/GHA).

---

### 400. Unbundle connective typeclasses; reconcile with fmontesi PR #607 (Waring's flag a)
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [400_reconcile_connectives_pr607/reports/01_pr607-engagement.md]
  - [400_reconcile_connectives_pr607/reports/02_engagement-strategy.md]
- **Plan**: [400_reconcile_connectives_pr607/plans/02_pr607-engagement.md]

**Description**: [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/reports/01_pr607-engagement.md] Engage fmontesi PR #607 (feat(Logic): logical operators) to land the connective typeclasses there instead of in #648 (Waring, Zulip 606970606). PREREQ DONE: our Connectives.lean removed from #648 (commit 85db79a6 on feat/propositional-ipl-base). PRIMARY POINT for the #607 review: #607 makes negation primitive (HasNot) and has NO HasBot; for IPL/MPL, neg is definitionally (phi -> bot), so #607 needs a HasBot (and HasTop) class with neg/top DERIVED, else the five-primitive Proposition (primitive bot) cannot register faithfully. SECONDARY: naming HasImpl/impl vs HasImp/imp; notation precedence conflicts (-> 25 vs 30, or 30 vs 35); bundle-vs-a-la-carte (PropositionalConnectives); notation ownership (typeclass notation + _def lemmas vs direct-on-Proposition). DELIVERABLE: human-authored review on #607 (Zulip AI policy), then register Proposition instances via #607 once the falsum question settles. Independent of the IPL-base work.

---

### 399. Update PR #648 to the settled IPL-base foundation per Waring's end-of-thread recommendation
- **Status**: [COMPLETED]
- **Task Type**: pr
- **Topic**: Propositional Logic
- **Dependencies**: Task 398
- **Research**: [399_refresh_pr648_ipl_base_foundation/reports/01_pr648-refresh-research.md]
- **Plan**: [399_refresh_pr648_ipl_base_foundation/plans/01_pr648-refresh-plan.md]
- **Artifact**:
  - [399_refresh_pr648_ipl_base_foundation/cherry-pick-recipe.md]
  - [399_refresh_pr648_ipl_base_foundation/prepare-foundation-branch.sh]
  - [399_refresh_pr648_ipl_base_foundation/pr-description.md]
  - [399_refresh_pr648_ipl_base_foundation/zulip-response.md]

**Description**: [REVISED 2026-06-29 — minimal additive approach supersedes the cherry-pick recipe. Implementation DONE & verified on branch feat/propositional-ipl-base, commit 5dbed274 (3-file diff, 594 jobs green, lint clean, zero sorry): ungated primitive efq constructor makes IPL the base; IPL:=∅; MPL/IsIntuitionistic/intuitionisticCompletion removed; classical layer kept. Update #648 via FAST-FORWARD push of feat/propositional-ipl-base:feat/propositional-v2 (no force-push). Remaining = human: review, ff-push, reword PR description, post Zulip 606970606. MPL-as-base dispute deferred to tasks 407/408/409. See ipl-base-minimal-revision.md.] Update PR #648 (feat/propositional-v2) following Thomas Waring's closing recommendation in the CSLib Zulip 'Propositional Logic' thread (606970606). PR #648 is ~239 commits behind fork main, which is why Waring reports the restored references and Zulip-thread link are 'not in the PR' (both ARE on main at NaturalDeduction/Basic.lean:76 + the Design trade-off note). PLAN (per the user's chosen strategy): branch off upstream/main and cherry-pick the propositional FOUNDATION as a focused, reviewable commit, then update #648 to that branch. Scope of the foundation: the five-primitive `Proposition` type with primitive `⊥`; NaturalDeduction/Basic with the settled IPL-as-base design (efq as a primitive ND rule — see task 398); restored references AND the Zulip-thread link (Waring's flag (b)). EXCLUDE connective typeclasses — Waring flagged these as a SEPARATE development (task 400); do not bundle them. Keep the PR small (Matthew + Waring both asked for small pieces); later layers (Hilbert+equivalence, algebraic semantics incl. retained MPL metatheory, conservativity chains, sequent LJ/LK, tableau) follow as separate stacked PRs. Note /pr is user-only (branch creation, CI, submission); this task prepares the cherry-pick + a human-authored PR/Zulip description for the user to push (Zulip AI policy). Waring will 'review the PR properly once we've settled on the design', so this depends on task 398 (efq/IPL-base implemented). Also coordinate with PR-readiness vet tasks 386/387/389. Source: Zulip thread 606970606.

---

### 398. Make IPL the base propositional logic: add efq as a primitive ND rule, preserving MPL metatheory
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 397
- **Research**: [398_efq_nd_rule_ipl_base_keep_mpl/reports/01_efq-primitive-ipl-base.md]
- **Plan**: [398_efq_nd_rule_ipl_base_keep_mpl/plans/01_efq-primitive-implementation.md]
- **Summary**: [398_efq_nd_rule_ipl_base_keep_mpl/summaries/01_efq-primitive-summary.md]

**Description**: DESIGN SETTLED (CSLib Zulip 'Propositional Logic' thread, Waring's closing message 606970606 + our synthesis): take IPL as the base propositional logic FOR NOW by adding ex-falso (efq / bottom-elimination) as a PRIMITIVE constructor of the ND `Derivation` so that the primitive `⊥` constructor is actually interpreted (Waring: 'it seems very unnatural to have a constructor with no semantics'). This makes minimal logic the positive fragment IPL<→,∧,∨,⊤> conceptually, and makes the conservativity results' `IsBotFree` predicate framing more natural (Waring's point). CRITICAL CONSTRAINT (our decision, diverging from Waring's 'forget minimal logic'): PRESERVE all completed MPL work — do NOT delete it. Keep MinSoundness, MinLindenbaum, MinStrongCompleteness, MPL completeness (`MPL.hilbert_alg_complete`), the `bot_val`/Johansson-algebra parametric semantics, and the MPL/IPL conservativity chains (MplConservativeChain, ConservativeChain, ImpConservative, etc.). Minimal logic stays as a retained LAYER beneath IPL, sequenced for later fragment work, not removed. Current state: efq is a DERIVED rule (`Theory.Derivation.botE`) gated by `[IsIntuitionistic T]` in NaturalDeduction/DerivedRules.lean; ND/Basic.lean documents the trade-off. WORK: (1) add efq as a primitive ND `Derivation` constructor available at IPL/CPL strength; (2) keep the ND<->Hilbert equivalence (`hilbert_iff_nd*`) provably intact so efq-as-rule and efq-as-axiom coincide and MPL (no efq rule) still corresponds; (3) keep substitution lemmas, DecidableEq, and the `FromPropositional` embeddings green; (4) update ND/Basic.lean Implementation-notes to record IPL-as-base with MPL retained; (5) postpone general fragment design (Waring). Verify full `lake build` + downstream Modal/Temporal/Bimodal. Honor Zulip AI policy (human-authored prose). Depends on 397 (green main for verification). Source: Zulip thread 606970606.

---

### 396. Salvage reusable lemmas from task-299 Soundness refactor for the per-branch-accessibility soundness redesign
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Evaluate and salvage the architecture-independent proof-engineering lemmas left on branch wip/task-299-soundness-refactor (commit 27d93e2d) by the stopped task-299 modal-K soundness re-attempt. Portable (acc-free) candidates: sfSat, sfSat_pos, sfSat_neg, RuleResultSat, and recognizer characterization lemmas (e.g. modalNegOf?_eq_some) in Cslib/Logics/Modal/Tableau/Soundness.lean, plus the branchSatisfiable Type (vs Type*) universe simplification. The FULL 299 refactor is UNBUILT and rewrites modalStepBranch_preserves_sat on the now-superseded global-Accessibility architecture, so do NOT merge it wholesale. Goal: decide which lemmas help the modal-tableau soundness-gap-redesign effort (the per-branch Accessibility 'task 384' tracked in the cslib-364 worktree / branch task-364-soundness-drift) and cherry-pick or restate them there if the propositional-rule recognizer layer hits the 'stuck on variable antecedent / consumed-scrutinee' friction documented in specs/364_modal_tableau_soundness_drift_repair/handoffs/BLOCKED-repair-guide.md (section 4). NOTE: 'task 384' here means the soundness-gap-redesign task in the cslib-364 worktree, which is a DIFFERENT task than main's own #384 (tableau_completeness_sorries) — task numbering diverged across worktrees. Reference branch: wip/task-299-soundness-refactor. Parent context: task 299 modal_k_tableau.

---

### 395. Review and revise vet tasks 384-394 after all worktrees merge into main
- **Status**: [COMPLETED]
- **Task Type**: meta
- **Topic**: Project Management
- **Dependencies**: None
- **Research**: [395_reconcile_vet_tasks_post_merge/reports/01_vet-reconciliation.md]

**Description**: META / coordination task. PRECONDITION: do NOT start until ALL feature worktrees branched off main have been merged into main (cslib-wt-orch = orchestrate-369-374-317-375-373-382; cslib-364 = task-364-soundness-drift; cslib-wt-orch2 = orchestrate-299-300-301-241). Once integrated, review and revise the vet fix-tasks 384-394 (created from specs/vet-propositional-foundations.md) against the work that actually landed, since several overlap in-flight worktree tasks. Known overlaps to reconcile by reading the merged CODE (worktree state.json statuses are stale): task 374 completed LK/LJ interpolation (maeharaCore sorry-free + public Craig theorem + barrel) => likely makes task 385 redundant; task 382 removed dead Dershowitz-Manna termination machinery => likely makes task 388 redundant; tasks 369 (parameterize int/min tableau) + 317 (unified completeness) advance task 384 (the 6 live tableau-completeness sorries). For each of 384-394: mark completed/abandoned if landed, revise scope/description for partial overlap, or keep as-is. Re-run the vet CI checks (lake build/lint/mk_all on Propositional+Foundations) after integration to refresh ground truth and add/remove tasks accordingly. Then commit the reconciled task list.

---

### 393. Consolidate duplicated Lindenbaum/Classical/conservativity constructions (Zulip first)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 386, Task 391, Task 395

**Description**: Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING before refactor. (a) Factor one generic quotient-Lindenbaum construction over the 3 parallel builds (~2100 lines): HilbertLindenbaum, HilbertLindenbaumRel, HilbertAlgCompleteness (4th in Bimodal). (b) Make litCtx_congr public and parameterize the 3 Classical completeness files (~700 lines, litCtx_congr' copied 3x) over the axiom predicate via GenericMCSBridge/HasMinimalAxioms. (c) Assess 3 Soundness modules + 8 conservativity modules + LJ/LK helper duplication. Source: §5.5.

---

### 392. Remove dead declarations and fix underscore/Extention naming
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 386, Task 387, Task 389, Task 395

**Description**: [Reconciled by task 395.] Tier-3. Delete grep-verified dead decls: Tableau/Classical/Soundness.lean:73-136 (12 classicalApplyOne_* private simp lemmas, 0 calls) + :486, Classical/Completeness.lean:435/447, Tableau/Defs.lean:81 propImpOrNegOf?, Intuitionistic/Rules.lean:114/203, Intuitionistic/Soundness.lean:431/505, NaturalDeduction/Equivalence.lean:305 hilbertAxiomToND, LK/Completeness.lean:69/73 mem_insert_*. Fix Extention->Extension typo (Equivalence.lean:256-257, Defs.lean:190/195). Rename underscore defs: modus_ponens constructor (Derivation.lean:77), lift_int_to_cl, goodSelection_seq, HasFresh to_infinite, emptyHrelation_apply. The LK/LJ cutAdm_*/ljCutAdm_* renames are DROPPED from this task — task 386 OWNS them (defsWithUnderscore). Sequence after 386. Source: §5.3-5.4 + 395.

---

### 391. Strip task-number jargon and fix stale docstrings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317, Task 389, Task 395

**Description**: [Reconciled by task 395.] Tier-3. Remove internal task/process jargon from public docstrings: ClassicalConjImpCompleteness.lean (task 352, CL-B rung), ClassicalConjImpBotCompleteness.lean (task 378, CL-C rung), ConservativeChain.lean:44-45, HilbertLindenbaumRel.lean:21-23 (Route A2, 341 proof files), Tableau/RuleResult.lean:35, Foundations/Logic/Tableau/PropositionalTableau.lean:7, ListImplication.lean:83-139. Connectives.lean jargon (PR#607/task 340/173) is OWNED by task 400 (Connectives owner) — coordinate, do NOT double-edit. Stale-count fixes: re-verify post-task-398. NOTE StrongCompleteness 3-case counts (atom/bot/imp) remain CORRECT (398 changed derivation constructors, not formula structure). Fix only genuinely-stale counts: IntSoundness, MinSoundness, IntLindenbaum:320 misattached docstring, Tableau Int/Min DecisionProcedure sorry counts, Minimal/Completeness:50-51. Source: §5.1-5.2 + 395.

---

### 390. Update ORGANISATION.md Propositional section (post-merge tree)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 387, Task 395

**Description**: [Refreshed post-merge vet.] The Propositional section (~ORGANISATION.md:100-105) is a 4-item stub. Update to reflect the actual 95+-file tree: SequentCalculus/{LJ,LK} (Interpolation, CutElimination, SubformulaProperty, Decidability); CurryHoward/{Defs,Isomorphism,Reduction}; Semantics/Algebra (25+ files: Brouwerian, HilbertAlgebra, Kripke, Glivenko, Conservative variants); Tableau/{Classical,Intuitionistic,Minimal} (Completeness/Soundness/DecisionProcedure); Subformula.lean; ProofSystemEquivalence.lean. Also update the Namespace Convention section re Cslib.Logic.PL vs Cslib.Logic.Propositional (task 387). Do before the PR lands.

---

### 389. Fix docBlame, barrel headers, unusedSectionVars, broken citation
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317, Task 395

**Description**: [Reconciled by task 395.] Tier-2. (a) Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean: add docstrings to 7 undocumented def/abbrev (fld:50 also rename himpFold, fmeLe:106, fmeEquiv:123, fmeSetoid:125, FreeMeetExtension:152, mk:159, freeMeetEmbed:257) — only hard docBlame in Foundations. (b) DROPPED — the 4 Tableau barrels already carry copyright + import Cslib.Init (verified post-merge). (c) Add omit for 14 unusedSectionVars (mostly Tableau/Classical/Completeness, Minimal/Soundness:118, Minimal/Completeness:89). (d) Add references.bib entry NegriVonPlato2001 (Negri & von Plato, Structural Proof Theory, CUP 2001) cited by OrImpConservative.lean. Sequence the Tableau/Classical+Minimal Completeness edits AFTER task 317. Source: §4.3-4.6 + 395.

---

### 388. Remove dead normalization track and heartbeat/simp debt in Termination.lean
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 395, Task 398

**Description**: [Reconciled by task 395, post-merge.] Tier-2. NaturalDeduction/Normalization/Termination.lean + Reduction.lean cleanup. The redexWeight + normMeasure fuel/measure track is ALREADY GONE (delivered by merged task 382). `normalize`/`normalizeAux` are NOW LIVE (task 398 added efq arms) — do NOT delete them. Remaining dead PRIVATE decls (0 callers, safe to delete): normalizeAux_fixpoint (Termination.lean:305), subs_maximalFormulas_mem (:492), subsOne_new_redex_complexity_lt (:775). Then clear residual lint debt: unused simp args, no-op/dead tactics, long lines, flexible-simp; remove or comment-justify maxHeartbeats overrides; decompose remaining heavy proofs. SEQUENCE AFTER task 398 (it is actively editing Termination.lean). Source: §4.2 + 395.

---

### 387. PL -> Propositional namespace rename (upstream-gated)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 395

**Description**: [Refreshed post-merge vet.] DECISION REQUIRES UPSTREAM AGREEMENT. All Propositional files use `namespace Cslib.Logic.PL`; ORGANISATION.md specifies `Cslib.Logic.Propositional`. The PR #648 foundation slice exposes this publicly (Defs.lean:78, NaturalDeduction/Basic.lean:94). Breaking rename -> open an upstream Zulip thread for maintainer consensus FIRST (human-authored, AI policy), then mechanically rename across all Propositional files + downstream consumers (Modal/Temporal/Bimodal FromPropositional/Embedding). Until agreed, note as pending in the PR #648 description. Does NOT block the PR #648 foundation cherry-pick.

---

### 386. Fix Propositional-specific lake lint violations (21, post-merge)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 395

**Description**: [Refreshed by post-merge vet sess_1782671052_6af6a1; supersedes the pre-merge scope.] Fix the 21 PL-specific lake lint violations (hard CI gate for a clean repo push). (a) defsWithUnderscore (13) -> lowerCamelCase: GenericMCSBridge.lean:133 deriv_tree_to_list, :165 unfold_listImp_in_tree, :192 list_deriv_to_tree; SequentCalculus/LJ/CutElimination.lean:116/225/350 ljCutAdm_principal_andR/orR/impR, :462/543 ljCutAdm_left/right; SequentCalculus/LK/CutElimination.lean:145/293/437 cutAdm_right_andR/orR/impR, :586/708 cutAdm_right/left. (b) defLemma (1): GenericMCSBridge.lean:133 deriv_tree_to_list def->lemma (same decl as the rename). (c) docBlame (3): docstrings for Tableau/Classical/Expansion.lean:125 classicalExpandBranches.processNext, Tableau/Intuitionistic/Expansion.lean:169 intExpandBranches.go, Tableau/Intuitionistic/Rules.lean:91 isAccessible.go. (d) unusedArguments (3): targeted @[nolint unusedArguments] + comment: Metalogic/DeductionTheorem.lean:85 deductionWithMem arg9 _hA, Normalization/Termination.lean:41 conclusionGrounded arg6 _d, Tableau/Intuitionistic/Soundness.lean:1643 intBotForces arg1. (e) simpNF (1): Subformula.lean:173 vars_neg LHS not simp-normal (rewrite LHS or @[nolint simpNF]). Coordinate GenericMCSBridge renames with the cross-cutting task (403). Verify `lake lint` PL-clean. Source: specs/369_*/.vet-findings.json. [395-reconciled: task 386 OWNS the LK/LJ cutAdm_*/ljCutAdm_* underscore renames (defsWithUnderscore); task 392 drops them. Re-run `lake lint` after the build is green (task 385/IntFMPSpike) to refresh the exact violation set before fixing.]

---

### 385. Complete and integrate IntFMPSpike, LK/Interpolation, Tableau Scheme
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 395

**Description**: [Reconciled by task 395, post-merge.] Tier-1. LK/Interpolation sub-part DROPPED — task 374 delivered LKProof.interpolation sorry-free (Interpolation.lean:864). TWO sub-parts remain: (1) BUILD-BLOCKER, DO FIRST: IntFMPSpike.lean has 2 compile errors (lines 201/231) and is the ONLY thing breaking repo-wide `lake build` (imported at Cslib.lean:419). Fix the 2 errors, strip spike/specs-370 framing, rename to IntDecidability.lean, keep wired into Cslib.lean + barrel. (2) Tableau/Intuitionistic/Scheme.lean: finish the 4 parked sorries (truthLemma:242 parametric over IntMinScheme; openBranch_countermodel:280/288/296 — :296 has ready classical analogue classicalExpandBranches_openBranch_initial_mem); ideally repoint Intuitionistic/Minimal completeness at the parametric route (coordinates with 317). Verify full lake build green + lint-style. Source: §3.2-3.4 + 395 reconciliation.

---

### 384. Resolve documented sorry in minimalTableau_complete
- **Status**: [ABANDONED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 395

**Description**: [Refreshed post-merge vet; scope narrowed.] The single remaining tableau sorry is at Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:110 (theorem minimalTableau_complete), documented in the module header as deferred to task 317. It bridges MValid phi to the per-branch forcing hypothesis for `tableau_complete minScheme`; resolution needs upward-closure of intExtractValuation and minBranchBotForces. Not in the PR #648 foundation slice. Decide with upstream whether acceptable as documented WIP or must be gated.

---

### 375. Proof system equivalence tableau sequent edges
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317, Task 363

**Description**: Complete the cross-system equivalence story by folding the tableau (and remaining sequent) decision systems into the proof-system TFAE. Cslib/Logics/Propositional/ProofSystemEquivalence.lean currently proves Hilbert<->ND<->LK for CPL (cplProofSystemsTfae) and Hilbert<->ND<->LJ for IPL (iplProofSystemsTfae), plus the MPL Hilbert<->ND two-way. Add the missing edges so the equivalence is genuinely complete across all proof systems: classical Tautology <-> LK provability <-> closed classical tableau, and intuitionistic validity <-> LJ provability <-> closed intuitionistic tableau, extending the TFAE lists accordingly. Requires the tableau soundness+completeness to be green (task 316 done for soundness; task 317 for completeness) and the classical tableau build repaired (task 363). No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 317, 363.

---

### 370. Int min metalogic decidability
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [370_int_min_metalogic_decidability/reports/01_int-min-decidability-fmp-vs-lj.md]
- **Plan**: [370_int_min_metalogic_decidability/plans/01_int-min-fmp-decidability.md]

**Description**: Close the decidability asymmetry in the metalogic layer: classical propositional logic has a decision procedure (instDecidableDerivablePropositionalAxiom via tautology enumeration, Metalogic/StrongCompleteness.lean:566), but intuitionistic (IntPropAxiom) and minimal (MinPropAxiom) logics have none. Establish Decidable (Derivable IntPropAxiom phi) and Decidable (Derivable MinPropAxiom phi) via the finite model property: bound the canonical Kripke models (prime DCCS / MinTheory worlds) by the subformulas of phi, give a terminating decision procedure over the finite model space, and prove it correct against the existing int/min strong-completeness theorems (IntStrongCompleteness.lean, MinStrongCompleteness.lean). Independent of the tableau decision procedures (which currently rest on unproved completeness witnesses). Note: the LJ sequent calculus already has a tableau-backed decidability instance (SequentCalculus/LJ/Decidability.lean) -- assess whether the FMP route or a bridge to LJ decidability is the cleaner source for the IPL instance before implementing. No new axioms (Classical.choice / Decidable.decide acceptable on noncomputable defs); CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake).

---

### 360. Repair 11 pre-existing broken modules failing repo-wide lake build
- **Status**: [ABANDONED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 363, Task 364

**Description**: The repo-wide 'lake build' currently fails (unrelated to vetted tasks 343/344/350/351/353/354, whose files build clean in isolation). Failing modules: Cslib.Logics.Modal.Denotation (simp made no progress, Denotation.lean:60), Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth (unsolved goals, multiple lines), Cslib.Logics.Temporal.ConservativeExtension (ambiguous term, lines 54/59/69), Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles (type mismatch, lines 84/164/176), Cslib.Logics.Temporal.Metalogic.DenseCompleteness (unsolved goals, line 166), Cslib.Logics.Propositional.SequentCalculus (duplicate _proof_1 environment clash between LJ and LK CutElimination), Cslib.Logics.Bimodal.Metalogic.Separation.Defs (many simp made no progress), Cslib.Logics.Propositional.Tableau.Minimal.Soundness, Cslib.Logics.Bimodal.ProofSystem.Substitution, Cslib.Logics.Modal.Tableau.Soundness, Cslib.Logics.Propositional.Tableau.Classical.Completeness. checkInitImports/shake also fail downstream due to missing oleans. Restore a green repo-wide build. Source: /vet CI run 2026-06-26.

---

### 321. Code hygiene logics foundations
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Review file size and structure throughout Logics/ and Foundations/ to identify and refactor files that are too long or poorly structured. Abstract and expose all and only what should be abstracted/exposed, maintaining the highest standards for code hygiene. Survey file lengths, identify candidates over ~400 lines, check for proper module boundaries, unnecessary public exports, missing abstraction barriers, and violations of single-responsibility principle. Produce a refactoring plan with prioritized actions

---

### 317. Propositional tableau completeness
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 316, Task 323, Task 363, Task 369
- **Plan**: [317_propositional_tableau_completeness/plans/02_tableau-completeness-unified.md]

**Description**: Fill the propositional tableau completeness sorries (7 real sorries; soundness is already sorry-free after task 316). The open obligations are the truth-lemma / countermodel-extraction proofs in the three Completeness modules. Classical (Tableau/Classical/Completeness.lean): classicalExpandBranches_hintikka (line ~462) -- note the module's separate build break (bad Mathlib lemma ref + unsolved goals) is repaired first under task 363. Intuitionistic (Tableau/Intuitionistic/Completeness.lean): intTruthLemma (line ~89), intuitionisticOpenBranch_countermodel (~98), intuitionisticTableau_complete (~112). Minimal (Tableau/Minimal/Completeness.lean): minTruthLemma (~168), minOpenBranch_countermodel (~179), minimalTableau_complete (~190). Core technique: Hintikka-set argument -- a saturated open branch satisfies Hintikka conditions, from which a countermodel is extracted (a Boolean valuation for classical; a finite Kripke model for intuitionistic/minimal) and a truth lemma by formula induction matches forced/not-forced to the signed formulas at each world. Because task 369 parameterizes the intuitionistic and minimal tableau over (closurePred, modelBot), the int and min cases should be discharged ONCE as a single parametric truth-lemma/countermodel pair rather than duplicated. The tableau Decidable instances become genuinely sorry-free once these land. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 316, 323, 363, 369.

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
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [299_modal_k_tableau/reports/01_modal-k-tableau-research.md]
- **Plan**: [299_modal_k_tableau/plans/02_modal-k-tableau-plan.md]

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
- **Topic**: Bimodal Porting
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
