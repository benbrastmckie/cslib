---
next_project_number: 475
---

# TODO

## Task Order

*Updated 2026-07-02. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,226,300,317,393,396,400,405,407,425,438,440,441,449,461,462,463,465,466,468,471,473,474 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,375,409,430,450,451,456,469,472 | 36,37,181,317,407,425,449,465 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41,413,414 | 39,40,181,215,300,301,375 | foundations, code hygiene |
| 4 | 412 | 41 | code hygiene |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
317 [PLANNED] — Fill the propositional tableau completeness sorries (7 real sorri
400 [BLOCKED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
407 [PR READY] — DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat
473 [NOT STARTED] — Prove the CPL implicational-fragment conservativity theorem promi
375 [NOT STARTED] — Complete the cross-system equivalence story by folding the tablea
409 [NOT STARTED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
430 [RESEARCHED] — Prove the atom-persistence / upward-closure structural lemma for 

### Modal Logic

300 [NOT STARTED] — Extend modal K tableau (task 299) with frame-specific rules for r
396 [NOT STARTED] — Evaluate and salvage the architecture-independent proof-engineeri
405 [PR READY] — Simplify the proof machinery in the task-402 modal tableau soundn
441 [PLANNED] — Refactor Modal.Proposition from the Lukasiewicz encoding (primiti
468 [NOT STARTED] — Re-sync PR #662 embedded propositional Lean files with the curren
471 [NOT STARTED] — Fix small PR #662 issues: restore Montesi attribution in Modal/Lo
469 [NOT STARTED] — Drop the unused Connectives.lean typeclass layer from PR #662 in 
472 [NOT STARTED] — Restore the model-class-parametric Proposition.Equiv and LogicalE

### Temporal Logic

425 [NOT STARTED] — [Decomposed from task 301, blocker C.] Establish the finite model
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic
301 [BLOCKED] — Implement tableau decision procedure for temporal logic (Cslib.Lo

### Bimodal Logic

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 
449 [NOT STARTED] — Foundation for the corrected TM-over-temporal conservativity resu
215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
450 [NOT STARTED] — Core corrected conservativity result. PR-BLOCKING for task 180. S
451 [NOT STARTED] — Deeper metatheory for the metric tense logic BX+ (defined in task

### Code Hygiene

393 [NOT STARTED] — Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING befo
412 [NOT STARTED] — [Split from task 278.] Simplify proofs in Foundations/Logic/ that
413 [NOT STARTED] — [Split from task 278.] Simplify Propositional/ proofs that use ma
414 [NOT STARTED] — [Split from task 278.] Simplify Modal/, Temporal/, and Bimodal/ p

### Pr & Upstreaming

438 [PR READY] — Upstream the comment/docstring cleanups identified by the task 43
440 [NOT STARTED] — PR review: GitHub PR https://github.com/leanprover/cslib/pull/648
465 [PR READY] — Review PR #607 (logical operators): post GitHub review covering t
466 [NOT STARTED] — Post comment on PR #648 linking the Zulip primitive-bot plus efq 
474 [PR READY] — Draft Zulip replies confirming CSLib meeting attendance to Montes

### Tableau Infrastructure

456 [NOT STARTED] — Generalize the Sfor-containment / subset-blocking device recurrin

### Uncategorized

461 [NOT STARTED] — Vet found 6 `linter.unusedSectionVars` warnings; add `omit [...] 
462 [NOT STARTED] — Vet of task 299 flagged two maintainability items (both non-block
463 [NOT STARTED] — Vet found low-severity documentation gaps (code placement itself 

## Tasks

### 474. Draft zulip replies meeting fragments
- **Status**: [PR READY]
- **Task Type**: general
- **Topic**: PR & Upstreaming
- **Dependencies**: None

**Description**: Draft Zulip replies confirming CSLib meeting attendance to Montesi and opening the fragment-design discussion Doty proposed

---

### 473. Prove cpl fragment conservativity
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Prove the CPL implicational-fragment conservativity theorem promised to Matthew Doty in the propositional Zulip thread

---

### 472. Restore model class equivalence pr 662
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 465

**Description**: Restore the model-class-parametric Proposition.Equiv and LogicalEquivalence framework integration removed by PR #662 in the Modal Lean sources, or document a defense of the standalone replacement

---

### 471. Fix small pr 662 issues
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Fix small PR #662 issues: restore Montesi attribution in Modal/LogicalEquivalence.lean, remove the fork-language doc comment, align iff notation precedence with the propositional convention, and prune spurious Mathlib imports

---

### 470. Restore grind automation pr 662
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Restore grind and simp attributes on PR #662 derived-connective characterization lemmas (neg_iff, and_iff, or_iff, diamond_iff, plus a restored iff characterization) and re-golf the manual Lean proofs back to grind one-liners

---

### 469. Drop connectives typeclass layer pr 662
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 465

**Description**: Drop the unused Connectives.lean typeclass layer from PR #662 in favor of the #607 Operators hierarchy

---

### 468. Resync pr 662 with 648 head
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 467

**Description**: Re-sync PR #662 embedded propositional Lean files with the current #648 head (primitive efq rule, IPL as empty theory, delete MPL, IsIntuitionistic, and intuitionisticCompletion) and correct the PR body description

---

### 467. Polish pr 648 bib and binder cleanup
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Polish PR #648 Lean sources: give the Gentzen1935 bib entry an English title, revert the explicit Gamma binder and subscript rename churn, restore the contra and efqRule derived rules, remove Atom named-argument noise, unify the CPL set-builder idiom, and normalize copyright headers

---

### 466. Record zulip settlement pr 648
- **Status**: [NOT STARTED]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: Task 467

**Description**: Post comment on PR #648 linking the Zulip primitive-bot plus efq settlement (Waring, 2026-06-28) and request re-review from ctchou

---

### 465. Review pr 607 logical operators
- **Status**: [PR READY]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: None

**Description**: Review PR #607 (logical operators): post GitHub review covering the red CI from the unmigrated HML LogicalEquivalence instance, the imp vs impl naming decision, operator file layout, NOTATION.md precedence documentation, and primitive-bot ownership of the propositional definitions file

---

### 464. Typst report structure first mpl arguments
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [464_typst_report_structure_first_mpl_arguments/reports/02_grounding-and-typst-scaffold.md]
- **Plan**: [464_typst_report_structure_first_mpl_arguments/plans/02_mpl-structure-first-report.md]
- **Summary**: [464_typst_report_structure_first_mpl_arguments/summaries/02_mpl-structure-first-report-summary.md]
- **Document**: [typst/MPL/MplReport.typ]

**Description**: Create a Typst report presenting the best arguments in support of the structure-first MPL design, output to /home/benjamin/Projects/cslib/typst/MPL/ (directory to be created; this is a document-writing/synthesis task — the deliverable is a compiled-clean Typst document, not Lean proofs).

THESIS TO ARGUE FOR: MPL (Minimal Propositional Logic) as the base logic in which bot (falsum) is a designated but TOTALLY UNCONSTRAINED nullary operator, added purely to keep the SAME SIGNATURE {bot, ->, and, or} as IPL — so at MPL strength bot is constrained only by type, carries NO proof rule, and its semantic clause is effectively vacuous (a free designated element bot_val : H). IPL = MPL PLUS a substantive semantic constraint (leastness: bot_val <= a for all a) AND a proof rule (efq: bot -> A). CPL adds classicality (peirce / double-negation elimination). Present and defend the conservative-extension ladder MPL < IPL < CPL.

KEY ARGUMENTS (already established in the codebase — synthesis, not new research): (1) substitution-invariance / free-monad argument: Proposition Atom is the free monad on {bot,->,and,or}, so bot is an ELEMENT of the algebra, not meta-syntax — rules out a bot-free MPL language (Design B1) and encoding bot as a distinguished atom (Design B2); decisive case for shared-signature Design A. (2) structure-first vs language-first (core CSLib Zulip debate): fix ONE language, interpret bot weakly, strengthen conservatively — preserves a single foundational architecture across the broader programme (identity, induced orders, hyperintensionality, tense, modality, categorical semantics). (3) modularity around properties, not connectives (explosion/leastness/initiality as independent typeclass/mixin modules). (4) the Hilbert-vs-ND definitional controversy and its resolution: Option C (re-frame task-398's [IsIntuitionistic T]-gated efq constructor as the explosion property module; MPL = the theory where efq is structurally unconstructible) over Option B (physically bot-rule-free MinDerivation base + Explosion extension, which re-opens the Curry-Howard/Prawitz subformula-property difficulty). (5) three-tier semantic ladder: designated bot (GHAValid=MPL) / HasLeastBot (IPL) / canonical bot from OrderBot (IPL/CPL via Heyting/Boolean). (6) conservative-extension results already formalized (ConservativeChain; per-class completeness over GHA/Heyting/Boolean).

SOURCE MATERIAL: CSLib Zulip "Propositional Logic" thread https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic (captured JSON snapshot at specs/407_mpl_base_structure_first_redesign/reports/zulip-propositional-logic.json — primary context for the debate); task-407 artifacts (mpl-base-design-note.md, reports/01-03, decisions.md); supporting audits task 415 (reports/01_lifting-audit.md) and task 419 (reports/04_abstract-picture-and-result-inventory.md); Lean source anchors for citing the realized design: Cslib/Logics/Propositional/Defs.lean, ProofSystem/Axioms.lean, NaturalDeduction/Basic.lean, Semantics/Algebra.lean + Semantics/Algebra/BotProperties.lean.

TYPST CONVENTIONS: follow the template, structure, and notation macros from /home/benjamin/Projects/BimodalLogic/Theories/Bimodal/typst/ — BimodalReference.typ, template.typ, notation/bimodal-notation.typ, chapters/ layout, README.md. Match notation macros and document conventions; adapt the notation file for propositional-logic symbols. DoD: typst compile clean under /home/benjamin/Projects/cslib/typst/MPL/.

CSLib Zulip AI policy: any prose intended for upstream posting must be human-authored; this document is an internal report.

---

### 463. Docs: update ORGANISATION.md Tableau/ tree sketches + strip internal task refs from public docstrings (task 299/455 vet)
- **Status**: [NOT STARTED]
- **Task Type**: markdown
- **Dependencies**: None

**Description**: Vet found low-severity documentation gaps (code placement itself is correct/idiomatic): (1) ORGANISATION.md:148 Modal/ tree sketch omits the `Tableau/` subdirectory; ORGANISATION.md:26 Foundations/Logic/ tree sketch omits `Tableau/` (Sign.lean, SignedFormula.lean, RuleResult.lean, Branch.lean, Closure.lean, ClosureCondition.lean, Measure.lean, PropositionalRules.lean) — add these entries to document existing placement. (2) Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:1178 and nearby: permanent public docstrings for `modalTableau_complete`/`modalTableau_decides` embed ephemeral internal notes like '(task 442 Phase 6, FINAL)', '(task 442 Phase 5a)' — replace with plain, durable mathematical descriptions.

---

### 462. Refactor duplicated case-arms + eliminate private-lemma re-derivation in modal tableau (task 299 vet)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: Task 457, Task 459

**Description**: Vet of task 299 flagged two maintainability items (both non-blocking, build/lint green): (1) `modalStepBranch_preserves_sat` (Cslib/Logics/Modal/Tableau/SoundnessStep.lean:178-1626, ~1450 lines) has ~15 near-verbatim duplicated leaf case-arms (identical simp skeletons differing only by Proposition constructor, e.g. 1402-1626 repeat a 12-line pattern ~15×) — extract a shared helper lemma/tactic to collapse them. (2) CompletenessLoop.lean:91-131 re-derives `modalLoop_stepBranch_none_saturated` as a local copy of the `private modalStepBranch_none_saturated` (Completeness.lean:683) plus bClosure/eClosure/worldBound facts, solely because `private` blocks cross-file reuse — mark those lemmas `protected` in Completeness.lean/FmpMeasure.lean and import/reuse them. Preserve zero sorry/axioms; confirm scoped `lake build` green.

---

### 461. Add omit [...] annotations for unused section variables in tableau proofs (task 299/455 vet)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Vet found 6 `linter.unusedSectionVars` warnings; add `omit [...] in` before each flagged lemma (matching the existing pattern already used elsewhere in these files): Cslib/Logics/Modal/Tableau/Branch.lean:104 (`modalNextWorld_gt`, omit [DecidableEq Atom] [Hashable Atom]), Branch.lean:132 (`label_le_modalMaxWorld`, omit [DecidableEq Atom]), Completeness.lean:71 (`extractModel_atom_sat_iff`, omit [Hashable Atom]), Completeness.lean:88 (`extractModel_bot_false`, omit [Hashable Atom]), SoundnessStep.lean:92 (`modalClosed_unsat`), and Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:1102 (`classicalStepBranch_mem_preserved`, omit [Hashable Atom]). Low severity, non-blocking.

---

### 460. Fix lake-build lint warnings in Classical/Completeness.lean (task 455 vet)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Vet of task 455 found lint warnings in the repointed consumer Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean: wrap 16 flagged >100-char lines (119,140,158,161,218,237,256,360,377,400,421,641,912,961,979,987); line 799 drop unused `[DecidableEq Atom]` from `classicalApplyOne_branching_length` (or use `classical`); lines 810,837 trim unused simp args per `simp?`; line 1102 add `omit [Hashable Atom] in` before `classicalStepBranch_mem_preserved`; line 1267 replace `simp at he` with `simp only [...]` (linter.flexible). Non-blocking; confirm `lake build` green.

---

### 459. Shorten >100-char lines in modal K tableau SoundnessStep + Completeness (task 299 vet)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None
- **Plan**: [459_vet_299_longline_style/plans/01_longline-style-fix.md]
- **Summary**: [459_vet_299_longline_style/summaries/01_longline-style-fix-summary.md]

**Description**: Vet of task 299 found 57 lines exceeding the 100-char `linter.style.longLine` limit: Cslib/Logics/Modal/Tableau/SoundnessStep.lean (48 lines: 268,334,348,371,384,398,412,522,545,568,686,709,732,850,873,896,1086,1136,1149,1164,1204,1219,1234,1256,1274,1292,1310,1328,1346,1364,1384,1402,1420,1437,1438,1455,1456,1473,1474,1491,1492,1512,1530,1548,1566,1584,1602,1620 — mostly long `refine ⟨...⟩` case-bash terms) and Completeness.lean (9 lines: 118,128,169,177,195,455,477,479,529). Mechanically wrap/restructure; no proof-logic changes. Confirm `lake build` stays green.

---

### 458. Fix lake shake import findings in shared Measure module + Classical consumer (task 455 vet)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Vet of task 455 (session sess_1782919557_8a4cc2) found 2 lake shake import findings. Cslib/Foundations/Logic/Tableau/Measure.lean:11 remove unused `import Mathlib.Algebra.BigOperators.Group.List.Basic`. Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:1 remove `public import Cslib.Logics.Propositional.Tableau.Classical.Soundness`, add `public import Cslib.Logics.Propositional.Tableau.Classical.Expansion` and `Cslib.Logics.Propositional.Semantics.Bool`. Re-run scoped `lake build` + `lake shake` to confirm. Non-blocking; CONTRIBUTING.md shake cleanliness.

---

### 457. Fix lake shake import findings in modal K tableau files (task 299 vet)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Vet of task 299 (session sess_1782919557_8a4cc2) found 6 lake shake import-hygiene findings (beyond the pre-existing systemic Cslib.Init pattern) in Cslib/Logics/Modal/Tableau/. Apply the shake-suggested add/remove: Defs.lean:17 remove unused `public import Cslib.Foundations.Logic.Tableau.PropositionalRules`; Branch.lean:10 add missing `public import Cslib.Foundations.Logic.Tableau.SignedFormula`; Rules.lean:10 add missing `public import Cslib.Foundations.Logic.Tableau.PropositionalRules`; Closure.lean:10 remove `...Modal.Tableau.Rules`, add `...Modal.Tableau.Defs`; Completeness.lean:10 remove `...Modal.Tableau.LoopInduction`; FmpMeasure.lean:20 remove `...Modal.Tableau.LoopInduction`. Then `lake build` the scoped modules to confirm no regressions and re-run `lake shake --add-public --keep-implied --keep-prefix`. Non-blocking; CONTRIBUTING.md shake cleanliness for upstream PR.

---

### 456. Shared tableau containment blocking
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Tableau Infrastructure
- **Dependencies**: Task 317

**Description**: Generalize the Sfor-containment / subset-blocking device recurring across tableau developments into a single label-generic module Cslib/Foundations/Logic/Tableau/Blocking.lean, built on the existing Branch.formulasAt (Foundations/Logic/Tableau/Branch.lean:81). Lift Temporal's timeType/isSubsetBlocked/isTemporallyBlocked (Temporal/Tableau/Branch.lean:101-174) and task 317's Sfor/containment check to: Branch.typeAt (deduplicated (Sign x F) forced-type at a label), Branch.containmentBlocked (containment test), and the once-proven core lemma Tableau.distinctTypes_le_pow ((b.labels.map b.typeAt).eraseDups.length <= 2^U.length for a subformula-closed universe U). Highest-value payoff: distinctTypes_le_pow is the shared core of BOTH task 317's intExpandBranches_world_bound_dedup (plan 04 Phase 5.1) AND the currently-[BLOCKED] Temporal soundness obligation (Temporal/Tableau/Soundness.lean:23-54, '<= 2^n time types' / loop-detection) - proving it once could unblock Temporal Phase 7. The definitional lift is cheap; the soundness lemma (blocking => bounded => countermodel) is the hard part, but hard exactly once instead of 2-3 times. DEPENDS ON task 317 landing first (so the (psi not in forced(x)) side-condition shape is settled); ideally co-scoped with the Temporal soundness unblock. Also add missing references.bib entries GargGenoveseNegri2012 and DershowitzManna1979 (ready in report 05 Q4). Source: task 317 reuse/abstraction research report 06 (R2). Verify scoped + full lake build green, checkInitImports/lint-style/shake pass, zero sorry.

---

### 455. Extract tableau measure arithmetic
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Tableau Infrastructure
- **Dependencies**: Task 317
- **Research**: [455_extract_tableau_measure_arithmetic/reports/01_tableau-measure-arithmetic-extraction.md]
- **Plan**: [455_extract_tableau_measure_arithmetic/plans/01_measure-arithmetic-extraction.md]

**Description**: Extract the logic-agnostic measure arithmetic duplicated across the Modal K FMP measure (task 442) and the Classical propositional tableau into a new shared module Cslib/Foundations/Logic/Tableau/Measure.lean. Move: sum_map_le_length_mul (FmpMeasure.lean:131), the geometric-sum capacity family modalCap/modalCap_le_pow (FmpMeasure.lean:776-833), and a small base-3 domination API (3^a<=3^C, 1<=3^C, 3^a+3^b<=3^(1+max)) currently hand-rolled inline in Classical/Completeness.lean:677-687 and FmpMeasure.lean:238. Target API (all F/L-free, pure Nat/List): Tableau.sum_map_le_length_mul, Tableau.geomCap (Sum_{i<=k} base^i), Tableau.geomCap_le_pow. ~80-150 lines moved; zero semantic risk (pure arithmetic); de-duplicates modal<->classical and updates call sites to the shared lemmas. Independent of task 317 - can run anytime. Source: task 317 reuse/abstraction research report 06 (R1), specs/317_propositional_tableau_completeness/reports/06_sfor-dedup-reuse-abstraction.md. Verify scoped + full lake build green, checkInitImports/lint-style/shake pass, zero sorry.

---

### 454. Consolidate duplicated Chronicle PointInsertion helper families across Bimodal and Temporal
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 449, Task 450
- **Research**: [454_consolidate_chronicle_pointinsertion_bimodal_temporal/reports/01_consolidate-chronicle-pointinsertion.md]

**Description**: From review 2026-07-01-2 (MEDIUM, finding #3). Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean (1019L) and Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean (704L), plus sibling Burgess.lean and Seeds.lean in both trees, share an entire family of identically-named private helpers: lemma27SinceSeed, l27sC5EventList, l27sB5GuardList, l27s_c5_event_list_mem, l27s_b5_guard_list_mem, lemma24SinceWithGuard, lemma_2_7_since, lemma_2_8_since, lemma_2_7_since_seed_consistent, lemma_2_8_since_seed_consistent. Same duplication disease as the GenericMCSBridge work (task 452) but in the Chronicle point-insertion layer. The files have diverged (Bimodal is ~45% larger), so this is consolidation-with-care, not a mechanical merge: reconcile the diverged portions, then factor the shared lemma_2_7/lemma_2_8 seed-consistency helpers into a common Chronicle-support module parameterized over the frame/relation interface. NOT covered by task 415 (propositional->modal lifting stack) or 449-451 (which define a NEW base logic BX+ rather than dedup existing Chronicle machinery). IMPORTANT: coordinate with tasks 449-451 (BX+) since they may rewrite TemporalConservativity and adjacent Chronicle files -- best sequenced after the BX+ restructure settles, or done in lockstep. DoD: shared point-insertion helpers factored to one location, both logics reduced to thin instantiations of the common core, lake build/test/lint green, zero new sorries.

---

### 453. Audit and reduce maxHeartbeats inflation across Bimodal/Temporal metalogic; normalize scoping to 'in'-scoped
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Plan**: [plans/01_reduce-maxheartbeats-inflation.md]
- **Research**: [reports/01_maxheartbeats-audit.md]
- **Summary**: [summaries/01_reduce-maxheartbeats-inflation-summary.md]

**Description**: From review 2026-07-01-2 (MEDIUM+LOW, findings #2+#4). 72 set_option maxHeartbeats sites in Cslib/Logics/{Bimodal,Temporal}/Metalogic/**, up to 32x the 200000 default: 3200000 x33, 1600000 x13, 800000 x12, 1200000 x3, 400000 x5, and 6400000 x1 (Temporal/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean:38). The mature upstream dirs (Foundations/Computability/Languages/Crypto) have ZERO maxHeartbeats settings -- this inflation is entirely in the active logic area and signals proof terms/tactics that should be restructured (intermediate haves, lemma extraction) rather than given more budget. ALSO (finding #4, LOW): 15 sites use file-wide unscoped 'set_option maxHeartbeats N' (masking which declaration is expensive) vs 54 declaration-scoped 'set_option ... in'; unscoped sites include Bimodal/Metalogic/Algebraic/{UltrafilterMCS.lean:34,BooleanStructure.lean:33} and Temporal/Metalogic/{Chronicle/TruthLemma.lean:40,Chronicle/RRelation.lean:29,DenseSoundness.lean:32,Completeness.lean:47,Soundness.lean:32,MCS.lean:38,WitnessSeed.lean:29,Chronicle/Frame.lean:28,Chronicle/PointInsertion/{Seeds,Burgess,Splitting,Since}.lean}. Approach: audit the 3.2M/6.4M offenders, restructure the worst to lower the ceiling (or document why irreducible); convert all unscoped sites to 'set_option ... in' on the specific expensive declaration. NOT covered by 412-414 (which target simp only [listImp_*, bigconj_*] lists, not heartbeat budgets). Self-contained, independent of other tasks. DoD: heartbeat ceilings reduced where feasible, all remaining high budgets documented, unscoped sites converted to scoped, lake build/test green.

---

### 452. Generalize GenericMCSBridge: hoist shared MCS-bridge trio into Foundations and collapse base/Fc duplication
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None

**Description**: From review 2026-07-01-2 (HIGH). The four GenericMCSBridge.lean files (Propositional 256L, Modal 267L, Temporal 370L, Bimodal/Core 405L; 1298L total) share a near-verbatim skeleton: HilbertOf tag type -> InferenceSystem/ModusPonens/HasAxiomImplyK/HasAxiomImplyS/MinimalHilbert instances -> AlgDS alias -> derivTreeToList -> unfoldListImpInTree (~19L) -> listDerivToTree (~15L) -> {logic}_deriv_iff_algebraic / _setConsistent_iff_algebraic / _setMaxConsistent_iff_algebraic. The trio uses only assumption/modus_ponens/weakening (no logic-specific content). Temporal and Bimodal ADDITIONALLY duplicate their own base/Fc sections internally (e.g. Temporal L66-221 vs L239-370). Approach: (1) collapse Temporal's and Bimodal's intra-file base/Fc duplication first by making the base bridge a specialization of the Fc-parameterized one (fc := .Base) -- ~130-150L each, lowest risk, no cross-logic abstraction; (2) extract unfoldListImpInTree, listDerivToTree, and the three iff-theorems into Cslib/Foundations/Logic/Metalogic/GenericMCS.lean, parameterized over a typeclass capturing 'tree-shaped derivation with ax/assumption/mp/weakening constructors', with extra rules (necessitation, temporal duality) passed as an optional hypothesis/callback. Est. elimination ~300-450 lines. NOT covered by tasks 415/393/439 (which build ON the bridge as infrastructure, verified against their reports). Sequence to avoid collision with in-flight tasks 441/442 (Modal refactor) and 449-451 (BX+). DoD: shared abstraction in Foundations, all four per-logic bridges reduced to thin instantiations, lake build/test/lint green, zero new sorries or axioms.

---

### 451. BX+ completeness over ordered-abelian-group time flows
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 449

**Description**: Deeper metatheory for the metric tense logic BX+ (defined in task 449). Optional-but-desired for rigor; also unlocks the semantic proof route for task 450. Depends on task 449.

GOAL: Prove BX+ (Temporal FrameClass.Metric) COMPLETE over the class of ordered-abelian-group temporal frames: every formula valid on all group-ordered flows is BX+-derivable (equivalently, every BX+-consistent formula has a group-ordered countermodel).

Research must decide the construction. Candidate routes (see specs/445_fix_temporal_conservativity_domain_mismatch_sorry/reports/02_literature-grounded-conservativity-obstruction.md):
- Adapt the existing Temporal completeness machinery (Chronicle / MCS construction under Cslib/Logics/Temporal/Metalogic/Chronicle/) to yield a countermodel whose order embeds into an ordered abelian group.
- Loewenheim-Skolem to a countable model, then Cantor (Order.iso_of_countable_dense) for the dense case plus a discreteness case-split, transporting satisfaction along the sound Satisfies.orderIso transport lemma sketched in the 445 report section 7.
Literature grounding: Xu1988, Burgess1984 sec 6.1, Gabbay1993 (irreflexivity rule), Reynolds. Confirm exactly which frame class BX+ is genuinely complete over before committing.

Zero-debt: no sorry, no vacuous defs; full CI green. If completeness turns out to need an open / research-level lemma, escalate with the exact goal rather than papering over it.

---

### 450. Prove TM (Bimodal Base) conservative over BX+ and close the TemporalConservativity sorry
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 181, Task 449

**Description**: Core corrected conservativity result. PR-BLOCKING for task 180. Supersedes abandoned task 445 and inherits its research: specs/445_fix_temporal_conservativity_domain_mismatch_sorry/reports/01_domain-mismatch-transfer-feasibility.md and 02_literature-grounded-conservativity-obstruction.md. Depends on task 449 (BX+ definition).

TARGET: Bimodal.ThDerivable = DerivationTree Bimodal.FrameClass.Base (Cslib/Logics/Bimodal/ProofSystem/Derivation.lean:111,119), and Bimodal Base includes the 5 uniformity axioms. The honest theorem is therefore:
  bimodal_conservative_over_temporal : Bimodal.ThDerivable phi.toBimodal -> BXplus.ThDerivable phi
where BXplus = DerivationTree Temporal.FrameClass.Metric (from task 449).

RESEARCH PHASE MUST SETTLE THE PROOF ROUTE:
- Route (i) SYNTACTIC box-erasure (preferred; needs no completeness result). Define eraseBox : Bimodal.Formula -> Temporal.Formula, prove Bimodal.DerivationTree FrameClass.Base G phi -> Temporal.DerivationTree FrameClass.Metric (G.map eraseBox) (eraseBox phi) by induction on the derivation tree, then specialise via eraseBox (phi.toBimodal) = phi (Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean). CRUX to verify per-axiom with lean_multi_attempt: S5 axioms for box erase to tautologies; the pure-temporal and uniformity axioms erase to BX+ axioms; the MODAL-TEMPORAL INTERACTION axioms modal_future (box phi -> box(G phi)) and discrete_box_necessity (chi -> box chi) are the only load-bearing cases. The definition of eraseBox on box must be chosen so BOTH land as BX+ theorems: naive eraseBox(box psi) = eraseBox(psi) sends modal_future to phi -> G phi, which is FALSE, so a smarter erasure is required. Ground the correct construction in Thomason 1984 (Combinations of Tense and Modality).
- Route (ii) SEMANTIC transfer. Uses BX+ completeness over group flows (task 451) + trivial bimodal expansion + Bimodal soundness, via contrapositive. Only viable once task 451 has landed; if research selects this route, add a dependency on task 451.

IMPLEMENTATION: In Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean, REPLACE the false temporal_valid_of_bimodal_derivable (:269), restate bimodal_conservative_over_temporal over BX+, and REMOVE set_option warn.sorry false in (:248) and the sorry (:269). Rewrite the module docstring's "Domain Mismatch Resolution" section to the correct account: TM is conservative over METRIC tense logic BX+, not over plain BX (cite Burgess1984 sec 6.1 and Thomason1984). This task OWNS TemporalConservativity.lean; task 444's naming/lint sweep runs AFTER this task so it sees the settled file.

Zero-debt: lean_verify on the restated bimodal_conservative_over_temporal must report only [propext, Classical.choice, Quot.sound] with zero sorry; full CI green. If a genuine load-bearing obstruction is hit, escalate with the exact open goal and candidate lemmas; do NOT reintroduce a sorry or a vacuous (:= True / trivial) placeholder.

---

### 449. Define BX+ (metric tense logic): temporal uniformity axioms, Metric frame class, and soundness over ordered-abelian-group flows
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: None

**Description**: Foundation for the corrected TM-over-temporal conservativity result. Supersedes abandoned task 445; inherits its research at specs/445_fix_temporal_conservativity_domain_mismatch_sorry/reports/01_domain-mismatch-transfer-feasibility.md and 02_literature-grounded-conservativity-obstruction.md.

BACKGROUND: Deep, machine-verified research established that bimodal_conservative_over_temporal as originally stated is FALSE. Bimodal TM's FrameClass.Base carries five "uniformity" axioms (discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd, discrete_box_necessity at Cslib/Logics/Bimodal/ProofSystem/Axioms.lean:248-273) encoding the translation-homogeneity and negation-symmetry of ordered-abelian-group time, whereas pure Burgess/Xu Temporal FrameClass.Base (complete over ALL serial linear orders) has none of them. TM is genuinely non-conservative over plain BX (witness phi_T = (untl bot top) -> G(untl bot top), refuted on the doubled rationals Lex(Q x Bool)). The fix is to state conservativity over the matching metric temporal base BX+.

GOAL: Introduce BX+ = the metric tense logic sound over ordered-abelian-group time.

1. Add a new Temporal frame class FrameClass.Metric with Base < Metric (extend the FrameClass inductive plus its LE / PartialOrder / DecidableRel instances and minFrameClass in Cslib/Logics/Temporal/ProofSystem/Axioms.lean, mirroring how Dense is handled). Do NOT add uniformity axioms to Base: Temporal Base must remain sound over all serial linear orders (Cslib/Logics/Temporal/Metalogic/Soundness.lean:409); breaking that is out of scope.

2. Add the FOUR pure-temporal uniformity axioms to the Temporal Axiom inductive, each gated to minFrameClass = .Metric:
   - discrete_symm_fwd:      U(bot,top) -> S(bot,top)
   - discrete_symm_bwd:      S(bot,top) -> U(bot,top)
   - discrete_propagate_fwd: U(bot,top) -> G(U(bot,top))
   - discrete_propagate_bwd: U(bot,top) -> H(U(bot,top))
   (The bimodal discrete_box_necessity chi -> box chi has no pure-temporal form; it erases to a tautology and is handled in task 450, NOT here.)

3. Define the semantic frame class of "metric" / ordered-abelian-group temporal frames (time D an ordered abelian group, matching the bimodal TaskFrame domain constraints AddCommGroup + LinearOrder + IsOrderedAddMonoid). Prove SOUNDNESS of each new axiom over this class: they are exactly the frame-validities of group-ordered time (propagation from translation-invariance, symmetry from negation). Extend the Temporal soundness result to FrameClass.Metric over the metric frame class.

4. Provide the Derivable / DerivationTree plumbing and a BX+ derivability abbreviation (DerivationTree FrameClass.Metric).

Zero-debt: no sorry, no vacuous defs (def X := True / trivial are prohibited). Verify with lean_verify; full lake build / lake lint / lake exe lint-style / lake test green. Docstrings in house style on every new declaration.

Definition of done: FrameClass.Metric and the 4 temporal uniformity axioms defined and gated; metric temporal frame semantics defined; soundness of BX+ over ordered-abelian-group flows proved sorry-free; CI green.

---

### 448. Study Deriv σ as a shared-metatheory substrate (proof-system morphism Vision B)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [448_study_deriv_shared_metatheory_substrate/reports/01_team-research.md]

**Description**: Study whether to elevate the committed forward-only proof-system-morphism layer (delivered by task 419) into a genuine SHARED-METATHEORY SUBSTRATE over Deriv sigma, and if so, do it in ROI-gated phases. Reference the definitive analysis in specs/419_generalize_derivation_lifting_intersystem/reports/04_abstract-picture-and-result-inventory.md (fork framing, representation options R1/R2/R3, and the full result lattice Layers 0-3).

Background: task 419 delivered ProofSig/Deriv/ProofSigHom/Deriv.map + functor laws (Foundations/Logic/Metalogic/ProofSystemMorphism.lean) with Modal+PL full Equiv and Bimodal forward+HEq, all sorry-free. The one open boundary is backward maps / full Equiv for multi-closure logics (Bimodal), blocked because Deriv.close carries closure-membership as a Prop (List.Mem, head/tail) so backward dispatch needs kernel-forbidden large elimination into Type.

Phase 1 (R1, surgical, sorry-free): change Deriv.close to carry a Fin (closures.length) index (data) instead of the Prop membership proof; update clMap to an index map with naturality, Deriv.map, and the three LiftViaMorphism overlays. Non-invasive: touches only the Foundations file + 3 overlays, no native DerivationTree inductive. Acceptance: functor laws re-proved, scoped build green, zero sorry.

Phase 2: define Bimodal ofDeriv and bimodalEquiv (DerivationTree fc Gamma phi = Deriv (bimodalSig fc) Gamma phi) now that backward dispatch is legal; make Modal/PL Equivs uniform with it (remove the singleton-closure special-casing). Optionally exhibit liftDerivationWith as a Deriv.map instance (pure assembly; all naturality lemmas already exist). Acceptance: round-trips proved, zero sorry.

Phase 3 (THE ROI GATE — do NOT land Phases 1-2 without this): identify and prove the FIRST genuinely-reusable generic metatheorem on Deriv sigma and transport it to at least one concrete logic via the Equiv. Candidates: a generic deduction theorem; a generic height/subformula induction principle; a soundness skeleton parameterized by a semantic algebra + axiom-soundness + per-closure soundness. This phase justifies the whole substrate; if no such consumer is found worthwhile, STOP and keep the forward-only layer as-is.

ANTI-GOALS (never pursue): A2 maximal inductive replacement (replacing native DerivationTree by Deriv sigma across ~193 files — regressive, exhaustiveness lost, zero proof payoff); Prop-ifying Bimodal's Type-valued Axiom family (breaks liftDerivationWith/conservativity); Classical.choice backward maps (noncomputable, round-trip unprovable). Zero-debt: every phase independently buildable and sorry-free, or [BLOCKED] and reported. Follows task 419 (completed).

---

### 447. Apply lake shake import-minimization fixes to files touched by tasks 321/406/431
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: PR & Upstreaming
- **Dependencies**: None
- **Research**: [447_apply_shake_import_minimization_fixes_tasks_321_406_431/reports/01_shake-import-minimization-verification.md]
- **Plan**: [447_apply_shake_import_minimization_fixes_tasks_321_406_431/plans/01_apply-shake-import-fixes.md]
- **Summary**: [447_apply_shake_import_minimization_fixes_tasks_321_406_431/summaries/01_apply-shake-import-fixes-summary.md]

**Description**: Vet (tasks 321/406/431/433/435) found 17 lake shake --add-public --keep-implied --keep-prefix import-minimization suggestions across files touched by tasks 321, 406, and 431. CI otherwise passes (build/test/checkInitImports green; zero sorries). Apply the genuine import-hygiene fixes and verify (do NOT blindly --fix):

FALSE-POSITIVE CANDIDATES (import Cslib.Init removals -- Cslib.Init sets up default linting/tactics, not a term-level dependency; verify, and if legitimately needed add the shake preserve-comment per 'lake shake --help' rather than removing):
- Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean (remove import Cslib.Init)
- Cslib/Logics/Modal/Tableau/Saturation.lean (remove import Cslib.Init; add public import Cslib.Logics.Modal.Tableau.Rules)
- Cslib/Logics/Modal/Tableau/LoopInduction.lean (remove import Cslib.Init + public import ...Saturation; add public import Cslib.Logics.Modal.Basic, Batteries.Data.List.Basic)
- Cslib/Logics/Modal/Tableau/Soundness.lean (remove import Cslib.Init)
- Cslib/Logics/Temporal/Tableau/Rules.lean (remove import Cslib.Init; add public import Cslib.Foundations.Logic.Tableau.PropositionalRules)
- Cslib/Logics/Temporal/Tableau/Saturation.lean (remove import Cslib.Init)

GENUINE IMPORT-HYGIENE FIXES:
- Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean (remove public import Mathlib.Data.Multiset.Basic)
- Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean (swap MCSProperties -> GenericMCS)
- Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean (swap MCSProperties -> GenericMCS)
- Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean (swap MCSProperties -> GenericMCS)
- Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/BurgessHelpers.lean (remove Finset.Max + Tactic.Linarith; add Tactic.NormNum)
- Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean (remove re-export of ...Elimination -- verify barrel still builds)
- Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/Structures.lean (remove Mathlib.Logic.Encodable.Basic) paired with Elimination.lean (add Mathlib.Logic.Encodable.Basic)
- Cslib/Logics/LTL/Semantics/GNBA/Closure.lean (remove Satisfies + Set.Finite.Powerset + Set.Finite.Lattice; add LTL.Syntax.Formula) paired with GNBA/Atoms.lean (add Satisfies)
- Cslib/Logics/Temporal/Metalogic/DenseMCS.lean (remove DeductionHelpers)

After edits, re-run: lake build, lake test, lake exe checkInitImports, lake exe lint-style, and lake shake --add-public --keep-implied --keep-prefix on the touched files to confirm the suggestions are resolved. Scope is limited to these files only -- do NOT attempt the codebase-wide shake backlog. Source: /vet session sess_1782884590_732b0b.

---

### 444. Uniformity pass: mathlib-conformant naming, style, and docstrings across the entire task-180 Temporal diff
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 181, Task 449, Task 450, Task 454

**Description**: Vet fix for task 180 (High), elevated scope. Do not merely rename the two flagged defs; bring the task-180 diff to a single, uniform, mathlib-conformant standard.

Hard fix (blocks PR): rename allFuture_iff_neg_someFuture_neg (Theorems.lean:51) and allPast_iff_neg_somePast_neg (Theorems.lean:68) to lowerCamelCase (they are data-carrying noncomputable defs returning DerivationTree, not theorem/lemma), updating every call site.

Ambitious cleanup:
- Audit every declaration introduced or modified by task 180 across Cslib/Logics/Temporal/{Syntax,Semantics,ProofSystem,Metalogic,Theorems} and the two Bimodal consumers (Embedding/TemporalEmbedding.lean, Metalogic/ConservativeExtension/TemporalConservativity.lean) for naming uniformity: data-returning defs in lowerCamelCase; propositions as theorem/lemma in snake_case; one consistent convention for the bridge-axiom wrappers, the MCS bridge lemmas (mcs_allFuture_iff family), and the Chronicle/TruthLemma helpers. INCLUDE the new declarations introduced by tasks 449 (BX+ / FrameClass.Metric axioms) and 450 (eraseBox, restated conservativity) in the uniformity sweep.
- Make lake lint fully green on these files for defsWithUnderscore, defLemma, docBlame, dupNamespace, topNamespace, simpNF, unusedSectionVars, not just the two flagged lines.
- Ensure every public declaration carries a concise, elegant docstring in the house style; unify the recurring "D3 honesty caveat" comment so it reads identically wherever it appears.
- Remove dead code, leftover scaffolding comments, and any development-only set_options no longer needed.

SCOPE EXCLUSION (conflict avoidance): do NOT touch Cslib/Logics/Temporal/Tableau/ (Defs, Rules, Completeness, Saturation, ...). That subtree is being actively redesigned by the task-301 tableau line (426/439/425); its naming/style cleanup is owned there. Coordinate rather than double-edit.

SEQUENCING: Depends on 449 (define BX+) and 450 (conservativity proof + close sorry). Run last so this sweep sees the final, settled declarations, including the new BX+ axioms from 449 and the restated conservativity theorem from 450. NOTE: TemporalConservativity.lean is REWRITTEN by task 450 (which removes the sorry and restates the theorem over BX+); once 450 is complete this file is settled and IS in scope for 444's naming/docstring sweep (it was excluded only while 450 was in flight). Task 446 (citation hygiene) is already COMPLETED. Original task 445 was ABANDONED (its theorem was proved false; superseded by 449/450).

Definition of done: lake build, lake lint, lake exe lint-style green on every in-scope task-180 file; consistent naming and docstrings verified by inspection; no behavioural change to any proof (renames + docs only).

---

### 442. Modal tableau fmp fuel measure
- **Effort**: 400-800 lines, multiple dispatches
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [299_modal_k_tableau/reports/06_spawn-analysis.md]
  - [442_modal_tableau_fmp_fuel_measure/reports/01_fmp-fuel-measure-research.md]
- **Plan**: [442_modal_tableau_fmp_fuel_measure/plans/01_fmp-fuel-measure-plan.md]
- **Summary**:
  - [Cslib/Logics/Modal/Tableau/CompletenessLoop.lean]
  - [Cslib/Logics/Modal/Tableau/FmpMeasure.lean]

**Description**: Fix the Phase 6 blocker in task 299 (modal K tableau completeness) by revising the fuel bound and formalizing the finite-model-property (FMP) termination measure. Constraints: ZERO sorry, ZERO new axioms; NO datatype or rule change (world-subset blocking is "option B", already tracked as task 441, and is explicitly OUT OF SCOPE here -- do not touch modalNextWorld's world-reuse behavior or any rule's output shape). Three-part scope: (1) Revise modalFuel (Cslib/Logics/Modal/Tableau/Saturation.lean:89) upward from the current polynomial O(n^2) to an exponential (or double-exponential, if the measure proof requires it) bound in the formula size. This step alone is soundness-safe: modalExpandBranches_closed_unsat (Soundness.lean:226) is fuel-agnostic (closed implies unsat holds for arbitrary fuel), so only the numeric value of modalFuel changes -- no soundness proof needs rework. (2) Formalize the FMP termination measure that discharges the fuel = 0 case of modalExpandBranches: an a-priori world-count / world-label bound (needed because modalNextWorld-minted labels are currently unbounded a priori); a finite signed-subformula universe U(phi); a subformula-closure lemma covering all four modal rules' outputs (witness + boxProps + diaNegProps) plus the propositional rule outputs, showing every formula produced during expansion lies in U(phi); output-disjointness (new formulas produced by a rule firing are fresh on the branch); and a per-branch weight ~3^R (where R measures unconsumed universe elements) to absorb the <=2-way propositional branching, mirroring the classical 3^complexity measure used in classicalExpandBranches_hintikka. (3) Prove modalStepBranch_none_saturated and then modalExpandBranches_hintikka by fuel induction plus inner Forall2-accessibility induction, mirroring classicalExpandBranches_hintikka (Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:924) and reusing the acc-threading pattern already established in modalExpandBranches_closed_unsat (Cslib/Logics/Modal/Tableau/Soundness.lean:165). Then discharge modalTableau_complete via the already-proven modalOpenBranch_countermodel (task 299 Phase 5d, green), and finally modalTableau_decides plus its Decidable instance (task 299 Phase 7, currently gated on this work). Reference templates: classicalExpandBranches_hintikka (Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:924), classicalStepBranch_none_saturated / classicalStepBranch_hintikka_inv (same file, lines 694/722), and the hoisted forall2_* worklist helpers already available in Cslib/Logics/Modal/Tableau/LoopInduction.lean. Full reference-signature detail and the precise per-rule dispatch obligations are recorded in task 299's plan (specs/299_modal_k_tableau/plans/05_modal-k-tableau-plan.md, Phase 6 "DECISIVE FINDING" addendum and "Precise residual obligation" list) and should be read as background before starting. Definition of done: modalStepBranch_none_saturated, modalExpandBranches_hintikka, modalTableau_complete, modalTableau_decides, and a Decidable instance all compile with ZERO sorry and ZERO new axioms; #print axioms on each shows only standard axioms; whole-library lake build stays green.

---

### 441. Modal proposition native refactor
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 299
- **Plan**: [441_modal_proposition_native_refactor/plans/01_modal-proposition-native-refactor.md]

**Description**: Refactor Modal.Proposition from the Lukasiewicz encoding (primitives atom/bot/imp/box; and/or/neg/diamond encoded as nested imp) to NATIVE constructors atom/bot/imp/and/or/box/diamond (diamond primitive), mirroring the propositional layer (PL.Proposition has native and/or). Goal: highest-quality mathematical foundations — one tableau rule/decomposer per connective, structural-induction truth lemma, no unsound uniform-imp bridge lemmas, no view/strong-induction workarounds. Cascades through Modal/Basic.lean (datatype+Satisfies+complexity+axiom theorems), Modal/LogicalEquivalence.lean (Context), all Modal/Tableau/*, and Bimodal/Embedding/ModalEmbedding.lean. Design captured in plans/01 (was task 299 plan v6). Depends on task 299 (encoding-based tableau) landing first; this then re-bases it onto native constructors. Zero sorry/admit/new-axiom. Est 1,500-2,000 lines touched.

---

### 440. Review pr leanprover cslib 648
- **Status**: [NOT STARTED]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: None

**Description**: PR review: GitHub PR https://github.com/leanprover/cslib/pull/648 — address ctchou CHANGES_REQUESTED feedback (Gentzen/Avigad references, Semantics restructuring confirmation, reviewer reply, coordinate #587/#607)

---

### 439. Refactor processnext to mutual def and prove instantstrict t
- **Effort**: 3-5 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 180
- **Research**: [426_temporal_tableau_ordconstraints_redesign/reports/03_spawn-analysis.md]
- **Plan**: [439_refactor_processnext_to_mutual_def_and_prove_instantstrict_t/plans/01_processnext-mutual-instantstrict.md]
- **Summary**: [439_refactor_processnext_to_mutual_def_and_prove_instantstrict_t/summaries/01_processnext-mutual-instantstrict-summary.md]

**Description**: Complete Phase 3 of task 426 (temporal_tableau_ordconstraints_redesign). Phases 1, 2, 4, 5 are already done and green. Only Phase 3 remains.

The blocker: in Cslib/Logics/Temporal/Tableau/Saturation.lean, `processNext` is a `let rec` nested inside `temporalExpandBranches`. The two functions are mutually recursive: `processNext` (line ~219) calls `temporalExpandBranches`, and `temporalExpandBranches` (line ~231) calls `processNext`. This mutual recursion is currently expressed via closure (nesting). Lean 4 generates no standalone recursion principle for `let rec` bindings, so the `InstantStrict` threading proof cannot be expressed as designed.

Step 3.1 (mechanical refactor): Convert the nested `let rec processNext` + `temporalExpandBranches` into a `mutual ... end` block at top level. The termination argument is lexicographic: `temporalExpandBranches` recurses on `fuel` (Nat), `processNext` recurses structurally on `List.length pending`; `processNext`'s call to `temporalExpandBranches` uses `fuel'` (strictly smaller). Verify with `lake build Cslib.Logics.Temporal.Tableau.Saturation` before attempting any proof. Commit the green refactor.

Step 3.2 (threading proof): Now that `processNext` is a top-level def in a `mutual` block, it has a recursion principle. Prove `InstantStrict` is preserved through the run by induction on fuel (for `temporalExpandBranches`) and structural induction on `pending` (for `processNext`), using the Phase 2 edge-by-edge lemmas (`InstantStrict.addFuture`, `InstantStrict.addPast`) as the inductive step. Commit green.

Step 3.3 (wire and finalize): Use the run-level `InstantStrict` result to discharge the order-preservation component of `openBranch_branchSat` for the D=Z/f=instant model, as far as the FMP boundary allows (Until/Since remain FMP-blocked, leave documented, no sorry). Run `lake build && lake test` and `lake exe checkInitImports`. Update task 426 to completed; update summary.

Reference: specs/426_temporal_tableau_ordconstraints_redesign/plans/02_phase3-streamlined.md for full step details. Files: Cslib/Logics/Temporal/Tableau/Saturation.lean (refactor), Cslib/Logics/Temporal/Tableau/Completeness.lean (wire). Territory constraint: serialize with task 427 on Completeness.lean (never parallelize). Zero-debt: no sorry allowed.

---

### 438. Pr task431 comment cleanups
- **Status**: [PR READY]
- **Task Type**: cslib
- **Topic**: PR & Upstreaming
- **Dependencies**: None
- **Research**: [438_pr_task431_comment_cleanups/reports/01_pr-prep-comment-cleanups.md]
- **Plan**: [438_pr_task431_comment_cleanups/plans/01_pr-prep-comment-cleanups.md]
- **Pr_description**: [438_pr_task431_comment_cleanups/pr-description.md]
- **Summary**: [438_pr_task431_comment_cleanups/summaries/01_pr-prep-comment-cleanups-summary.md]

**Description**: Upstream the comment/docstring cleanups identified by the task 431 audit via a CSLib PR. The edits are already applied and committed locally at 35436d7e (chore): (1) deleted the commented-out Term.subst_comm TODO stub in Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean, (2) reworded the stale 'removing the sorry' docstring in Cslib/Logics/LTL/Semantics/GNBA.lean:37 to past tense. Both are comment-only (no proof/build impact). Remaining work: submit to leanprover/cslib via /pr (user-only command) with a 'chore'/'doc' prefixed title. Optionally bundle any further doc-hygiene found in those two modules. Source: task 431 audit.

---

### 430. Prove atom persistence upward closure for intexpan
- **Effort**: 2-3 hours
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317
- **Research**:
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/01_atom-persistence-upward-closure.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/02_team-research.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/03_falsification-spike.md]

**Description**: Prove the atom-persistence / upward-closure structural lemma for open branches produced by `intExpandBranches`, and use it to discharge the two validity-bridge sorries in task 317.

## Context

Task 317 has two remaining validity-bridge sorries:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:112` (`intuitionisticTableau_complete`): needs `IValid φ → ∀ b, IForces (intExtractValuation b) (fun _ => False) 0 φ`.
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:109` (`minimalTableau_complete`): needs `MValid φ → ∀ b, IForces (intExtractValuation b) (minBranchBotForces b) 0 φ`.

Instantiating `IValid`/`MValid` at the branch model (World = Nat, val = intExtractValuation b) requires supplying upward-closure of `intExtractValuation b`:
  `T(atom p)@w ∈ b ∧ w ≤ w' → T(atom p)@w' ∈ b`

This atom-persistence property is NOT in `IBranchSaturation` (which covers compound-formula saturation only). The orchestrator handoff `.orchestrator-handoff.json` identifies this as blocker B3.

## What needs to be proved

Prove `intExpandBranches_openBranch_atom_persist` (or equivalent): if `intExpandBranches ... = .openBranch b`, then `intExtractValuation b` is upward-closed under the appropriate world accessibility relation.

Key structural facts to use:
- `propagatePersistence` (Rules.lean) copies ALL T(α) from parent world w to fresh child world w' when F(φ→ψ)@w fires (`intFImpRule`). So atoms propagate from direct parents to direct children.
- `applyAllTImpRules`/`applyPersistenceFixpoint` (Expansion.lean) run the T(φ→ψ) modus-ponens fixpoint across the edge list. Atoms are not directly handled here, but the T(→) consequences of atom propagation are.
- The explicit edge list `edges : IEdges` tracks `(child, parent)` pairs; `isAccessible edges w w'` is the reachability relation.

## Design decision the implementer must make

There are two viable paths:

**Path A (recommended if provable)**: Prove upward-closure under `≤` on Nat. This is the current countermodel's Preorder. Requires showing that whenever `T(atom p)@w ∈ b` and `w' > w` is a world on the branch, then `T(atom p)@w' ∈ b`. This follows from transitivity of `propagatePersistence` across the world tree, because new worlds are assigned strictly increasing labels and each inherits all T(α) from its parent. Verify with `lean_goal` at the sorry site whether this holds for the expansion invariant.

**Path B (fallback)**: If `≤` on Nat does not match the edge-list accessibility (sibling worlds may share `≤` ordering but not be accessible to each other), define the countermodel Kripke accessibility using `isAccessible edges` instead of `≤`. This requires:
- Defining a custom `Preorder` on Nat for the specific branch `b` and its edge list (or passing the edge list from `openBranch_countermodel` down to the validity bridges).
- Proving `intExtractValuation b` is upward-closed under `isAccessible edges`.
- Updating `openBranch_countermodel` to pass the edge list and use `isAccessible`-based Preorder.

## Exposition target

Expose the atom-persistence fact as ONE of:
1. A new field `sat_atom_persist` in `IBranchSaturation` (simplest if it can be proved from the expansion).
2. A standalone `private lemma intExpandBranches_openBranch_atom_persist` in `Scheme.lean`.
3. A wrapper helper `intExtractValuation_uc` proved inline at the sorry sites.

The chosen form must be sufficient to supply the upward-closure argument to `IValid`/`MValid` instantiation in both `intuitionisticTableau_complete` and `minimalTableau_complete`.

## Files to modify

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — add the persistence structural lemma (or new `IBranchSaturation` field + proof in `intExpandBranches_openBranch_sat`).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` — fill sorry at ~L112.
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` — fill sorry at ~L109.
- Possibly `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` and/or `Rules.lean` if invariants need to be stated there.

## Non-goals

- Do NOT touch the T(imp) sorry at Scheme.lean:330 (task 317's remaining obligation).
- Do NOT touch the `intExpandBranches_openBranch_sat` leaf sorries at Scheme.lean:481/536/550 (task 317's remaining obligation).
- Do NOT touch `*/Soundness.lean` (task 316 territory).

## Verification

After implementation:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` and `…Minimal.Completeness` succeed with the two validity-bridge sorries gone.
- `grep -n sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` returns nothing.
- `grep -n sorry Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` returns nothing.
- Build remains green (no regressions in Scheme.lean or Soundness files).

---

### 426. Temporal tableau ordconstraints redesign
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 439
- **Research**: [426_temporal_tableau_ordconstraints_redesign/reports/01_ordconstraints-redesign.md]
- **Plan**: [426_temporal_tableau_ordconstraints_redesign/plans/02_phase3-streamlined.md]
- **Summary**: [426_temporal_tableau_ordconstraints_redesign/summaries/01_partial-summary.md]

**Description**: [Decomposed from task 301, blocker A.] Redesign the time-ordering scheme in the temporal tableau so the ordering invariants hold. The lemma ordConstraints_strict (Cslib/Logics/Temporal/Tableau/Completeness.lean) is FALSE as stated: addPast t tNew adds the constraint (tNew, t) with tNew > t, violating the claimed invariant (a,b) in constraints -> a < b. Choose and implement a correct scheme (e.g. topological sort of the constraint graph, or a signed/relative integer time domain) so that extractModel builds a well-founded strict order, then prove the corrected ordConstraints lemma sorry-free. Start from green commit 7f052834. Independent of tasks 424 and 425.

---

### 425. Temporal tableau ptl fmp decidability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 426

**Description**: [Decomposed from task 301, blocker C.] Establish the finite model property (FMP) for Propositional Temporal Logic and use it to discharge temporalTruthLemma_untl and temporalTruthLemma_snce (Until/Since eventuality fulfilment), which in turn unblock eventualityDefect_unsat, temporalTableau_sound, openBranch_branchSat, temporalTableau_complete, and the final instDecidableValid in Cslib/Logics/Temporal/Tableau/. This is the theoretical gate for full decidability. Mirror the approach of COMPLETED task 421 (min_fmp_decidability), which added a sorry-free Decidable instance via FMP — reuse its pattern/infrastructure where possible. The hardest sub-part; gates task 301 completion. Independent of tasks 423 and 424 in principle, but final wiring of instDecidableValid needs all three landed.

---

### 419. Generalize derivation lifting to a cross-logic InferenceSystem layer (spike)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**:
  - [419_generalize_derivation_lifting_intersystem/reports/02_virtuous-unification.md]
  - [419_generalize_derivation_lifting_intersystem/reports/04_abstract-picture-and-result-inventory.md]
- **Plan**: [419_generalize_derivation_lifting_intersystem/plans/02_proof-system-morphism-overlay.md]

**Description**: [Spawned from task 415 audit — supports the structure-first vision; SPIKE.] Investigate hoisting liftDerivation / Derivable_mono (Modal/Metalogic/InterSystem/Lifting.lean:47) and Bimodal's liftDerivationWith onto the shared InferenceSystem / algebraicDerivationSystem abstraction already used by GenericMCSBridge, yielding ONE axiom-subsumption derivation-lifting result reusable by Modal, Bimodal, and PL. SPIKE FIRST: commit only if the necessitation / temporal_duality constructor variance is cleanly abstractable; otherwise document precisely why and stop (mark BLOCKED, never sorry). Benefits from task 417's Foundations placement (soft dependency). Effort L (abstraction risk). CI green if landed. Source: report §6, Rank 4.

---

### 415. Audit propositional->modal/temporal/bimodal lifting vs structure-first vision
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md]

**Description**: Audit how the structure-first propositional base (MPL/IPL/CPL: primitive nullary bot, gated efq/botL, property-module typeclasses) actually LIFTS into the Modal, Temporal, and Bimodal logics, and assess the result against the CSLib Zulip "Propositional Logic" thread (606970606) structure-first / fragment-genericity expectations -- with the explicit goal of identifying where the architecture can SURPASS those expectations. This is an infrastructure-verification (research/review) task; it produces a report and SPAWNS concrete follow-on implementation tasks, it does not itself refactor proofs.

THREE SEED FINDINGS to verify and deepen (from prior exploration):
1. CPL-ONLY EMBEDDING: toModal/toTemporal/toBimodal encode and/or via Lukasiewicz (Modal/FromPropositional.lean:35-41, Temporal/FromPropositional.lean:34-40, Bimodal/Embedding/PropositionalEmbedding.lean:33-41) -- classically valid but NOT intuitionistically valid. So only the CLASSICAL collapse of the propositional base lifts; the minimal/intuitionistic structure-first base does NOT survive the lift. Confirm with exact embedding defs + the semantic-preservation theorem statements (modal_satisfies_toModal_iff_evaluate:106 etc.), and characterize precisely what a structure-preserving (native and/or) embedding would require.
2. CONSERVATIVITY ASYMMETRY: Modal uses a PARAMETRIC conservativity lemma (modal_conservative_extension_param, Modal/Metalogic/ConservativeExtension.lean:54) while Temporal (ConservativeExtension.lean:87) and Bimodal (Metalogic/ConservativeExtension/PropositionalConservativity.lean:60) re-prove it CONCRETELY. Assess whether a single parametric/Foundations-level conservativity-lift framework can subsume all three.
3. GENERICLINDENBAUM DEBT: GenericLindenbaum.lean:47 defines a parametric explosion-parameterized substrate but Min/Int Lindenbaum, soundness, and strong-completeness remain ~50% duplicated; re-instantiation is "deferred to Phase 6" (task 407 residual). Scope the consolidation and its overlap with task 393.

ALSO: check the InterSystem liftDerivation (Modal/Metalogic/InterSystem/Lifting.lean:47) and whether the per-system structural metatheory (weakening/subst/cut across ND/LJ/LK) admits a shared parametric layer.

DELIVERABLE: a report at specs/415_*/reports/01_*.md that (a) verifies/refutes each finding with file:line evidence, (b) maps the lift architecture against the Zulip structure-first vision (met / partial / open), (c) for each gap gives a concrete Lean-level sketch of the fix and an effort estimate, and (d) proposes a prioritized set of spawnable follow-on tasks (e.g. structure-preserving embedding; unify conservativity; GenericLindenbaum Phase-6). Honor the Zulip AI policy (any prose intended for upstream must be human-authored). No code changes in this task.

---

### 414. Simplify proofs normalization modal family
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 180, Task 181, Task 215, Task 299, Task 300, Task 301, Task 444

**Description**: [Split from task 278.] Simplify Modal/, Temporal/, and Bimodal/ proofs that use manual `simp only [listImp_*, bigconj_*, toTemporal_*, toBimodal_*]` lists or verbose tactic chains over the task-268 normalization lemmas (including the Temporal/FromPropositional and Bimodal/Embedding/TemporalEmbedding embedding simp lemmas); replace with `grind`/`simp` where the new co-tags make the explicit lists redundant. Sequence after the modal-family proof-development settles: Modal 299/300; Temporal 180 (G/H primitives rewrite FromPropositional.lean), 241, 301; Bimodal 181 (propagates constructors through TemporalEmbedding.lean), 215, 275; plus the file-structure pass 321. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake.

---

### 413. Simplify proofs normalization propositional
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 317, Task 375

**Description**: [Split from task 278.] Simplify Propositional/ proofs that use manual `simp only [listImp_*, bigconj_*]` lists or verbose tactic chains over the task-268 normalization lemmas; replace with `grind`/`simp` where the new co-tags make the explicit lists redundant. Covers Hilbert/ND/completeness/decidability proof sites in Cslib/Logics/Propositional/. Sequence after the major PL proof-development tasks land (317 tableau completeness, 370 int/min decidability, 375 proof-system equivalence) and the Logics/Foundations file-structure pass (321). Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake.

---

### 412. Simplify proofs normalization foundations
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 41

**Description**: [Split from task 278.] Simplify proofs in Foundations/Logic/ that use manual `simp only [listImp_nil, listImp_cons, bigconj_nil, bigconj_singleton, bigconj_cons_cons, negBigconj_def, ...]` or verbose tactic chains over the task-268 normalization lemmas; replace with `grind`/`simp` where the @[simp, scoped grind =] co-tags (ListImplication.lean, Theorems/BigConj.lean) make the explicit lemma lists redundant. Audit ListImplication, BigConj, and downstream Foundations/Logic proof sites. Sequence after the Foundations completeness-infra abstraction (41) and the Logics/Foundations file-structure pass (321) to avoid re-sweeping moved code. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake.

---

### 409. Literal ⊥-rule-free base ND inductive (option B): split MinDerivation + Explosion; re-cut Curry-Howard & normalization
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 407

**Description**: SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- OPTIONAL / advanced. Task 407 adopts option C (re-frame the task-398 gated efq constructor as the explosion property module; the base relation is ⊥-rule-free UP TO the IsIntuitionistic gate). Option B is the LITERAL structure-first ND: split Theory.Derivation into a genuinely ⊥-rule-free base inductive MinDerivation (no efq constructor) plus an Explosion extension, prove all structural metatheory once on the base, and recover IPL-ND by adjoining efq. TRIGGER CONDITION: only pursue if a concrete downstream consumer needs a physically ⊥-free derivation object (e.g. a minimal-ND normalization theorem, or a lambda-calculus without an abort/efq combinator). COST/RISK: re-opens the single genuinely hard point from task 398 -- the subformula property under efq -- and forces re-cutting Curry-Howard (Theory.Term mirror) and Prawitz normalization (Basic/Reduction/Termination/SubformulaProperty) against the split. Reuse the task-398 decided strategy (atomic restriction + permutation conversions); treat any non-green proof as [BLOCKED], never sorry. HIGH effort -- use --hard. Depends on 407 (and ideally 408). Source: task 407 report 01 §5 option B / §7 W6, report 02 §5. ALIGNMENT NOTE: this two-inductive split is the Design-B-flavored route that the universal-algebra approach (task 407 option C) deliberately AVOIDS, because it duplicates derivation structure (exclude-then-add at the derivation level). Default remains task 407 option C: ONE derivation type with explosion as a property module. Pursue 409 ONLY if the trigger condition above fires.

---

### 407. Research & design: make MPL the structure-first base logic (⊥ as nullary connective; explosion/leastness/initiality as independent property modules)
- **Status**: [PR READY]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [407_mpl_base_structure_first_redesign/reports/01_mpl-base-structure-first.md]
  - [407_mpl_base_structure_first_redesign/reports/02_mpl-base-with-vs-without-bot.md]
  - [407_mpl_base_structure_first_redesign/reports/03_design-verification-plan-readiness.md]
- **Plan**: [407_mpl_base_structure_first_redesign/plans/04_mpl-base-waves-1-4-v2.md]
- **Summary**:
  - [407_mpl_base_structure_first_redesign/summaries/04_mpl-base-waves-1-4-v2-summary.md]
  - [407_mpl_base_structure_first_redesign/summaries/05_initial-object-witness-summary.md]
- **Design_note**: [407_mpl_base_structure_first_redesign/mpl-base-design-note.md]

**Description**: DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat.md) + codebase synthesis. Adopt the STRUCTURE-FIRST account: one fixed language ⟨Atom,⊥,∧,∨,→⟩; ⊥ is a primitive NULLARY connective whose meaning is intentionally underdetermined (a Johansson 'designated constant' supplied by every model, no intrinsic proof rule). MPL is the BASE proof theory (no rule/axiom mentions ⊥; ¬A:=A→⊥; A,A→⊥⊢⊥ is just impE). IPL = MPL + explosion (⊥/A) as an INDEPENDENT module; CPL = IPL + classical principles. Semantically, leastness (⊥≤a), initiality (universal property 0→A), and explosion-soundness are INDEPENDENT properties added by conservative strengthening, not changes to syntax or recursive clauses. Modularity organized around PROPERTIES (typeclasses/mixins), not connectives, so structural metatheory (weakening, substitution, admissibility, cut) is proved ONCE at MPL. RELATION TO 398: this is the deeper redesign 398 postponed (398 report §5). 398 took the OPPOSITE commitment (IPL-as-base via a gated ND efq constructor). Recommendation (report §5) is option (C): re-frame 398's gate as the explosion PROPERTY MODULE rather than revert it. FINDINGS (report 01): codebase is already ~70-80% structure-first. ALIGNED: algebraic semantics (AlgEvaluate with arbitrary bot_val; BrouwerianBot vs PointedBrouwerian; IsBotFree; conservativity chains) and Hilbert axioms (MinPropAxiom→IntPropAxiom+efq→PropositionalAxiom+peirce; IsIntuitionistic/MinimalAxioms typeclasses). GAPS: (1) ND inverted by 398 (gated efq = IPL-base); (2) sequent calculus LARGE gap (LJ/LK hard-code botL; no minimal LM; structural results per-system); (3) metalogic ~50% Min*/Int* duplication, Lindenbaum hard-wires EFQ; (4) semantic leastness/initiality/explosion present only implicitly (OrderBot + per-axiom proofs), not as a NAMED property hierarchy. SCOPE: research+design done (report 01). Plan should cover the cheap additive waves first: W1 design canonicalization+ND re-framing (C), W2 named semantic property hierarchy, W3 metalogic genericization, W4 tableau unification; and SPAWN W5 (minimal sequent calculus LM) and optional W6 (literal ⊥-rule-free ND, option B) as separate --hard tasks. Preserve ALL MPL/conservativity assets (do not revert 398). --hard recommended for planning. Honor Zulip AI policy. See OPEN QUESTIONS in report §9 (ND reconciliation C vs B; task scope; categorical/initiality timing; property naming; relation to task 400).

---

### 405. Proof style cleanup modal soundness
- **Status**: [PR READY]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 404
- **Research**: [405_proof_style_cleanup_modal_soundness/reports/01_proof-style-cleanup-modal-soundness.md]
- **Plan**: [405_proof_style_cleanup_modal_soundness/plans/01_proof-style-cleanup-modal-soundness.md]
- **Summary**: [405_proof_style_cleanup_modal_soundness/summaries/01_proof-style-cleanup-modal-soundness-summary.md]

**Description**: Simplify the proof machinery in the task-402 modal tableau soundness redesign before any upstream PR. Targets in Cslib/Logics/Modal/Tableau/Soundness.lean: modalApplyOne_fresh (uses unfold + extract_lets + `repeat first | Or.inl rfl | Or.inr ... | split` plus an apply_ite/ite_self cleanup) and the modalExpandBranches_closed_unsat per-branch accs/Forall2 reformulation. Improve readability/robustness without changing statements. Verify scoped + full lake build green, zero sorry, lint-style pass. Touches the same file as task 404 (sequence after it); overlaps code-hygiene task 321.

---

### 404. Forall2 mathlib cleanup soundness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [404_forall2_mathlib_cleanup_soundness/reports/01_forall2-mathlib-cleanup.md]
- **Plan**: [404_forall2_mathlib_cleanup_soundness/plans/01_forall2-mathlib-cleanup.md]
- **Summary**: [404_forall2_mathlib_cleanup_soundness/summaries/01_forall2-mathlib-cleanup-summary.md]

**Description**: Replace the local private re-proofs of List.Forall2 lemmas in Cslib/Logics/Modal/Tableau/Soundness.lean (forall2_append_aux, forall2_drop_aux, forall2_take_aux, forall2_of_zip_mem) with canonical Mathlib lemmas. These were added during task 402 because Mathlib.Data.List.Forall2 is not transitively imported by Cslib.Init. Either add the Mathlib import and switch call sites to library lemmas (List.Forall2.append/length_eq/etc.), or document why the local helpers are kept. Verify scoped + full lake build green, zero sorry, lint-style pass. Low-priority polish; helpers are correct as-is.

---

### 400. Unbundle connective typeclasses; reconcile with fmontesi PR #607 (Waring's flag a)
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [400_reconcile_connectives_pr607/reports/01_pr607-engagement.md]
  - [400_reconcile_connectives_pr607/reports/02_engagement-strategy.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/01_comparison-tables.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/02_falsum-bridge-sketch.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/03_grind-direction-finding.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/04_review-packet.md]
- **Plan**: [400_reconcile_connectives_pr607/plans/02_pr607-engagement.md]

**Description**: [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/reports/01_pr607-engagement.md] Engage fmontesi PR #607 (feat(Logic): logical operators) to land the connective typeclasses there instead of in #648 (Waring, Zulip 606970606). PREREQ DONE: our Connectives.lean removed from #648 (commit 85db79a6 on feat/propositional-ipl-base). PRIMARY POINT for the #607 review: #607 makes negation primitive (HasNot) and has NO HasBot; for IPL/MPL, neg is definitionally (phi -> bot), so #607 needs a HasBot (and HasTop) class with neg/top DERIVED, else the five-primitive Proposition (primitive bot) cannot register faithfully. SECONDARY: naming HasImpl/impl vs HasImp/imp; notation precedence conflicts (-> 25 vs 30, or 30 vs 35); bundle-vs-a-la-carte (PropositionalConnectives); notation ownership (typeclass notation + _def lemmas vs direct-on-Proposition). DELIVERABLE: human-authored review on #607 (Zulip AI policy), then register Proposition instances via #607 once the falsum question settles. Independent of the IPL-base work.

---

### 396. Salvage reusable lemmas from task-299 Soundness refactor for the per-branch-accessibility soundness redesign
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Evaluate and salvage the architecture-independent proof-engineering lemmas left on branch wip/task-299-soundness-refactor (commit 27d93e2d) by the stopped task-299 modal-K soundness re-attempt. Portable (acc-free) candidates: sfSat, sfSat_pos, sfSat_neg, RuleResultSat, and recognizer characterization lemmas (e.g. modalNegOf?_eq_some) in Cslib/Logics/Modal/Tableau/Soundness.lean, plus the branchSatisfiable Type (vs Type*) universe simplification. The FULL 299 refactor is UNBUILT and rewrites modalStepBranch_preserves_sat on the now-superseded global-Accessibility architecture, so do NOT merge it wholesale. Goal: decide which lemmas help the modal-tableau soundness-gap-redesign effort (the per-branch Accessibility 'task 384' tracked in the cslib-364 worktree / branch task-364-soundness-drift) and cherry-pick or restate them there if the propositional-rule recognizer layer hits the 'stuck on variable antecedent / consumed-scrutinee' friction documented in specs/364_modal_tableau_soundness_drift_repair/handoffs/BLOCKED-repair-guide.md (section 4). NOTE: 'task 384' here means the soundness-gap-redesign task in the cslib-364 worktree, which is a DIFFERENT task than main's own #384 (tableau_completeness_sorries) — task numbering diverged across worktrees. Reference branch: wip/task-299-soundness-refactor. Parent context: task 299 modal_k_tableau.

---

### 393. Consolidate duplicated Lindenbaum/Classical/conservativity constructions (Zulip first)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 391

**Description**: Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING before refactor. (a) Factor one generic quotient-Lindenbaum construction over the 3 parallel builds (~2100 lines): HilbertLindenbaum, HilbertLindenbaumRel, HilbertAlgCompleteness (4th in Bimodal). (b) Make litCtx_congr public and parameterize the 3 Classical completeness files (~700 lines, litCtx_congr' copied 3x) over the axiom predicate via GenericMCSBridge/HasMinimalAxioms. (c) Assess 3 Soundness modules + 8 conservativity modules + LJ/LK helper duplication. Source: §5.5.

---

### 392. Remove dead declarations and fix underscore/Extention naming
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 317, Task 389

**Description**: [Reconciled by task 395.] Tier-3. Delete grep-verified dead decls: Tableau/Classical/Soundness.lean:73-136 (12 classicalApplyOne_* private simp lemmas, 0 calls) + :486, Classical/Completeness.lean:435/447, Tableau/Defs.lean:81 propImpOrNegOf?, Intuitionistic/Rules.lean:114/203, Intuitionistic/Soundness.lean:431/505, NaturalDeduction/Equivalence.lean:305 hilbertAxiomToND, LK/Completeness.lean:69/73 mem_insert_*. Fix Extention->Extension typo (Equivalence.lean:256-257, Defs.lean:190/195). Rename underscore defs: modus_ponens constructor (Derivation.lean:77), lift_int_to_cl, goodSelection_seq, HasFresh to_infinite, emptyHrelation_apply. The LK/LJ cutAdm_*/ljCutAdm_* renames are DROPPED from this task — task 386 OWNS them (defsWithUnderscore). Sequence after 386. Source: §5.3-5.4 + 395.

---

### 391. Strip task-number jargon and fix stale docstrings
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 317, Task 389

**Description**: [Reconciled by task 395.] Tier-3. Remove internal task/process jargon from public docstrings: ClassicalConjImpCompleteness.lean (task 352, CL-B rung), ClassicalConjImpBotCompleteness.lean (task 378, CL-C rung), ConservativeChain.lean:44-45, HilbertLindenbaumRel.lean:21-23 (Route A2, 341 proof files), Tableau/RuleResult.lean:35, Foundations/Logic/Tableau/PropositionalTableau.lean:7, ListImplication.lean:83-139. Connectives.lean jargon (PR#607/task 340/173) is OWNED by task 400 (Connectives owner) — coordinate, do NOT double-edit. Stale-count fixes: re-verify post-task-398. NOTE StrongCompleteness 3-case counts (atom/bot/imp) remain CORRECT (398 changed derivation constructors, not formula structure). Fix only genuinely-stale counts: IntSoundness, MinSoundness, IntLindenbaum:320 misattached docstring, Tableau Int/Min DecisionProcedure sorry counts, Minimal/Completeness:50-51. Source: §5.1-5.2 + 395.

---

### 390. Update ORGANISATION.md Propositional section (post-merge tree)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Research**: [390_update_organisation_md/reports/01_update-propositional-organisation.md]
- **Plan**: [390_update_organisation_md/plans/01_update-propositional-organisation.md]
- **Summary**: [390_update_organisation_md/summaries/01_update-propositional-organisation-summary.md]

**Description**: [Refreshed post-merge vet.] The Propositional section (~ORGANISATION.md:100-105) is a 4-item stub. Update to reflect the actual 95+-file tree: SequentCalculus/{LJ,LK} (Interpolation, CutElimination, SubformulaProperty, Decidability); CurryHoward/{Defs,Isomorphism,Reduction}; Semantics/Algebra (25+ files: Brouwerian, HilbertAlgebra, Kripke, Glivenko, Conservative variants); Tableau/{Classical,Intuitionistic,Minimal} (Completeness/Soundness/DecisionProcedure); Subformula.lean; ProofSystemEquivalence.lean. Also update the Namespace Convention section re Cslib.Logic.PL vs Cslib.Logic.Propositional (task 387). Do before the PR lands.

---

### 389. Fix docBlame, barrel headers, unusedSectionVars, broken citation
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 317
- **Research**: [389_docstrings_headers_citations_propfound/reports/01_docstrings-headers-citations.md]

**Description**: [Reconciled by task 395.] Tier-2. (a) Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean: add docstrings to 7 undocumented def/abbrev (fld:50 also rename himpFold, fmeLe:106, fmeEquiv:123, fmeSetoid:125, FreeMeetExtension:152, mk:159, freeMeetEmbed:257) — only hard docBlame in Foundations. (b) DROPPED — the 4 Tableau barrels already carry copyright + import Cslib.Init (verified post-merge). (c) Add omit for 14 unusedSectionVars (mostly Tableau/Classical/Completeness, Minimal/Soundness:118, Minimal/Completeness:89). (d) Add references.bib entry NegriVonPlato2001 (Negri & von Plato, Structural Proof Theory, CUP 2001) cited by OrImpConservative.lean. Sequence the Tableau/Classical+Minimal Completeness edits AFTER task 317. Source: §4.3-4.6 + 395.

---

### 375. Proof system equivalence tableau sequent edges
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317

**Description**: Complete the cross-system equivalence story by folding the tableau (and remaining sequent) decision systems into the proof-system TFAE. Cslib/Logics/Propositional/ProofSystemEquivalence.lean currently proves Hilbert<->ND<->LK for CPL (cplProofSystemsTfae) and Hilbert<->ND<->LJ for IPL (iplProofSystemsTfae), plus the MPL Hilbert<->ND two-way. Add the missing edges so the equivalence is genuinely complete across all proof systems: classical Tautology <-> LK provability <-> closed classical tableau, and intuitionistic validity <-> LJ provability <-> closed intuitionistic tableau, extending the TFAE lists accordingly. Requires the tableau soundness+completeness to be green (task 316 done for soundness; task 317 for completeness) and the classical tableau build repaired (task 363). No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 317, 363.

---

### 317. Propositional tableau completeness
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Plan**: [plans/03_b2-fuel-sufficiency.md]

**Description**: Fill the propositional tableau completeness sorries (7 real sorries; soundness is already sorry-free after task 316). The open obligations are the truth-lemma / countermodel-extraction proofs in the three Completeness modules. Classical (Tableau/Classical/Completeness.lean): classicalExpandBranches_hintikka (line ~462) -- note the module's separate build break (bad Mathlib lemma ref + unsolved goals) is repaired first under task 363. Intuitionistic (Tableau/Intuitionistic/Completeness.lean): intTruthLemma (line ~89), intuitionisticOpenBranch_countermodel (~98), intuitionisticTableau_complete (~112). Minimal (Tableau/Minimal/Completeness.lean): minTruthLemma (~168), minOpenBranch_countermodel (~179), minimalTableau_complete (~190). Core technique: Hintikka-set argument -- a saturated open branch satisfies Hintikka conditions, from which a countermodel is extracted (a Boolean valuation for classical; a finite Kripke model for intuitionistic/minimal) and a truth lemma by formula induction matches forced/not-forced to the signed formulas at each world. Because task 369 parameterizes the intuitionistic and minimal tableau over (closurePred, modelBot), the int and min cases should be discharged ONCE as a single parametric truth-lemma/countermodel pair rather than duplicated. The tableau Decidable instances become genuinely sorry-free once these land. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 316, 323, 363, 369.

---

### 301. Temporal tableau
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 426, Task 425
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
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 442
- **Research**:
  - [299_modal_k_tableau/reports/03_completeness-decomposition.md]
  - [299_modal_k_tableau/reports/04_truth-lemma-architecture.md]
- **Plan**: [299_modal_k_tableau/plans/05_modal-k-tableau-plan.md]
- **Summary**: [299_modal_k_tableau/summaries/06_finalization-summary.md]

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
- **Status**: [EXPANDED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 41, Task 180, Task 181, Task 299, Task 301, Task 317, Task 375

**Description**: Simplify proofs using new simp/grind normalization tags. After task 268 adds @[simp, scoped grind =] tags to Hilbert system definitional lemmas, audit all proofs in Propositional/, Modal/, Temporal/, and Bimodal/ that use manual `simp only [listImp_nil, listImp_cons, bigconj_nil, ...]` or verbose tactic chains involving these normalization lemmas. Replace with `grind` or `simp` where the new tags make the explicit lemma lists redundant. Also check Foundations/Logic/ proofs. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake

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
- **Topic**: Bimodal Logic
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
- **Topic**: Bimodal Logic
- **Dependencies**: Task 180
- **Research**: [181_bimodal_primitive_dia_always_historically/reports/01_bimodal-primitive-expansion-research.md]

**Description**: Propagate primitive diamond, allFuture, and allPast constructors to the Bimodal layer, giving {atom, bot, imp, and, or, box, dia, untl, snce, allFuture, allPast} (11 primitives). This is the union of Modal (task 179) and Temporal (task 180) primitive sets. Scope: (1) Syntax/Formula.lean: add .dia/.allFuture/.allPast constructors, update all match cases. (2) Semantics/Truth.lean: structural truthAt clauses. (3) ProofSystem: axiom constructors for diamond duality and G/H axioms. (4) Embedding: extend ModalEmbedding (.dia), TemporalEmbedding (.allFuture/.allPast). (5) Metalogic: propagate through ~50 files (Core, Soundness, Completeness, BXCanonical, ConservativeExtension, Separation, Decidability, Algebraic). Follow task 177 playbook. (6) Classical equivalences become theorems. Verify full CI. Estimated ~50 files, ~2000 lines, similar scope to task 177.

---

### 180. Temporal primitive always historically
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**:
  - [180_temporal_primitive_always_historically/reports/01_primitive-always-historically-research.md]
  - [180_temporal_primitive_always_historically/reports/02_implementation-attempt-status.md]
  - [180_temporal_primitive_always_historically/reports/03_metalogic-obligations-research.md]
- **Plan**: [180_temporal_primitive_always_historically/plans/03_primitive-gh-metalogic-plan.md]

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
- **Topic**: Bimodal Logic
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
- **Topic**: Bimodal Logic
- **Dependencies**: Task BimodalLogic:discrete_sorry_elimination

**Description**: Port discrete completeness (completeness_discrete theorem) and WeakCanonical/IntegerModel/ infrastructure (~6 files). The discrete branch constructs countermodels on Int via the Reynolds pipeline. Currently blocked: upstream BimodalLogic has sorryAx tracing through chronicle_gap_contradiction → succ_cofinal → limitDomSubtype_isSuccArchimedean → succ_embed_surjective. Port after upstream sorry elimination completes.

**Source**: BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/IntegerModel/ (~6 files), discrete branch of BXCanonical/Completeness.lean
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic discrete completeness sorry elimination (36 sorries across IntegerModel/)
**Parent task**: 8 (expanded)
