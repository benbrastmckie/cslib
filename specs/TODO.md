---
next_project_number: 551
---

# TODO

## Task Order

*Updated 2026-07-24. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,226,317,393,400,405,407,425,438,440,449,463,465,466,474,497,519,522,530,534,535,537,542,544,545,546,549,550 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,375,409,430,450,451,456,511 | 36,37,181,317,407,425,449,535 | propositional logic, temporal logic, bimodal logic, ... |
| 3 | 41,413,506,548 | 39,40,375,511 | foundations, modal logic, code hygiene |
| 4 | 300,412 | 41,506 | modal logic, code hygiene |
| 5 | 414 | 181,215,300,301 | code hygiene |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
317 [IMPLEMENTING] — Fill the propositional tableau completeness sorries (7 real sorri
  └─ 375 [NOT STARTED] — Fold the TABLEAU decision systems into the propositional proof-sy
  └─ 430 [PLANNED] — Prove the atom-persistence / upward-closure structural lemma for 
400 [BLOCKED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
407 [PR READY] — DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat
  └─ 409 [NOT STARTED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
497 [NOT STARTED] — Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (P
545 [NOT STARTED] — ABSTRACTION CONSOLIDATION (review 2026-07-23, M8/M9). Two consoli

### Modal Logic

405 [PR READY] — Simplify the proof machinery in the task-402 modal tableau soundn
522 [PR READY] — Uniform frame-condition to axiom correspondence library for modal
535 [NOT STARTED] — Task 511 (S4 loop-checking termination) is BLOCKED at Phase 7 (de
  └─ 511 [BLOCKED] — Follow-on to task 506 (S4 loop-checking): close the S4 terminatio
    └─ 506 [BLOCKED] — Deliver plan Phases 5 and 6 of task 300 combined (specs/300_modal
      └─ 300 [BLOCKED] — Umbrella task for modal frame extensions T/S4/S5 (and the derived
    └─ 548 [NOT STARTED] — COMPLETENESS-MATRIX GAP (review 2026-07-23, M3). Tableau decidabi
537 [IMPLEMENTING] — Prove the general labelled SOUNDNESS direction nik_TS5_soundness 
546 [NOT STARTED] — REDUNDANCY (review 2026-07-23, M2). Cslib/Logics/Modal/Metalogic/

### Temporal Logic

425 [NOT STARTED] — [Decomposed from task 301, blocker C.] Establish the finite model
  └─ 301 [BLOCKED] — Implement tableau decision procedure for temporal logic (Cslib.Lo
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Bimodal Logic

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 
  └─ 450 [NOT STARTED] — Core corrected conservativity result. PR-BLOCKING for task 180. S
449 [NOT STARTED] — Foundation for the corrected TM-over-temporal conservativity resu
  └─ 450 [NOT STARTED] — Core corrected conservativity result. PR-BLOCKING for task 180. S (see above)
  └─ 451 [NOT STARTED] — Deeper metatheory for the metric tense logic BX+ (defined in task

### Code Hygiene

393 [NOT STARTED] — Consolidate duplicated Lindenbaum / MCS / conservativity construc
463 [NOT STARTED] — Vet found low-severity documentation gaps (code placement itself 
542 [NOT STARTED] — DOCSTRING HYGIENE (review 2026-07-23, M4/L8-L10). ~918 docstring 
544 [NOT STARTED] — NAMING/NOTATION UNIFORMITY (review 2026-07-23, M10/M11 + L1-L3/L1
412 [NOT STARTED] — [Split from task 278.] Simplify proofs in Foundations/Logic/ that
413 [NOT STARTED] — Simplify verbose Propositional/ proofs (manual simp only [listImp
414 [NOT STARTED] — Simplify verbose Modal/, Temporal/, and Bimodal/ proofs (manual s

### Pr & Upstreaming

438 [PR READY] — Upstream the comment/docstring cleanups identified by the task 43
440 [NOT STARTED] — PR review: GitHub PR https://github.com/leanprover/cslib/pull/648
465 [PR READY] — Review PR #607 (logical operators): post GitHub review covering t
466 [PR READY] — Post comment on PR #648 linking the Zulip primitive-bot plus efq 
474 [PR READY] — Draft Zulip replies confirming CSLib meeting attendance to Montes

### Tableau Infrastructure

456 [NOT STARTED] — Generalize the Sfor-containment / subset-blocking device recurrin

### Literature

519 [NOT STARTED] — Follow-up to task 518 (Simpson re-ingest). TWO PARTS.

### Uncategorized

530 [BLOCKED] — REDUNDANCY CLEANUP. Cslib/Logics/Bimodal/Metalogic/BXCanonical/Ch
534 [NOT STARTED] — COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree 
549 [NOT STARTED] — lake shake --add-public --keep-implied --keep-prefix flags Cslib/
550 [NOT STARTED] — Nine files touched by task 540 (Bimodal/Metalogic/Core/MCSPropert

## Tasks

### 550. Remove ported set_option linter suppressions in Bimodal/Temporal propositional-reasoning files
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Nine files touched by task 540 (Bimodal/Metalogic/Core/MCSProperties.lean, Bimodal/Theorems/{Combinators,Perpetuity/Helpers,Perpetuity/Principles,Propositional/Connectives,Propositional/Core,TemporalDerived}.lean, Temporal/Metalogic/{GeneralizedNecessitation,PropositionalHelpers}.lean) carry file-scoped `set_option linter.style.{emptyLine,longLine,setOption} false` / `set_option linter.{flexible,unusedSimpArgs} false`, inherited verbatim from the external BimodalLogic port. Reformat each file to satisfy the disabled linters (wrap long lines, remove stray blank lines, resolve flexible/unused-simp-arg findings) and drop the suppressions, or narrow them to per-declaration `set_option ... in` where only one declaration is affected.

---

### 549. Prune shake-flagged redundant imports in CanonicalModel.lean (task 540 follow-up)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: lake shake --add-public --keep-implied --keep-prefix flags Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean's `public import Cslib.Logics.Modal.Metalogic.MCS` and `public import Cslib.Logics.Modal.Semantics.Birelational` as unused now that task 540 added GenericMCSBridge/DerivationCombinators imports to the same file. Verify with `lake shake --fix` or manual removal, then `lake build` the module to confirm no regression (the MCS/Birelational names are referenced only in docstring prose, not as used Lean identifiers, per current inspection).

---

### 548. Decidability remaining eight modal cube corners
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 511, Task 535

**Description**: COMPLETENESS-MATRIX GAP (review 2026-07-23, M3). Tableau decidability instances exist for only 6 of the 15 modal-cube systems: K (Tableau/CompletenessLoop.lean:2295), T (FrameCompleteness.lean:1318), KB (:1933), S5 (:2429), K5/Five (:3220), KB5 (:4165); S4 is in flight (tasks 506/511/535 own the loop-checking termination). The 8 remaining corners — D, K4, K45, D4, D5, D45, DB, TB — have sorry-free soundness + strong completeness + compactness + conservative extension but NO Valid predicate, no tableau driver, and no Decidable instance: the decidability column of the cube is ragged. Work (BLOCKED on 511/535 landing the S4 termination machinery): extend the generic tableau driver to the remaining corners — transitive corners (K4, K45, D4, D45) reuse the S4 loop-checking mechanism; serial corners (D, D5, DB) need a serial successor rule; TB composes the existing T and B rules. Where filtration/FMP is cheaper than loop-checking for a given corner, route via FMP instead. Acceptance: either a Decidable instance per corner, or an explicit documented out-of-scope note per corner stating why (e.g. cost/benefit), so the matrix is intentionally complete rather than accidentally ragged. Zero sorry, zero new axioms; keep all frozen deliverables from 300/534/506 untouched.

---

### 547. Minimal sequent calculus lm close tfae matrix
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [547_minimal_sequent_calculus_lm_close_tfae_matrix/reports/01_minimal-sequent-calculus-lm.md]
- **Plan**: [547_minimal_sequent_calculus_lm_close_tfae_matrix/plans/01_lm-sequent-calculus-tfae.md]
- **Summary**: [547_minimal_sequent_calculus_lm_close_tfae_matrix/summaries/01_lm-sequent-calculus-tfae-summary.md]

**Description**: GAP FILL (review 2026-07-23, L5). The proof-system x logic matrix has a documented hole at (SequentCalculus, Minimal): Propositional/Metalogic/ProofSystemEquivalence.lean:19 states minimal logic gets only the two-way mplHilbertIffNd because 'no minimal sequent calculus exists in CSLib', while classical and intuitionistic get three-way TFAE (cplProofSystemsTfae, iplProofSystemsTfae). Work: add Cslib/Logics/Propositional/SequentCalculus/LM/ mirroring the existing LJ tree structure — rules (LJ minus ex falso / with restricted right rules per the standard minimal-logic sequent presentation), soundness against the minimal Kripke semantics (the min_soundness/min_completeness semantic layer already exists sorry-free), completeness, and equivalence with the minimal Hilbert system — then extend the equivalence to a symmetric three-way mplProofSystemsTfae. Cut elimination for LM may follow the LJ development where applicable but is not required for the TFAE. SCOPE GUARD: tableau membership in the TFAE stays out of scope (task 375 owns folding tableau systems into the TFAE). Zero sorry.

---

### 546. Factor intersystem lattice onto schemaunion
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: REDUNDANCY (review 2026-07-23, M2). Cslib/Logics/Modal/Metalogic/InterSystem/ carries 8 near-parallel files (~890 lines): ConstructiveLatticeSubsumption.lean (108), IntuitionisticLatticeSubsumption.lean (110), MinimalLatticeSubsumption.lean (104), PropositionalStrengthSubsumption.lean (230), plus four matching *Monotonicity.lean (83-88 each) — all proving the same 'direct-edge axiom subsumption via constructor case-split' shape (their own docstrings say so: ConstructiveLatticeSubsumption.lean:16-19, MinimalLatticeSubsumption.lean:16-19). The classical track already has the generic lemma this wants — SchemaUnion.subsumption (SchemaUnion.lean:155) — and SchemaUnion.lean:46-48 explicitly flags extending the SchemaUnion mechanism to the non-classical axiom families as intended but unrealized. Work: either (a) migrate the intuitionistic/minimal/constructive axiom families onto SchemaUnion (preferred — realizes the documented intent, and shrinks the parallel Lindenbaum/prime-theory scaffolding duplication between the Intuitionistic and Minimal tracks), or (b) factor a track-generic subsumption/monotonicity combinator parameterized over the axiom-tag type, collapsing the 8 files to instantiations. Zero sorry; all 8 files are currently sorry-free.

---

### 545. Collapse prop algebra completeness stack conservativity sprawl
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: ABSTRACTION CONSOLIDATION (review 2026-07-23, M8/M9). Two consolidations in Cslib/Logics/Propositional/Semantics/Algebra/: (1) COMPLETENESS STACK: a three-layer unification stack (FragmentGeneric.lean -> BrouwerianCompletenessGeneric.lean -> CanAlgComplete.lean) was added on top of the retained piecewise completeness files (HilbertCompleteness.lean, MplConservativeChain.lean, BrouwerianCompleteness.lean); CanAlgComplete's own docstring says it bundles results 'already proved piecewise' and 'only the unifying abstraction was missing', yet the piecewise public statements were never retired — four files express one fragment-completeness fact. Pick CanAlgComplete as the terminal generic interface; demote the subsumed piecewise completeness theorems to private corollaries inside it or delete the duplicated public statements. (2) FRAGMENT-CONSERVATIVITY SPRAWL: eight sibling files each carry one fragment-conservativity result (ImpConservative.lean, ConjImpConservative.lean, ConjImpBotConservative.lean, OrImpConservative.lean, Conservative.lean, ConservativeChain.lean ~19KB, MplConservativeChain.lean ~15KB, HilbertConservativeGlivenko.lean) in a near-linear import chain with no shared generic core — consolidate into a single FragmentConservativity.lean parameterized by the fragment predicate. SCOPE GUARD: task 393 owns CROSS-FAMILY conservativity/Lindenbaum consolidation; this task is strictly the intra-Propositional Algebra fragment layer — confirm the boundary against 393's plan before starting. Zero sorry; all inputs are currently sorry-free and must remain so.

---

### 544. Unify validity derivability naming notation
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: NAMING/NOTATION UNIFORMITY (review 2026-07-23, M10/M11 + L1-L3/L11). Mechanical rename sweep across the four logic families: (1) VALIDITY VOCABULARY: Propositional uses Tautology (Semantics/Bool.lean:90); Modal has no top-level validity predicate (only pointed Modal[m,w |= phi] at Modal/Basic.lean:277); Temporal uses capitalized Valid/ValidSerial/ValidDense/ValidDiscrete (Semantics/Validity.lean:74-94); Bimodal uses lowercase valid/validDense/validDiscrete (Semantics/Validity.lean:49,117,129). Align on ONE convention (lowercase valid* suggested), starting with the Temporal-Bimodal pair which share identical FrameClass vocabulary and differ only in capitalization. (2) Add the missing turnstile notation to Temporal: Bimodal defines |= phi and Gamma |= phi (Semantics/Validity.lean:60,81); Temporal has none — add the same scoped notation. (3) COMPLETENESS SUFFIX: Algebra layer uses _complete (44 uses: alg_complete, brouwerian_complete, ...) vs Metalogic layer _completeness (prop_completeness, int_completeness, min_completeness, ...) — standardize on _completeness (Mathlib longer-form convention). (4) NIKTheorem (Modal/Metalogic/Constructive/Labelled/Deduction.lean:316) breaks the otherwise-uniform Derivable naming (Propositional/ProofSystem/Derivation.lean:128, Modal/Metalogic/DerivationTree.lean:152, Bimodal/ProofSystem/Derivable.lean:38, Temporal/ProofSystem/Derivable.lean:35) — rename to NIKDerivable or NIK.Derivable. (5) S5 keeps legacy abbrev ModalAxiom := SchemaUnion s5Tags in Metalogic/DerivationTree.lean:69 while all 14 siblings define <Sys>Axiom in ProofSystem/Instances/<Sys>.lean — rename S5Axiom and relocate to Instances/S5.lean (keep a deprecated alias if churn is wide). (6) Conservativity names split between <x>_conservative_extension (Temporal:61, Modal:54, Bimodal PropositionalConservativity:97) and bimodal_conservative_over_<y> (ModalConservativity:246, TemporalConservativity:289) — standardize one scheme across all five. DISTINCT from task 497 (imp vs impl constructor naming) — do not touch that seam. Sequence AFTER tasks 539/540 land to avoid rebasing renames across those refactors.

---

### 543. Remove dead logic modules and dead end bridges
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Research**: [543_remove_dead_logic_modules_and_dead_end_bridges/reports/01_dead-logic-modules-triage.md]
- **Plan**: [543_remove_dead_logic_modules_and_dead_end_bridges/plans/01_remove-dead-logic-modules.md]
- **Summary**: [543_remove_dead_logic_modules_and_dead_end_bridges/plans/01_remove-dead-logic-modules.md]

**Description**: DEAD CODE (review 2026-07-23, M5-M7). Three dead or dead-end module groups in the logic trees: (1) Cslib/Foundations/Logic/PropositionalTableau.lean (212 lines) — header literally reads 'DEPRECATED: superseded by Cslib.Foundations.Logic.Tableau'; zero real imports (the two grep hits are docstring prose); sole build entry is the root barrel Cslib.lean:104. Delete the file and drop the barrel line. (2) Foundations/Logic/Automation/HilbertSearch.lean (268-line hilbert_search proof-search tactic) — imported by nothing; the two references (Bimodal AxiomMatcher.lean:48, ProofExtraction.lean:222) are 'when ported' comments. Either wire it into the Modal/Bimodal Hilbert derivations that hand-roll combinator proofs, or remove it (removal is acceptable; git preserves it). (3) Propositional/Semantics/Algebra/Bridge.lean (boolEvaluateEq/propEvaluateEq bridge, imported by nothing despite Semantics/Bool.lean:38-42 telling future work to reuse it) and KripkeBridge.lean (Kripke-algebraic Heyting duality, consumed by no completeness chain): either route Semantics/Bool.lean and the IPL completeness chain through them so their canonical-status docstrings become true, or explicitly mark both as independent showcase developments. Decision per module documented in the summary; net LOC should go down.

---

### 542. Strip task provenance stale claims docstrings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: DOCSTRING HYGIENE (review 2026-07-23, M4/L8-L10). ~918 docstring references to 'Task N' / 'Phase M' / 'now-deleted ...' / rollout narratives across the Modal tree — concentrated in Metalogic/GenericMCSBridge.lean, MCS.lean, SchemaSoundness.lean, SchemaTags.lean:18-30, Constructive/Labelled/PrimeLemma.lean:49-51,844,1684-1696, Constructive/Labelled/Soundness.lean:238-355, Intuitionistic/TruthLemma.lean:29,152,305 — documenting how the code was built rather than what it proves, and violating .claude/rules/no-task-references-in-deliverables.md. Sweep all four logic trees (Modal, Propositional, Temporal, Bimodal) plus Foundations/Logic: keep mathematical contracts and literature references, delete task/phase/implementation-history provenance. Also fix the specific stale/dead items: (a) Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean:51 claims 'one remaining sorry' but the file is now sorry-free; (b) Propositional/Semantics/Algebra/Bridge.lean:16 claims to be 'the single canonical home of the ONE evaluation story' while imported by nothing (soften or make true — coordinate with task 543 which decides that file's fate); (c) delete the ~40-line commented-out proof carcass with commented sorry markers in Temporal/Tableau/Completeness.lean:962-1005 (live gap owned by tasks 425/301 — leave a one-line pointer); (d) Propositional/Semantics/Bool.lean:40 forward-references 'Matthew Doty's forthcoming work' — verify covered by task 226 and remove the rot-prone reference. Coordinate with task 438 (comment-cleanup PR already committed) to avoid re-editing its files.

---

### 541. Ltl temporal semantic preservation bridge
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**: [541_ltl_temporal_semantic_preservation_bridge/reports/01_ltl-temporal-bridge-research.md]
- **Plan**: [541_ltl_temporal_semantic_preservation_bridge/plans/01_temporal-preservation-bridge.md]
- **Summary**: [541_ltl_temporal_semantic_preservation_bridge/plans/01_temporal-preservation-bridge.md]

**Description**: SEMANTIC GAP (review 2026-07-23, H3). Cslib/Logics/LTL/Embedding.lean:48 defines Formula.toTemporal (LTL -> Priorean tense logic) but the file contains ZERO theorems; its docstring (lines 22-27, 44-47) asserts the map is chosen 'to preserve semantics' — including a reflexive-until vs strict-until reconciliation — that is never proven. No file imports the module: LTL is a disconnected island despite complete, sorry-free GNBA correctness (gnba_language_eq, Baier-Katoen 5.39), omega-regularity (Formula.isRegular), and ltlModelChecking results that currently cannot transfer to the Temporal tree. Work: prove the satisfaction-preservation theorem LTL.Satisfies phi v <-> Temporal.Satisfies phi.toTemporal over the corresponding nat-indexed flow, settling the until-convention reconciliation, and wire at least one LTL result across the bridge (e.g. satisfiability transfer) so the module has a consumer. If the bridge is unprovable as currently stated, correct the translation and document the discrepancy — do not leave the unverified docstring claim standing. Zero sorry.

---

### 540. Retire wrap unwrap combinator bridge layers
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [540_retire_wrap_unwrap_combinator_bridge_layers/reports/01_bridge-lemma-elimination.md]
- **Plan**: [540_retire_wrap_unwrap_combinator_bridge_layers/plans/01_retire-bridge-layers.md]
- **Summary**: [540_retire_wrap_unwrap_combinator_bridge_layers/summaries/01_retire-bridge-layers-summary.md]

**Description**: BRIDGE-LEMMA ELIMINATION (review 2026-07-23, H2). The same 8-10 propositional combinators (doubleNegation, impTrans, lceImp, rceImp, dni, identity, pairing, ...) are re-declared statement-for-statement behind local wrap/unwrap bridges in THREE places: Temporal/Metalogic/PropositionalHelpers.lean (wrap:51, unwrap:56), Bimodal/Theorems/Perpetuity/Helpers.lean (wrap:56, unwrap:60), Bimodal/Theorems/Propositional/{Core,Connectives}.lean (28 defs, ~58 unwrap uses). These bridges exist solely because DerivationTree-style derivability and the Foundations InferenceSystem-indexed derivability share no definitional surface. Meanwhile Modal bypasses Foundations/Logic/Theorems entirely and reproves combinators locally (e.g. private imp_trans0 at Modal/Metalogic/Intuitionistic/CanonicalModel.lean:223). Work: (1) prove the wrapper family ONCE, generic over a Hilbert/InferenceSystem typeclass instance — the same pattern GenericMCS already uses for the deduction theorem — and have Temporal/Bimodal/Modal obtain the combinators by instance resolution; (2) delete the three wrap/unwrap wrapper layers; (3) route Modal's local combinator reproofs through the generic layer; (4) drop the 34 per-target rfl embedding-commutation restatements (toModal_atom/bot/imp at Modal/FromPropositional.lean:50-60; toTemporal_* at Temporal/FromPropositional.lean:49-59; Bimodal/Embedding/PropositionalEmbedding.lean:61-71 and the TemporalEmbedding/ModalEmbedding rfl blocks) in favor of the generic embed_* @[simp] lemmas already in Propositional/Embedding.lean:92-104, keeping only genuinely per-target lemmas (_and/_or/_neg/_box/_untl). SCOPE GUARD: tasks 393 (Lindenbaum/MCS consolidation) and 41 (completeness infra) own the MCS/deduction-theorem seams — this task owns only the combinator-wrapper and embedding-rfl layers; coordinate before touching GenericMCSBridge files.

---

### 539. Consolidate modal truth lemma single generic route
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [539_consolidate_modal_truth_lemma_single_generic_route/reports/01_truth-lemma-consolidation.md]
- **Plan**: [539_consolidate_modal_truth_lemma_single_generic_route/plans/01_consolidate-truth-lemma.md]
- **Summary**: [539_consolidate_modal_truth_lemma_single_generic_route/summaries/01_consolidate-truth-lemma-summary.md]

**Description**: TRUTH-LEMMA CONSOLIDATION (review 2026-07-23, H1). The canonical-model truth lemma is proved three times: k_truth_lemma (Systems/K/Completeness.lean:163, fully generic — box case needs only EFQ+K from kCore), truth_lemma (Metalogic/Completeness.lean:274, demands a semantically unnecessary h_T), d_truth_lemma (Systems/D/Completeness.lean:241, unnecessary h_D). Since every one of the 15 axiom predicates contains kCore, all 15 systems can use k_truth_lemma. Work: (1) promote k_truth_lemma into Metalogic/Completeness.lean as THE truth lemma (rename canonical_truth_lemma); (2) relocate the shared machinery out of the K/D leaf files (k_derive_box_from_inconsistency, k_mcs_box_witness, d_canonical_serial) so K/D shrink to the ~180-line instance shape of their 13 siblings; (3) delete truth_lemma, mcs_box_witness, mcs_box_closure, and the D-route box block (~545 duplicated lines); (4) repoint all 15 *_truth_lemma_applied at the promoted lemma; (5) dedupe the 13-tag schema-witness blocks — 432 `by decide` invocations copy-pasted across the 15 Systems/*/Completeness.lean files and re-listed inside each *_strong_completeness and *_compactness — via one generic core-witness lemma discharged from Finset.subset facts (SchemaUnion.insert_iff / SchemaUnion.subsumption, SchemaUnion.lean:155,179). Zero sorry, zero semantic change; the tree is currently sorry-free and must stay so.

---

### 537. Labelled cs5 general soundness biconditional
- **Effort**: 15-40 hours
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 517
- **Research**:
  - [537_labelled_cs5_general_soundness_biconditional/reports/01_general-soundness-strategies.md]
  - [537_labelled_cs5_general_soundness_biconditional/reports/02_direct-route-from-sources.md]
  - [537_labelled_cs5_general_soundness_biconditional/reports/03_tree-shape-invariant-audit.md]
  - [537_labelled_cs5_general_soundness_biconditional/reports/04_crosslabel-motive-audit.md]
- **Plan**:
  - [537_labelled_cs5_general_soundness_biconditional/plans/01_general-soundness.md]
  - [537_labelled_cs5_general_soundness_biconditional/plans/02_direct-route.md]
  - [537_labelled_cs5_general_soundness_biconditional/plans/03_direct-route-forest.md]

**Description**: Prove the general labelled SOUNDNESS direction nik_TS5_soundness : NIKTheorem TS5 phi -> CKValidFC cs5FCIncest phi, completing Simpson 1994 Thm 8.1.4's biconditional for CSLib constructive CS5/IS5. CONTEXT (from parent task 517, which delivered the completeness direction): cs5_completeness (Completeness.lean:132) and the anti-vacuity certificate nik_TS5_consistent + nik_soundness_onePoint (Soundness.lean) are LANDED sorry-free/axiom-clean. cs5FCIncest_lift (Soundness.lean:181) is a landed building block. THE OPEN OBSTRUCTION (established across 3 dispatches, no forced sorry): TS5={T,B,Four} makes TClosure TS5 G.R the TOTAL relation on the always-connected derivation graph, so the box edge-condition is an r-CLIQUE condition across all labels, not tree-adjacency; and cs5FCIncest's hfour/hsymbox/hincest conjuncts only ever produce EXISTENTIALLY-raised relational witnesses, whereas CKForces's box clause (and boxE) need EXACT edges/symmetry between independently-fixed points (persistence is only upward). No asymmetric countermodel refuted the obstruction; no closure proof completed it -- GENUINELY OPEN. THREE CANDIDATE STRATEGIES (ranked; none is a plain direct-implementation dispatch -- each needs research/re-plan): (1) prove cs5FCIncest forces symmetric/clique closure on finitely-generated substructures -- cheapest, possibly reuses the FLO closure machinery from parent Phases 1-7; (2) formalize Simpson's own modified sequent system L_m(TS5, empty), his stated fix for exactly this problem; (3) build the deferred Simpson Ch.6 Hilbert-labelled ADEQUACY bridge (NIKTheorem TS5 phi -> Derivable CS5ModalAxiom phi) and obtain labelled soundness as a corollary of the already-landed Hilbert soundness cs5_soundness_derivable_incest (CS5Canonical.lean:373) -- note this resurrects the bridge task 517 deliberately avoided (Track C, C5 'THE TRUE CRUX'). Full analysis: specs/517_labelled_bounded_context_cs5_completeness/handoffs/phase-11-general-soundness-blocked-20260719c.md and Soundness.lean's refined-analysis docstring. CONSTRAINTS: NO sorry, NO new axiom under Cslib/; do not weaken cs5FCIncest; do not regress parent's landed completeness/anti-vacuity. Research MUST use --lit (Simpson Ch 8 soundness, Lifting Lemma 8.1.3, L_m modified sequent system). BibKeys: Simpson1994, MarinMoralesStrassburger2021. HIGH uncertainty (the direct route may be genuinely open). Start with strategy (1) as a research/probe pass before committing. Depends on 517.

---

### 535. Abstract termination-measure interface for S4/B loop lemma (task 511 Phase 7 follow-on)
- **Effort**: 10-16 hours
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [511_s4_loop_checking_termination/reports/02_spawn-analysis.md]

**Description**: Task 511 (S4 loop-checking termination) is BLOCKED at Phase 7 (decidability) because of a driver/shadow-invariant mismatch, precisely documented in specs/511_s4_loop_checking_termination/handoffs/07_phase7-blocked-driver-mismatch.md. ROOT CAUSE: s4Valid's Decidable instance must run the REAL driver modalTableauS4 := modalTableauGen (modalApplyOneS4 phi) phi, whose minting guard blockingWorldS4 compares a prospective successor's birth content against the CURRENT LIVE relevantSetFinset of every existing known world. The landed termination machinery (S4LoopInv, modalStepBranchS4_worldBound, task 511 Phases 4-6, LoopChecking.lean, all sorry-free) is proven only for the keyed SHADOW stepper modalStepBranchS4Keyed, guarded by blockingWorldS4Keyed -- a comparison against a stable, birth-frozen keys list instead. This is directly visible in the step hypothesis of modalStepBranchS4_preserves_S4LoopInv, which takes modalStepBranchS4Keyed ... = some (...), not modalStepBranchS4. The two guards are NOT interchangeable: S4LoopInv.keyLowerBd gives only keys subset-of relevantSetFinset (a subset, not equality), so the live-set freshness guarantee blockingWorldS4_none_fresh does not imply a keys-freshness guarantee -- the world-bound guarantee is proven about a driver modalTableauS4 does not actually run. TARGET: close Decidable (s4Valid phi) and s4Valid completeness against Cube.S4. RESOLUTION PATHS (either is acceptable; survey first, then choose): (a) 9-A, generalize the shared driver framework (RuleApply/Accessibility in GenericDriver.lean, and/or the Aux-parametrized top-loop lemma modalExpandBranchesHintikka/AuxStepPreserved/AuxBounds/ModalLoopInvHintikka already landed in CompletenessLoop.lean for S5's ModalLoopAuxS5w) to support extra opaque per-branch threaded state generically (the S4 keys : List (WorldIndex x Finset (Sign x Proposition Atom)) list), not just a Prop-valued Aux. Note: wrapping keys inside an existential Aux(b,e,acc) := exists keys, S4LoopInv-fields does NOT avoid the mismatch by itself, because AuxStepPreserved would still need to re-derive keysDistinct preservation using the real (live-set) guard's contract -- the same insufficient argument; the generic interface's apply : RuleApply Atom is a single fixed function per call with no mechanism for extra per-branch threaded state to evolve across steps. (b) 9-B, build a bespoke S4-specific top-level driver (e.g. modalExpandBranchesS4Keyed/modalTableauS4Keyed) directly around the already-landed modalStepBranchS4Keyed, with its own full processNext-style fuel induction (mirroring the ~700-line modalExpandBranchesHintikka/modalExpandBranchesGen_hintikka precedent), plus re-verification that soundness (modalTableauS4_sound) and the truth lemma (modalTruthLemmaS4) reconnect against the keyed guard's Hintikka witnesses. Either path must also redefine modalTableauS4 (or add a new modalTableauS4Keyed and repoint s4Valid's Decidable instance to it) since the currently-shipped modalTableauS4 runs the live-set-guarded modalApplyOneS4, not the keyed guard the termination proof is about. SHARED FILES: Cslib/Logics/Modal/Tableau/CompletenessLoop.lean and Cslib/Logics/Modal/Tableau/GenericDriver.lean (the interface-generalization side), and Cslib/Logics/Modal/Tableau/LoopChecking.lean (the S4-consuming side, where modalTableauS4/modalStepBranchS4Keyed/S4LoopInv live). SHARED BENEFICIARIES: this is a shared-file change explicitly identified (Planner Decision 2, specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md) as benefiting the B-system decidability line (archived task 505_b_symmetric_decidability_via_generic_tableau_driver) and the generalized-tableau-soundness-over-spec line (archived task 513_generalize_tableau_soundness_chain_over_spec) in addition to unblocking task 511 -- survey both for reusable patterns before designing the interface. Task 515's already-landed modalExpandBranchesHintikka/Aux-parametrized machinery (CompletenessLoop.lean, built for S5) is a strong entry point for path (a) but is confirmed NOT sufficient by itself (see mismatch note above). HARD CONSTRAINTS: zero sorry, zero new axiom declarations, every new public declaration lean_verify-clean. If a phase genuinely cannot close, mark it [BLOCKED] with the exact reached lean_goal state -- never insert a sorry/admit/vacuous placeholder to force a green build. Do not modify the frozen, sorry-free task 511 Phases 1-6 deliverables in LoopChecking.lean (S4LoopInv, modalStepBranchS4Keyed, modalStepBranchS4_worldBound, modalHintikkaSetS4_eq) except as needed to wire the new interface/driver against them. Do not modify S5's ModalLoopAuxS5w/modalExpandBranchesHintikka call site in a way that regresses task 515's already-landed S5 decidability. Upon completion, task 511 Phase 7 should be resumed by wiring the new interface (or bespoke driver) against the Phases 1-6 machinery to close Decidable (s4Valid phi) and s4Valid completeness against Cube.S4.

---

### 534. Pure K5/5 Euclidean tableau completeness without the equivalence route
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: Task 531

**Description**: COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree (instDecidableFiveValid/instDecidableKb5Valid, FrameCompleteness.lean) is delivered via the KB5/S5 equivalence route, which leans on a full-equivalence closure. This task delivers genuine pure-K5 / pure-5 (Euclidean without full equivalence, no Mathlib closure operator) tableau soundness + completeness + decidability - the one modal-cube corner explicitly deferred out of the completed KB5/Euclidean task. Mirror the existing Five/KB5 development but over the bare Euclidean frame condition. Zero sorry, zero new axioms; keep the frozen equivalence-route deliverables untouched.

---

### 530. Consolidate the duplicated Chronicle construction across Bimodal and Temporal
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: None
- **Research**: [530_consolidate_chronicle_construction_bimodal_temporal/reports/01_chronicle-dedup-research.md]
- **Plan**: [530_consolidate_chronicle_construction_bimodal_temporal/plans/01_chronicle-consolidation.md]

**Description**: REDUNDANCY CLEANUP. Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ and Cslib/Logics/Temporal/Metalogic/Chronicle/ are two nearly-identical full trees sharing 8 filenames (ChronicleConstruction, ChronicleToCountermodel, ChronicleTypes, CounterexampleElimination, PointInsertion, RRelation, ...) with ~89% overlap. The partial task-454 consolidation already lifted PointInsertion; extend that: factor the shared chronicle/countermodel-elimination machinery into a label-generic module under Cslib/Foundations/Logic/Metalogic/Chronicle/ (which currently holds only SinceSeedConsistency.lean) and have both the bimodal and temporal trees instantiate it. Preserve all landed sorry-free results; this is a structural dedup, not a proof change. Watch the bimodal discrete-completeness sorries (blocked on external port) - do not entangle them.

---

### 522. Uniform frame condition axiom correspondence library
- **Status**: [PR READY]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [522_uniform_frame_condition_axiom_correspondence_library/reports/01_frame-condition-correspondence-survey.md]
- **Plan**: [522_uniform_frame_condition_axiom_correspondence_library/plans/01_frame-correspondence-library.md]

**Description**: Uniform frame-condition to axiom correspondence library for modal soundness. RECONCILED: Phase 1 delivered sorry-free - Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean provides the five explicit-hypothesis correspondence lemmas (Satisfies.modalT_axiom/modalFour_axiom/modalB_axiom/modalD_axiom/modalFive_axiom), registered in the barrel and re-exported via Soundness.lean. REMAINING (the actual dedup payoff): wire the 14 downstream Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean consumers to delegate to this library instead of reproving axiom-frame correspondence case-by-case; they are currently still byte-identical case-by-case proofs. Was gated pending a Zulip design decision on the library shape. DESIGN DECISION (resolved, user 2026-07-18): Public signature form = EXPLICIT-HYPOTHESIS primary — lemmas like Satisfies.modalT_axiom' m (h_refl : ∀ w, m.r w w) w φ; the 14 downstream Systems/*/Soundness.lean consumers delegate via one-line exact-delegation passing their existing h_refl/h_trans/… (zero other downstream edits). Additionally expose instance-arg [Std.Refl m.r] forms for new systems. Scope: one coherent PR = additive lemmas (already landed in FrameCorrespondence.lean) + wire the 14 consumers; defer completeness-FC re-expression and birelational dedup to follow-ups. Post a Zulip heads-up before the multi-file PR lands.

---

### 519. Fix literature ocr chunking and wijesekera
- **Effort**: 3-5 hours
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Topic**: Literature
- **Dependencies**: Task 518

**Description**: Follow-up to task 518 (Simpson re-ingest). TWO PARTS.

(1) RE-INGEST wijesekera_1990_constructivemodallogicsi (BibKey Wijesekera1990). Task 518's corpus audit found it has the IDENTICAL over-fragmentation signature that made Simpson unusable: 154 chunks, 468B mean, 62% under 300B. This document matters -- Wijesekera 1990 is THE source for CSLib's constructive (fallible-world) DIAMOND semantics, cited in Cslib/Logics/Modal/Metalogic/Constructive/ (CS4.lean and CS5.lean docstrings reference it for Definition 1.1.4 and Section 2), and is directly relevant to in-flight task 517. Apply task 518's proven fix (documented in specs/518_reingest_simpson1994_literature_corpus/summaries/01_reingest-summary.md): bypass the font-size heading heuristic, extract via pdftotext -layout, apply paragraph-reflow to repair OCR line-break noise, insert chapter/section-level headings only, then feed the existing unmodified literature-chunk.sh Pass-2 merge. VALIDATE that Definition 1.1.4 and the Section 2 diamond / fallible-world definitions return COMPLETE statements via literature-search.sh. Preserve the old chunk set as rollback, as 518 did.

(2) HARDEN THE ROOT CAUSE (the general fix that 518 deliberately left undone). literature-convert.sh's PyMuPDF path falls back to a FONT-SIZE heading-detection heuristic when a PDF has no embedded TOC. On OCRmyPDF/Tesseract scans the per-line font metrics are noisy, so it emits spurious markdown headings mid-sentence and mid-word, and literature-chunk.sh then splits at every one -- shredding lemma statements. Fix so it does not fire on OCR'd scans: detect the OCR producer (Tesseract / OCRmyPDF metadata), require corroborating cues (line length, position, numbering, blank-line context) before accepting a font-size heading, and/or add a post-check rejecting headings that split mid-sentence. ALSO add a guard so any future ingest yielding a pathological mean chunk size (under roughly 600B) warns loudly rather than silently landing a shredded corpus. Task 518 scoped its fix to Simpson only and left the shared scripts untouched; this task does the general repair so all future --lit work benefits.

NOTE the honest ceiling from 518: prose is recoverable but math symbols are frequently garbled by Tesseract. Do NOT attempt to fix OCR quality itself -- only the chunking/heading pathology. Do not touch Cslib/ Lean source. Low risk, high leverage.

---

### 511. S4 loop checking termination
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: Task 535
- **Plan**: [511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md]
- **Research**: [511_s4_loop_checking_termination/reports/01_s4-termination-guard-redesign.md]
- **Summary**: [511_s4_loop_checking_termination/summaries/01_s4-termination-bound-decidability-summary.md]
- **Handoff**: [511_s4_loop_checking_termination/handoffs/02_phase5-keylowerbd-fact-closed.md]

**Description**: Follow-on to task 506 (S4 loop-checking): close the S4 termination bound and complete decidability. Task 506 landed Phases 1-7 green (4-rule, LoopChecking.lean equality-blocking machinery, modalApplyOneS4/modalTableauS4, modalHintikkaSetS4, extractModelS4, modalTruthLemmaS4, s4Valid + 4-rule soundness; zero sorry/axiom) but Phase 8 (the #worlds <= 2^|modalSubfmls phi0| termination bound) is [BLOCKED]: worldSetsDistinct is not a genuine per-step invariant of modalStepBranchS4 as currently designed. Two documented gaps (see specs/506_s4_loopchecking_machinery_termination_bound_and_decidability/plans/01_s4-loopchecking-termination-decidability.md Phase 8 BLOCKER note): (1) persistent rule firings (K boxPos, T self-propagation, the 4-rule box-itself propagation) add formulas to an already-known world relevant set without re-checking distinctness against other known worlds; (2) the minting guard (blockingWorld) checks the SOURCE world uniqueness against existing worlds, not the freshly-minted world own prospective content, so a new world is not guaranteed distinct at creation. SCOPE: (a) redesign the minting guard or restate the invariant over a saturation-stable notion of a world relevant set so distinctness is actually preserved per step; (b) prove the pigeonhole bound #worlds <= 2^|modalSubfmls phi0| as a loop invariant under the corrected guard (build the sibling S4LoopInv, do NOT extend ModalPotentialInv whose rankEdge exact per-edge decrease transitive propagation falsifies); (c) modalStepBranchS4_worldBound; (d) then Phase 9: fuel sufficiency, s4Valid completeness, Decidable (s4Valid phi) against Cube.S4, consuming task 510 generalized modalHintikkaSetGen chain (verify modalHintikkaSetS4 aligns with modalHintikkaSetGen modalApplyOneS4, or build the S4 hintikka-production via the generic loop lemma). Zero sorry, zero axiom. Files: Cslib/Logics/Modal/Tableau/LoopChecking.lean, Cslib/Logics/Modal/Tableau/FrameCompleteness.lean, possibly a new FmpMeasure-sibling for S4LoopInv. Standing permission to land [BLOCKED] again with documented goal state if the pigeonhole invariant still does not close.

---

### 506. S4 loopchecking machinery termination bound and decidability
- **Effort**: 8-12 hours
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 511
- **Research**:
  - [506_s4_loopchecking_machinery_termination_bound_and_decidability/reports/01_frame-specific-tableau-extensions.md]
  - [506_s4_loopchecking_machinery_termination_bound_and_decidability/reports/02_spawn-analysis.md]
  - [506_s4_loopchecking_machinery_termination_bound_and_decidability/reports/03_parent-phase-plan-reference.md]
- **Plan**: [506_s4_loopchecking_machinery_termination_bound_and_decidability/plans/01_s4-loopchecking-termination-decidability.md]
- **Summary**: [506_s4_loopchecking_machinery_termination_bound_and_decidability/summaries/01_s4-loopchecking-termination-decidability-summary.md]

**Description**: Deliver plan Phases 5 and 6 of task 300 combined (specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md): the S4 (reflexive-transitive) system, the acknowledged crux of the task. This is deliberately NOT an instantiation of the generic driver built in the prerequisite task -- S4's termination argument (loop-checking / subset-blocking) is structurally different from the K-style finite-catalog counting measure, because K's depth-based modalWorldBound provably breaks under transitive box propagation. It does reuse the T-rule (modalApplyOneT, delivered by the prerequisite task) for its reflexive component and follows the same frame-specific driver-variant file/module conventions. Add the 4-rule to FrameRules.lean: T(box phi)@w + edge w->w' gives T(box phi)@w' and T(phi)@w' (propagate the box itself transitively), dually F(diamond phi)@w gives F(diamond phi)@w'. Build the equality-of-formula-set blocking machinery in a new Cslib/Logics/Modal/Tableau/LoopChecking.lean: formulasAtWorld, an equality test over modalSubfmls phi0, and the diamond-rule minting guard that adds a loop-back edge instead of minting a new world when an equal-set world exists. Extract the countermodel via Relation.ReflTransGen (Std.Refl + IsTrans free). Prove the box-positive truth-lemma bridge by induction on the ReflTransGen path (ReflTransGen.head_induction_on), carrying T(box phi) via the 4-rule and discharging the reflexive endpoint via the T-rule. Prove S4 soundness via Satisfies.four (Basic.lean). If the termination bound closes, prove #worlds <= 2^|modalSubfmls phi0| as a loop invariant under the equality-blocking guard, extend ModalPotentialInv (FmpMeasure.lean), establish fuel sufficiency, and state s4Valid / Decidable (s4Valid phi) against Cube.S4. This task carries explicit permission to land at [BLOCKED] (S4 rules/soundness/truth-lemma green, termination bound left open, documented goal state) rather than introduce a sorry or axiom -- do not force the 2^|Sf| invariant if it does not close within the run; document a recommended follow-on s4-loop-checking-termination task instead. Files: Cslib/Logics/Modal/Tableau/FrameRules.lean (4-rule), Cslib/Logics/Modal/Tableau/LoopChecking.lean (new), Cslib/Logics/Modal/Tableau/FrameCompleteness.lean (extractModelS4, S4 bridge), Cslib/Logics/Modal/Tableau/FrameSoundness.lean (S4 arm), Cslib/Logics/Modal/Tableau/FmpMeasure.lean (ModalPotentialInv extension, if termination closes).

---

### 497. Reconcile imp naming
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (Proposition.imp constructor and → notation) with the rest of the library once PR #607 lands, so the propositional connective naming is consistent library-wide (noting Modal uses 'impl'). Raised in review of PR #648 by thomaskwaring. BLOCKED until #607 (external PR, leanprover/cslib) is merged.

---

### 474. Draft zulip replies meeting fragments
- **Status**: [PR READY]
- **Task Type**: general
- **Topic**: PR & Upstreaming
- **Dependencies**: None

**Description**: Draft Zulip replies confirming CSLib meeting attendance to Montesi and opening the fragment-design discussion Doty proposed

---

### 466. Record zulip settlement pr 648
- **Status**: [PR READY]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: Task 467
- **Research**: [466_record_zulip_settlement_pr_648/reports/01_pr-review-research.md]
- **Plan**: [466_record_zulip_settlement_pr_648/plans/01_pr648-rereview-comment.md]
- **Pr_response**: [466_record_zulip_settlement_pr_648/pr-comment-draft.md]
- **Summary**: [466_record_zulip_settlement_pr_648/summaries/01_pr648-rereview-comment-summary.md]

**Description**: Post comment on PR #648 linking the Zulip primitive-bot plus efq settlement (Waring, 2026-06-28) and request re-review from ctchou

---

### 465. Review pr 607 logical operators
- **Status**: [PR READY]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: None

**Description**: Review PR #607 (logical operators): post GitHub review covering the red CI from the unmigrated HML LogicalEquivalence instance, the imp vs impl naming decision, operator file layout, NOTATION.md precedence documentation, and primitive-bot ownership of the propositional definitions file

---

### 463. Docs: update ORGANISATION.md Tableau/ tree sketches + strip internal task refs from public docstrings (task 299/455 vet)
- **Status**: [NOT STARTED]
- **Task Type**: markdown
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Vet found low-severity documentation gaps (code placement itself is correct/idiomatic): (1) ORGANISATION.md:148 Modal/ tree sketch omits the `Tableau/` subdirectory; ORGANISATION.md:26 Foundations/Logic/ tree sketch omits `Tableau/` (Sign.lean, SignedFormula.lean, RuleResult.lean, Branch.lean, Closure.lean, ClosureCondition.lean, Measure.lean, PropositionalRules.lean) — add these entries to document existing placement. (2) Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:1178 and nearby: permanent public docstrings for `modalTableau_complete`/`modalTableau_decides` embed ephemeral internal notes like '(task 442 Phase 6, FINAL)', '(task 442 Phase 5a)' — replace with plain, durable mathematical descriptions.

---

### 456. Shared tableau containment blocking
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Tableau Infrastructure
- **Dependencies**: Task 317

**Description**: Generalize the Sfor-containment / subset-blocking device recurring across tableau developments into a single label-generic module Cslib/Foundations/Logic/Tableau/Blocking.lean, built on the existing Branch.formulasAt (Foundations/Logic/Tableau/Branch.lean:81). Lift Temporal's timeType/isSubsetBlocked/isTemporallyBlocked (Temporal/Tableau/Branch.lean:101-174) and task 317's Sfor/containment check to: Branch.typeAt (deduplicated (Sign x F) forced-type at a label), Branch.containmentBlocked (containment test), and the once-proven core lemma Tableau.distinctTypes_le_pow ((b.labels.map b.typeAt).eraseDups.length <= 2^U.length for a subformula-closed universe U). Highest-value payoff: distinctTypes_le_pow is the shared core of BOTH task 317's intExpandBranches_world_bound_dedup (plan 04 Phase 5.1) AND the currently-[BLOCKED] Temporal soundness obligation (Temporal/Tableau/Soundness.lean:23-54, '<= 2^n time types' / loop-detection) - proving it once could unblock Temporal Phase 7. The definitional lift is cheap; the soundness lemma (blocking => bounded => countermodel) is the hard part, but hard exactly once instead of 2-3 times. DEPENDS ON task 317 landing first (so the (psi not in forced(x)) side-condition shape is settled); ideally co-scoped with the Temporal soundness unblock. Also add missing references.bib entries GargGenoveseNegri2012 and DershowitzManna1979 (ready in report 05 Q4). Source: task 317 reuse/abstraction research report 06 (R2). Verify scoped + full lake build green, checkInitImports/lint-style/shake pass, zero sorry.

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

### 440. Review pr leanprover cslib 648
- **Status**: [NOT STARTED]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: None

**Description**: PR review: GitHub PR https://github.com/leanprover/cslib/pull/648 — address ctchou CHANGES_REQUESTED feedback (Gentzen/Avigad references, Semantics restructuring confirmation, reviewer reply, coordinate #587/#607)

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
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317
- **Research**:
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/01_atom-persistence-upward-closure.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/02_team-research.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/03_falsification-spike.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/02_teammate-a-findings.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/02_teammate-b-findings.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/02_teammate-c-findings.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/02_teammate-d-findings.md]
- **Plan**: [430_prove_atom_persistence_upward_closure_for_intexpan/plans/03_upward-closure-bridge-discharge.md]

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

### 425. Temporal tableau ptl fmp decidability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 426

**Description**: [Decomposed from task 301, blocker C.] Establish the finite model property (FMP) for Propositional Temporal Logic and use it to discharge temporalTruthLemma_untl and temporalTruthLemma_snce (Until/Since eventuality fulfilment), which in turn unblock eventualityDefect_unsat, temporalTableau_sound, openBranch_branchSat, temporalTableau_complete, and the final instDecidableValid in Cslib/Logics/Temporal/Tableau/. This is the theoretical gate for full decidability. Mirror the approach of COMPLETED task 421 (min_fmp_decidability), which added a sorry-free Decidable instance via FMP — reuse its pattern/infrastructure where possible. The hardest sub-part; gates task 301 completion. Independent of tasks 423 and 424 in principle, but final wiring of instDecidableValid needs all three landed.

---

### 414. Simplify proofs normalization modal family
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 180, Task 181, Task 215, Task 299, Task 300, Task 301, Task 444

**Description**: Simplify verbose Modal/, Temporal/, and Bimodal/ proofs (manual simp only [listImp_*, bigconj_*, toTemporal_*, toBimodal_*] lists and long tactic chains) using the EXISTING normalization/embedding lemmas. RECONCILED: original premise cited task-268 'co-tags' which was abandoned - re-scoped to the lemmas that actually exist. Lower priority proof-golf; verify each simplification keeps the proof sorry-free.

---

### 413. Simplify proofs normalization propositional
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 317, Task 375

**Description**: Simplify verbose Propositional/ proofs (manual simp only [listImp_*, bigconj_*] lists and long tactic chains) using the EXISTING normalization lemmas (listImp_axiom_k/_s in Foundations/Logic/Metalogic/ListImplication.lean, bigconj_* in the syntax files). RECONCILED: the original premise cited task-268 'co-tags' as the enabler, but task 268 was abandoned - re-scoped to use the normalization lemmas that actually exist, replacing explicit rewrite lists with simp/grind where they are now redundant. Lower priority proof-golf; verify each simplification keeps the proof sorry-free.

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
- **Plan**:
  - [407_mpl_base_structure_first_redesign/plans/04_mpl-base-waves-1-4-v2.md]
  - [407_mpl_base_structure_first_redesign/plans/01_mpl-base-waves-1-4.md]
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

### 393. Consolidate duplicated Lindenbaum/Classical/conservativity constructions (Zulip first)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Consolidate duplicated Lindenbaum / MCS / conservativity constructions across the logic families. Duplication confirmed present: multiple parallel Lindenbaum algebra variants (HilbertLindenbaumAlgebra, ImpLindenbaumAlgebra, RelLindenbaumAlgebra, LindenbaumAlg) and MCS-extension variants (lindenbaumMCS/lindenbaumMCSSet/bimodal_lindenbaum); GenericMCSBridge.lean duplicated x4 (Propositional/Modal/Bimodal.Core/Temporal Metalogic dirs) as thin per-family re-instantiations of one Foundations pattern; LiftViaMorphism.lean x3 (Modal InterSystem, Propositional Semantics/Algebra, Bimodal ConservativeExtension). Consolidate onto the shared Foundations generic-MCS and morphism-lift machinery, retiring the per-family copies where they add no value. (Dependency on the archived-completed docstring task dropped.)

---

### 375. Proof system equivalence tableau sequent edges
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317

**Description**: Fold the TABLEAU decision systems into the propositional proof-system TFAE. RECONCILED: the sequent edges are ALREADY done - Cslib/Logics/Propositional/ProofSystemEquivalence.lean has cplProofSystemsTfae (Hilbert/ND/LK) and iplProofSystemsTfae (Hilbert/ND/LJ). REMAINING: add the tableau nodes to both TFAEs, wiring Propositional/Tableau/{Classical,Intuitionistic,Minimal}/Completeness.lean into the equivalence. Depends on task 317 (propositional tableau completeness) landing its remaining sorries.

---

### 317. Propositional tableau completeness
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Plan**:
  - [plans/03_b2-fuel-sufficiency.md]
  - [317_propositional_tableau_completeness/plans/01_tableau-completeness-plan.md]
  - [317_propositional_tableau_completeness/plans/02_tableau-completeness-unified.md]
  - [317_propositional_tableau_completeness/plans/03_b2-fuel-sufficiency.md]
  - [317_propositional_tableau_completeness/plans/04_sfor-dedup-fuel-sufficiency.md]
  - [317_propositional_tableau_completeness/plans/05_frame-change-and-fuel-raise.md]
  - [317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md]
- **Summary**:
  - [317_propositional_tableau_completeness/handoffs/01_phase1-continuation.md]
  - [317_propositional_tableau_completeness/summaries/03_b2-fuel-sufficiency-phase1-summary.md]
  - [317_propositional_tableau_completeness/summaries/03_b2-fuel-sufficiency-phase2a-blocked-summary.md]
  - [317_propositional_tableau_completeness/summaries/04_sfor-dedup-phase1-summary.md]
  - [317_propositional_tableau_completeness/summaries/04_sfor-dedup-phase2-summary.md]
  - [317_propositional_tableau_completeness/summaries/04_sfor-dedup-phase4-summary.md]
  - [317_propositional_tableau_completeness/summaries/05_frame-change-and-fuel-raise-summary.md]
  - [317_propositional_tableau_completeness/summaries/06_intuniverse-intwork-phase6-summary.md]
  - [317_propositional_tableau_completeness/summaries/07_expmeasure-phase7_2-and-phase8-blocked-summary.md]
  - [317_propositional_tableau_completeness/summaries/08_phase8-fuel-doubling-and-init-bound-summary.md]
  - [317_propositional_tableau_completeness/summaries/09_phase6-2-containment-worldbound-summary.md]
- **Research**:
  - [317_propositional_tableau_completeness/reports/10_wave-a-atomic-derisk.md]
  - [317_propositional_tableau_completeness/reports/01_tableau-completeness-research.md]
  - [317_propositional_tableau_completeness/reports/03_tableau-completeness-approach.md]
  - [317_propositional_tableau_completeness/reports/04_fuel-sufficiency-measure.md]
  - [317_propositional_tableau_completeness/reports/05_fuel-sufficiency-literature.md]
  - [317_propositional_tableau_completeness/reports/06_sfor-dedup-reuse-abstraction.md]
  - [317_propositional_tableau_completeness/reports/07_option-b-fuel-bound.md]
  - [317_propositional_tableau_completeness/reports/08_b1-truthlemma-timp.md]
  - [317_propositional_tableau_completeness/reports/09_phase2-escape-routes.md]

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
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 506
- **Research**:
  - [300_modal_extensions_t_s4_s5/reports/01_frame-specific-tableau-extensions.md]
  - [300_modal_extensions_t_s4_s5/reports/02_spawn-analysis.md]
- **Plan**: [300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md]

**Description**: Umbrella task for modal frame extensions T/S4/S5 (and the derived B/D/5/Euclidean cube corners). RECONCILED: T (instDecidableTValid), B (instDecidableBValid), S5 (instDecidableS5Valid), and 5/Euclidean (instDecidableFiveValid/instDecidableKb5Valid) are all delivered sorry-free in Cslib/Logics/Modal/Tableau/FrameCompleteness.lean via the generic tableau driver. The SOLE remaining phase is S4 (reflexive-transitive) loop-checking termination bound and decidability, tracked by task 506 (gated on the S4 termination task). This umbrella closes when S4 decidability (instDecidableS4Valid) lands.

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
