---
next_project_number: 537
---

# TODO

## Task Order

*Updated 2026-07-19. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,226,317,393,400,405,407,425,438,440,449,463,465,466,474,497,517,519,522,523,530,534,535 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,375,409,430,450,451,456,511,536 | 36,37,181,317,407,425,449,523,535 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41,413,506 | 39,40,375,511 | foundations, modal logic, code hygiene |
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

### Modal Logic

405 [PR READY] — Simplify the proof machinery in the task-402 modal tableau soundn
517 [BLOCKED] — ROUTE B (user-funded, full build): Build a LABELLED / bounded-con
522 [PR READY] — Uniform frame-condition to axiom correspondence library for modal
523 [IMPLEMENTING] — Schema-union axiom combinator to replace the hand-written per-sys
  └─ 536 [NOT STARTED] — Document the modal axiom-schema architecture in a new docs/ direc
535 [NOT STARTED] — Task 511 (S4 loop-checking termination) is BLOCKED at Phase 7 (de
  └─ 511 [BLOCKED] — Follow-on to task 506 (S4 loop-checking): close the S4 terminatio
    └─ 506 [BLOCKED] — Deliver plan Phases 5 and 6 of task 300 combined (specs/300_modal
      └─ 300 [BLOCKED] — Umbrella task for modal frame extensions T/S4/S5 (and the derived

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

## Tasks

### 536. Document modal axiom schema architecture
- **Status**: [NOT STARTED]
- **Task Type**: markdown
- **Topic**: Modal Logic
- **Dependencies**: Task 523

**Description**: Document the modal axiom-schema architecture in a new docs/ directory (create docs/ if absent). Write a durable architecture/design document covering the compositional design that the SchemaUnion combinator and the FrameCorrespondence library together establish: (1) the ModalSchemaTag 18-tag alphabet + ModalSchemaTag.Holds (schema = set of instances, existential encoding) + SchemaUnion (S : Finset ModalSchemaTag) combinator; (2) subsumption expressed as Finset.subset — the modal cube (K ⊂ T ⊂ S4 ⊂ S5, …) as a decide-able computation on tag sets, replacing the hand-written per-edge subsumption lemmas; (3) compositional soundness via unionSound as a syntax/semantics factorization, and how it consumes the five frame-condition→validity lemmas (Satisfies.modalT_axiom/modalFour_axiom/modalB_axiom/modalD_axiom/modalFive_axiom) from Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean — i.e. the frame-correspondence library (semantic side) and the schema-union combinator (syntactic side) are the two halves of one abstraction with unionSound as the hinge; (4) the representation-agnostic HasAxiom* typeclass insulation layer (Foundations/Logic/ProofSystem.lean); (5) the S5 = T+4+B disposition and why the KB5→S5 edge is deliberately omitted; (6) the design rationale — why Representation A (schema-tag def + Finset union) was chosen over Representation B (macro-generated inductives) for long-term foundations; (7) the scope boundary and how the intuitionistic/minimal families are a future instance of the same abstraction, not a fork. Cross-reference the actual module/file names as durable anchors. IMPORTANT: per .claude/rules/no-task-references-in-deliverables.md, the docs/ deliverable MUST NOT cite task numbers (522/523/etc.) — reference module names, file paths, and lemma names instead. Source material: the design invariants and phase structure in specs/523's plans/02 and reports/01, and the landed code in SchemaUnion.lean / SchemaSoundness.lean / FrameCorrespondence.lean once task 523 completes.

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

### 533. Discharge the 3 sorries in the intuitionistic modal truth lemma
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: COMPLETENESS GAP. Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean carries 3 active sorries that leave IK/IT/IS4/IS5 completeness (ivalid_completeness/mvalid_completeness in Intuitionistic/Completeness.lean) resting on unproven obligations. Discharge them so the intuitionistic modal grid is fully sorry-free, matching the classical cube. Verify against the birelational semantics (Modal/Semantics/Birelational.lean) and the shared CanonicalModel/PrimeTheory infrastructure. Zero sorry, zero new axioms.

---

### 532. Reconcile stale [BLOCKED] docstrings left by completed decidability tasks
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 503, Task 504, Task 515
- **Research**: [532_reconcile_stale_blocked_docstrings_generic_driver/reports/01_stale-blocked-docstring-sweep.md]
- **Plan**: [532_reconcile_stale_blocked_docstrings_generic_driver/reports/01_stale-blocked-docstring-sweep.md]
- **Summary**: [532_reconcile_stale_blocked_docstrings_generic_driver/summaries/01_reconcile-stale-blocked-docstrings-summary.md]

**Description**: CLEANUP. Now that the generic tableau driver and T/S5/5/Euclidean decidability are delivered, several docstrings still narrate them as blocked. Sweep and correct: Cslib/Logics/Modal/Tableau/GenericDriver.lean (~lines 131/149 still say Phase-6 Decidable tValid is blocked, though instDecidableTValid is live), plus any residual [BLOCKED]/pending narratives in Saturation.lean / FrameCompleteness.lean / CompletenessLoop.lean referencing the now-landed T/S5/Euclidean instances. Use durable anchors (declaration names, file/section references), never task-number citations, per the no-task-references rule. Docstring-only; no proof changes.

---

### 531. Merge the KB5 prime/double-prime tableau rule variants into one rule
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 529
- **Research**: [531_merge_kb5_prime_and_doubleprime_rule_variants/reports/01_kb5-prime-doubleprime-merge-research.md]
- **Plan**: [531_merge_kb5_prime_and_doubleprime_rule_variants/plans/01_retire-kb5-prime-family.md]
- **Summary**: [531_merge_kb5_prime_and_doubleprime_rule_variants/summaries/01_retire-kb5-prime-family-summary.md]

**Description**: REDUNDANCY CLEANUP. Cslib/Logics/Modal/Tableau/ carries two complementary but overlapping KB5 rule families: modalApplyOneKb5 prime (FiveSimplification.lean, ~200 refs, repairs the shallow root-only gap) and modalApplyOneKb5 double-prime (~377 refs, corrected-gate full-cluster rule handling the deeper edge-target case), each with a Prop sibling and duplicated root/non-root split lemma pairs. Both are currently load-bearing (referenced by live soundness/completeness theorems). Merge them into a single rule with one set of split lemmas - a genuine proof-merge (NOT a delete of the prime variant), retiring the redundant lemma pairs once the merged rule discharges every downstream obligation. Must stay sorry-free and axiom-clean; verify instDecidableKb5Valid/modalTableauKb5-complete still hold after the merge.

---

### 530. Consolidate the duplicated Chronicle construction across Bimodal and Temporal
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: None
- **Research**: [530_consolidate_chronicle_construction_bimodal_temporal/reports/01_chronicle-dedup-research.md]
- **Plan**: [530_consolidate_chronicle_construction_bimodal_temporal/plans/01_chronicle-consolidation.md]

**Description**: REDUNDANCY CLEANUP. Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ and Cslib/Logics/Temporal/Metalogic/Chronicle/ are two nearly-identical full trees sharing 8 filenames (ChronicleConstruction, ChronicleToCountermodel, ChronicleTypes, CounterexampleElimination, PointInsertion, RRelation, ...) with ~89% overlap. The partial task-454 consolidation already lifted PointInsertion; extend that: factor the shared chronicle/countermodel-elimination machinery into a label-generic module under Cslib/Foundations/Logic/Metalogic/Chronicle/ (which currently holds only SinceSeedConsistency.lean) and have both the bimodal and temporal trees instantiate it. Preserve all landed sorry-free results; this is a structural dedup, not a proof change. Watch the bimodal discrete-completeness sorries (blocked on external port) - do not entangle them.

---

### 529. Fix lake lint unusedArguments failures in FiveSimplification.lean (KB5 corrected-gate rule)
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: None
- **Research**: [529_fix_lint_unused_args_kb5_univ_rules/reports/01_nolint-kb5-univ-rules.md]
- **Summary**: [529_fix_lint_unused_args_kb5_univ_rules/reports/01_nolint-kb5-univ-rules.md]

**Description**: Add @[nolint unusedArguments] to modalKb5BoxAllUniv (Cslib/Logics/Modal/Tableau/FiveSimplification.lean:2172) and modalKb5DiaNegAllUniv (:2194), whose 5th argument _w : WorldIndex is genuinely and intentionally unused (the corrected-gate KB5 rule fires unconditionally on cluster-nonemptiness regardless of trigger world, by design, dropping the w == 0 conjunct the frozen modalKb5BoxAllFull/modalKb5DiaNegAllFull used it for). The underscore prefix does not suppress CSLib's unusedArguments environment linter, so lake lint currently fails with exactly these 2 errors. Precedent for the nolint pattern: Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean:204, Cslib/Logics/Temporal/Metalogic/DenseMCS.lean:202. Verify with: lake lint (must pass clean on these files). This is the sole CI failure attributable to the corrected-gate KB5 tableau rule work.

---

### 528. Correctedgate kb5 tableau rule soundness and completeness
- **Effort**: 10-14 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [525_kb5_completeness_and_decidability/reports/02_spawn-analysis.md]
- **Plan**: [528_correctedgate_kb5_tableau_rule_soundness_and_completeness/plans/01_corrected-gate-kb5-rule.md]

**Description**: Task 525 (KB5 tableau completeness + kb5Valid decidability) is blocked because its Phase 3 truth lemma `modalTruthLemmaKb5` is mathematically FALSE for task 524's frozen `modalApplyOneKb5'` rule. This was proven in-repo as `extractModelKb5_nonRoot_boxPos_gap` (Cslib/Logics/Modal/Tableau/FrameCompleteness.lean) with a concrete witness (phi0 = NOT(DIAMOND(DIAMOND(BOX p))): open branch with acc.edges = [(1,2),(0,1)], T(BOX p)@2 in branch, T(p)@0 NOT in branch, yet the extracted relation .r 2 0 holds -- a genuine countermodel-side failure). This has been architecturally pinned to ONE misplaced boolean gate (see specs/525_kb5_completeness_and_decidability/reports/02_s5-architecture-investigation.md, the authoritative root-cause report for this task -- read it in full before starting).

ROOT CAUSE: `modalKb5BoxAllFull`'s world-0-target arm (Cslib/Logics/Modal/Tableau/FiveSimplification.lean:1544, dually the diamond-negative arm at :1561) is gated on `w == 0 && clusterNonempty`. The CORRECT gate is `clusterNonempty` alone -- drop the trigger-identity conjunct (`w == 0`) so a non-root trigger also dumps its box-positive content onto world 0 when the cluster is connected to the root. The mint arms (T(DIAMOND phi)/F(BOX phi)) stay UNTOUCHED -- task 524 already established (FiveSimplification.lean:1517-1522, and the R7 refutation at S5Simplification.lean:1944-2035, machine-checked) that existential shapes must keep witness-reuse mints or termination diverges; only the universal-shape gate changes.

DO NOT modify `modalApplyOneKb5'`, its `RuleApplicationSpecCore` instance, its termination bound (`Kb5'WorldInv`), or `modalTableauKb5'_sound` -- these are a FROZEN, landed, sound task-524 deliverable. Instead, CLONE `modalApplyOneKb5'`/`modalKb5BoxAllFull`/`modalKb5DiaNegAllFull` into a new rule (naming per repo convention, e.g. `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv` and a dispatcher such as `modalApplyOneKb5''`) with the corrected gate. The new rule sits BESIDE the frozen one, exactly as `modalApplyOneKb5'` already sits beside the `modalApplyOneKb5 := modalApplyOneFive` alias.

EXTRACTION: `extractModelKb5 := extractModelWith (fun r => Relation.EuclGen (Relation.SymmGen r))` (FrameCompleteness.lean:3230-3270) is ALREADY the total/universal cluster on the branch's connected edge-touched world set -- the least PER (symmetric right-Euclidean relation) over a connected symmetric graph is total on its field. NO re-extraction and NO new cluster-membership bookkeeping device is needed: cluster membership for KB5 IS known-world-ness, already certified by the landed `accReachableInv` invariant (Cslib/Logics/Modal/Tableau/FrameSoundness.lean) and already consumed by task 524's soundness proof. Handoff fix (ii) -- keep the trigger-gated rule, change the extraction instead -- is a PROVEN DEAD END per the scout-lemma remark at FrameCompleteness.lean:3507-3511 (any kb5FC-satisfying relation preserving raw edges forces `r w 0` for chain-connected non-root `w`, so no admissible extraction can rescue a root-trigger-gated rule). Do not pursue this alternative.

Deliver the following in ONE coherent implementation (internal phases as needed, but do not split into separate tasks -- see rationale below):

1. NEW RULE: A corrected-gate rule cloning `modalApplyOneKb5'`/`modalKb5BoxAllFull`/`modalKb5DiaNegAllFull`, with the 0-target arm's gate changed from `w == 0 && clusterNonempty` to `clusterNonempty` alone (mint arms unchanged). Include the fresh `RuleApplicationSpecCore` instance and re-derived termination bound (mechanical clone of `modalApplyOneKb5'_specCore`; output-shape bounds should be unchanged since the emitted set only grows by at most the single @0 formula already present in the root-trigger case task 524 handled). Fresh membership dichotomy: target known-non-root, OR target 0 with cluster nonempty (trigger no longer appears in the dichotomy).

2. SOUNDNESS: A kb5FC-direct soundness theorem mirroring `modalTableauKb5'_sound` (FrameSoundness.lean:4821). This is nearly free: task 524's trigger-agnostic lemma family already covers 3 of 4 (trigger,target) cases -- `reachable_imp_related_kb5` (FrameSoundness.lean:1582) for (w=0,v!=0); `accReachableInv_related_kb5` (FrameSoundness.lean:1610) for (w!=0,v!=0); `accReachableInv_kb5_root_refl` (FrameSoundness.lean:1633) for (w=0,v=0). The ONLY new case is (w!=0,v=0), discharged by symmetrizing `reachable_imp_related_kb5` -- a one-line application of `Std.Symm.symm` (or the repo's equivalent symmetry combinator), not new mathematics.

3. TRUTH LEMMA + COMPLETENESS + DECIDABILITY: `modalTruthLemmaKb5` (mirroring `modalTruthLemmaFive`, FrameCompleteness.lean:2693-2886, by strong induction on modalComplexity), then `modalOpenBranchKb5'_countermodel` (mirror at FrameCompleteness.lean:2886) and `modalTableauKb5'_complete` (mirror at FrameCompleteness.lean:3131-3198, wired through the new rule's entry point) and `kb5Valid_decides` plus `instance instDecidableKb5Valid (phi) : Decidable (kb5Valid phi)` (mirroring `fiveValid_decides`/`instDecidableFiveValid`, FrameCompleteness.lean:3203-3216). REUSE task 525's already-landed Phase 1 lemmas verbatim: `symmEuclGen_mem_modalKnownWorlds_iff`, `extractModelKb5_root_reach_mem_modalKnownWorlds` (both in FrameCompleteness.lean, in the KB5 extraction section after `extractModelKb5_hasEdge_imp_r` ~3270). Task 525's Phase 2 Hintikka lemmas (`modalKb5BoxAllFull_mem_of`, `modalKb5DiaNegAllFull_mem_of`, `hintikkaKb5'_box_pos`, `hintikkaKb5'_diamond_neg`) are pinned to the FROZEN rule's trigger-sensitive dichotomy and survive only as a documentation/pattern precedent -- they need MECHANICAL RE-DERIVATION against the new rule's simpler trigger-free dichotomy (this is expected to be near-copies, not fresh design). The root box-positive case (trigger w=0 reaching every cluster world including w'=0) is exactly what the new rule's full-cluster + root-reflexive emission is designed to discharge per the architecture report Section 2.3: given `.r w v` (closure), `symmEuclGen_mem_modalKnownWorlds_iff` puts v in the known set; if v!=0 the unconditional non-root arm covers it; if v=0, any closure derivation contains at least one raw edge whose target is known and non-root, giving the cluster-nonempty witness the corrected gate needs.

4. DOCS + CI: Reconcile stale blocker/scope framing in FrameCompleteness.lean (the '## Phase 3 Blocker (task 525)' note left by task 525's implementer, and the older '## 5 / KB5 (Euclidean) Coverage via the S5 Route' docstring at ~565), FiveSimplification.lean (the 'completeness is deferred to a follow-on task' note ~1424-1443), and S5Simplification.lean (the 'KB5's completeness specifically remains open' sentence in the '## Scope Note: Pure-K5 / Pure-5' block ~2037+) to state KB5 completeness as delivered via the new rule's completeness theorem. Per no-task-references-in-deliverables.md, use durable anchors (declaration names, section headings) in these .lean docstrings, NEVER ephemeral task numbers. Extend CslibTests/ModalFrameSeparation.lean to exercise `instDecidableKb5Valid` / `by decide` and update its docstring framing (currently states the instance 'is not yet landed'). Diagnose (do not silently absorb) the pre-existing `decide`-reduction kernel stall in `modalExpandBranchesGen`'s fuel recursion (S5Simplification.lean:1959-1963, affects ModalFrameSeparation.lean) -- this stall is ORTHOGONAL to this fix and pre-existing from an earlier task; determine whether landing the new decidability instance resolves, sidesteps, or must be explicitly documented as still-present, and track any remaining stall as a separate follow-on concern rather than folding a fix for it into this task. Run the full CSLib CI pipeline in order per cslib.md: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake --add-public --keep-implied --keep-prefix`. If `lake build` surfaces LoopChecking.lean errors NOT caused by this task's changes, report them as a concurrent condition (that file is owned by a separate, still-partial task) -- do NOT edit LoopChecking.lean.

HARD CONSTRAINTS (apply to every phase): zero sorry, zero new axiom declarations, every new public declaration `lean_verify`-clean (fully-qualified name check). If any proof phase genuinely cannot close, mark it [BLOCKED] in the plan with the exact reached `lean_goal` state and what is missing -- NEVER insert a `sorry`, `admit`, or vacuous placeholder (`:= True`/`trivial`) to force a green build. Do not modify `modalApplyOneKb5'`, its specCore instance, its termination bound, or `modalTableauKb5'_sound` (frozen task-524 deliverables, out of scope). Do not touch `extractModelS5` or the S5 completeness route (unaffected by this fix per the architecture report). Do not edit LoopChecking.lean.

Upon completion, task 525 should be revisited: its remaining Phases 3-7 are either fully absorbed by this new task's deliverables (in which case task 525 should be marked superseded/completed by reference to this task's landed declarations) or reduced to thin reconciliation -- determine which at task 525's resume time by diffing this task's landed declarations against task 525's Phase 3-7 goals in specs/525_kb5_completeness_and_decidability/plans/01_kb5-completeness-decidability.md.

---

### 527. Fix stuck decide in ModalFrameSeparation.lean regression test
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Testing
- **Dependencies**: None

**Description**: lake test fails on CslibTests/ModalFrameSeparation.lean: the `decide`-based regression checks for the S5-vs-5 frame-class separation (`example : decide (s5Valid ...) = true := by decide` and `example : decide (fiveValid ...) = false := by decide`) get stuck / fail to reduce against `instDecidableS5Valid` / `instDecidableFiveValid`. This is a live regression (the file builds these countermodel checks via the tableau's Decidable instances rather than the semantic proofs). Diagnose why the `decide` kernel reduction no longer terminates/succeeds on the S5 and Five decidability instances: check whether a recent change to the modal tableau / validity Decidable instances (this area is under active work in the KB5 metalogic tasks) altered the reduction behaviour or made the instance non-computable. Fix so `lake test` passes on this file again — either by repairing the Decidable instance's computability or, if `decide` is genuinely no longer viable, by replacing the stuck `decide` checks with the proven separation theorems (mirroring the existing `kb5Valid` case at line 42, which already uses `boxImp_not_kb5Valid` from FrameSoundness.lean instead of `decide`). Verify with `lake build` + `lake test` (ModalFrameSeparation green). Surfaced during vet of task 502 as a pre-existing, out-of-scope issue; verified unrelated to the Segment.lean import change via git-stash reproduction.

---

### 526. Fix unusedArguments lint error in PrimeExclusion.lean
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: lake lint (batteries/runLinter) reports one `unusedArguments` linter error in Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean. Locate the flagged declaration (a hypothesis/argument bound in a def or theorem signature that is never used in the body and is not underscore-prefixed), and resolve it per CONTRIBUTING.md conventions: either prefix the unused binder with `_` (preferred when the argument is structurally required for the signature, e.g. an abstract `DerivationSystem`/typeclass parameter kept for uniformity with sibling lemmas) or remove it if genuinely dead. Do NOT alter the public API surface of `prime_exclusion`/`prime_set_exclusion` or their downstream instantiations in MinLindenbaum.lean/IntLindenbaum.lean without confirming callers still compile. Single-file change. Re-verify with `lake build` + `lake lint` (expect the PrimeExclusion unusedArguments error gone, no new warnings). Surfaced during vet of task 502 as a pre-existing, out-of-scope issue.

---

### 525. Kb5 completeness and decidability
- **Effort**: 5-8 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 524, Task 528
- **Research**: [515_s5_universal_rule_termination_unblock_504/reports/02_spawn-analysis.md]
- **Plan**: [525_kb5_completeness_and_decidability/plans/01_kb5-completeness-decidability.md]

**Description**: Completes task 515's re-scoped Phase 23 deliverable, resuming after the KB5-specific propagation rule and its soundness proof (New Task 1 / the task this depends on) are landed. Land `theorem modalTableauKb5_complete (phi) (h : kb5Valid phi) : modalTableauKb5 phi = .closed` (or the tableau-entry-point-equivalent name matching whatever New Task 1's new rule is wired through) in Cslib/Logics/Modal/Tableau/FrameCompleteness.lean, via extractModelKb5 (already landed sorry-free, FrameCompleteness.lean:3230-3270) plus the Phase 12 lift pattern used by modalTableauFive_complete. Build (or extend) the Euclidean-symmetric truth lemma's root box-positive case using New Task 1's rule: T(box psi)@0 in b must imply T(psi)@w' for every w' with (extractModelKb5 b acc).r 0 w', discharged via the full-cluster-dump plus root-reflexive-propagation guarantees New Task 1 proved sound against kb5FC. Land `instance instDecidableKb5Valid (phi) : Decidable (kb5Valid phi)`, mirroring instDecidableFiveValid's two-direction (soundness/completeness) decidability construction. Remove or update the 'Phase 23 Blocker' /-! -/ note (FrameCompleteness.lean:3300-3339) and reconcile the SCOUT section framing (FrameCompleteness.lean:3272-3299) to reflect the delivered state (the scout lemma extractModelKb5_root_reach_scout should stay as documentation of the design constraint the new rule satisfies, not read as an open blocker). Reconcile the '5/KB5 Coverage via the S5 Route' docstring in FrameCompleteness.lean and the 'Scope Note: Pure-K5 / Pure-5' block in Cslib/Logics/Modal/Tableau/S5Simplification.lean (both located by content, not stale line numbers) to state KB5 completeness as delivered. Extend CslibTests/ModalFrameSeparation.lean's kb5Valid regression coverage to use instDecidableKb5Valid / by decide now that the instance exists, replacing the current term-proof-only (boxImp_not_kb5Valid) check where appropriate. Run the full CSLib CI pipeline (lake build, checkInitImports, lake lint, lint-style, lake test, shake) to completion -- this was the one item Phase 23 left pending purely due to the concurrent LoopChecking.lean interruption from an unrelated task (511); by the time this task runs that file should be resolved, so this should require no further code changes, just verification. Constraint: zero sorry, zero new axiom declarations; every new public declaration lean_verify-clean.

---

### 524. Kb5 full cluster rule and soundness
- **Effort**: 6-10 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [515_s5_universal_rule_termination_unblock_504/reports/02_spawn-analysis.md]
- **Plan**: [524_kb5_full_cluster_rule_and_soundness/plans/01_kb5-full-cluster-rule-soundness.md]
- **Summary**: [524_kb5_full_cluster_rule_and_soundness/summaries/01_kb5-full-cluster-rule-soundness-summary.md]

**Description**: Task 515's Phase 22 landed `modalApplyOneKb5 := modalApplyOneFive` as a literal alias (Cslib/Logics/Modal/Tableau/FiveSimplification.lean:1436), sound for KB5 only because 'factor, not clone' lets a Five-sound rule transfer to the strictly-stronger kb5FC frame class. That alias only propagates content at DIRECT `acc.hasEdge` successors of the root -- by design, since Five's own soundness needs exactly that restriction (Five's root is not reflexive). But `extractModelKb5`'s relation (Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:3230) is forced to be `Relation.EuclGen (Relation.SymmGen acc.hasEdge)`, the least kb5FC-satisfying relation preserving every raw edge -- and this relation relates the root to INDIRECT chain targets too (a raw chain `0 -> a -> c` where non-root `a` mints a fresh witness `c` gives `(extractModelKb5 b acc).r 0 c`). This is proved by the already-landed, sorry-free, zero-axiom witness lemma `extractModelKb5_root_reach_scout` (FrameCompleteness.lean:3294), and confirmed algebraically to hold for ANY kb5FC-satisfying relation preserving raw edges -- not an artifact of this specific closure operator. Deliver a genuinely NEW KB5-specific tableau rule (a plausible name is `modalApplyOneKb5'`, landed either in FiveSimplification.lean's KB5 section or a new Kb5Simplification.lean -- implementer's choice) whose root box/diamond trigger propagates to the FULL known non-root cluster (matching the non-root propagation arm's own unconditional behavior), and which ALSO propagates the root's own box content back onto world 0 itself, justified by the already-landed `Relation.symm_rightEuclidean_root_refl` (Cslib/Foundations/Relation/Euclidean.lean:362: a rooted symmetric+right-Euclidean frame makes the root reflexive whenever it has a successor). Re-derive the termination bound for the new rule (Phase 19a's bound does not transfer for free since the new rule is no longer definitionally modalApplyOneFive). Land the RuleApplicationSpecCore instance for the new rule (mirroring modalApplyOneFive_specCore's nine-field discharge, FiveSimplification.lean:1389-1441). Land a NEW soundness theorem in Cslib/Logics/Modal/Tableau/FrameSoundness.lean, proved DIRECTLY against kb5FC (the frame-class-monotonicity shortcut Phase 22 used is NOT available here -- the new rule's unrestricted root propagation would be unsound for the strictly larger fiveFC class, per the Phase 23 blocker note at FrameCompleteness.lean:3300-3339). Reuse without re-deriving: extractModelKb5 and its extraction lemmas (extractModelKb5_r/_rightEuclidean/_symm/_hasEdge_imp_r, FrameCompleteness.lean:3230-3270), extractModelKb5_root_reach_scout (FrameCompleteness.lean:3294, the counterexample characterizing exactly what the new rule must handle), EuclGen.symm_of_symm + its Std.Symm (EuclGen r) instance and Relation.EuclGen/Relation.SymmGen (Cslib/Foundations/Relation/Euclidean.lean), Relation.symm_rightEuclidean_root_refl (Euclidean.lean:362), and the entire green S5/Five rule-design pattern in FiveSimplification.lean (mint-arm guards, witness reuse, source-split termination tagging) as structural template. Constraint: zero sorry, zero new axiom declarations anywhere; every new public declaration must be lean_verify-clean (only the standard [propext, Classical.choice, Quot.sound] subset). Do not introduce a vacuous placeholder (def X := True / theorem X := trivial) if a step cannot be completed -- mark [BLOCKED] instead per plan-compliance.md and lean4.md. Do not touch Cslib/Logics/Modal/Tableau/LoopChecking.lean unless it is already resolved by task 511's concurrent session by the time this task runs (check first).

---

### 523. Schema union axiom combinator for proofsystem instances
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [523_schema_union_axiom_combinator_for_proofsystem_instances/reports/01_schema-union-combinator-blast-radius.md]
- **Plan**: [523_schema_union_axiom_combinator_for_proofsystem_instances/plans/01_schema-union-staged-rollout.md]

**Description**: Schema-union axiom combinator to replace the hand-written per-system axiom inductives in Cslib/Logics/Modal/ProofSystem/Instances/*.lean. RECONCILED COUNT: there are 14 such inductives ({K,T,B,D,S4,K4,K5,K45,D4,D5,D45,DB,TB,KB5}Axiom), not 15 - S5.lean already reuses Modal.ModalAxiom directly and is the exact pattern the combinator should generalize to. Build a SchemaUnion/axiom-combinator so each system is expressed as a union of shared axiom schemas rather than a bespoke re-listing inductive. Gated on a Zulip design decision (representation A: closed inductive of schema tags, vs B: Set/predicate union). DESIGN DECISION (resolved, user 2026-07-18): Representation = A (schema-tag union). Build ModalSchemaTag inductive + ModalSchemaTag.Holds + SchemaUnion (S : Finset ModalSchemaTag) := fun χ => ∃ t ∈ S, t.Holds χ; each system = one-line SchemaUnion over its tag set. Collapse the 24 XAxiom_implies_YAxiom subsumption lemmas to one generic lemma + Finset.subset facts; soundness = per-tag validity table + one unionSound combinator. Accept the elimination-form change downstream (cases|ctor → obtain ⟨t,ht,hφ⟩; fin_cases t) and the ~36 genuine hand-rewrites in InterSystem/IntToClassical.lean. Keep intuitionistic/minimal families (IK/MK/CK/IS5/MT ModalAxiom) OUT of scope. Stage additively, each stage CI-green/zero-debt; Zulip heads-up before the PR lands (large shared-subtree blast radius).

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

### 521. Dedup minimal canonical model onto generic extension
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [521_dedup_minimal_canonical_model_onto_generic_extension/reports/01_dedup-minimal-canonical-model.md]
- **Plan**: [521_dedup_minimal_canonical_model_onto_generic_extension/plans/01_dedup-minimal-canonical-model.md]

**Description**: Consolidate the duplicated minimal-base canonical model. Cslib/Logics/Modal/Metalogic/Minimal/{MinCanonicalModel,MinTruthLemma,MinCompleteness}.lean are the older MK-only bespoke copies; MinExtension.lean is the Axioms-generic frame-condition-parametric version that MT/MS4/MS5 already instantiate (mkvalidFC_completeness). MK's own completeness (mk_completeness, MinCompleteness.lean:55) still runs through the old trio. Refactor mk_completeness/mk_soundness_completeness to instantiate mkvalidFC_completeness at MKModalAxiom + the trivial frame condition, then delete the bespoke MinCanonicalModel/MinTruthLemma/MinCompleteness trio (~1500 duplicated lines). The duplication is self-documented at MinExtension.lean:23-37. Preserve all public theorem names MK consumers rely on. Verify zero sorry, full CI, zero regression across the minimal base. Parallel-safe with task 515.

---

### 520. Composite conservativity bridges to classical column
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [520_composite_conservativity_bridges_to_classical_column/reports/01_composite-conservativity-bridges.md]
- **Plan**: [520_composite_conservativity_bridges_to_classical_column/plans/01_composite-conservativity-bridges.md]

**Description**: Add the missing composite conservativity bridges collapsing each non-classical base into the classical column, in Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean. Currently IntToClassical.lean provides IK->K/IT->T/IS4->S4/IS5->S5 and Axis-B provides MK->IK/CK->IK etc., but the one-line composites mkDerivable_implies_kDerivable, mtDerivable_implies_tDerivable, ms4Derivable_implies_s4Derivable, ms5Derivable_implies_s5Derivable, and the constructive analogues ckDerivable_implies_kDerivable etc. do NOT exist (confirmed by grep). Modularity.lean currently chains only into the intuitionistic IS5 corner. Compose the existing Axis-B (base->intuitionistic) and IntToClassical (intuitionistic->classical) edges to complete the 'every base collapses into classical' modularity story. Low effort, high elegance value. Parallel-safe with task 515 (separate file). Verify zero sorry, axioms [propext, Classical.choice, Quot.sound] only, full CI.

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

### 517. Labelled bounded context cs5 completeness
- **Effort**: 40-70 hours
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [517_labelled_bounded_context_cs5_completeness/reports/07_team-research.md]
- **Summary**: [517_labelled_bounded_context_cs5_completeness/summaries/18_phase8-canonical-model-truth-lemma-summary.md]
- **Plan**: [517_labelled_bounded_context_cs5_completeness/plans/13_labelled-completeness-full-soundness.md]

**Description**: ROUTE B (user-funded, full build): Build a LABELLED / bounded-context canonical model framework for CSLib constructive modal logic and prove CS5 (== IS5) constructive Kripke COMPLETENESS over it -- the only faithful path remaining. WHY THIS EXISTS (exhaustively established, mechanized + literature-grounded across tasks 509/512/516): every route that keeps CSLib's PRIME-THEORY canonical model is dead for ONE root reason -- prime non-maximal theories lack negation-completeness, so the symmetric back-clause is jointly unsatisfiable with refuting the box subject. Mechanized guardrail set (all sorry-free/axiom-clean): cs5_symmetric_tail_box_gap (CS5.lean:712, task 509 -- THE wall), cs5Incest_forces_symm (CS5Canonical.lean:643, axiom-free -- any <=-mediated condition collapses to plain symmetry since ckforces_persistence + cval force head-monotonicity under ANY <=), cs5TwoSidedR_iff_cs5Tail (CS5Canonical.lean:511 -- Simpson two-sided R == the old cs5Tail wall over CS5 quasi-prime theories), plus task-512's atom-sum results. Dead: atom-sum doubled-atom (512), one-sided-R (512 ph5), two-sided-R (512 ph7), independent-<= (516 report 01 -- refuted: Simpson uses <= = subset VERBATIM, Section 3.3), Simpson-faithful prime-theory Route A (516 report 02, ~95% -- Simpson NEVER does symmetric box-backward in prime-theory form; his Section 3.3 prime model is an 'outline' deferring IS5 symmetry to Fischer Servi). CS5 IS complete (CS5 == IS5, CS5.lean:93-99) -- the block is representational, NOT incompleteness. THE METHOD (Simpson 1994 Ch 7-8, the rigorous IS5 proof he actually carries out; extended by Marin-Morales-Strassburger 2021's labelled line): abandon prime theories for LABELLED 'T-prime bounded contexts'. Key targets: T-Comp graph completion (Simpson Lemma 8.2.5) for symmetry; the bounded canonical model lemma over labelled membership y:B in A (Lemma 8.2.6) for box-backward; a BOUNDED prime lemma; then the truth lemma and cs5_completeness. NOTE (important, settled by 516 report 02): the classical decidability-of-derivability step in Simpson's box-backward is NOT a blocker -- Lean has Classical.em; the prime-theory structural gap was the blocker, and labelled bounded contexts sidestep it. SCOPE: ~1500-2500 lines, ~ZERO reuse of the existing prime-theory canonical machinery (CKSegment/Segment/SegmentLindenbaum do not transfer) -- this is a NEW framework. Reuse what genuinely transfers: Proposition/Proposition.map (Basic.lean), the DerivationTree/Derivable infrastructure, the CS5ModalAxiom set, and task-512's landed CS5 soundness (cs5_axiom_sound_incest / cs5_soundness_incest, axiom-free) where the frame class matches. Any design MUST explain why it does not trip the four guardrail lemmas (labelled contexts are not prime theories, so cs5_symmetric_tail_box_gap should not apply -- state why explicitly). CONSTRAINTS: NO sorry, NO new axiom under Cslib/; zero-debt at every phase boundary; do NOT regress landed CK/CT/CS4/CS5 soundness or task-509 cs5FC''; build alongside. BibKeys: Simpson1994 (Ch 7-8), MarinMoralesStrassburger2021, Dosen1985, BozicDosen1984, AlechinaMendlerdePaivaRitter2001, Wijesekera1990, Pacheco2024 (all in references.bib). Research MUST use --lit (mine Simpson Ch 7-8 chunks: Lemmas 8.2.5, 8.2.6, the bounded prime lemma). HIGH effort, HIGH uncertainty. Depends on 509, 512, 516.

---

### 515. S5 universal rule termination unblock 504
- **Effort**: 8-12 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 525
- **Research**:
  - [515_s5_universal_rule_termination_unblock_504/reports/01_s5-termination-implementation-blueprint.md]
  - [515_s5_universal_rule_termination_unblock_504/reports/03_s5-infrastructure-deep-research.md]
  - [515_s5_universal_rule_termination_unblock_504/reports/06_k-aux-unprovability-audit.md]
- **Plan**: [515_s5_universal_rule_termination_unblock_504/plans/05_s5-termination-machinery.md]
- **Summary**: [515_s5_universal_rule_termination_unblock_504/summaries/16_phase21-hintikka-wall-landed-completed.md]

**Description**: PARENT TRACKER (S5 mandate DELIVERED). The terminating S5 tableau machinery, S5 soundness/completeness, S5 decidability, and the full Euclidean-5 route are all landed sorry-free and CI-green (headline commit af593180): modalTableauS5_sound (FrameSoundness.lean:2991), modalTableauS5_complete (FrameCompleteness.lean:2340), s5Valid_decides/instDecidableS5Valid (FrameCompleteness.lean:2411/2422), fiveValid_decides/instDecidableFiveValid (FrameCompleteness.lean:3203/3213). The rank obstruction was engineered around via a witness-reuse mint rule. The SOLE remaining deliverable is KB5 completeness + Decidable kb5Valid, delegated to child task 525: task 524's KB5 rule was mechanically proven insufficient (extractModelKb5_nonRoot_boxPos_gap, FrameCompleteness.lean:3544, sorry-free), so KB5 needs a NEW rule + extraction design (achievable per Blackburn-de Rijke-Venema 4.8-4.9), not a re-run. Deps corrected: dropped stale 514 (archived, research-only) and insufficient 524; real gate is 525. Do NOT re-attempt against task 524's frozen modalApplyOneKb5' rule -- its truth lemma is a machine-checked falsehood. Off-roadmap; no roadmap claims.

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

### 504. S5 and kb55route euclidean decidability via generic tableau 
- **Effort**: 5-7 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 515
- **Plan**: [504_s5_and_kb55route_euclidean_decidability_via_generic_tableau_/plans/01_s5-kb5-euclidean-decidability.md]
- **Research**:
  - [504_s5_and_kb55route_euclidean_decidability_via_generic_tableau_/reports/01_frame-specific-tableau-extensions.md]
  - [504_s5_and_kb55route_euclidean_decidability_via_generic_tableau_/reports/02_spawn-analysis.md]
  - [504_s5_and_kb55route_euclidean_decidability_via_generic_tableau_/reports/03_parent-phase-plan-reference.md]
- **Summary**: [504_s5_and_kb55route_euclidean_decidability_via_generic_tableau_/summaries/01_s5-kb5-euclidean-decidability-summary.md]

**Description**: Deliver plan Phases 3 and 7 of task 300 (specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md): S5 universal-cluster simplification (no loop-checking needed) and 5/Euclidean coverage via the KB5/S5 equivalence route. Implement the 'propagate box to ALL branch worlds' universal rule in a new Cslib/Logics/Modal/Tableau/S5Simplification.lean; extract the countermodel via Relation.EqvGen (Std.Refl+IsTrans+IsSymm/IsEquiv free). Discharge the structural hypotheses interface fixed by the generic driver delivered in the prerequisite task (world creation confined to the unmodified K diamondPos/boxNeg arms; each diamond mints at most once per formula). Prove the truth lemma over the universal relation; state s5Valid / Decidable (s5Valid phi) against Cube.S5. Additionally expose the Euclidean frame condition (Relation.RightEuclidean) for the equivalence-extracted model (every equivalence relation is Euclidean) and state 5/KB5 validity + completeness via Satisfies.five (Basic.lean) and Cslib/Foundations/Relation/Euclidean.lean's API (RightEuclidean.symm, refl_serial). Document in-file that genuine pure-K5 (Euclidean without full equivalence; no Mathlib closure operator) remains out of scope, per the parent plan's non-goals. Files: Cslib/Logics/Modal/Tableau/S5Simplification.lean (new), Cslib/Logics/Modal/Tableau/FrameSoundness.lean, Cslib/Logics/Modal/Tableau/FrameCompleteness.lean.

---

### 503. Generalize k tableau driver and complete tsystem decidabilit
- **Effort**: 10-14 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/reports/01_frame-specific-tableau-extensions.md]
  - [503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/reports/02_spawn-analysis.md]
  - [503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/reports/03_parent-phase-plan-reference.md]
  - [503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/handoffs/phase2-blocked-handoff.md]
- **Plan**: [503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/plans/01_generalize-tableau-driver-tsystem.md]
- **Summary**: [503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/summaries/01_generalize-tableau-driver-tsystem-summary.md]

**Description**: Parametrize the K tableau driver (Cslib/Logics/Modal/Tableau/Saturation.lean's modalStepBranch/modalExpandBranches/modalTableau and Cslib/Logics/Modal/Tableau/FmpMeasure.lean's termination measure, currently hard-coding modalApplyOne at 91 call sites across Saturation.lean/FmpMeasure.lean/CompletenessLoop.lean) over an abstract rule-application function matching modalApplyOne's signature, together with a small set of explicit structural hypotheses (no world creation outside the unmodified K diamondPos/boxNeg arms; all added formulas drawn from the finite modalUniverse phi0 catalog). Re-derive K itself as the trivial instantiation (must stay green, zero regression, zero sorry/axiom). Then instantiate the generic driver with the already-proved modalApplyOneT (Cslib/Logics/Modal/Tableau/FrameRules.lean) to build modalStepBranchT/modalExpandBranchesT/modalTableauT, discharge the T-specific structural hypotheses, close the T truth-lemma box-positive case (reflexive self-edge; reuse modalApplyOneT_eq_of_not_boxPos_diaNeg to reduce other cases to existing K bridge lemmas per specs/300_modal_extensions_t_s4_s5/handoffs/phase2-blocked-handoff.md), and state tValid's completeness + Decidable (tValid phi). This completes Phase 2 of the original task 300 plan (specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md). Build on the already-committed, green rule-level work in FrameRules.lean/FrameSoundness.lean/FrameCompleteness.lean (do not re-derive it). Every delivered result must be genuinely sorry-free/axiom-free; if the T truth-lemma or termination re-derivation cannot close, mark [BLOCKED] with a documented open goal state rather than introduce debt. Files: Cslib/Logics/Modal/Tableau/Saturation.lean, Cslib/Logics/Modal/Tableau/FmpMeasure.lean, Cslib/Logics/Modal/Tableau/CompletenessLoop.lean, Cslib/Logics/Modal/Tableau/FrameCompleteness.lean, Cslib/Logics/Modal/Tableau/FrameSoundness.lean.

---

### 502. Minimize Segment.lean imports per lake shake recommendation
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Research**: [502_fix_segment_import_minimization/reports/01_segment-import-minimization.md]
- **Plan**: [502_fix_segment_import_minimization/plans/02_segment-import-minimization.md]

**Description**: lake shake flags Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean: replace the transitive `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` with direct imports of `Cslib.Logics.Modal.Metalogic.DerivationTree` and `Cslib.Foundations.Logic.Metalogic.PrimeExclusion` (the two modules whose declarations Segment.lean actually consumes). Do NOT remove the plain `import Cslib.Init` line (shake's suggestion there is the systemic out-of-scope pattern and would violate CONTRIBUTING.md's Cslib.Init mandate). Single-file, single-import-line change; re-verify with lake build + lake shake --add-public --keep-implied --keep-prefix. From vet of task 493.

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
