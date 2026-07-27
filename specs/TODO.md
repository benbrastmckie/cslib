---
next_project_number: 572
---

# TODO

## Task Order

*Updated 2026-07-27. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,226,317,409,425,440,465,466,530,534,554,557,558,562,563,569,570 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,375,400,430,450,456,497,511,537,551,553,564,568,571 | 36,37,181,317,425,465,530,554,562,563 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41,413,506,548,565,566 | 39,40,375,511,564 | foundations, modal logic, code hygiene |
| 4 | 300,567 | 506,558,565,566 | modal logic |
| 5 | 414 | 181,215,300,301 | code hygiene |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
317 [IMPLEMENTING] — Fill the remaining propositional/intuitionistic tableau completen
  └─ 375 [NOT STARTED] — Fold the TABLEAU decision systems into the propositional proof-sy
  └─ 430 [PLANNED] — Prove the atom-persistence / upward-closure structural lemma for 
409 [RESEARCHED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
400 [BLOCKED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
497 [NOT STARTED] — Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (P

### Modal Logic

534 [NOT STARTED] — COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree 
554 [RESEARCHED] — [RESCOPED 2026-07-26 by explicit user decision, adopting report 0
  └─ 537 [BLOCKED] — Prove the general labelled SOUNDNESS direction nik_TS5_soundness 
  └─ 551 [BLOCKED] — Deliver NATIVE Hilbert canonical-model completeness for construct
557 [BLOCKED] — Refactor and restructure the modal Tableau subsystem to library-p
558 [NOT STARTED] — [Task A of the modal-tableau refactor programme; P0, highest valu
  └─ 567 [NOT STARTED] — [Task I of the modal-tableau refactor programme; P4, final accept
562 [NOT STARTED] — [Task D of the modal-tableau refactor programme; P2. Gated on the
  └─ 564 [NOT STARTED] — [Task F of the modal-tableau refactor programme; P3.] Migrate the
    └─ 565 [NOT STARTED] — [Task G of the modal-tableau refactor programme; P3. Depends on t
      └─ 567 [NOT STARTED] — [Task I of the modal-tableau refactor programme; P4, final accept (see above)
    └─ 566 [NOT STARTED] — [Task H of the modal-tableau refactor programme; P3.] Create Bone
      └─ 567 [NOT STARTED] — [Task I of the modal-tableau refactor programme; P4, final accept (see above)
563 [NOT STARTED] — [Task E of the modal-tableau refactor programme; P2. Gated on the
  └─ 511 [BLOCKED] — Follow-on to task 506 (S4 loop-checking): close the S4 terminatio
    └─ 506 [BLOCKED] — Deliver plan Phases 5 and 6 of task 300 combined (specs/300_modal
      └─ 300 [BLOCKED] — Umbrella task for modal frame extensions T/S4/S5 (and the derived
    └─ 548 [NOT STARTED] — COMPLETENESS-MATRIX GAP (review 2026-07-23, M3). Tableau decidabi
  └─ 553 [PLANNED] — Determine whether the S4 keyed loop-check guard can be made sound
  └─ 564 [NOT STARTED] — [Task F of the modal-tableau refactor programme; P3.] Migrate the (see above)

### Temporal Logic

425 [NOT STARTED] — [Decomposed from the temporal tableau umbrella, blocker C.] BLOCK
  └─ 301 [BLOCKED] — Implement tableau decision procedure for temporal logic (Cslib.Lo
569 [NOT STARTED] — [Created by the blocked-task review to break a two-task deadlock.
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Bimodal Logic

36 [NOT STARTED] — Port discrete completeness (completeness_discrete) from upstream 
  └─ 215 [BLOCKED] — Fill the discrete-gated sorry declarations in Cslib/Logics/Bimoda
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 571 [BLOCKED] — [Carved off the bimodal sorry task by the blocked-task review. Ho
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 
  └─ 450 [NOT STARTED] — Core corrected conservativity result. PR-BLOCKING for task 180. S

### Code Hygiene

530 [PLANNED] — REDUNDANCY CLEANUP. Cslib/Logics/Bimodal/Metalogic/BXCanonical/Ch
413 [NOT STARTED] — Simplify verbose Propositional/ proofs (manual simp only [listImp
414 [NOT STARTED] — Simplify verbose Modal/, Temporal/, and Bimodal/ proofs (manual s

### Pr & Upstreaming

440 [PR READY] — PR review: GitHub PR https://github.com/leanprover/cslib/pull/648
465 [PR READY] — Review PR #607 (logical operators): post GitHub review covering t
466 [PR READY] — Post comment on PR #648 linking the Zulip primitive-bot plus efq 

### Tableau Infrastructure

456 [NOT STARTED] — Generalize the Sfor-containment / subset-blocking device recurrin

### Bimodal And Temporal Logic

568 [BLOCKED] — [Follow-on created by the blocked-task review, at explicit user r

### Constructive Modal Logic

570 [NOT STARTED] — [Created by the blocked-task review: this sorry was flagged in-co

## Tasks

### 571. Fill the strict-Until/Since-gated Bimodal sorries (SuccRelation, UntilSinceCoherence)
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 37

**Description**: [Carved off the bimodal sorry task by the blocked-task review. Holding both halves as one task pinned the tractable discrete half behind this intractable one; they have different external gates and different prospects.] Fill the sorries gated on the strict Until/Since semantics gap in Cslib/Logics/Bimodal/Metalogic/:
- Bundle/SuccRelation.lean: 7 sorries (lines 257, 263, 270, 277, 284, 289, 294)
- Bundle/UntilSinceCoherence.lean: 2 sorries (lines 38, 43)

All 9 require axioms that were REMOVED AS UNSOUND (BX8/BX9 and the temporal-T axioms) under the strict Until/Since reading. They are therefore not merely unproved -- the statements may need restating before they are provable at all. Gated on the bimodal continuous port, which is itself gated on upstream BimodalLogic tasks 390/391 (Dedekind carrier construction and FrameClass scaffolding), both [NOT STARTED] upstream. Line numbers are as measured 2026-07-26. BEFORE PLANNING, establish whether the 9 obligations are stated soundly under the current semantics: if the removed axioms were genuinely unsound, some of these may need to be restated or retired rather than proved, and that determination should precede any port dependency.

---

### 570. Discharge nested_sound_impL via the source's induction over the Lambda chain
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Constructive Modal Logic
- **Dependencies**: None

**Description**: [Created by the blocked-task review: this sorry was flagged in-code as needing 'a dedicated later phase (not yet numbered in the plan)' and had NO tracking task.] Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1315 carries a documented strategic sorry in nested_sound_impL (soundness of the nested-sequent rule impL / imp-bullet). THE OBLIGATION: the source needs its own induction on n over the Lambda{ } chain (the L_X, L_Y, L_Z construction, page 10), mixing ctx.outputPruning.fillRhs-shaped and ctx.fillLhs-shaped premises against a ctx.fillLhs-shaped conclusion. It does NOT reduce to the already-landed congruence lemmas 4.4 / 4.5 / 4.8 alone -- that was checked and is why it was deferred rather than attempted. Build the Lambda-chain induction, then discharge the rule. Note the cut rule and NestedProof.CutFree are already landed and verified. INVARIANTS: no new axioms; the Cslib/ bare-sorry count must go DOWN by one; lake build and lake test green.

---

### 569. Establish whether continuous time needs axioms beyond density (Burgess 1982)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: [Created by the blocked-task review to break a two-task deadlock.] RESEARCH ONLY. Both the temporal and bimodal continuous-completeness tasks are recorded as blocked on 'the continuous case has not been developed upstream' -- but their SHARED real blocker is a literature question that depends on neither, and can be answered today: DO CONTINUOUS (Dedekind-complete) FRAMES REQUIRE ANY AXIOM BEYOND DENSITY? The standard result attributed to Burgess 1982 is that the Until/Since temporal logic over the reals has exactly the same theorems as over the rationals, which would make density sufficient and collapse both continuous tasks to near-trivial transports of the already-landed dense completeness. That equivalence is precisely what has never been checked here. DETERMINE: (1) the exact statement and proof strategy of the Burgess result, from the source -- not from secondary recollection; (2) whether it applies to THIS repository's Until/Since temporal language and frame conditions, or only to a variant; (3) if it applies, the cheapest sound route to a Continuous frame class and its completeness theorem, and whether the bimodal continuous port is needed at all or can be bypassed; (4) if it does NOT apply, which additional axiom schema (Dedekind completeness or equivalent) is required, and what that costs. Run with --lit. A negative or 'genuinely open' verdict is a valid deliverable. CONSUMERS: the temporal continuous-completeness task (which may be re-scoped or unblocked outright on the verdict) and the bimodal continuous port (which may turn out to be unnecessary as a dependency).

---

### 568. Research the highest-quality Chronicle-structure refactor for Bimodal/Temporal dedup
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal and Temporal Logic
- **Dependencies**: Task 530

**Description**: [Follow-on created by the blocked-task review, at explicit user request, to run AFTER the Chronicle consolidation task closes as a descoped partial.] RESEARCH ONLY -- produce a recommendation, do not implement. THE QUESTION: the Bimodal and Temporal Chronicle trees remain ~89% duplicated. The consolidation task successfully lifted ChronicleInterface, generic Types, the RRelation shared core and the CEE Structures + BurgessHelpers, then hit a hard wall: C5ForwardWalkResult, C5BackwardWalkResult, EliminationResult and ChronicleConstruction are indexed by each tree's LOCAL Chronicle Atom structure, and two independent deep investigations confirmed that generically bridging that indexing breaks downstream rcases/simp proofs. Descoping was the right call for a task mandated as 'structural dedup, not a proof change'; it does not answer what the RIGHT architecture is. DETERMINE: whether a Chronicle-type-alias architecture, a parameterization over the label type, a typeclass-mediated indexing, or some fourth option lets the walk-result and construction layers be shared without perturbing the proof scripts that consume them -- and what each would cost. Establish this against the actual proof scripts that broke, not against the type signatures alone; the failure mode was rcases/simp behaviour, so a design that type-checks is not evidence. REPORTING CONTRACT: deliver either (a) a concrete architecture with a phase-sized implementation sketch and an honest cost, or (b) a reasoned finding that the duplication is the correct steady state for this subsystem, with the reason stated in terms a future reader can act on. (b) is a valid and useful deliverable -- do not manufacture a refactor to avoid it. CONSTRAINTS: preserve every landed sorry-free result; do not entangle the discrete-completeness sorries in the bimodal tree, which are gated on a separate external port.

---

### 567. Run the CSLib vetting pipeline against the refactored Tableau subsystem as acceptance gate
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 558, Task 559, Task 561, Task 562, Task 563, Task 564, Task 565, Task 566

**Description**: [Task I of the modal-tableau refactor programme; P4, final acceptance gate. Depends on every other task in the programme.] Run the seven-step CI order from .claude/rules/cslib.md against CONTRIBUTING.md, NOTATION.md, ORGANISATION.md and CODE_OF_CONDUCT.md. It has never been run on this subsystem. PREREQUISITE, budget for it: lake exe checkInitImports currently FAILS on a stale build unrelated to this subsystem (a missing Constructive/Nested/Soundness.olean), so a full lake build must clear that before verification against the stated gate is meaningful. ACCEPTANCE CRITERIA: behaviour preservation demonstrated by modalTableauS4Keyed_complete and the six landed Decidable instances (K/T/B/S5/Five/KB5) remaining green; the Tableau sorry census not rising above its measured baseline of exactly 1; no new axioms above the measured subsystem baseline of zero; checkInitImports and lint-style clean; and the existing executable regression corpora (CslibTests/S4LoopGuardRegression.lean, 197 lines, plus the probe harnesses under the S4 loop-guard task's artifacts directory) reproducing their recorded verdicts EXACTLY.

---

### 566. Create Boneyard/ with its convention and move only re-verified zero-consumer declarations
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 564

**Description**: [Task H of the modal-tableau refactor programme; P3.] Create Boneyard/ at the repository root (it does not currently exist here; the convention is borrowed from the upstream repository, where it holds roughly 27k lines and 29 sorries excluded from porting, censuses and the build). Document the convention in Boneyard/README.md: quarantined, never imported by Cslib/, excluded from lake build, mk_all, lint-style, shake and all sorry/axiom censuses, retained for provenance rather than use. MOVE, never delete. RE-RUN THE CONSUMER AUDIT AT EXECUTION TIME -- the recorded audit is dated and this is a multi-task programme. Eligible subject to that re-check: blockedRedirect_diaNeg_mem_of_diaOrigin, blockedRedirect_boxctx_mem_of_boxOrigin, the keysRootEmpty / keysRootEmpty_entry pair, and the two outDegEq preservation lemmas ONLY if the migration task actually landed the field removal. TWO CARVE-OUTS ARE MANDATORY. (1) FrameSoundness.lean:1220-1244 (branchSatisfiableIn_s4FC_ancestor_redirect) is IMMOVABLE despite being zero-consumer: it carries the retained sorry that is an explicit user decision, and the rule protecting proven-and-consumed code does not by itself protect it. (2) keysOriginS4 is NOT eligible -- it has 22 code consumers, and the comment at LoopChecking.lean:2001-2002 claiming it was removed is FALSE. Nothing whose deletion cannot be justified by a re-verified zero-consumer check may be moved, and nothing proven and consumed may be moved at all. Also NOT eligible, these are route-independent assets to be PLACED by the abstraction decision rather than quarantined: modalS4Saturated (7 consumers), the strictly-weakened hintikkaS4 bridges (the set is 8, measured, not 10), hasEdge_accWithReds_iff, reflTransGen_accWithReds_first_red, and the two sorry-free blockedRedirect_unwrapped_{boxPos,diaNeg}_mem transfers with their Reds / accWithReds packaging.

---

### 565. Split LoopChecking.lean along the real S4 seams and update ORGANISATION.md
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 561, Task 563, Task 564

**Description**: [Task G of the modal-tableau refactor programme; P3. Depends on the review gate, box-plus and the migration, because the seams MOVE if box-plus is adopted.] Split LoopChecking.lean (10,540 lines / 230 declarations, measured) into an S4/ cluster of Universe, BirthKey, Guard, Invariant, Hintikka and Redirect modules. Note that these clusters' current source ranges are DISCONTIGUOUS -- itself the evidence that a line-count split would be wrong. DO NOT split mechanically by line count. Conform to ORGANISATION.md and NOTATION.md, preserve import acyclicity, and UPDATE ORGANISATION.md, which currently gives no line-count guidance and describes Modal/Tableau/ in one undifferentiated line. The Support-module dedup task should land first: it shrinks the files before the seams are cut.

---

### 564. Migrate the S4 Keyed drivers onto the St ladder and retire the duplicated keys' derivation
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 562, Task 563

**Description**: [Task F of the modal-tableau refactor programme; P3.] Migrate the S4 Keyed and KeyedOrdered drivers onto the RuleApplySt / St ladder and retire the duplicated keys' re-derivation -- the stepper currently re-derives the blockingWorldS4Keyed decision that modalApplyOneS4Keyed already made internally (LoopChecking.lean:951-953). Retiring that double derivation is where the unquantified line-count reduction actually lives. This task, NOT the Boneyard task, owns any removal of the S4LoopInv.outDegEq field. That removal is NOT a pure deletion: outDegEq has zero code consumers but its preservation proof is 386 lines across two variants (LoopChecking.lean:4917-5105 and an undocumented second ordered variant at :5111-5307), and it has THREE provision sites -- LoopChecking.lean:7569, :7633, and a POSITIONAL anonymous-constructor site inside modalTableauS4Keyed_initial at FrameCompleteness.lean:4217-4218, i.e. inside the landed completeness capstone. Run lake build before and after; if the cascade into the four other invariant proofs that destructure the structure is large, KEEP the field -- 386 lines are not worth a regression.

---

### 563. Adopt Lemmon box-plus pairing at the birth-key level
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 561

**Description**: [Task E of the modal-tableau refactor programme; P2. Gated on the review gate. This task is the live gate for BOTH the S4 termination follow-on and the S4 keyed soundness task -- keys and mint payload both change here, so land it before either resumes.] Add boxPlusPair and BoxPlusClosed; enrich successorBirthContent (LoopChecking.lean:384-393) to emit BOTH members of each pair -- {(pos, psi), (pos, box psi)} where it currently emits only the unwrapped (pos, psi) for T(box psi)@w -- and extend the two _preserves_keyLowerBd proofs accordingly. The enriched key stays inside the existing codomain signedSubfmls phi0 (modalSubfmls (.box a) = .box a :: modalSubfmls a, FmpMeasure.lean:79), so signedSubfmls_card_le, signedSubfmls_powerset_card_le, modalWorldBoundS4 and the pigeonhole argument are UNCHANGED -- box-plus is free in the world bound. The source never iterates box-plus beyond depth 1; where more discriminating power is needed it enlarges the filter Sigma instead, which WOULD change the codomain and is therefore expensive -- enrich with box-plus, not with the filter. Prior art to reuse: modalFourBoxProp (FrameRules.lean:133-138) and boxDiamondPersistence (Bimodal Tableau.lean:344) are already box-plus at the RULE level; only the key level is missing. THE ONE REAL RISK, and the mandatory gate: enriching keys changes which steps block, so modalTableauS4Keyed_complete may break. Gate on lake build Cslib.Logics.Modal.Tableau.FrameCompleteness. If it breaks, the completeness proof is quantified over driver behaviour (modalExpandBranchesS4Keyed_hintikka) and should transport -- but that must be DEMONSTRATED, not assumed. If it cannot be repaired sorry-free, mark [BLOCKED]; do NOT add a sorry. Box-plus is S4-scoped (the Lemmon filtration and ChagrovZakharyaschev Proposition 3.6 are stated for TRANSITIVE models only, satisfied by s4FC) and MUST NOT be lifted into Foundations/.

---

### 562. Introduce RuleApplySt additively and bridge modalExpandBranchesGen
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 561

**Description**: [Task D of the modal-tableau refactor programme; P2. Gated on the review gate.] MANDATORY FIRST STEP, non-negotiable per the programme constraint: a consumer audit of Saturation.lean before any edit. Then generalise RuleApply (Saturation.lean:107-111) to RuleApplySt sigma, with RuleApply = RuleApplySt Unit, added PURELY ADDITIVELY as new declarations -- modalExpandBranchesGen is never edited -- and prove modalExpandBranchesGen_eq_St. Zero risk to landed theorems by construction: because nothing existing is edited, none of the six true-rfl driver bridges (modalTableauB_eq, modalTableauS5_eq, modalTableauFive_eq, modalTableauKb5_eq, modalTableauKb5''_eq, modalExpandBranchesB_eq) can break. Migration onto the ladder and retirement of the double derivation are a SEPARATE, later task -- do not start them here.

---

### 561. REVIEW GATE: decision record adopting or rejecting box-plus birth keys and RuleApplySt
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Summary**: [561_tableau_abstraction_decision_record/decisions/01_abstraction-decision-record.md]

**Description**: [Task C of the modal-tableau refactor programme; P1. THIS IS THE REVIEW GATE. No file may be moved or split, and no abstraction may be implemented, until this decision record is reviewed and ACCEPTED.] Produce an explicit decision record adopting or rejecting (a) Lemmon box-plus birth keys and (b) the RuleApplySt generalization, on the evidence in the refactor research report's sections 3-5. Its input already exists -- this task has no research dependency. For (a): successorBirthContent (LoopChecking.lean:384-393) records only the unwrapped (pos, psi) when T(box psi)@w is on the branch, while relevantSetFinset records both wrapped and unwrapped forms; that asymmetry IS the wrapped/unwrapped mismatch that killed one of the dead soundness routes. Box-plus is licensed for S4 BY NAME (ChagrovZakharyaschev1997 Corollary 5.32) and is FREE in the world bound (modalSubfmls (.box a) = .box a :: modalSubfmls a, FmpMeasure.lean:79, keeps the enriched key inside signedSubfmls, leaving the cardinality lemmas, modalWorldBoundS4 and the pigeonhole argument untouched). Scope the expectation down: it subsumes none of the 8 bridges outright, collapses AT MOST 2 (the box_pos_self and dia_neg_self reflexive instances), and does NOT touch the reachability defect. It is S4-scoped and MUST NOT be lifted into Foundations/. For (b): exactly ONE driver family of nine forks off modalTableauGen / modalExpandBranchesGen -- the S4 Keyed and KeyedOrdered pair -- and only because RuleApply (Saturation.lean:107-111) has no slot for per-driver state, forcing the stepper to RE-DERIVE the blockingWorldS4Keyed decision modalApplyOneS4Keyed already made internally (admitted at LoopChecking.lean:951-953). The record must also state the disposition of the two downstream consumers waiting on it: the S4 termination follow-on and the S4 keyed soundness task, whose keys and mint payload both change under (a). Blocks every implementation task in this programme.

---

### 560. Repair the per-repo literature sub-index (Massacci corpus reported as 1 chunk, holds 77)
- **Status**: [COMPLETED]
- **Task Type**: meta
- **Topic**: Literature Infrastructure
- **Dependencies**: None
- **Research**: [560_repair_literature_subindex_massacci_chunks/reports/01_briefing-chunk-count-defect.md]
- **Plan**: [560_repair_literature_subindex_massacci_chunks/plans/01_briefing-chunk-count-repair.md]
- **Summary**: [560_repair_literature_subindex_massacci_chunks/summaries/01_chunk-count-repair-summary.md]

**Description**: [Task B2 of the modal-tableau refactor programme; P0, no dependency. REWRITTEN 2026-07-26: the original premise was verified INCORRECT and is retired.] RETIRED PREMISE, do not reinstate: the original description claimed specs/literature-index.json reports the massacci_2000_single_step_tableaux_for_modal_logics corpus as 1 chunk and needs repair. It does not. specs/literature-index.json is REFERENCE-ONLY (doc_id plus relevance; it stores no chunk counts at all) and validates clean at 34/34 doc_ids resolving against the global index. THE ACTUAL DEFECT: the '1 chunk' figure is GENERATED at briefing-build time by .claude/scripts/literature-briefing.sh:203-206, which derives a chunk count by counting global-index CHILD entries whose parent_doc equals the doc_id, with a chunk_count=1 fallback at :224. Massacci has 77 chunk_*.md files on disk and chunk_count:77 recorded on its PARENT entry, but ZERO child entries, so the child-entry count returns 0 and the fallback renders 1. The defect is SYSTEMIC, not Massacci-specific: 19 of 34 sub-index documents under-report identically, spanning 848 chunk files (simpson_1994:206, massacci:77, biermandepaiva_2000:53, alechina_2001:52, marin_2021:51, trufas_2024:48, post_1921:46, arisaka_2015:40, wijesekera_1990:38, from_2022:34, bentzen_2023:33, rabinovich_2014:30, henkin_1949:27, burgess_1982_i:25, burgess_1982_ii:24, johansson_1937:24, pacheco_2024:20, gabbay_1994_ch10:12, hodkinson_2006:8). CONSEQUENCE: every --lit briefing built over these documents understates available material by up to two orders of magnitude, which plausibly contributed to earlier under-use of the Massacci corpus. FIX (preferred, lowest risk): in .claude/scripts/literature-briefing.sh, prefer the parent entry's existing chunk_count field over the derived child-entry count, falling back to the child count only when the parent carries no chunk_count. This repairs all 19 documents without mutating corpus data. DO NOT fix this by rewriting ~/Projects/Literature/index.json: that is the user's SHARED global corpus, outside this repository, and mutating it affects every project on this machine. VERIFICATION: after the change, a briefing over massacci_2000_single_step_tableaux_for_modal_logics must report 77 chunks, and the sparse-coverage marker (<!-- lit-coverage ... -->) must reflect the corrected count; spot-check at least three further documents from the list above. Provenance: diagnosed during the modal-tableau refactor programme's baseline-capture phase; see specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/baseline.md.

---

### 559. Land the measured Tableau baseline and correct four documentation defects
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Summary**: [559_tableau_measured_baseline_doc_corrections/summaries/01_measured-baseline-doc-corrections-summary.md]

**Description**: [Task B of the modal-tableau refactor programme; P0, no dependency, runs in parallel with the Support dedup task.] Land the measured baseline table (with its exact reproduction commands) into the modal Tableau subsystem's module documentation, so the asserted-vs-actual drift that this programme's research found cannot recur. Measured figures: LoopChecking.lean 10,540 lines / 230 declarations; FrameSoundness.lean 5,317; FrameCompleteness.lean 4,307; three-file total 20,164; redirect semantic surface 4 clauses / 14 code lines at LoopChecking.lean:6557-6562; the hintikkaS4 bridge set is 8, not ten; subsystem axiom declarations 0; subsystem sorry census exactly 1. CORRECT EXACTLY FOUR ADJUDICATED DEFECTS, leaving the seven verified-TRUE claims alone: (1) LoopChecking.lean:2001-2002 -- the claim that keysOriginS4 was removed is FALSE (it has 22 code consumers); (2) LoopChecking.lean:8911-8912 -- stale references to the two _boxed reflTransGen bridge variants, removed in commit c4b33f63; (3) LoopChecking.lean:2000-2004 -- resolve the 'possibly orphaned' hedge on keysRootEmpty using the consumer audit as evidence; (4) FrameSoundness.lean:1215-1219 -- add BOTH the zero-consumer fact AND the finding that Massacci2000 Theorem 8.1 (blocking preserves satisfiability) is STATED AND NEVER PROVED there (Appendix B.2 proves only Theorem 8.4; section 10.2 defers 8.1 to Gore's model graphs), because that changes how a future reader assesses the obstruction and prevents another route from trying to reconstruct a proof its cited source does not contain. Documentation-only: no proof or definition may change.

---

### 558. Extract re-derived private Tableau facts into public Support modules
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: [Task A of the modal-tableau refactor programme; P0, highest value/risk ratio in the whole programme, NO dependency on any other task.] Cslib/Logics/Modal/Tableau/ contains 77 comment-attested 'Local re-derivation of X (unavailable across files)' sites, root-caused by FmpMeasure.lean marking 50 declarations private: modalSubfmls_trans is re-derived in three files (S5Simplification.lean:97, FiveSimplification.lean:736, BDriver.lean:211), modalKnownWorlds_fold_spec in four, hasEdge_addEdge_cases in four. Extract those facts as PUBLIC declarations into Cslib/Logics/Modal/Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean and DELETE the 77 re-derivations. This is mechanical and behaviour-preserving by construction, requires no abstraction decision, and it shrinks the oversized files BEFORE any split seams are chosen -- so it must precede the module split. Verify with lake build, lake exe checkInitImports, lake exe lint-style, and lake shake --add-public --keep-implied --keep-prefix. Constraint: do not edit Rules.lean, Saturation.lean or Branch.lean. Preserve every proven, consumed result; modalTableauS4Keyed_complete and the six landed Decidable instances (K/T/B/S5/Five/KB5) must be green at every commit. Subsystem sorry census must stay at exactly 1 (FrameSoundness.lean:1244, retained by explicit user decision) and axiom count at 0.

---

### 557. Modal tableau refactor abstractions boneyard
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [557_modal_tableau_refactor_abstractions_boneyard/reports/01_tableau-abstraction-boneyard-analysis.md]
- **Plan**: [557_modal_tableau_refactor_abstractions_boneyard/plans/01_tableau-refactor-abstractions-boneyard.md]

**Description**: Refactor and restructure the modal Tableau subsystem to library-publication quality, identifying the correct abstractions and module divisions, archiving unnecessary code to a new Boneyard/ quarantine, and systematically discharging the documentation debt. MOTIVATION: four successive soundness routes for the S4 keyed loop-check guard have failed at the same obligation by four different mechanisms (Route P: redirect-inertness lemmas machine-checked FALSE at a reachable state; origin-edge invariant revision: abandoned; ancestor-only blocking: defeated by the existentially arbitrary branchSatisfiableIn witness model; subtractive blocking with a completeness-only redirect channel: its free transfer yields only an UNWRAPPED branch fact at the redirect target). This task treats the factoring as a first-class defect rather than continuing to route around it. It is NOT a soundness-proof task and must not attempt the soundness obligation. THE DEFECT, RELOCATED BY THE COMPLETED HARD-MODE ANALYSIS (reports/01_tableau-abstraction-boneyard-analysis.md): the mis-factoring is edge-addition where both source calculi identify worlds, not the bridge set. A blocked minting step has modalApplyOneS4Keyed return (.linear [], acc.addEdge sf.label wBlock) -- two lines, LoopChecking.lean:753 and :757 -- creating the obligation m.r (f src) (f wBlock) against branchSatisfiableIn's existentially arbitrary witness model (FrameSoundness.lean:110), whereas Massacci2000 Definition 10.2's SST-interpretation is explicitly NOT required injective (identify the blocked world with its shorter modal copy rather than relate them) and Pruning Lemma 8.2 instead DELETES the descendant-closed subtree Ftree(sigma.n). The real seam: completeness already CONSTRUCTS its model, extractModelS4 b acc = extractModelWith Relation.ReflTransGen b acc (FrameCompleteness.lean:143-146), while soundness quantifies EXISTENTIALLY, so containment is an obligation rather than a construction step, where ChagrovZakharyaschev1997 Theorem 5.51 discharges the same condition by building its relation inside the ambient one. The guard docstring already names this as NO REACHABILITY RESTRICTION (LoopChecking.lean:491-493) and the mechanism is recorded at FrameSoundness.lean:1183-1190. This REPLACES the earlier diagnosis that the absence of a persistence mechanism for unwrapped facts was the single most valuable thing to name: that absence is real and is verbatim the obstruction at LoopChecking.lean:8830-8832, but it is only the CONTENT half, and :478-501 already says fixing one of the two named defects does not fix the other. RETIRED PREMISES, do not reinstate: (a) there is no theorem numbered interval theorem -- chunk_0246.md:43-65 (print p. 141) is unnumbered prose after Theorem 5.23 and an UNPROVED authorial remark with no counterexample frame supplied, and its finest and coarsest relations live on the filtration QUOTIENT, so its nontransitivity sentence, accurate as a quotation, is NOT precisely the failure mode of a subtractive or redirect-channel design; cite it by chunk and page, never as a theorem, and build no inference on it; (b) Massacci2000 Theorem 8.1, that blocking preserves satisfiability, is STATED AND NEVER PROVED there -- Appendix B.2 proves only Theorem 8.4, and section 10.2 defers 8.1 to Gore's model graphs (chunk_0054.md:3-7) -- so the four dead routes were reconstructing a proof their cited source does not contain, and this belongs in FrameSoundness.lean's documentation; (c) Theorem 5.51 concerns Grz via SELECTIVE filtration, not S4 via filtration; (d) box-plus is defined in Chapter 3 (chunk_0173.md:11-14, print p. 98) as the syntactic analogue of reflexivization, not in chunk_0248, which holds the Lemmon filtration itself (:24-31, print p. 142, also unnumbered). MEASURED BASELINE replacing every asserted figure, with reproduction commands in section 2 of report 01. LoopChecking.lean 10,540 lines / 230 declarations (asserted 10,674 / 150); FrameSoundness.lean 5,317 (exact); FrameCompleteness.lean 4,307 (asserted 4,532); three-file total 20,164. Redirect semantic surface 4 clauses / 14 code lines at LoopChecking.lean:6557-6562 (exact) plus :8779-8782 and :8786-8789 (asserted locations shifted +23). The hintikkaS4 bridge set is 8, not ten, and the asserted ten WAS correct when written: the two _boxed reflTransGen variants were removed in commit c4b33f63, and the comment at :8911-8912 still references them. The axiom drift was a SCOPE CONFUSION, not a drift -- the Tableau subsystem has ZERO axiom declarations and 3 raw axiom word matches, while repo-wide Cslib/ has 26 declarations and 1,701 raw matches -- so fix it by recording the measured baseline with its command, never by adjusting a number. Sorry census: the whole Tableau subsystem is exactly 1, at FrameSoundness.lean:1244, inside a ZERO-consumer declaration; repo-wide Cslib/ is 10. Tags confirmed exact: 0 FIX/TODO/NOTE/QUESTION in the three files, 11 TODO and 8 NOTE repo-wide. outDegEq: zero code consumers of S4LoopInv.outDegEq re-verified, but its preservation proof is 386 lines, not 188 (:4917-5105 at 189 plus an undocumented second ordered variant at :5111-5307 at 197), and it has THREE provision sites -- LoopChecking.lean:7569, :7633, and a POSITIONAL anonymous-constructor site inside modalTableauS4Keyed_initial at FrameCompleteness.lean:4217-4218, i.e. inside the landed completeness capstone -- so removing the field is NOT a pure deletion. ModalTableauResult is referenced across 11 Tableau modules (asserted 8), though its (b, acc) shape claim holds. The amplification figures (4 declarations / 1,036 lines, 43 / 1,983 reachable from modalTableauS4Keyed_complete) were NOT re-measured -- they need an elaborated-environment dependency query, not a text scan -- and no substitute was fabricated; the qualitative claim stands on the verified 4-clause surface plus 85 private lemmas in LoopChecking.lean and 50 in FmpMeasure.lean. Boneyard/ confirmed absent; CslibTests/S4LoopGuardRegression.lean confirmed at 197 lines; the six landed Decidable instances confirmed as exactly K/T/B/S5/Five/KB5. PREREQUISITE: lake exe checkInitImports currently FAILS on a stale build unrelated to this subsystem (a missing Constructive/Nested/Soundness.olean), so a full lake build must clear it before verification against that stated gate is meaningful. SCOPE. A. ABSTRACTIONS AND UNIFICATION: adopt the Lemmon box-plus pairing at the BIRTH-KEY level. successorBirthContent (LoopChecking.lean:384-393) records only the unwrapped (pos, psi) when T(box psi)@w is on the branch while relevantSetFinset records both forms, and that asymmetry IS the wrapped/unwrapped mismatch; add boxPlusPair and BoxPlusClosed and emit both members of each pair. It is licensed for S4 BY NAME (Corollary 5.32 names K4, D4 and S4 as admitting filtration via the transitive closure of the finest filtration or the Lemmon filtration) and it is FREE in the world bound, because modalSubfmls (.box a) = .box a :: modalSubfmls a (FmpMeasure.lean:79) keeps the enriched key inside the existing codomain signedSubfmls, leaving the cardinality lemmas, modalWorldBoundS4 and the pigeonhole argument untouched; the one path by which it could have cost anything, iteration to depth greater than 1, is closed negatively from the source. But SCOPE THE EXPECTATION DOWN: box-plus subsumes none of the 8 bridges outright and collapses AT MOST 2 (the box_pos_self and dia_neg_self reflexive instances), and it does NOT touch the reachability defect. The other six are faithful transcriptions of Massacci Proposition 8.1 and ChagrovZakharyaschev Proposition 3.6 plus two orthogonal witness conjuncts, and the weakened hypotheses were a minimisation from modalHintikkaSetS4 to modalS4Saturated -- a factoring improvement that already happened, not a wrong abstraction. Box-plus is S4-scoped (the Lemmon filtration and Proposition 3.6 are stated for TRANSITIVE models only, satisfied by s4FC) and MUST NOT be lifted into Foundations/; note that enlarging the FILTER instead, as the source must for K4.1/S4.1/K5, would change modalWorldBoundS4 where box-plus enrichment is free. Prior art to reuse: modalFourBoxProp (FrameRules.lean:133-138) and boxDiamondPersistence (Bimodal Tableau.lean:344) are already box-plus at the RULE level, and MonotoneEdges (Intuitionistic Soundness.lean:367-369) is already a persistence-carrying soundness-invariant predicate; only the key level is missing. Second unification target: exactly ONE driver family of nine forks off modalTableauGen / modalExpandBranchesGen -- the S4 Keyed and KeyedOrdered pair, the unkeyed S4 driver already being generic -- and only because RuleApply (Saturation.lean:107-111) has no slot for per-driver state, forcing the stepper to RE-DERIVE the blockingWorldS4Keyed decision modalApplyOneS4Keyed already made internally, as the code admits at LoopChecking.lean:951-953. Generalise to RuleApplySt sigma with RuleApply = RuleApplySt Unit, added ADDITIVELY first so the six true-rfl driver bridges cannot break, then bridged, then migrated; retiring the double derivation is where the unquantified line-count reduction lives. The one landed theorem at risk is modalTableauS4Keyed_complete, since enriching keys changes which steps block; gate on lake build and, if it cannot be repaired sorry-free, mark BLOCKED rather than adding a sorry. B. MODULE DIVISION: FIRST, and independent of every abstraction decision, discharge the highest-value item the original scope omitted -- 77 comment-attested LOCAL RE-DERIVATION sites, root-caused by FmpMeasure.lean's 50 private declarations being unavailable across files (modalSubfmls_trans re-derived in three files, modalKnownWorlds_fold_spec in four, hasEdge_addEdge_cases in four). Extract those facts as PUBLIC declarations into Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean and delete the re-derivations: mechanical, behaviour-preserving by construction, needing no abstraction decision, and it shrinks the oversized files BEFORE split seams are chosen. Then split along the real seams identified (an S4/ cluster of Universe, BirthKey, Guard, Invariant, Hintikka and Redirect modules, whose current source ranges are DISCONTIGUOUS -- itself evidence a line-count split would be wrong), conforming to ORGANISATION.md and NOTATION.md, preserving import acyclicity, and UPDATING ORGANISATION.md, which gives no line-count guidance and describes Modal/Tableau/ in one undifferentiated line. Do not split mechanically by line count. C. BONEYARD: create Boneyard/ at the repository root -- it does NOT currently exist here; it is a convention borrowed from the source repository, where it held roughly 27k lines and 29 sorries excluded from porting, censuses, and the build. Document the convention in Boneyard/README.md: quarantined, never imported by Cslib/, excluded from lake build, mk_all, lint-style, shake, and all sorry/axiom censuses, retained for provenance rather than use. Move there rather than deleting, and only after RE-RUNNING the consumer audit at execution time because the recorded one is dated: blockedRedirect_diaNeg_mem_of_diaOrigin, blockedRedirect_boxctx_mem_of_boxOrigin, the keysRootEmpty / keysRootEmpty_entry pair, and the two outDegEq preservation lemmas only once the field removal has actually landed. TWO CARVE-OUTS ARE MANDATORY: FrameSoundness.lean:1220-1244 (branchSatisfiableIn_s4FC_ancestor_redirect) is IMMOVABLE despite being zero-consumer, because it carries the retained sorry that is an explicit user decision and the rule protecting proven-and-consumed code does not by itself protect it; and keysOriginS4 is NOT eligible, having 22 code consumers, so the comment at LoopChecking.lean:2001-2002 claiming it was removed is FALSE. Nothing whose deletion cannot be justified by a re-verified zero-consumer check may be moved, and nothing proven and consumed may be moved at all. D. DOCUMENTATION: the debt in the three modal Tableau files is prose-shaped, not tag-shaped. Seven adjudicated claims verified TRUE must be LEFT ALONE; four defects must be corrected: LoopChecking.lean:2001-2002 (the keysOriginS4 removal claim is FALSE), :8911-8912 (stale _boxed bridge references), :2000-2004 (resolve the possibly-orphaned hedge on keysRootEmpty with the audit as evidence), and FrameSoundness.lean:1215-1219 (add both the zero-consumer fact and the Massacci Theorem 8.1 gap, which change how a future reader assesses the obstruction). Land the measured baseline table with its exact commands into the subsystem documentation so the same drift cannot recur, and repair the per-repo literature index, which reports the Massacci corpus as 1 chunk where it holds 77 plus a full text: run /literature --validate. CONSTRAINTS. Never edit Rules.lean, Saturation.lean (ModalTableauResult carries only (b, acc)), or Branch.lean without an explicit consumer audit first; a Saturation.lean change IS proposed (RuleApplySt) and its audit is a mandatory gate. Preserve every proven, consumed result: this is a restructuring task and must be behaviour-preserving on all landed theorems, with modalTableauS4Keyed_complete and the six landed Decidable instances (K/T/B/S5/Five/KB5) green at every commit. The sorry at FrameSoundness.lean:1244 is retained by explicit user decision and its disposition is a separate decision, not this task's to make. Route-independent assets deliberately kept from the subtractive attempt -- modalS4Saturated (7 consumers, not eligible), the strictly-weakened hintikkaS4 bridges (the set is 8, measured, not 10), hasEdge_accWithReds_iff, reflTransGen_accWithReds_first_red, and the two sorry-free blockedRedirect_unwrapped_{boxPos,diaNeg}_mem transfers, together with the Reds / accWithReds packaging they are stated over -- are inputs to be placed correctly by the abstraction decision, not candidates for the Boneyard. Run the CSLib vetting pipeline against CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, and CODE_OF_CONDUCT.md as an acceptance gate; it has never been run on this subsystem. VERIFICATION: behaviour preservation demonstrated by the landed capstones and Decidable instances remaining green, the Tableau sorry census not rising above its measured baseline of exactly 1, no new axioms above the measured subsystem baseline of zero, checkInitImports and lint-style clean after the stale-build repair above, and the existing executable regression corpora (CslibTests/S4LoopGuardRegression.lean at 197 lines, plus the probe harnesses under the S4 loop-guard task's artifacts directory) reproducing their recorded verdicts exactly. Expect this task to need expansion into several tasks. The abstraction analysis is now COMPLETE (report 01) and must be REVIEWED AND ACCEPTED in an explicit decision record before any file is moved or split and before any abstraction is implemented.

---

### 555. Literature search fidelity schema quarantine
- **Status**: [COMPLETED]
- **Task Type**: general
- **Dependencies**: None
- **Research**: [555_literature_search_fidelity_schema_quarantine/reports/02_blocker-disposition-research.md]
- **Plan**: [555_literature_search_fidelity_schema_quarantine/plans/02_blocker-resolution-and-decision-memo.md]
- **Summary**: [555_literature_search_fidelity_schema_quarantine/summaries/02_blocker-resolution-summary.md]

**Description**: Repair literature search visibility for index entries written under the doc_id/chunks_dir schema. MEASURED SITUATION (all figures verified directly, not inferred): the global Literature index.json carries two entry schemas -- 273 entries with id + path="sources/<dir>/", and 18 with doc_id + chunks_dir=<absolute path>. literature-search.sh's load_fidelity_map() derives its lookup key ONLY from a path prefix of "sources/", so no chunks_dir-schema entry ever lands in the map; get_fidelity() then fail-opens to unverified_summary, which is on QUARANTINED_FIDELITY_VALUES (literature-search.sh:53), so default search drops them and reports degraded=true with zero results. THE 18 SPLIT INTO TWO GROUPS THAT NEED DIFFERENT FIXES. GROUP A (2 docs: wijesekera_1990_constructivemodallogicsi, simpson_1994_intuitionisticmodallogic) already carry an honest, human-adjudicated stamp provenance_fidelity=ocr_rescanned_reflowed_partial_symbol_loss, which is NOT on the quarantine list. These are invisible purely because of the key-derivation bug -- their correct fidelity value exists in index.json but is unreachable. Fixing key derivation alone fully restores them. This is the tractable half and should ship first. GROUP B (16 docs, including arisakadasstrassburger_2015, marinmoralesstrassburger_2021, pacheco_2024, biermandepaiva_2000, alechinamendlerdepaivaritter_2001, chagrovzakharyaschev_1997, massacci_2000, plus 8 unrelated hyperproperty/verification docs) have provenance_fidelity=null. After the key-derivation fix, fmap.get(doc_id) still returns null and get_fidelity still fail-opens to unverified_summary, so they REMAIN quarantined. The key fix does nothing for them. CRITICAL CONSTRAINT ON GROUP B -- do not plan to solve this by extending literature-fidelity-audit.sh: that script classifies by comparing converted markdown against pdftotext output of the source PDF, and these directories contain only chunk_*.md files with NO source PDF present (verified for arisaka, wijesekera, pacheco), and zotero-library.json has no matching entries either. With no baseline available the audit's own honest verdict would be unverified_no_baseline, which is ITSELF on the quarantine list -- so an extended audit would correctly re-quarantine them and change nothing. The fail-open-to-unverified design is deliberate and correct (it prevents an unverified conversion being cited as authoritative) and MUST NOT be weakened by simply removing values from QUARANTINED_FIDELITY_VALUES. GROUP B THEREFORE NEEDS A DECISION, NOT ONLY CODE. Three honest options, to be presented to the user rather than chosen unilaterally: (a) re-acquire the source PDFs so the audit can classify them properly -- most correct, most work, requires the PDFs to be obtainable; (b) per-document adjudication stamping an honest fidelity value, which is exactly what produced Group A's two working stamps; (c) introduce a new non-quarantined fidelity value meaning second-pipeline conversion with no obtainable baseline and content spot-checked -- a policy change requiring care about what downstream consumers may then cite as authoritative. SCOPE FOR THIS TASK: (1) Fix load_fidelity_map() to derive its directory key from the chunks_dir basename when path is absent, preserving existing sources/ behaviour for the older schema. NOTE load_fidelity_map is duplicated at FOUR sites in literature-search.sh (approx lines 227, 527, 764, 908) -- fix all four or factor to a single definition. (2) Verify Group A: default (no-flag) literature-search.sh must return non-degraded results for wijesekera and simpson content. (3) Preserve fail-open semantics exactly: a missing map entry still defaults to unverified, never verified_conversion. (4) Do NOT silently resolve Group B -- write up options (a)/(b)/(c) with costs and surface them for a user decision. WORKAROUND available meanwhile and already in use: literature-search.sh --include-unverified returns correct results for all 18 today; it is the honest mechanism, being an explicit opt-in to sources that genuinely lack a verified baseline. Do not touch Cslib/ Lean source. === PDF RE-ACQUISITION COMPLETED (user-directed, 2026-07-25): 8 of 18 source files RECOVERED and preserved to $LITERATURE_DIR/.sources-recovered/ (~17MB). Provenance discovered: chunks_dir-schema entries DO carry a source_path field, and it pointed at per-session scratchpad temp dirs under /tmp/claude-*/ for 4 of them -- these were minutes-to-days from deletion and are now durable. RECOVERED (all of this repo's modal-logic working set): arisakadasstrassburger_2015 (the cut-free CS5 source), marinmoralesstrassburger_2021, pacheco_2024, wijesekera_1990, simpson_1994, biermandepaiva_2000, alechinamendlerdepaivaritter_2001, chagrovzakharyaschev_1997 (djvu). NOT RECOVERABLE (10): massacci_2000_single_step_tableaux (relevant to tableau work, source gone), plus 9 unrelated documents (6 hyperproperty/verification papers, 2 Cariani modal-future items, 1 book chapter). Group B is therefore now tractable via option (a) for the 8 recovered: literature-fidelity-audit.sh can classify them against a real baseline once the entries are reachable. The remaining 10 still need option (b) adjudication or (c) a policy value. TWO ADDITIONAL FINDINGS: (i) the real Zotero profile is ~/Documents/Zotero (NOT ~/Zotero, which also exists and is stale/different -- a query against it returns 0 for these titles while the real profile returns hits); (ii) $LITERATURE_DIR/zotero-library.json is a stale/incomplete CSL-JSON export (400 records, dated 2026-07-01, right domain -- Carnap/Kripke/Holliday/Kurucz -- but containing NONE of the 18), so the Better BibTeX 'Keep updated' export is not capturing these items. Re-exporting from the correct profile should precede any future Zotero-based discovery. ALSO: the ingestion pipeline that wrote these entries records source_path into a session-scoped temp dir, which is why the baselines vanished; that pipeline should copy sources into durable storage at ingest time, or this recurs.

---

### 554. Cs5 pair seed disjunction property cutfree research
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [554_cs5_pair_seed_disjunction_property_cutfree_research/reports/02_cutfree-literature-grounded.md]
- **Plan**: [554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md]

**Description**: [RESCOPED 2026-07-26 by explicit user decision, adopting report 02 section 8.] Research on the CS5 pair-seed disjunction property is COMPLETE; two rounds of probes and a literature-grounded assessment are landed. The adopted route is section 8.2's narrow probe plus section 8.1's zero-risk landings. NOTHING ELSE IS IN SCOPE.

LAND NOW (mechanical, no research risk, do these first and independently):
(1) Fix the refutable statement per section 1.1 -- the named Prop CS5PairSeedDisjunctionProperty (Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean) is REFUTABLE AS STATED and needs the `A not-in cl_CS5 (boxInv H)` hypothesis. Land probe_refute_disjunctionProperty as a regression test so the unconditioned form can never be reintroduced.
(2) Land round 1 section 4.1's promotions under the corrected statement: the hOpen <-> hR equivalence, hR -> hL, single-hypothesis derivExcludes, the retraction bound.
(3) Land cs5Axiom_to_is5Axiom / cs5_deriv_to_is5 / cs5_closure_subset_is5_closure -- small, library-grade, load-bearing for the product-model route.
(4) Docstring corrections: [Marin2021] is for IK, not CK, so drop the 'a correct proof is expected to require a cut-free/nested-sequent argument ([Marin2021])' claim; the applicable cut-free system is [ADS15] but at prohibitive cost (section 5.4 cost table); drop 'No semantic witness exists' (the product model is a genuine candidate); correct Non-Goal 2's stated reason.

THEN THE SINGLE PROBE (section 8.2, de-risk R-a before any planning): does every IS5-consistent set have an is5FC model with TOTAL r? This one decidable-by-probe question determines the whole product-model route. If R-a holds, the product construction is ~200-400 lines of standard induction and the task reduces to R-b. If R-a fails, the route is dead and this task closes [BLOCKED] with the section 5.4 cost table as justification -- a negative result is a valid deliverable.

EXPLICITLY NOT ADOPTED, do not re-propose: (a) opening a nested-sequent or labelled-calculus formalisation task (section 8.3, prohibitive cost); (b) the fallback collapse route deriving idb then bridging CS5 -> IS5 -- still not adopted, and section 6 adds an independent reason for wariness, namely that its published basis (Pacheco's CS5 = IS5) rests on the same unsound Lemma 16; (c) the two recorded dead ends (the circular semantic route via pair-axiom soundness, and the signature-collapse retraction).

TWO CONSUMERS: the native-Hilbert pair-Lindenbaum completeness task needs to know whether the named open Prop can be discharged; the labelled CS5 general-soundness task needs to know whether a context-fold that splits compound context facts is derivable without the box-over-disjunction bridge. Report on both explicitly. Machine-checked durable assets from the labelled front live under that task's probes/theta_place_*.lean (all compile clean, no sorryAx).

---

### 553. S4 loop guard soundness reachability restriction
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 535, Task 561, Task 563
- **Plan**:
  - [553_s4_loop_guard_soundness_reachability_restriction/plans/01_s4-settled-context-scheduling.md]
  - [553_s4_loop_guard_soundness_reachability_restriction/plans/02_origin-edge-invariant-revision.md]
  - [553_s4_loop_guard_soundness_reachability_restriction/plans/03_ancestor-only-blocking.md]
  - [553_s4_loop_guard_soundness_reachability_restriction/plans/04_subtractive-blocking-red-channel.md]
  - [553_s4_loop_guard_soundness_reachability_restriction/plans/05_pinned-witness-truth-lemma.md]
- **Research**:
  - [553_s4_loop_guard_soundness_reachability_restriction/reports/01_s4-keyed-guard-soundness-falsified.md]
  - [553_s4_loop_guard_soundness_reachability_restriction/reports/02_redirect-inertness-divergence-audit.md]
  - [553_s4_loop_guard_soundness_reachability_restriction/reports/03_soundness-strength-necessity.md]

**Description**: Determine whether the S4 keyed loop-check guard can be made sound, and if so repair it. This task carries EXPLICIT authorization to edit the otherwise-frozen blockingWorldS4Keyed code that the completeness-line task holds constant. FRAMING MATTERS: this is not 'apply the reachability restriction', it is 'determine whether the guard can be narrowed at all without collapsing the termination argument'. THE DEFECT: blockingWorldS4Keyed (LoopChecking.lean approx 469) picks its blocking world by matching birth-content across ALL recorded worlds, with no reachability restriction to the current label. The redirect then adds a bare edge whose soundness needs the two labels to be related in an arbitrary model. Since the S4 frame condition is reflexive and transitive but NOT symmetric, common-ancestor reachability does not yield relatedness, and the S5 precedent relies on symmetry so it does not transfer. As stated, the keyed S4 soundness theorem is likely FALSE. CANDIDATE FIX: restrict candidates to those reachable via ReflTransGen of the accessibility edge relation. CRITICAL PREDICTION TO VERIFY FIRST, derived from hypothesis shapes and NOT yet confirmed: narrowing the guard may break TERMINATION, not merely completeness. The S4 outputs-subset-universe lemma consumes the world-bound lemma, whose hypotheses are exactly the pigeonhole facts that distinct worlds have distinct keys and that keys are contained in the signed subformulas of the root. Key-distinctness is precisely what the UNRESTRICTED guard buys: under a reachability restriction, two mutually-unreachable worlds with the same birth content could both be born, breaking key-distinctness, the world bound, and hence the termination line. Verify this before committing to any fix; if it holds, the guard cannot simply be narrowed and a different soundness route is required. DOWNSTREAM CONSUMERS deferred here from the completeness-line task: the keyed S4 soundness theorem, its successor phase, and the decidability half of the S4 validity decidability instance, which needs BOTH the soundness and completeness lines and is therefore not achievable until this lands. Evidence: the completeness-line task's report on remaining work and the Phase 9 obstruction, plus the carry-forward risk section of its rescope plan.

---

### 552. Tableau calculus conformance rule completeness repair
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [552_tableau_calculus_conformance_rule_completeness_repair/reports/01_tableau-conformance-rule-completeness.md]
- **Plan**: [552_tableau_calculus_conformance_rule_completeness_repair/plans/01_tableau-conformance-rule-completeness.md]

**Description**: Shared calculus-conformance and rule-completeness repair unblocking BOTH the temporal PTL FMP/decidability front and the propositional tableau completeness front, which independently converged on the same class of defect: a rule set too weak to close valid formulas, combined with fuel machinery justified by a bound that does not hold. DELIVERABLE 1 (shared, do first): a CONFORMANCE HARNESS that executes each tableau on a corpus of known-valid and known-invalid formulas and asserts the verdict. This class of defect is invisible to type-checking and was found only by execution, so the harness is the asset that prevents recurrence. DELIVERABLE 2 (temporal, seriality): the G and H rules propagate only to ord.futureOf t and return .notApplicable when it is empty (Rules.lean approx 227-244), and the only fresh-time path from a negative until is gated on ord.timeCount greater than 0 (Rules.lean approx 312), which is false at the root. Add the missing seriality rule. DELIVERABLE 3 (temporal, time cap): the same timeCount gate hard-caps times at 4; on the valid family with iterated F the verdict flips to OPEN at exactly k=4. Remove the cap. DELIVERABLE 4 (temporal, fuel): temporalFuel equals 4n^2+12n+10 (Saturation.lean approx 78), which is quadratic, while its own docstring justifies it by a 2^n type-count bound. Measured minimal sufficient fuel on a tautology family fits 1.5*2^k-2, so the bound is FALSE at the current constant and merely restating it is not available. Either raise the constant or add the missing deduplication. DELIVERABLE 5 (temporal, trackers): Saturation.lean approx 156-158 returns the tracker unchanged on the .branching arm, so recurring untlPos and sncePos copies are never registered pending. Saturation.lean approx 303 replicates one tracker across all output branches, but untlPos's two branches have genuinely different pending sets, so the return type must become a list of EventualityTracker. DELIVERABLE 6 (propositional): the persistent T-implication rule is positive-only and never plants F-tags, leaving subformula determinacy and bivalence unprovable in the current 6-rule calculus. Add the missing branching rule. Every rule addition requires a soundness re-audit of the affected calculus. Evidence: the executed counterexamples and the measured fuel table are recorded in the temporal task's report on the island-versus-periodic strategic decision. DELIVERABLE 7 (temporal, Finding 2b/2c, promoted to first-class scope in Phase 8): temporalApplyNeg had no asAllFuture?/asAllPast? arms, so G/F duality (¬Gp -> F¬p) and the K-for-G schema were unprovable, and allFuturePosAt/allPastPosAt only checked direct-time membership, missing transitive G/H propagation across someFuture/somePast-created intermediate times (Gp -> GGp, Hp -> HHp, p -> GPp, p -> HFp). The negative arms and a transitive-closure fix for allFuturePosAt landed in Phase 6. A residual asymmetry bug was found in Phase 7: allPastPosAt reused the future-only TimeOrdering.ancestorTimes exactly as allFuturePosAt does, checking whether t is in t_anc's forward light-cone -- correct for propagating T(Gphi) forward, wrong for propagating T(Hphi) backward, which needs the reversed check (t_anc in t's forward light-cone). This left Hp -> HHp open even after Gp -> GGp correctly closed. Fixed by swapping the arguments in allPastPosAt's condition; all Finding 2b/2c rows are now CLOSED as expected.

---

### 551. Cs5 native hilbert pair lindenbaum completeness
- **Effort**: large
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 554
- **Probe**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/probes/cs5-pair-combined-atomsum.lean]
- **Summary**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/summaries/01_native-hilbert-cs5-completeness-summary.md]
- **Research**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/reports/03_remaining-obligations-and-path.md]
- **Plan**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/plans/02_incremental-assets-deferred-route.md]

**Description**: Deliver NATIVE Hilbert canonical-model completeness for constructive CS5 over the fallible-world CKValid semantics (cs5_completeness'' : CKValidFC cs5FC'' phi -> Derivable CS5ModalAxiom phi), uniform with the CK/CT/CS4 column -- NOT via IS5 transport (Route A) or the labelled adequacy bridge (Route C). The single open obstruction is the box-backward truth-lemma case: B's symmetry forces a two-sided canonical relation whose witness is a simultaneous maximal-theory PAIR <H',T> with cross-conditions boxInv H' subseteq T, boxInv T subseteq H' and designated-formula exclusions Box A notin H', A notin T. Landed sorry-free: soundness cs5_axiom_sound'' over cs5FC'' (CS5.lean:366), the symmetric tail with symmetry-by-construction (cs5Tail_symm), the collapse axioms cs5_dia_or (k3) + cs5_dia_bot_imp_bot (k5), and 3 of 4 pair-Lindenbaum ingredients (seed/chain-union/component-maximality, probes/cs5-pair-primeness.lean). Every one-set canonical relation is MECHANICALLY refuted (cs5Incest_cs5CanonMreach_false, cs5Incest_cs5PrimeMreach_false, cs5TwoSidedR_iff_cs5Tail, general monotonicity collapse). Pacheco Lemma 18->16 is UNSOUND here (uses phi notin Theta => neg phi in Theta). The gap is component PRIMENESS of the pair: the natural cross-condition predicate Cons_Y Z := boxInv Z subseteq Y is not cl-stable, so prime_maximal_is_prime (PrimeExclusion.lean:428) does not apply. SKETCHED SOUND REPAIR (not built): encode the pair as a SINGLE quasi-prime theory over the doubled atom space Atom (+) Atom under a combined axiom system that internalises the two cross-condition implications, making them cl-stable by construction, then project back via Sum.inl/Sum.inr. Main risk R1: are the combined cross-condition axioms simultaneously sound and closure-stable without breaking per-component primeness -- de-risk in a probe (cs5-pair-combined-atomsum.lean) before any library edit.

---

### 548. Decidability remaining eight modal cube corners
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 511, Task 535

**Description**: COMPLETENESS-MATRIX GAP (review 2026-07-23, M3). Tableau decidability instances exist for only 6 of the 15 modal-cube systems: K (Tableau/CompletenessLoop.lean:2295), T (FrameCompleteness.lean:1318), KB (:1933), S5 (:2429), K5/Five (:3220), KB5 (:4165); S4 is in flight (tasks 506/511/535 own the loop-checking termination). The 8 remaining corners — D, K4, K45, D4, D5, D45, DB, TB — have sorry-free soundness + strong completeness + compactness + conservative extension but NO Valid predicate, no tableau driver, and no Decidable instance: the decidability column of the cube is ragged. Work (BLOCKED on 511/535 landing the S4 termination machinery): extend the generic tableau driver to the remaining corners — transitive corners (K4, K45, D4, D45) reuse the S4 loop-checking mechanism; serial corners (D, D5, DB) need a serial successor rule; TB composes the existing T and B rules. Where filtration/FMP is cheaper than loop-checking for a given corner, route via FMP instead. Acceptance: either a Decidable instance per corner, or an explicit documented out-of-scope note per corner stating why (e.g. cost/benefit), so the matrix is intentionally complete rather than accidentally ragged. Zero sorry, zero new axioms; keep all frozen deliverables from 300/534/506 untouched.

---

### 537. Labelled cs5 general soundness biconditional
- **Effort**: 15-40 hours
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 554
- **Summary**:
  - [537_labelled_cs5_general_soundness_biconditional/summaries/02_gate-c-blocked-handoff-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/03_phase1-box-dia-iff-base-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/04_phase2-box-dia-iff-tclosure-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/04_phase4-2-boxI-lift-star-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/05_phase3-f2-here-helpers-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/06_phase6-forest-invariant-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/07_phase7-boxI-lift-partial-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/08_phase7-boxI-lift-complete-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/09_phase8-blocked-crosslabel-efq-summary.md]
- **Research**: [537_labelled_cs5_general_soundness_biconditional/reports/05_efq-orE-motive-defect-and-path.md]
- **Plan**: [537_labelled_cs5_general_soundness_biconditional/plans/06_target-independent-theta-translation.md]

**Description**: Prove the general labelled SOUNDNESS direction nik_TS5_soundness : NIKTheorem TS5 phi -> CKValidFC cs5FCIncest phi, completing Simpson 1994 Thm 8.1.4's biconditional for CSLib constructive CS5/IS5. CONTEXT (from parent task 517, which delivered the completeness direction): cs5_completeness (Completeness.lean:132) and the anti-vacuity certificate nik_TS5_consistent + nik_soundness_onePoint (Soundness.lean) are LANDED sorry-free/axiom-clean. cs5FCIncest_lift (Soundness.lean:181) is a landed building block. THE OPEN OBSTRUCTION (established across 3 dispatches, no forced sorry): TS5={T,B,Four} makes TClosure TS5 G.R the TOTAL relation on the always-connected derivation graph, so the box edge-condition is an r-CLIQUE condition across all labels, not tree-adjacency; and cs5FCIncest's hfour/hsymbox/hincest conjuncts only ever produce EXISTENTIALLY-raised relational witnesses, whereas CKForces's box clause (and boxE) need EXACT edges/symmetry between independently-fixed points (persistence is only upward). No asymmetric countermodel refuted the obstruction; no closure proof completed it -- GENUINELY OPEN. THREE CANDIDATE STRATEGIES (ranked; none is a plain direct-implementation dispatch -- each needs research/re-plan): (1) prove cs5FCIncest forces symmetric/clique closure on finitely-generated substructures -- cheapest, possibly reuses the FLO closure machinery from parent Phases 1-7; (2) formalize Simpson's own modified sequent system L_m(TS5, empty), his stated fix for exactly this problem; (3) build the deferred Simpson Ch.6 Hilbert-labelled ADEQUACY bridge (NIKTheorem TS5 phi -> Derivable CS5ModalAxiom phi) and obtain labelled soundness as a corollary of the already-landed Hilbert soundness cs5_soundness_derivable_incest (CS5Canonical.lean:373) -- note this resurrects the bridge task 517 deliberately avoided (Track C, C5 'THE TRUE CRUX'). Full analysis: specs/517_labelled_bounded_context_cs5_completeness/handoffs/phase-11-general-soundness-blocked-20260719c.md and Soundness.lean's refined-analysis docstring. CONSTRAINTS: NO sorry, NO new axiom under Cslib/; do not weaken cs5FCIncest; do not regress parent's landed completeness/anti-vacuity. Research MUST use --lit (Simpson Ch 8 soundness, Lifting Lemma 8.1.3, L_m modified sequent system). BibKeys: Simpson1994, MarinMoralesStrassburger2021. HIGH uncertainty (the direct route may be genuinely open). Start with strategy (1) as a research/probe pass before committing. Depends on 517.

---

### 534. Pure K5/5 Euclidean tableau completeness without the equivalence route
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 531

**Description**: COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree (instDecidableFiveValid/instDecidableKb5Valid, FrameCompleteness.lean) is delivered via the KB5/S5 equivalence route, which leans on a full-equivalence closure. This task delivers genuine pure-K5 / pure-5 (Euclidean without full equivalence, no Mathlib closure operator) tableau soundness + completeness + decidability - the one modal-cube corner explicitly deferred out of the completed KB5/Euclidean task. Mirror the existing Five/KB5 development but over the bare Euclidean frame condition. Zero sorry, zero new axioms; keep the frozen equivalence-route deliverables untouched.

---

### 530. Consolidate the duplicated Chronicle construction across Bimodal and Temporal
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Research**: [530_consolidate_chronicle_construction_bimodal_temporal/reports/01_chronicle-dedup-research.md]
- **Plan**: [530_consolidate_chronicle_construction_bimodal_temporal/plans/01_chronicle-consolidation.md]
- **Summary**: [530_consolidate_chronicle_construction_bimodal_temporal/summaries/01_chronicle-consolidation-summary.md]

**Description**: REDUNDANCY CLEANUP. Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ and Cslib/Logics/Temporal/Metalogic/Chronicle/ are two nearly-identical full trees sharing 8 filenames (ChronicleConstruction, ChronicleToCountermodel, ChronicleTypes, CounterexampleElimination, PointInsertion, RRelation, ...) with ~89% overlap. The partial task-454 consolidation already lifted PointInsertion; extend that: factor the shared chronicle/countermodel-elimination machinery into a label-generic module under Cslib/Foundations/Logic/Metalogic/Chronicle/ (which currently holds only SinceSeedConsistency.lean) and have both the bimodal and temporal trees instantiate it. Preserve all landed sorry-free results; this is a structural dedup, not a proof change. Watch the bimodal discrete-completeness sorries (blocked on external port) - do not entangle them. [USER SCOPING DECISION 2026-07-26 -- path (B), descope]: phases 3b, 3c, 4a and 4b are DESCOPED. Do not attempt further generic lifting of c5ForwardWalk / c5BackwardWalk, the Phase 3c elimination driver, or Phase 4a/4b ChronicleConstruction. Two deep investigations (Phase 1 and Phase 3b) independently confirmed that generically bridging types indexed by each tree's LOCAL Chronicle Atom structure breaks downstream rcases/simp proofs, and repairing that exceeds this task's own 'structural dedup, not a proof change' mandate. Keep every landed lift (ChronicleInterface skeleton, generic Types, RRelation shared core, CEE Structures + BurgessHelpers -- all sorry-free, committed, full lake test green), run Phase 5 cleanup, annotate the plan file's 3b-4b headings as [DESCOPED] with a pointer to this decision, and close as a partial consolidation. Run /revise first to produce the descoped plan version, then /implement. The deeper Chronicle-structure question -- what the highest-quality refactor actually is, given that the walk-result types are structurally the obstacle -- is carried by a dedicated follow-on research task and is NOT to be attempted here.

---

### 519. Fix literature ocr chunking and wijesekera
- **Effort**: 3-5 hours
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: Literature
- **Dependencies**: Task 518
- **Research**: [519_fix_literature_ocr_chunking_and_wijesekera/reports/01_wijesekera-ocr-chunking-fix.md]
- **Plan**: [519_fix_literature_ocr_chunking_and_wijesekera/plans/01_wijesekera-reingest-ocr-hardening.md]
- **Summary**: [519_fix_literature_ocr_chunking_and_wijesekera/summaries/01_wijesekera-reingest-summary.md]

**Description**: Follow-up to task 518 (Simpson re-ingest). TWO PARTS.

(1) RE-INGEST wijesekera_1990_constructivemodallogicsi (BibKey Wijesekera1990). Task 518's corpus audit found it has the IDENTICAL over-fragmentation signature that made Simpson unusable: 154 chunks, 468B mean, 62% under 300B. This document matters -- Wijesekera 1990 is THE source for CSLib's constructive (fallible-world) DIAMOND semantics, cited in Cslib/Logics/Modal/Metalogic/Constructive/ (CS4.lean and CS5.lean docstrings reference it for Definition 1.1.4 and Section 2), and is directly relevant to in-flight task 517. Apply task 518's proven fix (documented in specs/518_reingest_simpson1994_literature_corpus/summaries/01_reingest-summary.md): bypass the font-size heading heuristic, extract via pdftotext -layout, apply paragraph-reflow to repair OCR line-break noise, insert chapter/section-level headings only, then feed the existing unmodified literature-chunk.sh Pass-2 merge. VALIDATE that Definition 1.1.4 and the Section 2 diamond / fallible-world definitions return COMPLETE statements via literature-search.sh. Preserve the old chunk set as rollback, as 518 did.

(2) HARDEN THE ROOT CAUSE (the general fix that 518 deliberately left undone). literature-convert.sh's PyMuPDF path falls back to a FONT-SIZE heading-detection heuristic when a PDF has no embedded TOC. On OCRmyPDF/Tesseract scans the per-line font metrics are noisy, so it emits spurious markdown headings mid-sentence and mid-word, and literature-chunk.sh then splits at every one -- shredding lemma statements. Fix so it does not fire on OCR'd scans: detect the OCR producer (Tesseract / OCRmyPDF metadata), require corroborating cues (line length, position, numbering, blank-line context) before accepting a font-size heading, and/or add a post-check rejecting headings that split mid-sentence. ALSO add a guard so any future ingest yielding a pathological mean chunk size (under roughly 600B) warns loudly rather than silently landing a shredded corpus. Task 518 scoped its fix to Simpson only and left the shared scripts untouched; this task does the general repair so all future --lit work benefits.

NOTE the honest ceiling from 518: prose is recoverable but math symbols are frequently garbled by Tesseract. Do NOT attempt to fix OCR quality itself -- only the chunking/heading pathology. Do not touch Cslib/ Lean source. Low risk, high leverage.

---

### 511. S4 loop checking termination
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 535, Task 561, Task 563
- **Plan**: [511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md]
- **Research**:
  - [511_s4_loop_checking_termination/reports/01_s4-termination-guard-redesign.md]
  - [511_s4_loop_checking_termination/reports/02_spawn-analysis.md]
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
- **Dependencies**: Task 393, Task 425, Task 449, Task 535, Task 542

**Description**: Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (Proposition.imp constructor and → notation) with the rest of the library once PR #607 lands, so the propositional connective naming is consistent library-wide (noting Modal uses 'impl'). Raised in review of PR #648 by thomaskwaring. BLOCKED until #607 (external PR, leanprover/cslib) is merged.

---

### 466. Record zulip settlement pr 648
- **Status**: [PR READY]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: None
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
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Research**: [463_vet_299_455_doc_touchups/reports/01_organisation-tableau-and-docstring-cleanup.md]
- **Plan**: [463_vet_299_455_doc_touchups/plans/01_organisation-tableau-docstring-anchors.md]
- **Summary**: [463_vet_299_455_doc_touchups/summaries/01_organisation-tableau-docstring-anchors-summary.md]

**Description**: Vet found low-severity documentation gaps (code placement itself is correct/idiomatic): (1) ORGANISATION.md:148 Modal/ tree sketch omits the `Tableau/` subdirectory; ORGANISATION.md:26 Foundations/Logic/ tree sketch omits `Tableau/` (Sign.lean, SignedFormula.lean, RuleResult.lean, Branch.lean, Closure.lean, ClosureCondition.lean, Measure.lean, PropositionalRules.lean) — add these entries to document existing placement. (2) Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:1178 and nearby: permanent public docstrings for `modalTableau_complete`/`modalTableau_decides` embed ephemeral internal notes like '(task 442 Phase 6, FINAL)', '(task 442 Phase 5a)' — replace with plain, durable mathematical descriptions.

---

### 456. Shared tableau containment blocking
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Tableau Infrastructure
- **Dependencies**: Task 317

**Description**: Generalize the Sfor-containment / subset-blocking device recurring across tableau developments into a single label-generic module Cslib/Foundations/Logic/Tableau/Blocking.lean, built on the existing Branch.formulasAt (Foundations/Logic/Tableau/Branch.lean:81). Lift Temporal's timeType/isSubsetBlocked/isTemporallyBlocked (Temporal/Tableau/Branch.lean:101-174) and task 317's Sfor/containment check to: Branch.typeAt (deduplicated (Sign x F) forced-type at a label), Branch.containmentBlocked (containment test), and the once-proven core lemma Tableau.distinctTypes_le_pow ((b.labels.map b.typeAt).eraseDups.length <= 2^U.length for a subformula-closed universe U). Highest-value payoff: distinctTypes_le_pow is the shared core of BOTH task 317's intExpandBranches_world_bound_dedup (plan 04 Phase 5.1) AND the currently-[BLOCKED] Temporal soundness obligation (Temporal/Tableau/Soundness.lean:23-54, '<= 2^n time types' / loop-detection) - proving it once could unblock Temporal Phase 7. The definitional lift is cheap; the soundness lemma (blocking => bounded => countermodel) is the hard part, but hard exactly once instead of 2-3 times. DEPENDS ON task 317 landing first (so the (psi not in forced(x)) side-condition shape is settled); ideally co-scoped with the Temporal soundness unblock. Also add missing references.bib entries GargGenoveseNegri2012 and DershowitzManna1979 (ready in report 05 Q4). Source: task 317 reuse/abstraction research report 06 (R2). Verify scoped + full lake build green, checkInitImports/lint-style/shake pass, zero sorry.

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

### 440. Review pr leanprover cslib 648
- **Status**: [PR READY]
- **Task Type**: pr
- **Topic**: PR & Upstreaming
- **Dependencies**: None
- **Research**: [440_review_pr_leanprover_cslib_648/reports/01_pr-review-research.md]
- **Plan**: [440_review_pr_leanprover_cslib_648/plans/01_ctchou-review-response.md]
- **Pr_response**: [440_review_pr_leanprover_cslib_648/pr-response.md]

**Description**: PR review: GitHub PR https://github.com/leanprover/cslib/pull/648 — address ctchou CHANGES_REQUESTED feedback (Gentzen/Avigad references, Semantics restructuring confirmation, reviewer reply, coordinate #587/#607)

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
- **Dependencies**: Task 552
- **Plan**:
  - [425_temporal_tableau_ptl_fmp_decidability/plans/03_validity-corrected-fmp-plan.md]
  - [425_temporal_tableau_ptl_fmp_decidability/plans/01_ptl-fmp-decidability-plan.md]
- **Summary**: [425_temporal_tableau_ptl_fmp_decidability/summaries/01_ptl-fmp-summary.md]
- **Research**: [425_temporal_tableau_ptl_fmp_decidability/reports/04_island-vs-periodic-strategic-decision.md]

**Description**: [Decomposed from the temporal tableau umbrella, blocker C.] BLOCKER CLEARED 2026-07-26: the shared conformance/rule-completeness repair this was gated on is COMPLETE. It landed the per-branch eventuality tracker (temporalStepBranch now returns one tracker per output branch, so untlPos's branch1/branch2 genuinely diverge in their pending sets), the temporal rule arms (seriality, G/H duality, transitive propagation), cap removal and fuel raise, and fixed two real directional defects in ancestorTimes / allPastPosAt. Cslib/Logics/Temporal/Tableau/Completeness.lean:127-140 now marks remaining-work items 1, 2 and 2a as Done. REMAINING SCOPE, restated: prove the fuel-sufficiency/pigeonhole theorem -- that temporalFuel guarantees isSubsetBlocked holds among a fuel-exhausted branch's own labels whenever pending eventualities remain. That is the sole prerequisite for wiring extractModelZPeriodic / periodicReducePast in as the real extractModelZ, and then discharging temporalTruthLemma_untl / _snce, openBranch_branchSat, eventualityDefect_unsat, temporalTableau_sound, temporalTableau_complete and the final instDecidableValid. NOTE THIS IS A DISTINCT OBLIGATION from the intuitionistic persistence-fixpoint fuel measure (that one is closed); do not conflate them. Mirror COMPLETED task 421 (min_fmp_decidability), which added a sorry-free Decidable instance via FMP -- reuse its pattern where possible. RESEARCH FIRST: Completeness.lean:138-140 explicitly recommends a dedicated research pass before further planning; run /research before /plan. Gates the temporal tableau umbrella.

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

### 409. Literal ⊥-rule-free base ND inductive (option B): split MinDerivation + Explosion; re-cut Curry-Howard & normalization
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 407
- **Research**: [409_bot_rule_free_nd_option_b/reports/01_bot-free-nd-option-b-research.md]

**Description**: SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- OPTIONAL / advanced. Task 407 adopts option C (re-frame the task-398 gated efq constructor as the explosion property module; the base relation is ⊥-rule-free UP TO the IsIntuitionistic gate). Option B is the LITERAL structure-first ND: split Theory.Derivation into a genuinely ⊥-rule-free base inductive MinDerivation (no efq constructor) plus an Explosion extension, prove all structural metatheory once on the base, and recover IPL-ND by adjoining efq. TRIGGER CONDITION: only pursue if a concrete downstream consumer needs a physically ⊥-free derivation object (e.g. a minimal-ND normalization theorem, or a lambda-calculus without an abort/efq combinator). COST/RISK: re-opens the single genuinely hard point from task 398 -- the subformula property under efq -- and forces re-cutting Curry-Howard (Theory.Term mirror) and Prawitz normalization (Basic/Reduction/Termination/SubformulaProperty) against the split. Reuse the task-398 decided strategy (atomic restriction + permutation conversions); treat any non-green proof as [BLOCKED], never sorry. HIGH effort -- use --hard. Depends on 407 (and ideally 408). Source: task 407 report 01 §5 option B / §7 W6, report 02 §5. ALIGNMENT NOTE: this two-inductive split is the Design-B-flavored route that the universal-algebra approach (task 407 option C) deliberately AVOIDS, because it duplicates derivation structure (exclude-then-add at the derivation level). Default remains task 407 option C: ONE derivation type with explosion as a property module. Pursue 409 ONLY if the trigger condition above fires.

---

### 400. Unbundle connective typeclasses; reconcile with fmontesi PR #607 (Waring's flag a)
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 465
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
- **Dependencies**: Task 552
- **Plan**:
  - [plans/03_b2-fuel-sufficiency.md]
  - [317_propositional_tableau_completeness/plans/01_tableau-completeness-plan.md]
  - [317_propositional_tableau_completeness/plans/02_tableau-completeness-unified.md]
  - [317_propositional_tableau_completeness/plans/03_b2-fuel-sufficiency.md]
  - [317_propositional_tableau_completeness/plans/04_sfor-dedup-fuel-sufficiency.md]
  - [317_propositional_tableau_completeness/plans/05_frame-change-and-fuel-raise.md]
  - [317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md]
  - [317_propositional_tableau_completeness/plans/11_tableau-completeness-assembly.md]
  - [317_propositional_tableau_completeness/plans/12_world-bound-prereq-threading.md]
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
  - [317_propositional_tableau_completeness/summaries/11_tableau-completeness-assembly-summary.md]
- **Handoff**:
  - [317_propositional_tableau_completeness/handoffs/11_phase0-spike-decisions.md]
  - [317_propositional_tableau_completeness/handoffs/11_phase2-blocker-findings.md]
- **Research**:
  - [317_propositional_tableau_completeness/reports/01_tableau-completeness-research.md]
  - [317_propositional_tableau_completeness/reports/03_tableau-completeness-approach.md]
  - [317_propositional_tableau_completeness/reports/04_fuel-sufficiency-measure.md]
  - [317_propositional_tableau_completeness/reports/05_fuel-sufficiency-literature.md]
  - [317_propositional_tableau_completeness/reports/06_sfor-dedup-reuse-abstraction.md]
  - [317_propositional_tableau_completeness/reports/07_option-b-fuel-bound.md]
  - [317_propositional_tableau_completeness/reports/08_b1-truthlemma-timp.md]
  - [317_propositional_tableau_completeness/reports/09_phase2-escape-routes.md]
  - [317_propositional_tableau_completeness/reports/10_wave-a-atomic-derisk.md]
  - [317_propositional_tableau_completeness/reports/11_team-research.md]

**Description**: Fill the remaining propositional/intuitionistic tableau completeness sorries. BOTH HISTORIC BLOCKERS ARE NOW CLOSED (verified 2026-07-26 against the code, not against prior notes): Gap 2 (Sub(phi0) determinacy/bivalence) is RESOLVED -- the shared conformance/rule-completeness repair landed the `.pos, .imp` branching arm at Rules.lean:274-275 producing [[F(phi)], [T(psi)]], and Scheme.lean:581 records the resolution in-code. Gap 1 (fuel sufficiency for the persistence fixpoint) is RESOLVED -- `applyPersistenceFixpoint_genuine_of_count_le_fuel` is landed sorry-free at Scheme.lean:2907, with `intUniverse_length_le` giving the polynomial fuel bound. REMAINING SCOPE IS ASSEMBLY ONLY, and now also absorbs the separately-tracked sat_timp task (removed as a duplicate; its file pointer was wrong): (1) add the `sat_timp` field to `IBranchSaturation` and discharge it at its sole construction site `IExpandedConsistent_sat`, consuming the genuine-fixpoint lemma; (2) close truthLemma's T-imp case at Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:592; (3) close the fuel=0 base case of `intExpandBranches_openBranch_sat` at Scheme.lean:1498; (4) close the two IValid/MValid bridges at Intuitionistic/Completeness.lean:133 and Minimal/Completeness.lean:125. Because the int and min tableaux are parameterized over (closurePred, modelBot), discharge the truth-lemma/countermodel pair ONCE parametrically rather than duplicating. MANDATORY DOCSTRING REPAIR: the block at Scheme.lean:~3000 ('GAP 2 investigation ... determinacy remains BLOCKED') is STALE and contradicts line 581; it predates the branching-rule landing and will re-block a future dispatch that reads it. Correct or delete it as part of this task. The tableau Decidable instances become genuinely sorry-free once these land. No new axioms; Cslib/ bare-sorry count must go DOWN; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake); the 43-row CslibTests/TableauConformance.lean regression guard must stay green.

---

### 301. Temporal tableau
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 425
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
  - [226_propositional_semantics_upstream_pr/reports/03_upstream-packaging-research.md]

**Description**: Cherry-pick propositional semantics from the local codebase into a <500 LOC follow-up PR stacked on PR #648. PR #648 contributes the formula type and natural deduction; this follow-up adds the semantics layer. Scope: (1) Semantics/Algebra.lean — GHA evaluation with bot_val parameter for minimal/intuitionistic/classical logic. (2) Semantics/Bool.lean — BoolEvaluate with bridge to AlgEvaluate. (3) Semantics/SemanticConsequence.lean — semantic consequence and tautology definitions. (4) Semantics/Kripke.lean — Kripke semantics with botForces for minimal logic (include if LOC budget permits). All four files already exist locally with full implementations. Task is to select, trim, and package for upstream submission. Ensure lake build, lake test, lake exe checkInitImports, lake exe lint-style, and lake shake all pass on the PR branch. Write PR description referencing the Zulip Propositional Logic thread.

---

### 215. Fill the discrete-gated Bimodal sorries (BXCanonical Chronicle and Frame)
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 36
- **Research**: [215_fill_bimodal_sorries/reports/01_sorry-analysis.md]

**Description**: Fill the discrete-gated sorry declarations in Cslib/Logics/Bimodal/Metalogic/:
- BXCanonical/Chronicle/ChronicleToCountermodel.lean: 12 sorries (lines 75, 145, 146, 152, 157, 162, 172, 173, 174, 175, 176, 187)
- BXCanonical/Frame.lean: 1 sorry (line 161)

All are gated on the discrete completeness pipeline (discrete_embed_strictMono, gap_contradicts_prior, the discrete FMCS construction), which the discrete port task delivers. Counts above are as measured 2026-07-26, superseding the earlier asserted figures. The strict-Until/Since sorries are tracked separately. Note: countermodel_dense (ChronicleToCountermodelBasic.lean:825) and completeness_dense (Dense.lean:122) were carved off previously and remain out of scope.

---

### 181. Bimodal primitive dia always historically
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 180, Task 393
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
- **Dependencies**: None

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic. This task is blocked pending upstream development of continuous frame completeness.

**Source**: Not yet developed in BimodalLogic
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic continuous extension development
**Parent task**: 8 (expanded)

---

### 36. Port discrete completeness bimodal
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Bimodal Logic
- **Dependencies**: None

**Description**: Port discrete completeness (completeness_discrete) from upstream BimodalLogic. EXTERNAL BLOCKER CLEARED 2026-07-26 (verified directly against the upstream working tree, not against prior notes): upstream Theories/Bimodal/Metalogic/BXCanonical/Completeness.lean:302 now documents completeness_discrete as sorryAx-free, with #print axioms giving exactly [propext, Classical.choice, Quot.sound]. The chain this task was blocked on (chronicle_gap_contradiction -> succ_cofinal -> limitDomSubtype_isSuccArchimedean -> succ_embed_surjective) was DEAD CODE on no live call path and has been archived upstream to Boneyard/DeadChronicleGapElimination/. succ_cofinal itself remains provably unfixable (Z+Z counterexample) and is correctly bypassed. SCOPE HAS CHANGED -- DO NOT PORT FROM THE OLD DESCRIPTION. The live discrete path is countermodel_discrete_reynolds_v2 (WeakCanonical/IntegerModel/ReynoldsBridge.lean:739) -> limitdom_is_good -> no_gaps_discrete_model_surgery -> US_expressively_complete_over_prior -> kamp_prior_expressive_completeness -> nf_characterizable_temporal_prior -> nf_nvar_exist_all_depths, with the formerly-sorry |_k+2 arm retired by the zeta wire kampArm_zeta (ZetaUniformExtract.lean, the unary E[Sigma]-atom re-architecture of Rabinovich Def 4.1 / Prop 4.3 / Thm 4.4). The port surface is therefore ReynoldsBridge + the Kamp/KampPrior/ZetaUniformExtract cluster, NOT the '~6 IntegerModel files' originally scoped. Note that IntegerModel/GoodStructuresModelSurgery.lean still carries two sorries (gap_prior_UZ_contradiction / gap_prior_SZ_contradiction, Reynolds Lemmas 6-13) -- confirm at port time whether the live path depends on them or whether they sit on the alternative route. RUN /research AND /revise BEFORE /implement: the port map must be re-derived against the current upstream tree before any plan is written. Target: Cslib/Logics/Bimodal/Metalogic/. Unblocks 12 of the bimodal sorries and the temporal discrete completeness task.
