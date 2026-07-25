---
next_project_number: 556
---

# TODO

## Task Order

*Updated 2026-07-25. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,226,400,409,440,465,466,511,530,534,552,553,554,555 | -- | propositional logic, modal logic, bimodal logic, ... |
| 2 | 39,40,215,317,425,450,506,537,548,551 | 36,37,181,511,552,554 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41,300,301,375,430,456,497 | 39,40,317,425,506 | foundations, propositional logic, modal logic, ... |
| 4 | 413,414 | 181,215,300,301,375 | code hygiene |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
400 [BLOCKED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
409 [RESEARCHED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
317 [BLOCKED] — Fill the propositional tableau completeness sorries (7 real sorri
  └─ 375 [NOT STARTED] — Fold the TABLEAU decision systems into the propositional proof-sy
  └─ 430 [PLANNED] — Prove the atom-persistence / upward-closure structural lemma for 
497 [NOT STARTED] — Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (P

### Modal Logic

511 [BLOCKED] — Follow-on to task 506 (S4 loop-checking): close the S4 terminatio
  └─ 506 [BLOCKED] — Deliver plan Phases 5 and 6 of task 300 combined (specs/300_modal
    └─ 300 [BLOCKED] — Umbrella task for modal frame extensions T/S4/S5 (and the derived
  └─ 548 [NOT STARTED] — COMPLETENESS-MATRIX GAP (review 2026-07-23, M3). Tableau decidabi
534 [NOT STARTED] — COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree 
552 [PARTIAL] — Shared calculus-conformance and rule-completeness repair unblocki
553 [PARTIAL] — Determine whether the S4 keyed loop-check guard can be made sound
554 [PARTIAL] — Research-only task: establish or refute the CS5 pair-seed disjunc
  └─ 537 [BLOCKED] — Prove the general labelled SOUNDNESS direction nik_TS5_soundness 
  └─ 551 [BLOCKED] — Deliver NATIVE Hilbert canonical-model completeness for construct

### Temporal Logic

39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic
301 [BLOCKED] — Implement tableau decision procedure for temporal logic (Cslib.Lo
425 [BLOCKED] — [Decomposed from task 301, blocker C.] Establish the finite model
  └─ 301 [BLOCKED] — Implement tableau decision procedure for temporal logic (Cslib.Lo (see above)

### Bimodal Logic

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 
  └─ 450 [NOT STARTED] — Core corrected conservativity result. PR-BLOCKING for task 180. S

### Code Hygiene

530 [BLOCKED] — REDUNDANCY CLEANUP. Cslib/Logics/Bimodal/Metalogic/BXCanonical/Ch
413 [NOT STARTED] — Simplify verbose Propositional/ proofs (manual simp only [listImp
414 [NOT STARTED] — Simplify verbose Modal/, Temporal/, and Bimodal/ proofs (manual s

### Pr & Upstreaming

440 [PR READY] — PR review: GitHub PR https://github.com/leanprover/cslib/pull/648
465 [PR READY] — Review PR #607 (logical operators): post GitHub review covering t
466 [PR READY] — Post comment on PR #648 linking the Zulip primitive-bot plus efq 

### Tableau Infrastructure

456 [NOT STARTED] — Generalize the Sfor-containment / subset-blocking device recurrin

### Uncategorized

555 [PARTIAL] — Repair literature search visibility for index entries written und

## Tasks

### 555. Literature search fidelity schema quarantine
- **Status**: [PARTIAL]
- **Task Type**: general
- **Dependencies**: None
- **Research**: [555_literature_search_fidelity_schema_quarantine/reports/01_fidelity-schema-key-derivation.md]
- **Plan**: [555_literature_search_fidelity_schema_quarantine/plans/01_fidelity-key-derivation-and-legacy-audit.md]
- **Summary**: [555_literature_search_fidelity_schema_quarantine/summaries/01_fidelity-key-derivation-summary.md]

**Description**: Repair literature search visibility for index entries written under the doc_id/chunks_dir schema. MEASURED SITUATION (all figures verified directly, not inferred): the global Literature index.json carries two entry schemas -- 273 entries with id + path="sources/<dir>/", and 18 with doc_id + chunks_dir=<absolute path>. literature-search.sh's load_fidelity_map() derives its lookup key ONLY from a path prefix of "sources/", so no chunks_dir-schema entry ever lands in the map; get_fidelity() then fail-opens to unverified_summary, which is on QUARANTINED_FIDELITY_VALUES (literature-search.sh:53), so default search drops them and reports degraded=true with zero results. THE 18 SPLIT INTO TWO GROUPS THAT NEED DIFFERENT FIXES. GROUP A (2 docs: wijesekera_1990_constructivemodallogicsi, simpson_1994_intuitionisticmodallogic) already carry an honest, human-adjudicated stamp provenance_fidelity=ocr_rescanned_reflowed_partial_symbol_loss, which is NOT on the quarantine list. These are invisible purely because of the key-derivation bug -- their correct fidelity value exists in index.json but is unreachable. Fixing key derivation alone fully restores them. This is the tractable half and should ship first. GROUP B (16 docs, including arisakadasstrassburger_2015, marinmoralesstrassburger_2021, pacheco_2024, biermandepaiva_2000, alechinamendlerdepaivaritter_2001, chagrovzakharyaschev_1997, massacci_2000, plus 8 unrelated hyperproperty/verification docs) have provenance_fidelity=null. After the key-derivation fix, fmap.get(doc_id) still returns null and get_fidelity still fail-opens to unverified_summary, so they REMAIN quarantined. The key fix does nothing for them. CRITICAL CONSTRAINT ON GROUP B -- do not plan to solve this by extending literature-fidelity-audit.sh: that script classifies by comparing converted markdown against pdftotext output of the source PDF, and these directories contain only chunk_*.md files with NO source PDF present (verified for arisaka, wijesekera, pacheco), and zotero-library.json has no matching entries either. With no baseline available the audit's own honest verdict would be unverified_no_baseline, which is ITSELF on the quarantine list -- so an extended audit would correctly re-quarantine them and change nothing. The fail-open-to-unverified design is deliberate and correct (it prevents an unverified conversion being cited as authoritative) and MUST NOT be weakened by simply removing values from QUARANTINED_FIDELITY_VALUES. GROUP B THEREFORE NEEDS A DECISION, NOT ONLY CODE. Three honest options, to be presented to the user rather than chosen unilaterally: (a) re-acquire the source PDFs so the audit can classify them properly -- most correct, most work, requires the PDFs to be obtainable; (b) per-document adjudication stamping an honest fidelity value, which is exactly what produced Group A's two working stamps; (c) introduce a new non-quarantined fidelity value meaning second-pipeline conversion with no obtainable baseline and content spot-checked -- a policy change requiring care about what downstream consumers may then cite as authoritative. SCOPE FOR THIS TASK: (1) Fix load_fidelity_map() to derive its directory key from the chunks_dir basename when path is absent, preserving existing sources/ behaviour for the older schema. NOTE load_fidelity_map is duplicated at FOUR sites in literature-search.sh (approx lines 227, 527, 764, 908) -- fix all four or factor to a single definition. (2) Verify Group A: default (no-flag) literature-search.sh must return non-degraded results for wijesekera and simpson content. (3) Preserve fail-open semantics exactly: a missing map entry still defaults to unverified, never verified_conversion. (4) Do NOT silently resolve Group B -- write up options (a)/(b)/(c) with costs and surface them for a user decision. WORKAROUND available meanwhile and already in use: literature-search.sh --include-unverified returns correct results for all 18 today; it is the honest mechanism, being an explicit opt-in to sources that genuinely lack a verified baseline. Do not touch Cslib/ Lean source. === PDF RE-ACQUISITION COMPLETED (user-directed, 2026-07-25): 8 of 18 source files RECOVERED and preserved to $LITERATURE_DIR/.sources-recovered/ (~17MB). Provenance discovered: chunks_dir-schema entries DO carry a source_path field, and it pointed at per-session scratchpad temp dirs under /tmp/claude-*/ for 4 of them -- these were minutes-to-days from deletion and are now durable. RECOVERED (all of this repo's modal-logic working set): arisakadasstrassburger_2015 (the cut-free CS5 source), marinmoralesstrassburger_2021, pacheco_2024, wijesekera_1990, simpson_1994, biermandepaiva_2000, alechinamendlerdepaivaritter_2001, chagrovzakharyaschev_1997 (djvu). NOT RECOVERABLE (10): massacci_2000_single_step_tableaux (relevant to tableau work, source gone), plus 9 unrelated documents (6 hyperproperty/verification papers, 2 Cariani modal-future items, 1 book chapter). Group B is therefore now tractable via option (a) for the 8 recovered: literature-fidelity-audit.sh can classify them against a real baseline once the entries are reachable. The remaining 10 still need option (b) adjudication or (c) a policy value. TWO ADDITIONAL FINDINGS: (i) the real Zotero profile is ~/Documents/Zotero (NOT ~/Zotero, which also exists and is stale/different -- a query against it returns 0 for these titles while the real profile returns hits); (ii) $LITERATURE_DIR/zotero-library.json is a stale/incomplete CSL-JSON export (400 records, dated 2026-07-01, right domain -- Carnap/Kripke/Holliday/Kurucz -- but containing NONE of the 18), so the Better BibTeX 'Keep updated' export is not capturing these items. Re-exporting from the correct profile should precede any future Zotero-based discovery. ALSO: the ingestion pipeline that wrote these entries records source_path into a session-scoped temp dir, which is why the baselines vanished; that pipeline should copy sources into durable storage at ingest time, or this recurs.

---

### 554. Cs5 pair seed disjunction property cutfree research
- **Status**: [PARTIAL]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [554_cs5_pair_seed_disjunction_property_cutfree_research/reports/02_cutfree-literature-grounded.md]
- **Plan**: [554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md]

**Description**: Research-only task: establish or refute the CS5 pair-seed disjunction property, which is the single remaining obligation of the native-Hilbert CS5 completeness route. THE OBLIGATION, already isolated sorry-free as a named Prop in Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean, is the seed-exclusion statement that the left-tagged box of A joined with the right-tagged A is not in the closure of the two-sided seed. Equivalently it is the constructive disjunction property of the pair axiom set under the box-inverse cross-constraint. This is Pacheco 2024 Lemma 16, which is UNSOUND AS PUBLISHED, and it has NO semantic witness. TWO DEAD ENDS, recorded as Non-Goals, must not be re-proposed: the semantic route via pair-axiom soundness is circular because it presupposes the truth lemma being built; and the signature-collapse route via a sum-elimination retraction fails because the first cross axiom's image, box B implies B, is not an instance of the modal axiom schema, so the retraction is not schema-compatible. RECOMMENDED APPROACH: a cut-free or nested-sequent proof system for CS5, following Marin, Morales and Strassburger 2021 on fully labelled proof systems for intuitionistic modal logics, and Arisaka, Das and Strassburger 2015 on nested sequents for constructive modal logics. Both are present in the literature corpus. The aim is to repair Pacheco Lemma 16 and 17, or to establish that the property fails. REPORTING CONTRACT: deliver either (a) a proof strategy concrete enough to discharge the named Prop, or (b) a refutation with a countermodel, or (c) a reasoned statement that the property is open, with the specific obstruction named. A negative or open result is a valid and useful deliverable. FALLBACK if the property is refuted or judged unreachable: the deferred collapse route, which proves that CS5 derives the idb axiom (currently absent from every constructive CS5 file), then the CS5-to-IS5 derivability and validity bridges, composing the already-landed IS5 completeness theorem. Adopting that route is a mandate change requiring explicit user authorization. Evidence: the parent task's reports on the conservativity blocker route decision and on remaining obligations and path.  SECOND CONSUMER (widened brief): this research also gates the labelled CS5 general-soundness biconditional task, which hit the SAME obstruction family from an independent direction. Its Phase 9 probe gate failed definitively after three dispatches on the non-theorem box(A-or-B) implies (box-A or box-B) -- box failing to distribute over disjunction, which is the same constructive-disjunction-property wall as the pair-seed obligation above. Machine-checked evidence lives in that task under probes/theta_place_validation.lean, probes/theta_place_layered.lean, and probes/theta_place_final_gate.lean; all three compile clean with no sorryAx and are durable assets for this research. Because two independent formalization fronts converged on the same wall, a cut-free or nested-sequent treatment that recovers disjunction-property reasoning would unblock BOTH. When reporting, state explicitly what each consumer would gain: for the pair-seed task, whether the named open Prop can be discharged; for the labelled-soundness task, whether a context-fold that splits compound context facts is derivable without the box-over-disjunction bridge.

---

### 553. S4 loop guard soundness reachability restriction
- **Status**: [PARTIAL]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 535
- **Research**: [553_s4_loop_guard_soundness_reachability_restriction/reports/01_s4-keyed-guard-soundness-falsified.md]
- **Plan**: [553_s4_loop_guard_soundness_reachability_restriction/plans/01_s4-settled-context-scheduling.md]

**Description**: Determine whether the S4 keyed loop-check guard can be made sound, and if so repair it. This task carries EXPLICIT authorization to edit the otherwise-frozen blockingWorldS4Keyed code that the completeness-line task holds constant. FRAMING MATTERS: this is not 'apply the reachability restriction', it is 'determine whether the guard can be narrowed at all without collapsing the termination argument'. THE DEFECT: blockingWorldS4Keyed (LoopChecking.lean approx 469) picks its blocking world by matching birth-content across ALL recorded worlds, with no reachability restriction to the current label. The redirect then adds a bare edge whose soundness needs the two labels to be related in an arbitrary model. Since the S4 frame condition is reflexive and transitive but NOT symmetric, common-ancestor reachability does not yield relatedness, and the S5 precedent relies on symmetry so it does not transfer. As stated, the keyed S4 soundness theorem is likely FALSE. CANDIDATE FIX: restrict candidates to those reachable via ReflTransGen of the accessibility edge relation. CRITICAL PREDICTION TO VERIFY FIRST, derived from hypothesis shapes and NOT yet confirmed: narrowing the guard may break TERMINATION, not merely completeness. The S4 outputs-subset-universe lemma consumes the world-bound lemma, whose hypotheses are exactly the pigeonhole facts that distinct worlds have distinct keys and that keys are contained in the signed subformulas of the root. Key-distinctness is precisely what the UNRESTRICTED guard buys: under a reachability restriction, two mutually-unreachable worlds with the same birth content could both be born, breaking key-distinctness, the world bound, and hence the termination line. Verify this before committing to any fix; if it holds, the guard cannot simply be narrowed and a different soundness route is required. DOWNSTREAM CONSUMERS deferred here from the completeness-line task: the keyed S4 soundness theorem, its successor phase, and the decidability half of the S4 validity decidability instance, which needs BOTH the soundness and completeness lines and is therefore not achievable until this lands. Evidence: the completeness-line task's report on remaining work and the Phase 9 obstruction, plus the carry-forward risk section of its rescope plan.

---

### 552. Tableau calculus conformance rule completeness repair
- **Status**: [PARTIAL]
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
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Research**: [530_consolidate_chronicle_construction_bimodal_temporal/reports/01_chronicle-dedup-research.md]
- **Plan**: [530_consolidate_chronicle_construction_bimodal_temporal/plans/01_chronicle-consolidation.md]
- **Summary**: [530_consolidate_chronicle_construction_bimodal_temporal/summaries/01_chronicle-consolidation-summary.md]

**Description**: REDUNDANCY CLEANUP. Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ and Cslib/Logics/Temporal/Metalogic/Chronicle/ are two nearly-identical full trees sharing 8 filenames (ChronicleConstruction, ChronicleToCountermodel, ChronicleTypes, CounterexampleElimination, PointInsertion, RRelation, ...) with ~89% overlap. The partial task-454 consolidation already lifted PointInsertion; extend that: factor the shared chronicle/countermodel-elimination machinery into a label-generic module under Cslib/Foundations/Logic/Metalogic/Chronicle/ (which currently holds only SinceSeedConsistency.lean) and have both the bimodal and temporal trees instantiate it. Preserve all landed sorry-free results; this is a structural dedup, not a proof change. Watch the bimodal discrete-completeness sorries (blocked on external port) - do not entangle them.

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
- **Dependencies**: Task 535
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
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 552
- **Plan**:
  - [425_temporal_tableau_ptl_fmp_decidability/plans/03_validity-corrected-fmp-plan.md]
  - [425_temporal_tableau_ptl_fmp_decidability/plans/01_ptl-fmp-decidability-plan.md]
- **Summary**: [425_temporal_tableau_ptl_fmp_decidability/summaries/01_ptl-fmp-summary.md]
- **Research**: [425_temporal_tableau_ptl_fmp_decidability/reports/04_island-vs-periodic-strategic-decision.md]

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

### 375. Proof system equivalence tableau sequent edges
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317

**Description**: Fold the TABLEAU decision systems into the propositional proof-system TFAE. RECONCILED: the sequent edges are ALREADY done - Cslib/Logics/Propositional/ProofSystemEquivalence.lean has cplProofSystemsTfae (Hilbert/ND/LK) and iplProofSystemsTfae (Hilbert/ND/LJ). REMAINING: add the tableau nodes to both TFAEs, wiring Propositional/Tableau/{Classical,Intuitionistic,Minimal}/Completeness.lean into the equivalence. Depends on task 317 (propositional tableau completeness) landing its remaining sorries.

---

### 317. Propositional tableau completeness
- **Status**: [BLOCKED]
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
  - [226_propositional_semantics_upstream_pr/reports/03_upstream-packaging-research.md]

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
