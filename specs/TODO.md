---
next_project_number: 520
---

# TODO

WARNING: Task 512 not assigned to a wave (possible circular dependency)
WARNING: Task 517 not assigned to a wave (possible circular dependency)
## Task Order

*Updated 2026-07-15. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,226,317,393,400,405,407,425,438,440,449,463,465,466,474,497,502,503,504,511,515,519 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,375,409,430,450,451,456,506 | 36,37,181,317,407,425,449,511 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41,300,413 | 39,40,375,503,504,506 | foundations, modal logic, code hygiene |
| 4 | 412,414 | 41,181,215,300,301 | code hygiene |
| 99 | 512,517 | 512,517 | modal logic |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 
317 [IMPLEMENTING] — Fill the propositional tableau completeness sorries (7 real sorri
  └─ 375 [NOT STARTED] — Complete the cross-system equivalence story by folding the tablea
  └─ 430 [PLANNED] — Prove the atom-persistence / upward-closure structural lemma for 
400 [BLOCKED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
407 [PR READY] — DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat
  └─ 409 [NOT STARTED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
497 [NOT STARTED] — Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (P

### Modal Logic

405 [PR READY] — Simplify the proof machinery in the task-402 modal tableau soundn
503 [BLOCKED] — Parametrize the K tableau driver (Cslib/Logics/Modal/Tableau/Satu
  └─ 300 [BLOCKED] — Extend modal K tableau (task 299) with frame-specific rules for r
504 [BLOCKED] — Deliver plan Phases 3 and 7 of task 300 (specs/300_modal_extensio
  └─ 300 [BLOCKED] — Extend modal K tableau (task 299) with frame-specific rules for r (see above)
515 [IMPLEMENTING] — Implement the terminating S5 tableau machinery recommended by tas
506 [BLOCKED] — Deliver plan Phases 5 and 6 of task 300 combined (specs/300_modal
  └─ 300 [BLOCKED] — Extend modal K tableau (task 299) with frame-specific rules for r (see above)
512 [BLOCKED] — Prove CS5 (constructive S5 = CK+T+4+B) Kripke completeness via a 
  └─ 517 [BLOCKED] — ROUTE B (user-funded, full build): Build a LABELLED / bounded-con
    └─ 512 [BLOCKED] — Prove CS5 (constructive S5 = CK+T+4+B) Kripke completeness via a  (see above)

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

393 [NOT STARTED] — Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING befo
463 [NOT STARTED] — Vet found low-severity documentation gaps (code placement itself 
502 [NOT STARTED] — lake shake flags Cslib/Logics/Modal/Metalogic/Constructive/Segmen
412 [NOT STARTED] — [Split from task 278.] Simplify proofs in Foundations/Logic/ that
413 [NOT STARTED] — [Split from task 278.] Simplify Propositional/ proofs that use ma
414 [NOT STARTED] — [Split from task 278.] Simplify Modal/, Temporal/, and Bimodal/ p

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

511 [BLOCKED] — Follow-on to task 506 (S4 loop-checking): close the S4 terminatio
  └─ 506 [BLOCKED] — (Modal Logic: Deliver plan Phases 5 and 6 of task 300 ) (see above)

## Tasks

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

### 518. Reingest simpson1994 literature corpus
- **Effort**: 2-4 hours
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: Literature
- **Dependencies**: None

**Description**: LITERATURE INFRASTRUCTURE FIX: re-ingest Simpson 1994 (The Proof Theory and Semantics of Intuitionistic Modal Logic, BibKey Simpson1994) into the global Literature corpus. PROBLEM (found by task 517 research, report 01): the current Simpson chunks are UNUSABLE for lemma statements -- 1091 chunks with ~312 byte mean, and 122-140 byte fragments that TRUNCATE the very lemma statements they contain. IMPACT: task 516's report 02 rated Route B and cited Simpson lemmas from these truncated fragments and got the chapter structure WRONG (it cited Ch 7-8 Lemmas 8.2.4/8.2.5/8.2.6 as the IS5 completeness spine; in fact Ch 8 EXPLICITLY EXCLUDES IS5 -- p.161 verbatim "we fix L as any logic in Dec_T, other than IS5" -- and is the finite model property, not completeness; the real spine is Ch 5-6: Prime Lemma 5.3.1, Canonical Model Lemma 5.3.2, Adequacy Theorem 6.2.1). Task 517's research had to bypass the corpus and work from the source PDF. ALL prior Simpson citations in tasks 512/516 rest on the broken chunks and are suspect (NOTE: the mechanized Lean guardrail lemmas are unaffected -- they are proofs, not citations). SCOPE: locate the Simpson 1994 source PDF; re-convert/re-chunk with settings that preserve lemma statements intact (larger chunks / structure-aware segmentation rather than the current ~312-byte fragmentation); re-index in the global index.json + FTS5 db; update specs/literature-index.json; validate that a literature-search.sh query for "Lemma 5.3.1 prime" / "Lemma 5.3.2 canonical model" / "Theorem 6.2.1 adequacy" returns COMPLETE lemma statements. Also audit whether other large corpus documents suffer the same over-fragmentation. Deliverable: usable Simpson chunks + a short note on the chunking settings changed. Low risk, high leverage for tasks 517 and any future literature-grounded work.

---

### 517. Labelled bounded context cs5 completeness
- **Effort**: 40-70 hours
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 509, Task 512, Task 516

**Description**: ROUTE B (user-funded, full build): Build a LABELLED / bounded-context canonical model framework for CSLib constructive modal logic and prove CS5 (== IS5) constructive Kripke COMPLETENESS over it -- the only faithful path remaining. WHY THIS EXISTS (exhaustively established, mechanized + literature-grounded across tasks 509/512/516): every route that keeps CSLib's PRIME-THEORY canonical model is dead for ONE root reason -- prime non-maximal theories lack negation-completeness, so the symmetric back-clause is jointly unsatisfiable with refuting the box subject. Mechanized guardrail set (all sorry-free/axiom-clean): cs5_symmetric_tail_box_gap (CS5.lean:712, task 509 -- THE wall), cs5Incest_forces_symm (CS5Canonical.lean:643, axiom-free -- any <=-mediated condition collapses to plain symmetry since ckforces_persistence + cval force head-monotonicity under ANY <=), cs5TwoSidedR_iff_cs5Tail (CS5Canonical.lean:511 -- Simpson two-sided R == the old cs5Tail wall over CS5 quasi-prime theories), plus task-512's atom-sum results. Dead: atom-sum doubled-atom (512), one-sided-R (512 ph5), two-sided-R (512 ph7), independent-<= (516 report 01 -- refuted: Simpson uses <= = subset VERBATIM, Section 3.3), Simpson-faithful prime-theory Route A (516 report 02, ~95% -- Simpson NEVER does symmetric box-backward in prime-theory form; his Section 3.3 prime model is an 'outline' deferring IS5 symmetry to Fischer Servi). CS5 IS complete (CS5 == IS5, CS5.lean:93-99) -- the block is representational, NOT incompleteness. THE METHOD (Simpson 1994 Ch 7-8, the rigorous IS5 proof he actually carries out; extended by Marin-Morales-Strassburger 2021's labelled line): abandon prime theories for LABELLED 'T-prime bounded contexts'. Key targets: T-Comp graph completion (Simpson Lemma 8.2.5) for symmetry; the bounded canonical model lemma over labelled membership y:B in A (Lemma 8.2.6) for box-backward; a BOUNDED prime lemma; then the truth lemma and cs5_completeness. NOTE (important, settled by 516 report 02): the classical decidability-of-derivability step in Simpson's box-backward is NOT a blocker -- Lean has Classical.em; the prime-theory structural gap was the blocker, and labelled bounded contexts sidestep it. SCOPE: ~1500-2500 lines, ~ZERO reuse of the existing prime-theory canonical machinery (CKSegment/Segment/SegmentLindenbaum do not transfer) -- this is a NEW framework. Reuse what genuinely transfers: Proposition/Proposition.map (Basic.lean), the DerivationTree/Derivable infrastructure, the CS5ModalAxiom set, and task-512's landed CS5 soundness (cs5_axiom_sound_incest / cs5_soundness_incest, axiom-free) where the frame class matches. Any design MUST explain why it does not trip the four guardrail lemmas (labelled contexts are not prime theories, so cs5_symmetric_tail_box_gap should not apply -- state why explicitly). CONSTRAINTS: NO sorry, NO new axiom under Cslib/; zero-debt at every phase boundary; do NOT regress landed CK/CT/CS4/CS5 soundness or task-509 cs5FC''; build alongside. BibKeys: Simpson1994 (Ch 7-8), MarinMoralesStrassburger2021, Dosen1985, BozicDosen1984, AlechinaMendlerdePaivaRitter2001, Wijesekera1990, Pacheco2024 (all in references.bib). Research MUST use --lit (mine Simpson Ch 7-8 chunks: Lemmas 8.2.5, 8.2.6, the bounded prime lemma). HIGH effort, HIGH uncertainty. Depends on 509, 512, 516.

---

### 516. Constructive modal independent le canonical model
- **Effort**: 30-50 hours
- **Status**: [ABANDONED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 509, Task 512

**Description**: FOUNDATIONAL REBUILD (funds task 512's independent-<= route). Rebuild CSLib's constructive-modal canonical model with the intuitionistic preorder <= as an INDEPENDENT relation, DECOUPLED from theory-inclusion, following Simpson 1994 Ch.3 labelled/birelational IS4/IS5 models (also Dosen 1985, Alechina-Mendler-dePaiva-Ritter 2001, Marin-Morales-Strassburger 2021 Thm 7.1/7.2), in order to achieve CS5 constructive Kripke completeness -- the goal task 512 proved UNREACHABLE in CSLib's current representation. WHY (mechanized in task 512, all sorry-free/axiom-clean): over CSLib theory-inclusion canonical worlds (worlds = quasi-prime theories, <= = subset, boxInv monotone), (i) cs5Incest_forces_symm (axiom-free, CS5Canonical.lean:643) proves ANY <=-mediated incestuality/symmetry condition collapses to PLAIN symmetry -- the mediating witness u'>=u buys no room because larger worlds only add boxed formulas; (ii) cs5TwoSidedR_iff_cs5Tail (CS5Canonical.lean:511) proves Simpson's two-sided box+diamond relation is extensionally IDENTICAL to the old cs5Tail wall for CS5 quasi-prime theories (the B axiom's box/diamond-inverse duality, cs5_boxInv_subset_iff, CS5.lean:589); (iii) with task-509's cs5_symmetric_tail_box_gap (CS5.lean:712), plain symmetry on the canonical frame is exactly what box-backward CANNOT have -- so symmetry-verification and box-backward are JOINTLY UNSATISFIABLE for any single design over theory-inclusion worlds. CS5 == IS5 (CS5.lean:93-99) IS complete and sound (report 05); the block is REPRESENTATIONAL, not incompleteness. THE FIX (this task): make <= an independent preorder so Simpson's <=-mediated conditions regain genuine <=-room. SCOPE: (1) DESIGN/RESEARCH -- grounded in Simpson Ch.3, determine the exact independent-<= canonical construction (labelled worlds or an abstract birelational frame where <= is not subset), how box-backward and the symmetry/incestuality frame condition are verified with independent <= (via the disjunction property / prime lemma, NO negation-completeness), and confirm the collapse lemmas cs5Incest_forces_symm / cs5TwoSidedR_iff_cs5Tail provably DO NOT apply once <= is decoupled. (2) IMPACT ASSESSMENT on shared constructive-modal canonical infra: CKSegment/CKForces/Segment/SegmentLindenbaum (Segment.lean, SegmentLindenbaum.lean) currently bake <= = head-inclusion; decide whether to generalize this infra or build a parallel independent-<= model; preserve existing CK/CT/CS4 completeness (either re-derive over the new model or leave the old model intact for them). (3) BUILD the independent-<= canonical model; prove cs5_box_backward, cs5_truth_lemma, cs5_completeness / cs5_soundness_completeness over it. REUSE task-512's landed cs5_axiom_sound_incest (birelational soundness, axiom-free) where valid. CONSTRAINTS: NO sorry, NO new axiom under Cslib/; do not regress landed CK/CT/CS4/CS5 soundness or task-509 cs5FC''. HIGH effort and HIGH uncertainty (foundational, touches shared infra) -- a design/research phase MUST precede implementation. Depends on 509 (base canonical machinery) and 512 (obstruction findings + soundness rework; see task-512 reports 03-06 and handoffs 03-05 + phase5-blocker-handoff).

---

### 515. S5 universal rule termination unblock 504
- **Effort**: 8-12 hours
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 514
- **Research**: [515_s5_universal_rule_termination_unblock_504/reports/01_s5-termination-implementation-blueprint.md]
- **Plan**: [515_s5_universal_rule_termination_unblock_504/plans/02_s5-termination-machinery.md]
- **Summary**: [515_s5_universal_rule_termination_unblock_504/summaries/02_s5-termination-machinery-summary.md]

**Description**: Implement the terminating S5 tableau machinery recommended by task 514 to unblock task 504 Phases 2/4/5/6 (S5/KB5 Euclidean decidability). The edge-local rank measure is PROVEN inapplicable to S5's universal rule (task 504: modalApplyOneS5_rankStep_not_dischargeable) -- do NOT re-attempt the B/T mirror. Implement instead, per task 514's recommendation, either (a) a restricted S5 rule design preserving rank-compatibility while still achieving full equivalence-closure reachability, or (b) a bespoke S5-specific termination argument (prefix loop-checking / global caching / filtration-based FMP) that does NOT route through RuleApplicationSpec.rankStep. Deliver: the S5 termination/decidability spec replacing or supplementing modalApplyOneS5_spec; the generic Hintikka lift + truth lemma over the universal relation (Phase 4); S5 soundness triple modalTableauS5_sound (Phase 5); s5Valid + Decidable (s5Valid phi) against Cube.S5 (Phase 6); and 5/KB5 validity + completeness via Satisfies.five (Basic.lean) and Cslib/Foundations/Relation/Euclidean.lean RightEuclidean API (Phase 7 completion). REUSE the CI-green Phase 1/3 assets already landed and committed by task 504: S5Simplification.lean (universal rule modalApplyOneS5 + driver instantiation) and FrameCompleteness.lean (extractModelS5 via Relation.EqvGen + RightEuclidean exposure). Zero sorry, zero new axiom; run full CSLib CI (lake build, checkInitImports, lint-style, lint, test, shake) at every milestone and commit incrementally at each green milestone; scope git add narrowly (concurrent sessions). If a sub-piece cannot close sorry-free, mark [BLOCKED] with the exact open goal state -- never introduce debt. Files: Cslib/Logics/Modal/Tableau/S5Simplification.lean, GenericDriver.lean (if interface extension needed), FrameSoundness.lean, FrameCompleteness.lean.

---

### 514. S5 tableau termination literature grounding
- **Effort**: 3-5 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [514_s5_tableau_termination_literature_grounding/reports/01_s5-termination-literature-grounding.md]

**Description**: Ground task 504's PROVEN S5 tableau termination obstruction in the literature and produce a concrete, lemma-level implementation recommendation for task 515. Root cause to confirm and characterize precisely: S5's universal/global box rule (modalApplyOneS5) propagates box-formulas to ALL branch worlds irrespective of accessibility edges, so there is no edge-relation against which to decrement a modal-depth rank -- the edge-local rank-potential FMP argument (RuleApplicationSpec.rankStep, GenericDriver.lean) is provably inapplicable (task 504 landed modalApplyOneS5_rankStep_not_dischargeable, a sorry/axiom-free counterexample). (1) ACQUIRE + full-text ingest Massacci2000 (Single Step Tableaux for Modal Logics, J. Automated Reasoning 24(3):319-364, DOI 10.1023/A:1006155811656) and Gore1999 (Tableau Methods for Modal and Temporal Logics, Handbook of Tableau Methods, pp.297-396, DOI 10.1007/978-94-017-1754-0_6) via /literature Mode B; both are registered in references.bib (BibKeys Massacci2000, Gore1999) and specs/literature/SOURCES.md but PDFs are NOT yet acquired (paywalled, no OA copy found via Semantic Scholar/Unpaywall/arXiv). If PDFs remain unavailable, fall back to Gore's openly-available ANU/RSISE tech-report versions and the in-corpus surrogates ChagrovZakharyaschev1997 (filtration, FMP) and blackburn_2002_book. (2) Cross-check the literature's account of WHY S5 (and universal/global modalities) needs loop-checking / prefix-management / filtration rather than a depth-decrement measure, against task 504's mechanized obstruction. (3) Extract the concrete terminating strategy (single-step prefix loop-checking a la Massacci; semantic filtration FMP; or global caching) and MAP it onto CSLib's generic driver: specify what a rank-machinery-bypassing S5 termination/decidability interface looks like, which RuleApplicationSpec fields change or are replaced, and whether it can coexist with the existing K/T/B instantiations without regression. Deliverable: a research report with a BibKey-cited, lemma-level recommendation sufficient to plan task 515. Read-only survey: Cslib/Logics/Modal/Tableau/{GenericDriver,S5Simplification,FrameCompleteness,BDriver}.lean; specs/504_*/summaries/01_*.md and the Phase-2 obstruction proof. Comparable in scope to the S4/task-511 loop-checking analysis.

---

### 513. Generalize tableau soundness chain over spec
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 510
- **Plan**: [513_generalize_tableau_soundness_chain_over_spec/plans/01_generalize-soundness-chain.md]
- **Research**: [513_generalize_tableau_soundness_chain_over_spec/reports/01_generalize-soundness-chain-over-spec.md]
- **Summary**: [513_generalize_tableau_soundness_chain_over_spec/summaries/01_generalize-soundness-chain-summary.md]

**Description**: Generalize the tableau SOUNDNESS chain over the abstract rule-application interface, mirroring task 510 (which did this for the completeness/Hintikka chain). This is the shared blocker for Decidable(tValid) (task 503 Phase 6), Decidable(bValid) (task 505), and Decidable(s5Valid) (task 504): the completeness direction is fully generic (task 510), but the soundness direction is not. Root cause: modalStepBranch_preserves_sat (Cslib/Logics/Modal/Tableau/Soundness.lean, ~500 lines) is stated and proved concretely against modalApplyOne, so modalTableauT phi = .closed -> tValid phi (T soundness lifted to the driver/branch level) cannot be obtained by instantiation. Favourable structural fact found by task 503 Phase 6 (verified, documented at GenericDriver.lean:147-151): the ambient Kripke model is NEVER replaced throughout modalStepBranch_preserves_sat proof -- only the world-assignment function is redefined at fresh worlds -- so a branchSatisfiableIn-generalized version is structurally low-risk, though still multi-lemma. SCOPE: (1) generalize modalStepBranch_preserves_sat and its dependency chain in Soundness.lean/SoundnessStep.lean over (apply, spec : RuleApplicationSpec apply), following task 510 pattern (raw-hypothesis _gen lemmas where import topology forces it, bundled (apply, spec) wrappers where the file is a leaf; check import edges as 510 did); determine which existing RuleApplicationSpec fields (now 11 after task 510) suffice and whether any new soundness-side field is needed, deriving the field list from what the proof actually consumes, NOT assumed. (2) Re-instantiate K trivially with byte-identical public soundness statements (zero regression). (3) Instantiate at modalApplyOneT + modalApplyOneT_spec to expose modalTableauT_sound, then complete tValid_decides / instDecidableTValid (task 503 Phase 6) against Cube.T / Satisfies.t. Zero sorry, zero axiom, zero vacuous placeholders; mark [BLOCKED] with documented goal state rather than introduce debt. Run full CSLib CI at every milestone; scope git add narrowly (concurrent sessions). On completion unblocks task 503 Phase 6 and the Decidable side of tasks 505 (B) and 504 (S5). Files: Cslib/Logics/Modal/Tableau/Soundness.lean, Cslib/Logics/Modal/Tableau/SoundnessStep.lean, Cslib/Logics/Modal/Tableau/GenericDriver.lean, Cslib/Logics/Modal/Tableau/TDriver.lean, Cslib/Logics/Modal/Tableau/FrameCompleteness.lean (tValid_decides).

---

### 512. Cs5 box backward atom sum completeness
- **Effort**: 10-16 hours
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 509, Task 517
- **Research**:
  - [512_cs5_box_backward_atom_sum_completeness/reports/01_box-backward-atom-sum.md]
  - [512_cs5_box_backward_atom_sum_completeness/reports/02_phase3-seed-consistency.md]
  - [512_cs5_box_backward_atom_sum_completeness/reports/03_alternative-techniques.md]
  - [512_cs5_box_backward_atom_sum_completeness/reports/04_birelational-feasibility.md]
  - [512_cs5_box_backward_atom_sum_completeness/reports/05_collapse-s5-probe.md]
- **Plan**:
  - [512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md]
  - [512_cs5_box_backward_atom_sum_completeness/plans/02_birelational-pivot.md]
- **Summary**:
  - [512_cs5_box_backward_atom_sum_completeness/summaries/02_phase3-route2-partial-summary.md]
  - [512_cs5_box_backward_atom_sum_completeness/summaries/01_box-backward-atom-sum-summary.md]
  - [512_cs5_box_backward_atom_sum_completeness/summaries/03_necessity-transfer-summary.md]

**Description**: Prove CS5 (constructive S5 = CK+T+4+B) Kripke completeness via a BIRELATIONAL canonical model (Dosen 1985 / Bozic-Dosen 1984 / Simpson 1994 / Marin-Morales-Strassburger 2021), SUPERSEDING the abandoned doubled-atom "atom-sum" architecture. Established across reports 03-05 (six dispatches): (a) the doubled-atom repair AND any direct attack within CSLib's two-sided cs5Tail architecture are eliminated -- the two-sided back-inclusion boxInv T subset H IS the negation-completeness step quasi-prime theories cannot take (mechanized: cs5_two_sided_witness_can_fail_to_omit, cs5FC''_hub_forces_spoke_connectivity, cs5_symmetric_tail_box_gap); (b) CS5 IS complete -- CS5 == IS5 (CS5.lean:93-99), Pacheco's CKB=IKB collapse extends to S5 (mechanized via cs5_dia_or, cs5_dia_bot_imp_bot), so "bank a negative result" is REFUTED (no genuine obstruction exists); (c) the birelational route uses a ONE-SIDED relation R = boxInv Gamma subset Delta with symmetry as the <=-mediated incestuality frame condition (Marin Thm 7.1), under which box-backward dissolves to the landed box_refuting_theory. Phase-1 GO/NO-GO gate PASSED (cs5_box_backward_onesided, sorry-free/axiom-clean). Active plan: plans/02_birelational-pivot.md (7 phases; Phase 1 COMPLETE). Remaining: discard the ~520-line CS5Combined scaffold (Phase 2); define one-sided R + incestuality frame class (Phase 3); REWORK CS5 soundness over the new frame class -- TOUCHES landed task-509 cs5FC'' (Phase 4, high-cost, ~250-400 lines, preserve 509 proofs alongside); verify canonical-frame incestuality Dosen-style, negation-completeness-free (Phase 5); land cs5_box_backward + cs5_truth_lemma (Phase 6); cs5_completeness + file split (Phase 7). Zero-debt invariant: no sorry, no new axiom at any phase boundary. BibKeys added: Dosen1985, BozicDosen1984, Ewald1986, AlechinaMendlerdePaivaRitter2001, MarinMoralesStrassburger2021. Depends on 509.

---

### 511. S4 loop checking termination
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: None
- **Plan**: [511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md]
- **Research**: [511_s4_loop_checking_termination/reports/01_s4-termination-guard-redesign.md]
- **Summary**: [511_s4_loop_checking_termination/summaries/01_s4-termination-bound-decidability-summary.md]

**Description**: Follow-on to task 506 (S4 loop-checking): close the S4 termination bound and complete decidability. Task 506 landed Phases 1-7 green (4-rule, LoopChecking.lean equality-blocking machinery, modalApplyOneS4/modalTableauS4, modalHintikkaSetS4, extractModelS4, modalTruthLemmaS4, s4Valid + 4-rule soundness; zero sorry/axiom) but Phase 8 (the #worlds <= 2^|modalSubfmls phi0| termination bound) is [BLOCKED]: worldSetsDistinct is not a genuine per-step invariant of modalStepBranchS4 as currently designed. Two documented gaps (see specs/506_s4_loopchecking_machinery_termination_bound_and_decidability/plans/01_s4-loopchecking-termination-decidability.md Phase 8 BLOCKER note): (1) persistent rule firings (K boxPos, T self-propagation, the 4-rule box-itself propagation) add formulas to an already-known world relevant set without re-checking distinctness against other known worlds; (2) the minting guard (blockingWorld) checks the SOURCE world uniqueness against existing worlds, not the freshly-minted world own prospective content, so a new world is not guaranteed distinct at creation. SCOPE: (a) redesign the minting guard or restate the invariant over a saturation-stable notion of a world relevant set so distinctness is actually preserved per step; (b) prove the pigeonhole bound #worlds <= 2^|modalSubfmls phi0| as a loop invariant under the corrected guard (build the sibling S4LoopInv, do NOT extend ModalPotentialInv whose rankEdge exact per-edge decrease transitive propagation falsifies); (c) modalStepBranchS4_worldBound; (d) then Phase 9: fuel sufficiency, s4Valid completeness, Decidable (s4Valid phi) against Cube.S4, consuming task 510 generalized modalHintikkaSetGen chain (verify modalHintikkaSetS4 aligns with modalHintikkaSetGen modalApplyOneS4, or build the S4 hintikka-production via the generic loop lemma). Zero sorry, zero axiom. Files: Cslib/Logics/Modal/Tableau/LoopChecking.lean, Cslib/Logics/Modal/Tableau/FrameCompleteness.lean, possibly a new FmpMeasure-sibling for S4LoopInv. Standing permission to land [BLOCKED] again with documented goal state if the pigeonhole invariant still does not close.

---

### 510. Generalize completeness loop hintikka chain over spec
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 507
- **Research**: [510_generalize_completeness_loop_hintikka_chain_over_spec/reports/01_generalize-hintikka-chain-over-spec.md]
- **Plan**: [510_generalize_completeness_loop_hintikka_chain_over_spec/plans/01_generalize-hintikka-chain-over-spec.md]
- **Summary**: [510_generalize_completeness_loop_hintikka_chain_over_spec/summaries/01_generalize-hintikka-chain-over-spec-summary.md]

**Description**: Generalize the Hintikka-set / saturation-characterisation chain over the abstract rule-application interface, so that T (503), B (505), and S5 (504) all instantiate ONE generic development rather than each re-deriving an ~850-line system-specific analog. This is the direct successor to task 507 (which generalized FmpMeasure.lean's termination measure over RuleApplicationSpec, CI-green, zero sorry/axiom, commit 009cc348) and applies the same play one layer up. Blocker origin: task 503 Phase 5 (see specs/503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/.orchestrator-handoff.json and plan Phase 5) -- producing a modalHintikkaSetT witness from an open modalExpandBranchesT result requires modalExpandBranches_hintikka and its entire private dependency chain, all stated directly against the concrete modalApplyOne rather than an abstract apply. Scope: (1) Extend RuleApplicationSpec (Cslib/Logics/Modal/Tableau/GenericDriver.lean, currently 7 fields after task 507) with a saturation component -- an abstract saturation predicate plus a noneIffSaturated characterisation (apply returns none iff the branch is saturated w.r.t. that predicate) and a Hintikka-lift hook (the saturation predicate implies the Hintikka clause conditions). "Saturated" is genuinely rule-dependent -- T's saturation includes the T-rule self-conjunct -- so this MUST be abstracted, not assumed. Expect the interface may need a further field round; that is anticipated, not a failure. (2) Generalize Completeness.lean:665-778 (modalHintikkaClause / modalApplyOne_fst_eq_of_not_box / modalHintikkaClause_lift) over (apply, spec). (3) Generalize Completeness.lean:784-935 (modalStepBranch_none_saturated / modalStepBranch_hintikka_inv). (4) Generalize CompletenessLoop.lean:57-712 (ModalLoopInv, modalStep_preserves_invariant, the ~6 private witness-invariant helpers) over (apply, spec), reusing the already-generic modalStepBranchGen_potential_step / modalStepBranchGen_worldBound from task 507 for the potential/world-bound conjuncts. (5) Generalize modalExpandBranches_hintikka (CompletenessLoop.lean:746) as modalExpandBranchesGen_hintikka. (6) Re-instantiate K as the trivial instance at modalApplyOne + modalApplyOne_spec: K's public theorem statements (kValid, modalTableau_decides, instDecidableKValid) must stay byte-identical, zero regression. (7) Instantiate at modalApplyOneT + modalApplyOneT_spec (already delivered in Cslib/Logics/Modal/Tableau/TDriver.lean by task 503 Phase 4) to expose modalExpandBranchesT_hintikka, the exact lemma task 503 Phase 5 is blocked on. Note the known import-cycle constraint discovered by task 507: GenericDriver.lean -> FmpMeasure.lean forces _gen lemmas to take raw hypotheses with bundled (apply, spec) wrappers living in GenericDriver.lean; follow the same pattern. Zero sorry, zero axiom, zero regression to K. Run the full CSLib CI (lake build, lake exe checkInitImports, lake exe lint-style, lake lint, lake test, lake exe mk_all --module, lake shake) at every phase milestone and commit incrementally at each green milestone; scope git add narrowly (concurrent sessions run in this repo). If a sub-piece cannot close sorry-free, mark it [BLOCKED] with the exact open lemma name and goal state documented -- never introduce a sorry or axiom. On completion this unblocks task 503 Phases 5-7 (T truth lemma, Decidable (tValid phi), downstream contract docs) and is the shared prerequisite for tasks 505 (B) and 504 (S5/KB5). Task 506 (S4) is out of scope -- its loop-checking termination is structurally different. Files: Cslib/Logics/Modal/Tableau/GenericDriver.lean, Cslib/Logics/Modal/Tableau/Completeness.lean, Cslib/Logics/Modal/Tableau/CompletenessLoop.lean, Cslib/Logics/Modal/Tableau/TDriver.lean.

---

### 509. Rescope CK CS5 constructive completeness
- **Effort**: 12-20 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 508
- **Research**: [509_rescope_CK_CS5_constructive_completeness/reports/01_cs5-symmetric-tail-construction.md]
- **Plan**: [509_rescope_CK_CS5_constructive_completeness/plans/01_cs5-symmetric-tail-completeness.md]
- **Summary**:
  - [509_rescope_CK_CS5_constructive_completeness/summaries/01_cs5-symmetric-tail-completeness-phases1-7-summary.md]
  - [509_rescope_CK_CS5_constructive_completeness/summaries/02_cs5-phases8-11-summary.md]

**Description**: OWNS CK CONSTRUCTIVE CS5 COMPLETENESS ENTIRELY (re-scoped from task 501; task 508 follow-up). This task is the sole owner of CS5 completeness for the CK column of the constructive modal cube — task 501 delivered CS5 axioms + soundness (cs5_soundness, landed and axiom-free) and is now CLOSED with CS5 completeness explicitly out of its scope. Task 508 closed CS4 completeness sorry-free by weakening the frame condition to cs4FC' plus a hereditary diamond-exclusion tail, but proved that technique provably does NOT extend to CS5. Mechanized negative results from 508 (specs/508_unblock_CK_CS4_CS5_completeness/probes/cs5-obstruction-verified.lean, compiling): (1) bDia_not_valid_over_cs5FCweak — a two-world Bool countermodel satisfying reflexivity, both cs4FC' clauses, and weakened symmetry, yet refuting the-diamond-of-box-p implies p; so bDia is UNSOUND over the weakened condition that makes CS4 work. (2) cs5_dia_bot_imp_bot — CS5 proves the-diamond-of-bot implies bot (unlike CK/CT/CS4), a NEW lead enabling a Set.univ-free tail redesign. Remaining gap: the frame condition that would validate bDia (FCbdia: r w u implies exists u' >= u and t <= w with r u' t) fails canonically because u := cexpl forces Set.univ into every realized tail; discharging it needs genuine canonical symmetry (boxInv(u.head) subset w.head), whose classical proof requires maximality (B not in head implies not-B in head) — unavailable for quasi-prime (intuitionistic) heads. IMPORTANT — do not repeat prior mistakes: 501 held the frame condition FIXED and searched for a better tail construction, and 508 proved the frame condition is the FREE PARAMETER. Also note 501 Phase 7 wrongly asserted CS5 shares CS4's root cause; 508 refuted this — CS5's obstruction is different and deeper. SCOPE CAVEAT: the countermodel rules out the CS4 technique, NOT CS5 completeness as such; the broader infeasibility verdict is a limitation-of-known-technique argument, not an impossibility theorem. Investigate whether cs5_dia_bot_imp_bot supports a Set.univ-free canonical world type admitting symmetry without maximality, or whether CS5 constructive completeness requires different semantics (e.g. birelational models with a separate intuitionistic preorder). A rigorous NEGATIVE result is an ACCEPTABLE and VALUABLE outcome: if CS5 completeness is not achievable over the CK segment/fallible-world model, document the obstruction as a mechanized theorem and leave CS5.lean completeness BLOCKED citing it. Files: Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean. Depends on 508.

---

### 508. Unblock CK CS4 CS5 completeness
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [508_unblock_CK_CS4_CS5_completeness/reports/01_cs4-cs5-completeness-technique.md]
- **Plan**: [508_unblock_CK_CS4_CS5_completeness/plans/01_cs4-completeness-integration.md]
- **Summary**: [508_unblock_CK_CS4_CS5_completeness/summaries/01_cs4-completeness-integration-summary.md]

**Description**: Unblock CK constructive CS4/CS5 completeness (task 501 follow-up) — task 501 delivered CT/CS4/CS5 soundness and CT completeness, but CS4/CS5 completeness is [BLOCKED] on a mechanically-verified obstruction: over CK's segment/fallible-world model, the diamRefutingSegment tail-exclusion witness needed for the truth lemma's diamond-backward 'far' clause cannot be shown to propagate through further relational steps (no maximal-tail invariant makes cs4FC transitivity / cs5FC symmetry hold globally on the restricted canonical world type). Research and implement an alternative canonical-model technique to close CS4/CS5 completeness sorry-free: candidate approaches (a) a hereditary/maximal diamond-refuting construction that keeps the exclusion invariant stable under cmreach steps, or (b) filtration over the CK segment model. Files: Cslib/Logics/Modal/Metalogic/Constructive/{CS4,CS5}.lean (currently soundness-only + BLOCKED completeness sections). Depends on 501.

---

### 507. Generalize k fmp termination measure over ruleapplicationspec
- **Effort**: 12-16 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/reports/02_spawn-analysis.md]
  - [507_generalize_k_fmp_termination_measure_over_ruleapplicationspec/reports/01_frame-specific-tableau-extensions.md]
  - [507_generalize_k_fmp_termination_measure_over_ruleapplicationspec/reports/03_parent-phase-plan-reference.md]
- **Plan**: [507_generalize_k_fmp_termination_measure_over_ruleapplicationspec/plans/01_generalize-fmp-termination-measure.md]
- **Summary**: [507_generalize_k_fmp_termination_measure_over_ruleapplicationspec/summaries/01_generalize-fmp-termination-measure-summary.md]

**Description**: Complete task 503's Phase 3 (plans/01_generalize-tableau-driver-tsystem.md): generalize Cslib/Logics/Modal/Tableau/FmpMeasure.lean's rule-dependent termination/FMP step lemmas -- modalStepBranch_potential_step (~line 2146), modalStepBranch_worldBound (~line 2376), and modalExpMeasure_step_lt (~line 2873) -- to take an abstract (apply : RuleApply Atom) (spec : RuleApplicationSpec apply) in place of the concrete modalApplyOne, defined in Cslib/Logics/Modal/Tableau/GenericDriver.lean (commit d5b24e67). Before attempting the top-level lemmas, first re-derive the ~900-line dependency chain generically: modalStepBranch_exists_rank' (~line 1058), modalStepBranch_knownWorlds (~line 1901), modalStepBranch_preserves_outDegEq (~line 1365), outDeg_le_of_expandedNodup (~line 1509), and ~10 further private helpers (FmpMeasure.lean lines ~1058-2415), each of which today independently rcases on modalApplyOne's four concrete RuleResult shapes (propositional/boxPos/diamondNeg/diamondPos/boxNeg) rather than going through RuleApplicationSpec. This will likely require extending RuleApplicationSpec (GenericDriver.lean) with additional fields capturing the exact outDeg/rank-map interaction at the fresh-world mint point (not just 'a fresh edge is added', but 'the fresh edge's source outDeg was < Sf beforehand, by exactly the amount the catalog bounds') so the existing geomCap-based EXACT potential-drop identity (lines ~2251-2270) can be replayed generically, not merely bounded. Keep modalUniverse/modalWork/modalExpMeasure/modalFuel (world-agnostic size bounds) unchanged -- only the rule-dependent step lemmas move behind the interface. Re-instantiate K's termination lemmas as the generic lemmas applied to modalApplyOne + the already-proved modalApplyOne_spec witness (Phase 2), and confirm FmpMeasure.lean's existing K corollaries and CompletenessLoop.lean's uses still typecheck via the Phase-1 modalStepBranch_eq/modalExpandBranches_eq/modalTableau_eq bridge lemmas (Saturation.lean, commit e9f350c7). Zero regression to K's public theorem statements; zero sorry; zero axiom. If any sub-piece cannot close sorry-free, mark the affected sub-goal [BLOCKED] with the exact open lemma name and goal state documented, and sequence the remainder into further phases within this task's own plan rather than deferring silently. Run the full CSLib CI (lake build, lake exe checkInitImports, lake lint, lake exe lint-style, lake test, lake exe mk_all --module, lake shake) at every milestone. On completion this unblocks task 503's Phases 4-7 (T driver instantiation, T truth lemma, Decidable (tValid phi)) and is a prerequisite for tasks 504 (S5/KB5) and 505 (B), which are documented to reuse the same generic termination measure. Task 506 (S4) is explicitly out of scope -- its transitive-box termination argument is structurally different and not an instance of this interface.

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

### 505. B symmetric decidability via generic tableau driver
- **Effort**: 5-7 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 513
- **Research**:
  - [505_b_symmetric_decidability_via_generic_tableau_driver/reports/01_frame-specific-tableau-extensions.md]
  - [505_b_symmetric_decidability_via_generic_tableau_driver/reports/02_spawn-analysis.md]
  - [505_b_symmetric_decidability_via_generic_tableau_driver/reports/03_parent-phase-plan-reference.md]
- **Plan**: [505_b_symmetric_decidability_via_generic_tableau_driver/plans/01_b-symmetric-tableau-implementation.md]
- **Summary**: [505_b_symmetric_decidability_via_generic_tableau_driver/summaries/01_b-symmetric-tableau-summary.md]

**Description**: Deliver plan Phase 4 of task 300 (specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md): the B (symmetric-frame) system. Add the symmetric box rule to Cslib/Logics/Modal/Tableau/FrameRules.lean: box-positives propagate backward along recorded edges (T(box phi)@w + edge v->w gives T(phi)@v), dually for F(diamond); add the backward-propagation saturation conjunct. Extract the countermodel via Relation.SymmGen (Std.Symm free from Relation.SymmGen.instSymm). Discharge the structural hypotheses interface fixed by the generic driver delivered in the prerequisite task (backward propagation adds formulas only at existing worlds, so the K world bound and finite formula catalog survive unchanged). Prove the B truth-lemma bridge over the symmetric closure. State bValid / Decidable (bValid phi) against Cube.B / Satisfies.b (Basic.lean). Files: Cslib/Logics/Modal/Tableau/FrameRules.lean (B arms), Cslib/Logics/Modal/Tableau/FrameCompleteness.lean (extractModelB, B bridge, bValid + Decidable), Cslib/Logics/Modal/Tableau/FrameSoundness.lean (B arm).

---

### 504. S5 and kb55route euclidean decidability via generic tableau 
- **Effort**: 5-7 hours
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 513, Task 505
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
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 513
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
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: lake shake flags Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean: replace the transitive `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` with direct imports of `Cslib.Logics.Modal.Metalogic.DerivationTree` and `Cslib.Foundations.Logic.Metalogic.PrimeExclusion` (the two modules whose declarations Segment.lean actually consumes). Do NOT remove the plain `import Cslib.Init` line (shake's suggestion there is the systemic out-of-scope pattern and would violate CONTRIBUTING.md's Cslib.Init mandate). Single-file, single-import-line change; re-verify with lake build + lake shake --add-public --keep-implied --keep-prefix. From vet of task 493.

---

### 501. CK constructive modal extensions CT CS4 CS5
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 493, Task 508
- **Research**: [501_CK_constructive_modal_extensions_CT_CS4_CS5/reports/01_ct-cs4-cs5-segment-extensions.md]
- **Plan**: [501_CK_constructive_modal_extensions_CT_CS4_CS5/plans/01_ct-cs4-cs5-extensions.md]
- **Summary**: [501_CK_constructive_modal_extensions_CT_CS4_CS5/summaries/01_ct-cs4-cs5-extensions-summary.md]

**Description**: CK constructive modal extensions CT / CS4 (+ CS5 soundness) — RE-SCOPED: CS5 completeness moved to task 509, which owns it entirely. 501 scope is now: sound and complete axiomatizations of the constructive (CK-based) analogues of T and S4 as modular extensions of CK (task 493), over birelational semantics (task 490) instantiating the intuitionistic modal framework (task 480), PLUS CS5 axioms + soundness. CK is the weaker constructive base (drops IK's diamond-bot->bot and diamond(A or B)->diamond A or diamond B), so box and diamond stay fully independent; establish the axiom<->birelational-frame-condition correspondences over that base and prove soundness + completeness by the birelational (prime-theory) canonical model. DELIVERED: CKExtension.lean; CT soundness+completeness; CS4 soundness+completeness (completeness closed by task 508 via the weakened frame condition cs4FC' + hereditary diamond-refuting tail); CS5 axioms + soundness (cs5_soundness, no axioms). NOT IN SCOPE: CS5 completeness — see task 509 and the mechanized obstruction bDia_not_valid_over_cs5FCweak. Contributes the CK column of the constructive modal cube (CK analogue of task 494 for IK and task 496 for minimal); the column is CT+CS4-complete with CS5 completeness outstanding under 509. Depends on 493.

---

### 497. Reconcile imp naming
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (Proposition.imp constructor and → notation) with the rest of the library once PR #607 lands, so the propositional connective naming is consistent library-wide (noting Modal uses 'impl'). Raised in review of PR #648 by thomaskwaring. BLOCKED until #607 (external PR, leanprover/cslib) is merged.

---

### 496. Minimal modal extensions
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 495
- **Research**: [496_minimal_modal_extensions/reports/01_minimal-modal-extensions.md]
- **Plan**: [496_minimal_modal_extensions/plans/01_minimal-modal-extensions.md]
- **Summary**: [496_minimal_modal_extensions/summaries/01_minimal-modal-extensions-summary.md]

**Description**: Minimal modal extensions — minimal-base analogues of T / S4 / S5 as modular extensions of minimal K (task 495), via the axiom↔frame-condition correspondences over the minimal/birelational semantics. Lower priority / exploratory; establishes that the modular extension pattern also holds over the minimal propositional base. Depends on 495.

---

### 484. Metalogic conservative extension modularity
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 478, Task 479, Task 480, Task 481, Task 482, Task 483, Task 492, Task 494, Task 495, Task 496
- **Research**: [484_metalogic_conservative_extension_modularity/reports/01_conservative-extension-modularity.md]
- **Plan**: [484_metalogic_conservative_extension_modularity/plans/01_conservative-extension-modularity.md]
- **Summary**: [484_metalogic_conservative_extension_modularity/summaries/01_conservative-extension-modularity-summary.md]

**Description**: Conservative-extension and modularity results across the FULL propositional-strength × modal-axiom lattice: relate minimal ⊆ intuitionistic ⊆ classical propositional bases crossed with the modal-axiom lattice (K ⊆ T ⊆ S4 ⊆ S5, plus D/serial and B/symmetric correspondences), ensuring each axiom↔frame-condition module composes cleanly, stronger logics conservatively extend weaker ones, and the classical systems arise from the intuitionistic/minimal ones by adding DNE/efq. Establishes the compositional guarantees that make the axiomatizations modular. Depends on 478-483 (classical), 480/492 (intuitionistic), 495 (minimal).

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
- **Dependencies**: Task 391

**Description**: Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING before refactor. (a) Factor one generic quotient-Lindenbaum construction over the 3 parallel builds (~2100 lines): HilbertLindenbaum, HilbertLindenbaumRel, HilbertAlgCompleteness (4th in Bimodal). (b) Make litCtx_congr public and parameterize the 3 Classical completeness files (~700 lines, litCtx_congr' copied 3x) over the axiom predicate via GenericMCSBridge/HasMinimalAxioms. (c) Assess 3 Soundness modules + 8 conservativity modules + LJ/LK helper duplication. Source: §5.5.

---

### 375. Proof system equivalence tableau sequent edges
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 317

**Description**: Complete the cross-system equivalence story by folding the tableau (and remaining sequent) decision systems into the proof-system TFAE. Cslib/Logics/Propositional/ProofSystemEquivalence.lean currently proves Hilbert<->ND<->LK for CPL (cplProofSystemsTfae) and Hilbert<->ND<->LJ for IPL (iplProofSystemsTfae), plus the MPL Hilbert<->ND two-way. Add the missing edges so the equivalence is genuinely complete across all proof systems: classical Tautology <-> LK provability <-> closed classical tableau, and intuitionistic validity <-> LJ provability <-> closed intuitionistic tableau, extending the TFAE lists accordingly. Requires the tableau soundness+completeness to be green (task 316 done for soundness; task 317 for completeness) and the classical tableau build repaired (task 363). No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 317, 363.

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
- **Dependencies**: Task 299, Task 503, Task 504, Task 505, Task 506
- **Research**:
  - [300_modal_extensions_t_s4_s5/reports/01_frame-specific-tableau-extensions.md]
  - [300_modal_extensions_t_s4_s5/reports/02_spawn-analysis.md]
- **Plan**: [300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md]

**Description**: Extend modal K tableau (task 299) with frame-specific rules for reflexive (T), transitive (S4), and equivalence-relation (S5) frames. T: reflexivity rule (box phi at w implies phi at w). S4: transitivity-aware propagation with loop-checking for termination. S5: equivalence-class simplification (mirrors bimodal approach). Include rules for B (symmetric) and 5 (Euclidean) to cover full modal cube. Each extension needs own completeness proof showing extracted countermodel satisfies frame condition. Files: FrameRules.lean, LoopChecking.lean, S5Simplification.lean, FrameSoundness.lean, FrameCompleteness.lean. Estimated: 1,200-1,800 lines.

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
