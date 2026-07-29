# Change Log

## 2026-06-24

Archived 6 tasks:
- Task 304: hilbert_algebra_typeclass — COMPLETED
- Task 309: hilbert_algebra_soundness_completeness — COMPLETED
- Task 315: lj_intuitionistic_sequent_calculus — COMPLETED
- Task 318: ipl_conservative_over_conj_imp_bot — COMPLETED
- Task 291: three_way_proof_system_equivalence — COMPLETED
- Task 313: zulip_propositional_logic_proof_systems_overview — ABANDONED (No longer needed)

## 2026-07-24

Archived 21 tasks:
- Task 550: remove_bimodal_temporal_linter_suppressions — COMPLETED
- Task 549: prune_canonicalmodel_redundant_imports — COMPLETED
- Task 474: draft_zulip_replies_meeting_fragments — COMPLETED
- Task 393: reuse_consolidation_lindenbaum_classical — COMPLETED
- Task 405: proof_style_cleanup_modal_soundness — COMPLETED
- Task 407: mpl_base_structure_first_redesign — COMPLETED
- Task 412: simplify_proofs_normalization_foundations — COMPLETED
- Task 438: pr_task431_comment_cleanups — COMPLETED
- Task 449: define_bxplus_metric_tense_base — COMPLETED
- Task 451: bxplus_completeness_over_group_flows — COMPLETED
- Task 522: uniform_frame_condition_axiom_correspondence_library — COMPLETED
- Task 535: abstract_termination_measure_interface_s4b_loop — COMPLETED
- Task 539: consolidate_modal_truth_lemma_single_generic_route — COMPLETED
- Task 540: retire_wrap_unwrap_combinator_bridge_layers — COMPLETED
- Task 541: ltl_temporal_semantic_preservation_bridge — COMPLETED
- Task 542: strip_task_provenance_stale_claims_docstrings — COMPLETED
- Task 543: remove_dead_logic_modules_and_dead_end_bridges — COMPLETED
- Task 544: unify_validity_derivability_naming_notation — COMPLETED
- Task 545: collapse_prop_algebra_completeness_stack_conservativity_sprawl — COMPLETED
- Task 546: factor_intersystem_lattice_onto_schemaunion — COMPLETED
- Task 547: minimal_sequent_calculus_lm_close_tfae_matrix — COMPLETED

## 2026-07-26

Archived 8 tasks:
- Task 463: vet_299_455_doc_touchups — COMPLETED (markdown) — ORGANISATION.md tree-sketch entries for Foundations/Logic/ and Logics/Modal/; 4 ephemeral task-number docstring citations in LoopChecking.lean rewritten to durable S4LoopInv-structure anchors
- Task 519: fix_literature_ocr_chunking_and_wijesekera — COMPLETED (general)
- Task 552: tableau_calculus_conformance_rule_completeness_repair — COMPLETED (cslib) — 8 phases; conformance harness gate, propositional T(->) branching arm and soundness re-proof, per-branch eventuality tracker, temporal rule arms, cap removal. Fixed two real defects: undirected ancestorTimes traversal in Branch.lean/SignedFormula.lean, and allPastPosAt using future-only ordering in Rules.lean. All 43 conformance rows green; build 3253/3253, test 9247/9247; sorry count 5, axiom count 26 unchanged
- Task 555: literature_search_fidelity_schema_quarantine — COMPLETED (general)
- Task 559: tableau_measured_baseline_doc_corrections — COMPLETED (cslib) — measured baseline table with reproduction commands landed in LoopChecking.lean module docs; 4 adjudicated documentation defects corrected, including recording that Massacci2000 Theorem 8.1 is stated but never proved in its cited source. Documentation-only; subsystem sorry census unchanged at 1
- Task 560: repair_literature_subindex_massacci_chunks — COMPLETED (meta) — four-tier chunk-count precedence in literature-briefing.sh; 19 of 34 sub-index documents repaired (Massacci 1->77, simpson_1994 1->206); regression sentinel held at 6. Open follow-up: .claude/ is git-excluded, so the fixed script is untracked
- Task 561: tableau_abstraction_decision_record — COMPLETED (cslib) — 645-line modal-tableau abstraction decision record with seven verdicts D1-D7, no DEFERs. Tasks 562-567 remain gated pending human sign-off of section 12
- Task 570: nested_sound_impL_lambda_chain_induction — COMPLETED (cslib) — discharged nested_sound_impL via the source's page-10 Lambda-chain induction plus three pre-existing defect repairs (missing lemma 4.7(ii), off-by-one InputCtx.outputPruning at Lambda = [], missing NestedProof.cut case). Cslib/ bare-sorry census 41 -> 40; build 3259/3259, test 9253/9253; all three theorems axiom-clean

Memory harvest: 3 memories created from Task 552 (CslibTests conformance harness config, Fitting-split T-implication pattern, executed-conformance-before-completeness-proofs technique).

## 2026-07-29

Archived 6 tasks:
- Task 317: propositional_tableau_completeness — COMPLETED (cslib) — plan v14 fuel-materialization repair: per-branch-fuel expansion engine replaced the unmaterializable global-fuel engine (Phases 1-4C), hUniv/hNW/hFuel threading invariants and R1 restatement (Phases 5-6), documentation-accuracy + full-CI-gate phase (Phase 8). Phase 7 (truthLemma T-imp Gap 1) BLOCKED with named owner: closure route structurally unavailable after the ancestor-blocking calculus repair removed the self-copy channel, and reinstating it would not suffice since truthLemma's frame ranges over an augmented accessibility relation the channel cannot reach. T-imp sorry re-annotated as DP-5 with follow_up_task 430. Terminal state: 4 bare sorries in subtree (DP-2 -> task 585, DP-3/DP-4/DP-5 -> task 430), all strategic and tracked; axiom profile clean; build/test/lint-style/shake green
- Task 413: simplify_proofs_normalization_propositional — COMPLETED (cslib) — removed all 20 redundant `simp only [listImp_*|bigconj_*]` rewrite invocations plus 19 accompanying `unfold ListDeriv` lines across 8 files repo-wide, each replaced with the bare `exact` that already discharges the goal by defeq. Scope corrected from Propositional-only to repo-wide per the research report's verified finding. Four one-line defeq-reliance doc comments added to the per-logic derivTreeToList* bridge lemmas. All 7 phases, no exclusions or reverts
- Task 414: simplify_proofs_normalization_modal_family — COMPLETED (cslib) — collapsed hand-rolled classical reasoning in the and/or arms of bimodal_truthAt_toBimodal_iff_satisfies (ModalConservativity.lean) to single-line simp only + tauto (3 insertions, 20 deletions); box/diamond arms untouched. Full CI green (build 3309/3309, test 9374/9374, lint, lint-style, shake, checkInitImports)
- Task 456: shared_tableau_containment_blocking — COMPLETED (cslib) — logic-agnostic containment-blocking module at Foundations/Logic/Tableau/Blocking.lean across five phases: definitional layer (Branch.typeAt, posTypeAt, containmentBlocked with membership/iff specs) and counting layer (corrected distinctTypes_le_pow bounding distinct label types by 2^n, pigeonhole corollary exists_typeAt_eq_of_card_lt, Dershowitz-Manna strict-chain bound strictChain_le_card) — zero-sorry on the standard 3 axioms. Temporal timeType/isSubsetBlocked redirected onto the shared layer as defeq wrappers, 24 TableauConformance rows green; references.bib gained DershowitzManna1979 and enriched GargGenoveseNegri2012
- Task 530: consolidate_chronicle_construction_bimodal_temporal — COMPLETED (cslib) — PARTIAL consolidation per recorded user scoping decision: Phases 0/1/2/3a (ChronicleInterface skeleton, generic Types, RRelation shared core, CEE Structures + BurgessHelpers) landed sorry-free; Phases 3b/3c/4a/4b formally DESCOPED after two independent investigations confirmed generic lifting breaks rcases/simp on Finset-membership subterms indexed by each logic's local Chronicle type; Phase 5 cleanup completed. Blocker-escalation cycle corrected the plan's completion bar in place: the original end-to-end pre-pr-check.sh bar is unsatisfiable by construction for any scoped task (steps 1 and 5 are repo-wide sorry gates across four Cslib/ trees), replaced with the task-scoped form the gate actually supports
- Task 574: tableau_calculus_repair_ancestor_blocking — COMPLETED (cslib) — repaired the intuitionistic propositional tableau's divergence on a complexity-9 witness formula by removing a self-copy channel and replacing the descendant-directed loop-check with ancestor-directed Sfor-containment blocking (intFImpReuseWitnessAnc?), then closed the resulting proof-side gap using a loop-back-edge augmented accessibility relation (Garg-Genovese-Negri M-union-C countermodel construction) threaded through intExpandBranches_openBranch_sat's induction, after an initial blocking-quotient-frame approach (~480 lines, landed then deleted) proved structurally unable to carry the induction. Acceptance gate intExpandBranches_closed_unsat sorry-free and axiom-clean; repo-wide bare-sorry count at its exact 6-entry pre-task baseline; TableauConformance.lean regenerated to 44 rows with a termination-regression guard for the divergence witness

Deferred: Task 557 (modal_tableau_refactor_abstractions_boneyard, EXPANDED) held back — subtasks 558, 562-567 still active.

Memory harvest: 4 memories created from Task 317 (T-imp sibling-copy counterexample, #eval-computable-defs-before-proving pattern, mutually-incompatible-design-fixes root cause, validated fast-language re-implementation as research instrument).
