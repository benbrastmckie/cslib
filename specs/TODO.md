---
next_project_number: 588
---

# TODO

## Task Order

*Updated 2026-08-06. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,375,400,409,425,554,567,568,569,583 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,450,497,511,534,537,551,571,576,582 | 36,37,181,425,554,567,568 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41,506,548 | 39,40,511 | foundations, modal logic |
| 4 | 300 | 506 | modal logic |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

375 [NOT STARTED] — Fold the TABLEAU decision systems into the propositional proof-sy
400 [NOT STARTED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
409 [BLOCKED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
583 [BLOCKED] — Restate `intExpandBranches_openBranch_sat` (Cslib/Logics/Proposit
497 [NOT STARTED] — Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (P

### Modal Logic

554 [BLOCKED] — [RESCOPED 2026-07-26 by explicit user decision, adopting report 0
  └─ 537 [BLOCKED] — Prove the general labelled SOUNDNESS direction nik_TS5_soundness 
  └─ 551 [BLOCKED] — Deliver NATIVE Hilbert canonical-model completeness for construct
567 [PLANNED] — [Task I of the modal-tableau refactor programme; P4, final accept
  └─ 511 [BLOCKED] — Follow-on to task 506 (S4 loop-checking): close the S4 terminatio
    └─ 506 [BLOCKED] — Deliver plan Phases 5 and 6 of task 300 combined (specs/300_modal
      └─ 300 [BLOCKED] — Umbrella task for modal frame extensions T/S4/S5 (and the derived
    └─ 548 [NOT STARTED] — COMPLETENESS-MATRIX GAP (review 2026-07-23, M3). Tableau decidabi
  └─ 534 [NOT STARTED] — COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree 
  └─ 582 [NOT STARTED] — Resolve `branchSatisfiableIn_s4FC_ancestor_redirect` (Cslib/Logic

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

### Bimodal And Temporal Logic

568 [BLOCKED] — [Follow-on created by the blocked-task review, at explicit user r
  └─ 576 [NOT STARTED] — Resolve the `namespace Chronicle` / `structure Chronicle` NAME CO

## Tasks

### 587. Canonical witness restriction probe
- **Effort**: 6-9 hours
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Plan**: [587_canonical_witness_restriction_probe/plans/01_canonical-witness-restriction-probe.md]
- **Research**: [587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md]
- **Summary**: [587_canonical_witness_restriction_probe/summaries/01_canonical-witness-restriction-probe-summary.md]

**Description**: Task 553 (s4_loop_guard_soundness_reachability_restriction) is blocked: plan v5's Gate A (Phase 1, 'DECISION GATE A -- the pinned redirect-preservation lemma') died at a machine-checked stuck goal, recorded in that plan's `#### Phase 1 Verdict` (specs/553_s4_loop_guard_soundness_reachability_restriction/plans/05_pinned-witness-truth-lemma.md). The stuck goal: the structural-induction agreement lemma `Satisfies m x chi <-> Satisfies m' x chi` (needed to show the redirect edge preserves `branchSatisfiablePinnedIn s4FC`) escapes to model points outside `modalKnownWorlds b` when the induction unwinds a `.box`/`.diamond` subformula, and neither `accPinnedBy` nor `hbox`/`hdia` (both deliberately restricted to known branch labels) supply any fact there. The Phase 1 Verdict names, but explicitly declines to price, the fix: a canonicity assumption on the witness model (WLOG `W := WorldIndex`, `f := id`, so every model point is trivially a known label). This task's job is to answer that priced-viability question, not to redo work already completed: (1) do NOT re-run or re-propose the FrameCompleteness refactor programme -- it already landed (its box-plus birth content is now inline in the mainline `successorBirthContent`/`blockingWorldS4Keyed` in Cslib/Logics/Modal/Tableau/LoopChecking.lean, not as the separate parallel `...Boxed` family plan v5's Phases 5-7 anticipated -- that framing is stale); (2) do NOT touch the pre-existing, standing `sorry` at Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1251 (`branchSatisfiableIn_s4FC_ancestor_redirect`), retained by explicit user decision; (3) DO preserve and reuse, do not re-derive, the already-landed, sorry-free, standard-axioms-only sub-step 1.1 declarations `accPinnedBy`, `branchSatisfiablePinnedIn`, and `branchSatisfiablePinnedIn_redirect_mechanical` (Cslib/Logics/Modal/Tableau/FrameSoundness.lean, currently at :5323-5390 -- re-locate by `grep -n '^def\|^lemma\|^theorem'` rather than trusting these line numbers, since the file continues to drift). Concretely: (a) attempt a machine-checked micro-probe of the box-positive and diamond-negative agreement-lemma cases under the added hypothesis that `x`/the witness carrier is restricted to `WorldIndex` via `f := id` (mirroring the existing precedent `extractModelS4`/`extractModelWith` in Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:85-148, which already builds `Model WorldIndex Atom` directly with no existential `W`/`f` -- this is the same canonical-model shape Massacci2000 Thm 10.6 uses on the completeness side); determine whether restricting the carrier actually closes the exact stuck goal recorded in the Phase 1 Verdict, or dies at a new, different obstruction; (b) if the probe succeeds (even partially, i.e. one of box-positive/diamond-negative closes and the other's failure mode is well understood), price the consequences: which existential fields of `branchSatisfiablePinnedIn` must be re-shaped or collapse under the restriction, whether sub-step 1.1's three mechanical conjuncts (the `IsTrans`/`Std.Refl`/edge-conjunct/`accPinnedBy`-preservation cluster) survive verbatim against a fixed carrier or need re-derivation, and a phase-count/effort estimate for a resulting v6 plan; (c) if the probe fails, record the exact machine-checked stuck goal (in the same style as the plan's existing `#### Phase 1 Verdict`) and state plainly that no route is currently known, rather than proposing a further ad hoc route. Follow the plan's own front-loaded kill-gate discipline: do not scaffold any large construction before the micro-probe's own verdict is in. Write findings as a research report under specs/553_s4_loop_guard_soundness_reachability_restriction/reports/ (or this new task's own specs/ directory per the standard artifact convention) with a clear go/no-go verdict and, if go, a priced next-step recommendation for a task-553 v6 plan.

---

### 586. Adjudicate and delete the audited duplicate re-derivation families
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 553
- **Research**: [586_tableau_adjudicate_duplicate_families/reports/01_adjudicate-duplicate-families.md]
- **Plan**: [586_tableau_adjudicate_duplicate_families/plans/01_delete-surviving-duplicate.md]
- **Summary**: [586_tableau_adjudicate_duplicate_families/summaries/01_delete-surviving-duplicate-summary.md]

**Description**: [Continuation of Task A of the modal-tableau refactor programme; adjudicates the duplicate families the Support-module extraction left unresolved.] The statement-equivalence audit is DONE and is the input to this task -- do not re-run it: specs/558_tableau_support_private_dedup/reports/02_statement-equivalence-audit.md classifies 45 surviving re-derivation rows across four families (KNOWNWORLDS, SUBFMLS/UNIVERSE, ACCESSIBILITY, MEASURE) as 38 IDENTICAL, 6 WEAKER, 1 DIFFERENT, 0 NOT_FOUND. Delete the adjudicated duplicates and replace them with imports of the public origins.
--- THE THREE VERDICT CLASSES AND WHAT EACH REQUIRES ---
- 38 IDENTICAL rows: byte-for-byte or alpha-equivalent to their origins (notational spellings of the same proposition, e.g. list subset written as a forall-membership, and explicit-vs-implicit binder mode, both count as identical). Safe to delete and replace with an import mechanically.
- 6 WEAKER rows, ALL one family: every non-FmpMeasure copy of modalKnownWorlds_fold_spec drops BOTH the hws0 : ws0.Nodup hypothesis AND the .Nodup conjunct, keeping only the forall-iff half. MANDATORY PRE-DELETION CHECK: confirm no call site consumes the .1 (Nodup) component of the origin conjunction before deleting whole-cloth. S5Simplification.lean additionally carries _fold_nodup_S5, a separate lemma proving only the missing Nodup half; the other four files obtain it from modalKnownWorlds_nodup_S4/_S5 instead. Nothing is lost project-wide, but the recovery route differs per file -- verify per file, not once.
- 1 DIFFERENT row, and the one genuine trap: LoopChecking.lean hasEdge_mem_successorsOf_origin is the CONVERSE of a different lemma (hasEdge_mem_successorsOf, still private in the same file), NOT a copy of FmpMeasure.lean mem_successorsOf_hasEdge. Its own docstring says so. It belongs to a separate origin/converse chain and MUST NOT be deleted as a duplicate.
--- SCOPE BOUNDARY, EXPLICIT ---
This task owns statement-equivalence duplicates ONLY. It does NOT own the second roadmap item recorded on the Support-module extraction: the 5 confirmed-unreachable, privacy-caused duplicate families whose root cause is import REACHABILITY (three consumers cannot reach Soundness.lean), which de-privatization alone cannot fix. The audit supplies no verdict bearing on those; they need an architectural change and belong in their own task. Do not silently absorb them here.
--- CITATION-GRAPH AND NAMING NOTES FROM THE AUDIT (avoid rediscovering these) ---
- FiveSimplification modalMaxWorld_foldl_le_of_forall_Five / modalMaxWorld_le_of_forall_label_le_Five cite S5Simplification _S5w pair, NOT FmpMeasure directly. The chain FmpMeasure -> S5w -> Five is content-preserving, but the direct citation runs through S5Simplification.lean. Import the true origin, not the intermediate, unless the intermediate is itself public and closer.
- hasEdge_addEdge_cases_Five lives in FrameCompleteness.lean, not FiveSimplification.lean. Locate by declaration name.
- known_label_le_modalMaxWorld_Five is a renamed copy of modalKnownWorlds_le_modalMaxWorld -- identical statement, divergent name. Name divergence is not statement divergence; do not treat it as a separate fact.
- modalSubfmls_self_mem and modalKnownWorlds_nodup_S4 are already PUBLIC, not private, despite sitting in the re-derivation inventory.
- modalExpMeasure_const_exp_S4 was not in the original re-derivation enumeration (only _split and _append were); it was added because the generic engine depends on it. Provenance gap, not a statement deviation.
--- VERIFICATION ---
Behaviour-preserving by construction: every deletion must be replaced by an import of a statement-identical public origin. Gate on lake build Cslib green with the job count matching the pre-task baseline (re-measure it; the St-ladder and box-plus landings have moved it), Modal/Tableau sorry census exactly 1 (branchSatisfiableIn_s4FC_ancestor_redirect, FrameSoundness.lean -- count actual sorry terms, since naive grep over-counts on docstring prose such as sorry-free and on LoopChecking.lean own census-script text), zero new axioms, lake shake unchanged at 9 findings with NONE in Modal/Tableau (do NOT gate on shake exit 0), lake lint gated on DELTA not exit 0 (145 pre-existing findings repo-wide), checkInitImports and lint-style exit 0, lake test green.
--- ANCHOR ON DECLARATION NAMES, NEVER LINE NUMBERS. The audit records no line numbers for exactly this reason; the Support extraction, the St ladder and the box-plus landing have all moved code.

---

### 585. Prove post blocking world bound chain and mint invariant
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 317
- **Research**: [585_prove_post_blocking_world_bound_chain_and_mint_invariant/reports/01_dp2-mint-invariant-transfer.md]
- **Plan**: [585_prove_post_blocking_world_bound_chain_and_mint_invariant/plans/01_dp2-worldhist-mint-invariant.md]
- **Summary**: [585_prove_post_blocking_world_bound_chain_and_mint_invariant/summaries/01_dp2-worldhist-mint-invariant-summary.md]

**Description**: Discharge the single remaining strategic sorry DP-2 in Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean, left by the parent task's plan v14 (specs/317_propositional_tableau_completeness/plans/14_fuel-materialization-repair.md), which superseded the v13 fuel-sufficiency skeleton this task was originally scoped against.

SCOPE: DP-2 ONLY.

DP-1 RESOLVED -- OUT OF SCOPE. The ancestor-chain bound lemma `intCreatedChain_le` (Scheme.lean:1757) was discharged under plan v14 and is now fully proved and sorry-free, via exactly the route the original description anticipated: pigeonhole on `(posFormulasAt, psi)` pairs against the five-conjunct negation of the `intFImpReuseWitnessAnc?` reuse witness. It is no longer an obligation here; it is available leverage (see below). Note that the old description's guard clause -- "if the parent implementation closed both proofs inline and placed no sorry, close this task as unnecessary" -- does NOT fire: only one of the two closed. This task remains live for DP-2 alone.

DP-2 -- THE ACTUAL OBLIGATION. Current state of the tree at Scheme.lean:2602-2605:

    private lemma intFreshMint_preserves_nw {phi0 : Proposition Atom} {nw : Nat}
        (hnwB : nw <= WBound phi0) :
        nw + 1 <= WBound phi0 := by
      sorry

As literally stated this lemma is FALSE: `hnwB` is consistent with `nw = WBound phi0`, which makes the conclusion `WBound phi0 + 1 <= WBound phi0` unprovable. The bare hypothesis is genuinely insufficient. The work is therefore NOT "prove the lemma as written", but:

(a) Establish the runtime-check-to-final-branch transfer -- i.e. that a fresh-mint firing is LICENSED by the pigeonhole tree-size bound (labels minted on a branch <= tree size <= WBound phi0), not merely that the runtime counter has not yet overflowed.

(b) Restate `intFreshMint_preserves_nw` with the strict premise that transfer supplies (`nw < WBound phi0` at the point of firing, or the creation-count invariant it derives from), and thread that premise through the fresh-mint arm of `go`'s recursion at the call site.

Read the verbatim sorry comment at Scheme.lean:2580-2601 -- especially the paragraph beginning "sorry: assumes the creation-count invariant above (equivalently, that this fresh-mint firing is licensed by the pigeonhole tree-size bound, not merely that the counter has not yet overflowed)" -- and preserve its precision; it names the obligation exactly, including its own assessment that "establishing the runtime-check-to-final-branch transfer is genuinely unproven research work". The parent task's Phase 5 dispatch flagged this transfer as unowned; see the cross-references at Scheme.lean:2373 and Scheme.lean:2592, and `intCreatedChain_le`'s own docstring, which explicitly assigns the transfer to "the invariant-threading development" -- that is, to this task.

AVAILABLE LEVERAGE (all landed post-v14, all sorry-free -- the bound EXISTS and is PROVED; what is missing is only the tie to the runtime counter):
- `intCreatedChain_le` (Scheme.lean:1757) -- the pigeonhole chain bound. Supplies the tree-size side of the invariant. The remaining gap is the TRANSFER from this bound to the runtime counter `nw` on the final branch, not the bound itself.
- `WBound phi0` (Scheme.lean:1692) and `intChainBound phi0` (Scheme.lean:1683) -- the post-blocking world bound and the chain bound it rests on.
- `intUniverseExt` (Scheme.lean:2107).
- `applyPersistenceFixpoint_genuine_of_count_le_fuel` (Scheme.lean:3563).
- `intApplyRuleFull_linearResult_nextWorld` (`nw' = nw + 1` on the world-creating arm) and the sibling non-minting preservation lemmas immediately preceding DP-2 (around Scheme.lean:2571).

LINE NUMBERS are current as of commit 640b68d4. If they have shifted, re-locate by declaration name and content, never by line number. The full file:line inventory of remaining sorries lives in the parent task's summaries/14_phase7-reannotation-and-phase8-completion-summary.md sorry inventory.

SCOPE BOUNDARY. DP-2 is the ONLY sorry this task owns. The subtree Cslib/Logics/Propositional/Tableau/ currently holds exactly four bare sorries; the other three are owned by the atom-persistence/upward-closure task (specs/430_prove_atom_persistence_upward_closure_for_intexpan/, whose plan was widened to positive-formula persistence along the augmented relation in plans/04_positive-formula-persistence-augmented.md) and MUST NOT be attempted here:
- DP-5: `truthLemma` T-imp case, Scheme.lean:633
- DP-3: Intuitionistic/Completeness.lean:140
- DP-4: Minimal/Completeness.lean:128

COORDINATION RISK: both this task and the atom-persistence task edit Scheme.lean. Serialize against it, or coordinate edits explicitly; do not run concurrently on that file without a merge plan.

ACCEPTANCE GATE:
- DP-2 discharged: the sorry at Scheme.lean:2605 removed, replaced by a real proof of a correctly-premised statement.
- `lake build` green.
- Repo bare-sorry count strictly decreased by exactly one (4 -> 3).
- No weakening of any statement. Strengthening `intFreshMint_preserves_nw`'s hypotheses is expected and required per (b) above, but every consumer must be re-supplied with the new premise -- a premise added and then never discharged at the call site is a weakening in disguise.
- No sorry relocated: moving the obligation into a new sorry-bearing helper does not count as discharge.

BINDING CONSTRAINTS (carried forward from the parent plan's Postmortem Constraints, where still applicable):
- NEVER use the unsigned `eraseDups`/`2 ^ U.length` bound form.
- NEVER edit `intFImpReuseWitnessAnc?`.
- The bound MUST come from blocking combinatorics, NEVER from `intUniverse`'s linear range. This constraint is now doubly binding: the parent task's research established that the linear world bound is REFUTED OUTRIGHT for the pre-repair calculus, and that the sound post-repair bound is `WBound phi0`.
- The vacuous-definition prohibition applies (`def X := True`, `theorem X := trivial`, and kin are semantically equivalent to sorry and are not discharges). If the transfer cannot be established, mark the phase [BLOCKED] with what was tried and what goal state was reached, rather than substituting a placeholder.

---

### 584. Give pre-pr-check.sh step 1 a baseline ratchet or changed-files mode
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None
- **Research**: [584_scope_pre_pr_check_sorry_gate/reports/01_scope-pre-pr-check-sorry-gate.md]
- **Plan**: [584_scope_pre_pr_check_sorry_gate/plans/01_scope-sorry-gate-delegation.md]
- **Summary**: [584_scope_pre_pr_check_sorry_gate/summaries/01_scope-sorry-gate-delegation-summary.md]

**Description**: Step 1 of scripts/pre-pr-check.sh is a TREE-WIDE gate wearing a scoped label. It finds every *.lean under four whole trees (Cslib/Foundations/Logic/, Cslib/Logics/Modal/, Cslib/Logics/Temporal/, Cslib/Logics/Bimodal/) and fails on ANY sorry found anywhere in them, despite announcing itself as 'Checking for sorry instances in PR scope...'. The script's own comment above the step-8/9 ratchets states the contrast outright: step 1 'scans a narrow, hand-picked directory set and fails on ANY sorry found there', whereas steps 8/9 'ratchet whole-tree sorry/suppression/axiom-taint debt against a frozen baseline, and pass on the existing debt by construction'.

CONSEQUENCE: the completion bar 'pre-pr-check.sh passes end to end' is unsatisfiable by construction for ANY scoped task -- it can only be met when the entire repository is simultaneously sorry-free. It is worse for a task whose guardrails deliberately FREEZE a sorry baseline inside its own file_scope: such a task cannot make step 1 pass without violating the scoping decision that defines it. This already forced one completed consolidation task into a spurious [PARTIAL] and a blocker-escalation cycle that resolved by correcting the completion bar rather than by any proof work. Every future scoped Lean task inherits the same wall.

MEASURED STATE (verified 2026-07-28, full gate run): steps 1 and 5 FAIL; steps 2, 3, 4, 6, 7, 8, 9 all pass with every ratchet exactly at baseline (blanket suppressions 19/19, shake-flagged files 9/9, markers 18/18, sorries 28/28, sorryAx-tainted declarations 43/43). Step 1's real failure set is 24 sorry hits across 6 files: ChronicleToCountermodel.lean (12), Bundle/SuccRelation.lean (7), Bundle/UntilSinceCoherence.lean (2), Modal/Tableau/FrameSoundness.lean (1), ConservativeExtension/TemporalConservativity.lean (1), BXCanonical/Frame.lean (1).

WORK: give step 1 the treatment steps 6-9 already have -- either a frozen per-file sorry baseline it ratchets against (failing only on NEW debt), or a changed-files mode that scans only what the current branch actually touches (e.g. `git diff --name-only` against the merge base), or both behind a flag. scripts/check-sorry-suppressions.sh is the working in-repo pattern to mirror; prefer reusing its baseline machinery over inventing a second one. Fix step 1's misleading 'in PR scope' wording to match whatever behaviour is chosen.

EXPLICIT NON-GOAL: do NOT narrow step 5 (`lake build --wfail --iofail`). It deliberately mirrors CI and must keep failing on repo-wide sorry warnings; weakening it would hide real regressions. Note also that steps 1 and 5 have DIFFERENT scopes and are not redundant -- three Propositional/Tableau/* files trip step 5 but are not scanned by step 1 at all, so neither check substitutes for the other. Do not attempt to resolve any of the existing sorries as part of this task; this is gate-scoping work, not proof work.

---

### 583. Restate intexpandbranches openbranch sat
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 574
- **Research**: [583_restate_intexpandbranches_openbranch_sat/reports/01_restate-openbranch-sat.md]

**Description**: Restate `intExpandBranches_openBranch_sat` (Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:2583, sorry at :2623) so that it is provable, then discharge it.

THE GOAL IS FALSE AS STATED -- this is not a proof-effort obligation and cannot be closed by proving harder. The in-file comment (Scheme.lean:2598-2622) records an explicit Lean-verified counter-instance to the `fuel = 0` base case: with `branches = [[<.neg, p /\ q, 0>]]`, `expandedSets = [[]]`, `nextWorlds = [1]`, `edgeSets = [[]]`, every hypothesis of the lemma holds while `IBranchSaturation` fails. The comment states outright: "No proof can close this `sorry` at the lemma current statement."

SCOPE: determine the correct strengthened statement (most likely an added saturation or fuel-sufficiency precondition on the `fuel = 0` case), restate the lemma, repair its call sites, and discharge the sorry.

RELATIONSHIP TO THE DIVERGENCE REPAIR: the divergence-repair task addresses the root cause shared by all four propositional tableau sorries (the fuel-bounded persistence loop in `applyAllTImpRules` copying `T(phi->psi)` into accessible worlds). The restatement here may fall out of that repair, or may need to be done independently -- resolve that first. This task exists because the restatement obligation is named in no other task description and must not be silently skipped when the divergence repair lands.

VERIFY BEFORE STARTING: re-read Scheme.lean:2598-2622 and confirm the counter-instance still refutes the current statement; if the divergence repair has already restated the lemma, close this task as superseded rather than duplicating the work.

---

### 582. Resolve the S4 ancestor-redirect sorry, the only sorry with no owning task
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 553, Task 566, Task 567, Task 586

**Description**: Resolve `branchSatisfiableIn_s4FC_ancestor_redirect` (Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1252) -- the ONLY sorry in the repository with no owning task.

WHY THIS TASK EXISTS: every other sorry in Cslib/ is owned (the intuitionistic/minimal tableau completeness cluster, the bimodal discrete-gated set, the bimodal strict-Until/Since set, and the temporal conservativity obligation each have a task). This one is protected but not owned: the Boneyard-migration task carves it out as IMMOVABLE precisely BECAUSE it carries a retained sorry, which keeps it in the tree indefinitely without anyone being tasked to close it.

THE OBSTRUCTION IS DOCUMENTED AND UNUSUAL -- READ THE IN-FILE DOCSTRING FIRST (FrameSoundness.lean, immediately above the lemma). Its central finding: successive soundness routes for this guard have appealed to Massacci (2000), "Single Step Tableaux for Modal Logics", Theorem 8.1 (blocking preserves satisfiability), but IN THAT PAPER THEOREM 8.1 IS STATED AND NEVER PROVED. Its Appendix B.2, headed "PROOFS OF SECTION 8", proves Theorem 8.4 only; where the section-8 (pi-modal-completed) extension is discussed, the paper defers it to the completeness proofs of its references [7] (prefixed tableaux) and [20] (completeness via model graphs). CONSEQUENCE: any further attempt to close this sorry by following that citation will find nothing to follow. Do not re-derive this finding from scratch; it is recorded so it is not rediscovered a fourth time.

CONSUMER AUDIT (re-run live at task creation, superseding the docstring's stale "1 hit" phrasing): 3 grep hits for the name across Cslib/ and CslibTests/, of which exactly ONE is the declaration itself; the other two are docstrings -- one at FrameSoundness.lean:1231 quoting the audit command, one at LoopChecking.lean:113 cross-referencing it. So the substantive claim holds: ZERO code consumers. The sorry propagates into no other result and is a recorded obstruction rather than load-bearing debt. RE-RUN THIS AUDIT at execution time before acting on it.

THE DECISION THIS TASK MUST MAKE (research first, then choose explicitly and record why):
(a) IMPORT the model-graph construction from Massacci's references [7]/[20] and prove the guard sound. Largest scope; the only route that yields a genuine proof.
(b) RESTATE the lemma to something provable from the driver-independent hypothesis set actually available, if a weaker but still meaningful statement exists. The docstring's obstruction paragraph describes what that hypothesis set can and cannot supply -- start there.
(c) DELETE the lemma. Legitimate precisely because it has zero code consumers: removing it discharges the sorry without weakening any result that anything depends on. This requires reversing the retain-by-user-decision that currently keeps it, and coordinating with the Boneyard-migration task, whose carve-out rationale ("it carries the retained sorry") evaporates the moment the sorry is gone.

DO NOT close this sorry by weakening the statement into something vacuous or trivially true. If (b) is chosen, the restated lemma must still say something about satisfiability preservation under ancestor redirect, and the restatement must be justified in the commit and the docstring.

DEPENDENCY RATIONALE: sequenced after the S4 loop-guard soundness task, which holds explicit authorization to edit the otherwise-frozen keyed-guard code and lists FrameSoundness.lean in its own file_scope. Its finding -- whether the guard can be narrowed at all without collapsing the termination argument -- directly informs whether route (b) has a target at all. Starting first risks doing the work twice.

DEFINITION OF DONE: route (a), (b), or (c) is chosen with the reasoning recorded in the plan AND in the file (or in the commit, if the file is removed); FrameSoundness.lean contains no sorry; `lake build --wfail --iofail` emits strictly fewer sorry warnings than before and no new warnings of any kind; `lake test` stays exit 0; no other proof, definition, or theorem statement is altered; if route (c) is taken, the Boneyard-migration task's carve-out is updated to record that its rationale no longer applies.

---

### 576. Resolve the Chronicle namespace/structure name coincidence and its 36 load-bearing suppressions
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal and Temporal Logic
- **Dependencies**: Task 530, Task 568

**Description**: Resolve the `namespace Chronicle` / `structure Chronicle` NAME COINCIDENCE, and delete the 36 suppressions it forces (33 @[nolint], 3 set_option) across the three ChronicleTypes/Types files, 9 declarations each.

ORIGIN: identified during the repo-wide lint-hygiene work as the genuine residual defect behind a group of dupNamespace suppressions. That work closed its doubled-namespace phase at 7 of 10 files and deliberately EXCLUDED the three Chronicle modules, because the original doubled-namespace diagnosis was WRONG there: `namespace ...Metalogic.Chronicle` contains `structure Chronicle`, so `def Chronicle.c0` correctly declares a structure-projection member that 81 dot-notation call sites (chi.c0, chi.c3, ...) depend on. A mechanical prefix strip fails with "Invalid field 'c0': the environment does not contain ...Chronicle.Chronicle.c0". The 36 suppressions are LOAD-BEARING until the coincidence itself is resolved -- do NOT delete them before the restructure lands.

THE DECISION: either (a) move `structure Chronicle` to the parent namespace, or (b) rename the namespace across the whole Chronicle/ subtree, or (c) a better option surfaced by the dependency below. This alters definitions, which is why it was barred from the hygiene-only lint task.

DEPENDENCY RATIONALE (task 568): 568 asks what the RIGHT Chronicle architecture is for Bimodal/Temporal dedup, evaluating type-alias, label-type parameterization, and typeclass-mediated indexing. Its file_scope is the three Chronicle DIRECTORIES and strictly contains this task's three files. If 568 recommends parameterizing the structure away, the naming question resolves differently -- or evaporates entirely. Renaming first would risk doing the work twice. Sequence after 568 reports.

DEFINITION OF DONE: the namespace/structure coincidence is resolved by an explicit, recorded decision; all 36 suppressions are deleted; dupNamespace is clean across the three files; the 81 dot-notation call sites still resolve; `lake build --wfail --iofail` shows no new warnings and `lake test` is unchanged.

CONSTRAINT: preserve every landed sorry-free result; do not discharge, add, or relocate any sorry.

---

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

## LINE NUMBERS ARE STALE (repo-wide lint/CI audit)

The line numbers in the body above are dated 2026-07-26 and have since moved -- the repo-wide lint-hygiene pass rewrapped long lines, deleted blank lines inside single-command blocks, and narrowed blanket linter suppressions to declaration scope across these files. RE-DERIVE EVERY LINE NUMBER LIVE (`grep -n sorry <file>`) before acting; do not trust the recorded positions.

The FILE-LEVEL scope and the sorry COUNTS per file are unchanged and remain accurate. The sorries in these files are currently hidden from `lake build --wfail --iofail` by `set_option warn.sorry false in` markers; filling them must also DELETE the corresponding marker, so the suppression count drops with the sorry count. A suppression ratchet is being added under a separate task to enforce exactly that.

---

### 569. Establish whether continuous time needs axioms beyond density (Burgess 1982)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 530

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
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 553, Task 558, Task 562, Task 563, Task 564, Task 565, Task 566, Task 586
- **Research**: [567_tableau_vetting_pipeline_acceptance_gate/reports/01_acceptance-gate-ci-verification.md]
- **Plan**: [567_tableau_vetting_pipeline_acceptance_gate/plans/01_acceptance-gate-fixes-verdict.md]

**Description**: [Task I of the modal-tableau refactor programme; P4, final acceptance gate. Depends on every other task in the programme.] Run the seven-step CI order from .claude/rules/cslib.md against CONTRIBUTING.md, NOTATION.md, ORGANISATION.md and CODE_OF_CONDUCT.md. It has never been run on this subsystem. PREREQUISITE, budget for it: lake exe checkInitImports currently FAILS on a stale build unrelated to this subsystem (a missing Constructive/Nested/Soundness.olean), so a full lake build must clear that before verification against the stated gate is meaningful. ACCEPTANCE CRITERIA: behaviour preservation demonstrated by modalTableauS4Keyed_complete and the six landed Decidable instances (K/T/B/S5/Five/KB5) remaining green; the Tableau sorry census not rising above its measured baseline of exactly 1; no new axioms above the measured subsystem baseline of zero; checkInitImports and lint-style clean; and the existing executable regression corpora (CslibTests/S4LoopGuardRegression.lean, 197 lines, plus the probe harnesses under the S4 loop-guard task's artifacts directory) reproducing their recorded verdicts EXACTLY.
--- ESTABLISHED BY THE SUPPORT-MODULE EXTRACTION (landed; supersedes any conflicting figure above) ---
- Cslib/Logics/Modal/Tableau/Support/Accessibility.lean and Support/KnownWorlds.lean NOW EXIST as public modules importing only Branch. Facts formerly re-derived per-file (hasEdge_addEdge_cases, mem_modalKnownWorlds, modalKnownWorlds_mono_append and relatives) are imported, not restated. Do not reintroduce a local copy.
- A third Support/Subfmls.lean was evaluated and REJECTED: modalSubfmls/modalUniverse are defined in FmpMeasure.lean itself, so such a module would sit ABOVE it and buy nothing; those facts were de-privatized in place. Two Support modules is the final shape, not three.
- The duplicate inventory was re-measured by SIGNATURE matching, not by counting 'Local re-derivation' comments: 72-74 duplicate declarations across 41-43 families. 17 duplicates carried NO such comment, and the comments also mislead in the other direction (they falsely flagged a byte-identical lemma as deviant). If this task counts, deletes, or audits duplicates, drive off signatures; a comment-string grep silently under-counts.
- Root cause is import REACHABILITY, not privacy: three consumers cannot reach Soundness.lean, so de-privatization alone cannot fix that class. At least one duplicate exists for an unrelated reason (an ambient [Hashable Atom] instance callers cannot omit).
- VERIFICATION BASELINE: lake build Cslib green at 3313 jobs; Modal/Tableau sorry census exactly 1; zero axioms in the subsystem; lake shake exit 1 with 9 findings, NONE in Modal/Tableau -- do NOT gate on shake exit 0, gate on "no Modal/Tableau findings AND count stays 9"; checkInitImports and lint-style both exit 0.
- ANCHOR ON DECLARATION NAMES, NEVER LINE NUMBERS. The extraction deleted code and moved declarations; any line number in this description may already be stale.

---

### 566. Create Boneyard/ with its convention and move only re-verified zero-consumer declarations
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 553, Task 563, Task 564, Task 586
- **Research**: [566_boneyard_creation_eligible_moves/reports/01_boneyard-convention-and-consumer-reaudit.md]
- **Plan**: [566_boneyard_creation_eligible_moves/plans/01_boneyard-creation-eligible-moves.md]
- **Summary**: [566_boneyard_creation_eligible_moves/summaries/01_boneyard-creation-eligible-moves-summary.md]

**Description**: [Task H of the modal-tableau refactor programme; P3.] Create Boneyard/ at the repository root (it does not currently exist here; the convention is borrowed from the upstream repository, where it holds roughly 27k lines and 29 sorries excluded from porting, censuses and the build). Document the convention in Boneyard/README.md: quarantined, never imported by Cslib/, excluded from lake build, mk_all, lint-style, shake and all sorry/axiom censuses, retained for provenance rather than use. MOVE, never delete. RE-RUN THE CONSUMER AUDIT AT EXECUTION TIME -- the recorded audit is dated and this is a multi-task programme. Eligible subject to that re-check: blockedRedirect_diaNeg_mem_of_diaOrigin, blockedRedirect_boxctx_mem_of_boxOrigin, the keysRootEmpty / keysRootEmpty_entry pair, and the two outDegEq preservation lemmas ONLY if the migration task actually landed the field removal. TWO CARVE-OUTS ARE MANDATORY. (1) FrameSoundness.lean, lemma branchSatisfiableIn_s4FC_ancestor_redirect -- locate BY NAME; post-extraction the declaration is ~1227 and its sorry ~1251, not 1220-1244 (branchSatisfiableIn_s4FC_ancestor_redirect) is IMMOVABLE despite being zero-consumer: it carries the retained sorry that is an explicit user decision, and the rule protecting proven-and-consumed code does not by itself protect it. (2) keysOriginS4 is NOT eligible -- it has 22 code consumers, and the comment at LoopChecking.lean:2001-2002 claiming it was removed is FALSE. Nothing whose deletion cannot be justified by a re-verified zero-consumer check may be moved, and nothing proven and consumed may be moved at all. Also NOT eligible, these are route-independent assets to be PLACED by the abstraction decision rather than quarantined: modalS4Saturated (7 consumers), the strictly-weakened hintikkaS4 bridges (the set is 8, measured, not 10), hasEdge_accWithReds_iff, reflTransGen_accWithReds_first_red, and the two sorry-free blockedRedirect_unwrapped_{boxPos,diaNeg}_mem transfers with their Reds / accWithReds packaging.
--- ESTABLISHED BY THE SUPPORT-MODULE EXTRACTION (landed; supersedes any conflicting figure above) ---
- Cslib/Logics/Modal/Tableau/Support/Accessibility.lean and Support/KnownWorlds.lean NOW EXIST as public modules importing only Branch. Facts formerly re-derived per-file (hasEdge_addEdge_cases, mem_modalKnownWorlds, modalKnownWorlds_mono_append and relatives) are imported, not restated. Do not reintroduce a local copy.
- A third Support/Subfmls.lean was evaluated and REJECTED: modalSubfmls/modalUniverse are defined in FmpMeasure.lean itself, so such a module would sit ABOVE it and buy nothing; those facts were de-privatized in place. Two Support modules is the final shape, not three.
- The duplicate inventory was re-measured by SIGNATURE matching, not by counting 'Local re-derivation' comments: 72-74 duplicate declarations across 41-43 families. 17 duplicates carried NO such comment, and the comments also mislead in the other direction (they falsely flagged a byte-identical lemma as deviant). If this task counts, deletes, or audits duplicates, drive off signatures; a comment-string grep silently under-counts.
- Root cause is import REACHABILITY, not privacy: three consumers cannot reach Soundness.lean, so de-privatization alone cannot fix that class. At least one duplicate exists for an unrelated reason (an ambient [Hashable Atom] instance callers cannot omit).
- VERIFICATION BASELINE: lake build Cslib green at 3313 jobs; Modal/Tableau sorry census exactly 1; zero axioms in the subsystem; lake shake exit 1 with 9 findings, NONE in Modal/Tableau -- do NOT gate on shake exit 0, gate on "no Modal/Tableau findings AND count stays 9"; checkInitImports and lint-style both exit 0.
- ANCHOR ON DECLARATION NAMES, NEVER LINE NUMBERS. The extraction deleted code and moved declarations; any line number in this description may already be stale.

---

### 565. Split LoopChecking.lean along the real S4 seams and update ORGANISATION.md
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 553, Task 563, Task 564, Task 566, Task 586
- **Research**: [565_loopchecking_split_s4_modules/reports/01_split-loopchecking-into-s4-modules.md]
- **Plan**: [565_loopchecking_split_s4_modules/plans/01_split-loopchecking-s4-modules.md]
- **Summary**: [565_loopchecking_split_s4_modules/summaries/01_split-loopchecking-s4-modules.md]

**Description**: [Task G of the modal-tableau refactor programme; P3. Depends on the review gate, box-plus and the migration, because the seams MOVE if box-plus is adopted.] Split LoopChecking.lean (10,540 lines / 230 declarations, measured) into an S4/ cluster of Universe, BirthKey, Guard, Invariant, Hintikka and Redirect modules. Note that these clusters' current source ranges are DISCONTIGUOUS -- itself the evidence that a line-count split would be wrong. DO NOT split mechanically by line count. Conform to ORGANISATION.md and NOTATION.md, preserve import acyclicity, and UPDATE ORGANISATION.md, which currently gives no line-count guidance and describes Modal/Tableau/ in one undifferentiated line. The Support-module dedup task should land first: it shrinks the files before the seams are cut.
--- ESTABLISHED BY THE SUPPORT-MODULE EXTRACTION (landed; supersedes any conflicting figure above) ---
- Cslib/Logics/Modal/Tableau/Support/Accessibility.lean and Support/KnownWorlds.lean NOW EXIST as public modules importing only Branch. Facts formerly re-derived per-file (hasEdge_addEdge_cases, mem_modalKnownWorlds, modalKnownWorlds_mono_append and relatives) are imported, not restated. Do not reintroduce a local copy.
- A third Support/Subfmls.lean was evaluated and REJECTED: modalSubfmls/modalUniverse are defined in FmpMeasure.lean itself, so such a module would sit ABOVE it and buy nothing; those facts were de-privatized in place. Two Support modules is the final shape, not three.
- The duplicate inventory was re-measured by SIGNATURE matching, not by counting 'Local re-derivation' comments: 72-74 duplicate declarations across 41-43 families. 17 duplicates carried NO such comment, and the comments also mislead in the other direction (they falsely flagged a byte-identical lemma as deviant). If this task counts, deletes, or audits duplicates, drive off signatures; a comment-string grep silently under-counts.
- Root cause is import REACHABILITY, not privacy: three consumers cannot reach Soundness.lean, so de-privatization alone cannot fix that class. At least one duplicate exists for an unrelated reason (an ambient [Hashable Atom] instance callers cannot omit).
- VERIFICATION BASELINE: lake build Cslib green at 3313 jobs; Modal/Tableau sorry census exactly 1; zero axioms in the subsystem; lake shake exit 1 with 9 findings, NONE in Modal/Tableau -- do NOT gate on shake exit 0, gate on "no Modal/Tableau findings AND count stays 9"; checkInitImports and lint-style both exit 0.
- ANCHOR ON DECLARATION NAMES, NEVER LINE NUMBERS. The extraction deleted code and moved declarations; any line number in this description may already be stale.

---

### 564. Migrate the S4 Keyed drivers onto the St ladder and retire the duplicated keys' derivation
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 553, Task 562, Task 563
- **Research**: [564_tableau_s4keyed_migration_st_ladder/reports/01_s4keyed-st-ladder-migration.md]
- **Plan**: [564_tableau_s4keyed_migration_st_ladder/plans/01_migrate-s4keyed-st-ladder.md]
- **Summary**: [564_tableau_s4keyed_migration_st_ladder/summaries/01_migrate-s4keyed-st-ladder-summary.md]

**Description**: [Task F of the modal-tableau refactor programme; P3.] Migrate the S4 Keyed and KeyedOrdered drivers onto the RuleApplySt / St ladder and retire the duplicated keys' re-derivation -- the stepper currently re-derives the blockingWorldS4Keyed decision that modalApplyOneS4Keyed already made internally (LoopChecking.lean:951-953). Retiring that double derivation is where the unquantified line-count reduction actually lives. This task, NOT the Boneyard task, owns any removal of the S4LoopInv.outDegEq field. That removal is NOT a pure deletion: outDegEq has zero code consumers but its preservation proof is 386 lines across two variants (LoopChecking.lean:4917-5105 and an undocumented second ordered variant at :5111-5307), and it has THREE provision sites -- LoopChecking.lean:7569, :7633, and a POSITIONAL anonymous-constructor site inside modalTableauS4Keyed_initial at FrameCompleteness.lean:4217-4218, i.e. inside the landed completeness capstone. Run lake build before and after; if the cascade into the four other invariant proofs that destructure the structure is large, KEEP the field -- 386 lines are not worth a regression.
--- ESTABLISHED BY THE SUPPORT-MODULE EXTRACTION (landed; supersedes any conflicting figure above) ---
- Cslib/Logics/Modal/Tableau/Support/Accessibility.lean and Support/KnownWorlds.lean NOW EXIST as public modules importing only Branch. Facts formerly re-derived per-file (hasEdge_addEdge_cases, mem_modalKnownWorlds, modalKnownWorlds_mono_append and relatives) are imported, not restated. Do not reintroduce a local copy.
- A third Support/Subfmls.lean was evaluated and REJECTED: modalSubfmls/modalUniverse are defined in FmpMeasure.lean itself, so such a module would sit ABOVE it and buy nothing; those facts were de-privatized in place. Two Support modules is the final shape, not three.
- The duplicate inventory was re-measured by SIGNATURE matching, not by counting 'Local re-derivation' comments: 72-74 duplicate declarations across 41-43 families. 17 duplicates carried NO such comment, and the comments also mislead in the other direction (they falsely flagged a byte-identical lemma as deviant). If this task counts, deletes, or audits duplicates, drive off signatures; a comment-string grep silently under-counts.
- Root cause is import REACHABILITY, not privacy: three consumers cannot reach Soundness.lean, so de-privatization alone cannot fix that class. At least one duplicate exists for an unrelated reason (an ambient [Hashable Atom] instance callers cannot omit).
- VERIFICATION BASELINE: lake build Cslib green at 3313 jobs; Modal/Tableau sorry census exactly 1; zero axioms in the subsystem; lake shake exit 1 with 9 findings, NONE in Modal/Tableau -- do NOT gate on shake exit 0, gate on "no Modal/Tableau findings AND count stays 9"; checkInitImports and lint-style both exit 0.
- ANCHOR ON DECLARATION NAMES, NEVER LINE NUMBERS. The extraction deleted code and moved declarations; any line number in this description may already be stale.

---

### 563. Adopt Lemmon box-plus pairing at the birth-key level
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [563_tableau_boxplus_birth_keys/reports/01_boxplus-birth-keys.md]
- **Plan**: [563_tableau_boxplus_birth_keys/plans/01_boxplus-birth-keys.md]
- **Summary**: [563_tableau_boxplus_birth_keys/summaries/01_boxplus-birth-keys-summary.md]

**Description**: [Task E of the modal-tableau refactor programme; P2. Gated on the review gate. This task is the live gate for BOTH the S4 termination follow-on and the S4 keyed soundness task -- keys and mint payload both change here, so land it before either resumes.] Add boxPlusPair and BoxPlusClosed; enrich successorBirthContent (LoopChecking.lean:384-393) to emit BOTH members of each pair -- {(pos, psi), (pos, box psi)} where it currently emits only the unwrapped (pos, psi) for T(box psi)@w -- and extend the two _preserves_keyLowerBd proofs accordingly. The enriched key stays inside the existing codomain signedSubfmls phi0 (modalSubfmls (.box a) = .box a :: modalSubfmls a, FmpMeasure.lean, def modalSubfmls -- locate by name, ~line 81 post-extraction), so signedSubfmls_card_le, signedSubfmls_powerset_card_le, modalWorldBoundS4 and the pigeonhole argument are UNCHANGED -- box-plus is free in the world bound. The source never iterates box-plus beyond depth 1; where more discriminating power is needed it enlarges the filter Sigma instead, which WOULD change the codomain and is therefore expensive -- enrich with box-plus, not with the filter. Prior art to reuse: modalFourBoxProp (FrameRules.lean:133-138) and boxDiamondPersistence (Bimodal Tableau.lean:344) are already box-plus at the RULE level; only the key level is missing. THE ONE REAL RISK, and the mandatory gate: enriching keys changes which steps block, so modalTableauS4Keyed_complete may break. Gate on lake build Cslib.Logics.Modal.Tableau.FrameCompleteness. If it breaks, the completeness proof is quantified over driver behaviour (modalExpandBranchesS4Keyed_hintikka) and should transport -- but that must be DEMONSTRATED, not assumed. If it cannot be repaired sorry-free, mark [BLOCKED]; do NOT add a sorry. Box-plus is S4-scoped (the Lemmon filtration and ChagrovZakharyaschev Proposition 3.6 are stated for TRANSITIVE models only, satisfied by s4FC) and MUST NOT be lifted into Foundations/.
--- ESTABLISHED BY THE SUPPORT-MODULE EXTRACTION (landed; supersedes any conflicting figure above) ---
- Cslib/Logics/Modal/Tableau/Support/Accessibility.lean and Support/KnownWorlds.lean NOW EXIST as public modules importing only Branch. Facts formerly re-derived per-file (hasEdge_addEdge_cases, mem_modalKnownWorlds, modalKnownWorlds_mono_append and relatives) are imported, not restated. Do not reintroduce a local copy.
- A third Support/Subfmls.lean was evaluated and REJECTED: modalSubfmls/modalUniverse are defined in FmpMeasure.lean itself, so such a module would sit ABOVE it and buy nothing; those facts were de-privatized in place. Two Support modules is the final shape, not three.
- The duplicate inventory was re-measured by SIGNATURE matching, not by counting 'Local re-derivation' comments: 72-74 duplicate declarations across 41-43 families. 17 duplicates carried NO such comment, and the comments also mislead in the other direction (they falsely flagged a byte-identical lemma as deviant). If this task counts, deletes, or audits duplicates, drive off signatures; a comment-string grep silently under-counts.
- Root cause is import REACHABILITY, not privacy: three consumers cannot reach Soundness.lean, so de-privatization alone cannot fix that class. At least one duplicate exists for an unrelated reason (an ambient [Hashable Atom] instance callers cannot omit).
- VERIFICATION BASELINE: lake build Cslib green at 3313 jobs; Modal/Tableau sorry census exactly 1; zero axioms in the subsystem; lake shake exit 1 with 9 findings, NONE in Modal/Tableau -- do NOT gate on shake exit 0, gate on "no Modal/Tableau findings AND count stays 9"; checkInitImports and lint-style both exit 0.
- ANCHOR ON DECLARATION NAMES, NEVER LINE NUMBERS. The extraction deleted code and moved declarations; any line number in this description may already be stale.

---

### 562. Introduce RuleApplySt additively and bridge modalExpandBranchesGen
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [562_tableau_ruleapplyst_additive_introduction/reports/01_ruleapplyst-additive-ladder.md]
- **Plan**: [562_tableau_ruleapplyst_additive_introduction/plans/01_st-ladder-additive-insertion.md]
- **Summary**: [562_tableau_ruleapplyst_additive_introduction/summaries/01_st-ladder-additive-insertion-summary.md]

**Description**: [Task D of the modal-tableau refactor programme; P2. Gated on the review gate.] MANDATORY FIRST STEP, non-negotiable per the programme constraint: a consumer audit of Saturation.lean before any edit. Then generalise RuleApply (Saturation.lean:107-111) to RuleApplySt sigma, with RuleApply = RuleApplySt Unit, added PURELY ADDITIVELY as new declarations -- modalExpandBranchesGen is never edited -- and prove modalExpandBranchesGen_eq_St. Zero risk to landed theorems by construction: because nothing existing is edited, none of the six true-rfl driver bridges (modalTableauB_eq, modalTableauS5_eq, modalTableauFive_eq, modalTableauKb5_eq, modalTableauKb5''_eq, modalExpandBranchesB_eq) can break. Migration onto the ladder and retirement of the double derivation are a SEPARATE, later task -- do not start them here.
--- ESTABLISHED BY THE SUPPORT-MODULE EXTRACTION (landed; supersedes any conflicting figure above) ---
- Cslib/Logics/Modal/Tableau/Support/Accessibility.lean and Support/KnownWorlds.lean NOW EXIST as public modules importing only Branch. Facts formerly re-derived per-file (hasEdge_addEdge_cases, mem_modalKnownWorlds, modalKnownWorlds_mono_append and relatives) are imported, not restated. Do not reintroduce a local copy.
- A third Support/Subfmls.lean was evaluated and REJECTED: modalSubfmls/modalUniverse are defined in FmpMeasure.lean itself, so such a module would sit ABOVE it and buy nothing; those facts were de-privatized in place. Two Support modules is the final shape, not three.
- The duplicate inventory was re-measured by SIGNATURE matching, not by counting 'Local re-derivation' comments: 72-74 duplicate declarations across 41-43 families. 17 duplicates carried NO such comment, and the comments also mislead in the other direction (they falsely flagged a byte-identical lemma as deviant). If this task counts, deletes, or audits duplicates, drive off signatures; a comment-string grep silently under-counts.
- Root cause is import REACHABILITY, not privacy: three consumers cannot reach Soundness.lean, so de-privatization alone cannot fix that class. At least one duplicate exists for an unrelated reason (an ambient [Hashable Atom] instance callers cannot omit).
- VERIFICATION BASELINE: lake build Cslib green at 3313 jobs; Modal/Tableau sorry census exactly 1; zero axioms in the subsystem; lake shake exit 1 with 9 findings, NONE in Modal/Tableau -- do NOT gate on shake exit 0, gate on "no Modal/Tableau findings AND count stays 9"; checkInitImports and lint-style both exit 0.
- ANCHOR ON DECLARATION NAMES, NEVER LINE NUMBERS. The extraction deleted code and moved declarations; any line number in this description may already be stale.

---

### 558. Extract re-derived private Tableau facts into public Support modules
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Plan**: [558_tableau_support_private_dedup/plans/01_tableau-support-private-dedup.md]
- **Research**: [558_tableau_support_private_dedup/reports/02_statement-equivalence-audit.md]

**Description**: [Task A of the modal-tableau refactor programme; P0, highest value/risk ratio in the whole programme, NO dependency on any other task.] Cslib/Logics/Modal/Tableau/ contains 77 comment-attested 'Local re-derivation of X (unavailable across files)' sites, root-caused by FmpMeasure.lean marking 50 declarations private: modalSubfmls_trans is re-derived in three files (S5Simplification.lean:97, FiveSimplification.lean:736, BDriver.lean:211), modalKnownWorlds_fold_spec in four, hasEdge_addEdge_cases in four. Extract those facts as PUBLIC declarations into Cslib/Logics/Modal/Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean and DELETE the 77 re-derivations. This is mechanical and behaviour-preserving by construction, requires no abstraction decision, and it shrinks the oversized files BEFORE any split seams are chosen -- so it must precede the module split. Verify with lake build, lake exe checkInitImports, lake exe lint-style, and lake shake --add-public --keep-implied --keep-prefix. Constraint: do not edit Rules.lean, Saturation.lean or Branch.lean. Preserve every proven, consumed result; modalTableauS4Keyed_complete and the six landed Decidable instances (K/T/B/S5/Five/KB5) must be green at every commit. Subsystem sorry census must stay at exactly 1 (FrameSoundness.lean:1244, retained by explicit user decision) and axiom count at 0.

---

### 557. Modal tableau refactor abstractions boneyard
- **Status**: [EXPANDED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [557_modal_tableau_refactor_abstractions_boneyard/reports/01_tableau-abstraction-boneyard-analysis.md]
- **Plan**: [557_modal_tableau_refactor_abstractions_boneyard/plans/01_tableau-refactor-abstractions-boneyard.md]

**Description**: Refactor and restructure the modal Tableau subsystem to library-publication quality, identifying the correct abstractions and module divisions, archiving unnecessary code to a new Boneyard/ quarantine, and systematically discharging the documentation debt. MOTIVATION: four successive soundness routes for the S4 keyed loop-check guard have failed at the same obligation by four different mechanisms (Route P: redirect-inertness lemmas machine-checked FALSE at a reachable state; origin-edge invariant revision: abandoned; ancestor-only blocking: defeated by the existentially arbitrary branchSatisfiableIn witness model; subtractive blocking with a completeness-only redirect channel: its free transfer yields only an UNWRAPPED branch fact at the redirect target). This task treats the factoring as a first-class defect rather than continuing to route around it. It is NOT a soundness-proof task and must not attempt the soundness obligation. THE DEFECT, RELOCATED BY THE COMPLETED HARD-MODE ANALYSIS (reports/01_tableau-abstraction-boneyard-analysis.md): the mis-factoring is edge-addition where both source calculi identify worlds, not the bridge set. A blocked minting step has modalApplyOneS4Keyed return (.linear [], acc.addEdge sf.label wBlock) -- two lines, LoopChecking.lean:753 and :757 -- creating the obligation m.r (f src) (f wBlock) against branchSatisfiableIn's existentially arbitrary witness model (FrameSoundness.lean:110), whereas Massacci2000 Definition 10.2's SST-interpretation is explicitly NOT required injective (identify the blocked world with its shorter modal copy rather than relate them) and Pruning Lemma 8.2 instead DELETES the descendant-closed subtree Ftree(sigma.n). The real seam: completeness already CONSTRUCTS its model, extractModelS4 b acc = extractModelWith Relation.ReflTransGen b acc (FrameCompleteness.lean:143-146), while soundness quantifies EXISTENTIALLY, so containment is an obligation rather than a construction step, where ChagrovZakharyaschev1997 Theorem 5.51 discharges the same condition by building its relation inside the ambient one. The guard docstring already names this as NO REACHABILITY RESTRICTION (LoopChecking.lean:491-493) and the mechanism is recorded at FrameSoundness.lean:1183-1190. This REPLACES the earlier diagnosis that the absence of a persistence mechanism for unwrapped facts was the single most valuable thing to name: that absence is real and is verbatim the obstruction at LoopChecking.lean:8830-8832, but it is only the CONTENT half, and :478-501 already says fixing one of the two named defects does not fix the other. RETIRED PREMISES, do not reinstate: (a) there is no theorem numbered interval theorem -- chunk_0246.md:43-65 (print p. 141) is unnumbered prose after Theorem 5.23 and an UNPROVED authorial remark with no counterexample frame supplied, and its finest and coarsest relations live on the filtration QUOTIENT, so its nontransitivity sentence, accurate as a quotation, is NOT precisely the failure mode of a subtractive or redirect-channel design; cite it by chunk and page, never as a theorem, and build no inference on it; (b) Massacci2000 Theorem 8.1, that blocking preserves satisfiability, is STATED AND NEVER PROVED there -- Appendix B.2 proves only Theorem 8.4, and section 10.2 defers 8.1 to Gore's model graphs (chunk_0054.md:3-7) -- so the four dead routes were reconstructing a proof their cited source does not contain, and this belongs in FrameSoundness.lean's documentation; (c) Theorem 5.51 concerns Grz via SELECTIVE filtration, not S4 via filtration; (d) box-plus is defined in Chapter 3 (chunk_0173.md:11-14, print p. 98) as the syntactic analogue of reflexivization, not in chunk_0248, which holds the Lemmon filtration itself (:24-31, print p. 142, also unnumbered). MEASURED BASELINE replacing every asserted figure, with reproduction commands in section 2 of report 01. LoopChecking.lean 10,540 lines / 230 declarations (asserted 10,674 / 150); FrameSoundness.lean 5,317 (exact); FrameCompleteness.lean 4,307 (asserted 4,532); three-file total 20,164. Redirect semantic surface 4 clauses / 14 code lines at LoopChecking.lean:6557-6562 (exact) plus :8779-8782 and :8786-8789 (asserted locations shifted +23). The hintikkaS4 bridge set is 8, not ten, and the asserted ten WAS correct when written: the two _boxed reflTransGen variants were removed in commit c4b33f63, and the comment at :8911-8912 still references them. The axiom drift was a SCOPE CONFUSION, not a drift -- the Tableau subsystem has ZERO axiom declarations and 3 raw axiom word matches, while repo-wide Cslib/ has 26 declarations and 1,701 raw matches -- so fix it by recording the measured baseline with its command, never by adjusting a number. Sorry census: the whole Tableau subsystem is exactly 1, at FrameSoundness.lean:1244, inside a ZERO-consumer declaration; repo-wide Cslib/ is 10. Tags confirmed exact: 0 FIX/TODO/NOTE/QUESTION in the three files, 11 TODO and 8 NOTE repo-wide. outDegEq: zero code consumers of S4LoopInv.outDegEq re-verified, but its preservation proof is 386 lines, not 188 (:4917-5105 at 189 plus an undocumented second ordered variant at :5111-5307 at 197), and it has THREE provision sites -- LoopChecking.lean:7569, :7633, and a POSITIONAL anonymous-constructor site inside modalTableauS4Keyed_initial at FrameCompleteness.lean:4217-4218, i.e. inside the landed completeness capstone -- so removing the field is NOT a pure deletion. ModalTableauResult is referenced across 11 Tableau modules (asserted 8), though its (b, acc) shape claim holds. The amplification figures (4 declarations / 1,036 lines, 43 / 1,983 reachable from modalTableauS4Keyed_complete) were NOT re-measured -- they need an elaborated-environment dependency query, not a text scan -- and no substitute was fabricated; the qualitative claim stands on the verified 4-clause surface plus 85 private lemmas in LoopChecking.lean and 50 in FmpMeasure.lean. Boneyard/ confirmed absent; CslibTests/S4LoopGuardRegression.lean confirmed at 197 lines; the six landed Decidable instances confirmed as exactly K/T/B/S5/Five/KB5. PREREQUISITE: lake exe checkInitImports currently FAILS on a stale build unrelated to this subsystem (a missing Constructive/Nested/Soundness.olean), so a full lake build must clear it before verification against that stated gate is meaningful. SCOPE. A. ABSTRACTIONS AND UNIFICATION: adopt the Lemmon box-plus pairing at the BIRTH-KEY level. successorBirthContent (LoopChecking.lean:384-393) records only the unwrapped (pos, psi) when T(box psi)@w is on the branch while relevantSetFinset records both forms, and that asymmetry IS the wrapped/unwrapped mismatch; add boxPlusPair and BoxPlusClosed and emit both members of each pair. It is licensed for S4 BY NAME (Corollary 5.32 names K4, D4 and S4 as admitting filtration via the transitive closure of the finest filtration or the Lemmon filtration) and it is FREE in the world bound, because modalSubfmls (.box a) = .box a :: modalSubfmls a (FmpMeasure.lean:79) keeps the enriched key inside the existing codomain signedSubfmls, leaving the cardinality lemmas, modalWorldBoundS4 and the pigeonhole argument untouched; the one path by which it could have cost anything, iteration to depth greater than 1, is closed negatively from the source. But SCOPE THE EXPECTATION DOWN: box-plus subsumes none of the 8 bridges outright and collapses AT MOST 2 (the box_pos_self and dia_neg_self reflexive instances), and it does NOT touch the reachability defect. The other six are faithful transcriptions of Massacci Proposition 8.1 and ChagrovZakharyaschev Proposition 3.6 plus two orthogonal witness conjuncts, and the weakened hypotheses were a minimisation from modalHintikkaSetS4 to modalS4Saturated -- a factoring improvement that already happened, not a wrong abstraction. Box-plus is S4-scoped (the Lemmon filtration and Proposition 3.6 are stated for TRANSITIVE models only, satisfied by s4FC) and MUST NOT be lifted into Foundations/; note that enlarging the FILTER instead, as the source must for K4.1/S4.1/K5, would change modalWorldBoundS4 where box-plus enrichment is free. Prior art to reuse: modalFourBoxProp (FrameRules.lean:133-138) and boxDiamondPersistence (Bimodal Tableau.lean:344) are already box-plus at the RULE level, and MonotoneEdges (Intuitionistic Soundness.lean:367-369) is already a persistence-carrying soundness-invariant predicate; only the key level is missing. Second unification target: exactly ONE driver family of nine forks off modalTableauGen / modalExpandBranchesGen -- the S4 Keyed and KeyedOrdered pair, the unkeyed S4 driver already being generic -- and only because RuleApply (Saturation.lean:107-111) has no slot for per-driver state, forcing the stepper to RE-DERIVE the blockingWorldS4Keyed decision modalApplyOneS4Keyed already made internally, as the code admits at LoopChecking.lean:951-953. Generalise to RuleApplySt sigma with RuleApply = RuleApplySt Unit, added ADDITIVELY first so the six true-rfl driver bridges cannot break, then bridged, then migrated; retiring the double derivation is where the unquantified line-count reduction lives. The one landed theorem at risk is modalTableauS4Keyed_complete, since enriching keys changes which steps block; gate on lake build and, if it cannot be repaired sorry-free, mark BLOCKED rather than adding a sorry. B. MODULE DIVISION: FIRST, and independent of every abstraction decision, discharge the highest-value item the original scope omitted -- 77 comment-attested LOCAL RE-DERIVATION sites, root-caused by FmpMeasure.lean's 50 private declarations being unavailable across files (modalSubfmls_trans re-derived in three files, modalKnownWorlds_fold_spec in four, hasEdge_addEdge_cases in four). Extract those facts as PUBLIC declarations into Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean and delete the re-derivations: mechanical, behaviour-preserving by construction, needing no abstraction decision, and it shrinks the oversized files BEFORE split seams are chosen. Then split along the real seams identified (an S4/ cluster of Universe, BirthKey, Guard, Invariant, Hintikka and Redirect modules, whose current source ranges are DISCONTIGUOUS -- itself evidence a line-count split would be wrong), conforming to ORGANISATION.md and NOTATION.md, preserving import acyclicity, and UPDATING ORGANISATION.md, which gives no line-count guidance and describes Modal/Tableau/ in one undifferentiated line. Do not split mechanically by line count. C. BONEYARD: create Boneyard/ at the repository root -- it does NOT currently exist here; it is a convention borrowed from the source repository, where it held roughly 27k lines and 29 sorries excluded from porting, censuses, and the build. Document the convention in Boneyard/README.md: quarantined, never imported by Cslib/, excluded from lake build, mk_all, lint-style, shake, and all sorry/axiom censuses, retained for provenance rather than use. Move there rather than deleting, and only after RE-RUNNING the consumer audit at execution time because the recorded one is dated: blockedRedirect_diaNeg_mem_of_diaOrigin, blockedRedirect_boxctx_mem_of_boxOrigin, the keysRootEmpty / keysRootEmpty_entry pair, and the two outDegEq preservation lemmas only once the field removal has actually landed. TWO CARVE-OUTS ARE MANDATORY: FrameSoundness.lean:1220-1244 (branchSatisfiableIn_s4FC_ancestor_redirect) is IMMOVABLE despite being zero-consumer, because it carries the retained sorry that is an explicit user decision and the rule protecting proven-and-consumed code does not by itself protect it; and keysOriginS4 is NOT eligible, having 22 code consumers, so the comment at LoopChecking.lean:2001-2002 claiming it was removed is FALSE. Nothing whose deletion cannot be justified by a re-verified zero-consumer check may be moved, and nothing proven and consumed may be moved at all. D. DOCUMENTATION: the debt in the three modal Tableau files is prose-shaped, not tag-shaped. Seven adjudicated claims verified TRUE must be LEFT ALONE; four defects must be corrected: LoopChecking.lean:2001-2002 (the keysOriginS4 removal claim is FALSE), :8911-8912 (stale _boxed bridge references), :2000-2004 (resolve the possibly-orphaned hedge on keysRootEmpty with the audit as evidence), and FrameSoundness.lean:1215-1219 (add both the zero-consumer fact and the Massacci Theorem 8.1 gap, which change how a future reader assesses the obstruction). Land the measured baseline table with its exact commands into the subsystem documentation so the same drift cannot recur, and repair the per-repo literature index, which reports the Massacci corpus as 1 chunk where it holds 77 plus a full text: run /literature --validate. CONSTRAINTS. Never edit Rules.lean, Saturation.lean (ModalTableauResult carries only (b, acc)), or Branch.lean without an explicit consumer audit first; a Saturation.lean change IS proposed (RuleApplySt) and its audit is a mandatory gate. Preserve every proven, consumed result: this is a restructuring task and must be behaviour-preserving on all landed theorems, with modalTableauS4Keyed_complete and the six landed Decidable instances (K/T/B/S5/Five/KB5) green at every commit. The sorry at FrameSoundness.lean:1244 is retained by explicit user decision and its disposition is a separate decision, not this task's to make. Route-independent assets deliberately kept from the subtractive attempt -- modalS4Saturated (7 consumers, not eligible), the strictly-weakened hintikkaS4 bridges (the set is 8, measured, not 10), hasEdge_accWithReds_iff, reflTransGen_accWithReds_first_red, and the two sorry-free blockedRedirect_unwrapped_{boxPos,diaNeg}_mem transfers, together with the Reds / accWithReds packaging they are stated over -- are inputs to be placed correctly by the abstraction decision, not candidates for the Boneyard. Run the CSLib vetting pipeline against CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, and CODE_OF_CONDUCT.md as an acceptance gate; it has never been run on this subsystem. VERIFICATION: behaviour preservation demonstrated by the landed capstones and Decidable instances remaining green, the Tableau sorry census not rising above its measured baseline of exactly 1, no new axioms above the measured subsystem baseline of zero, checkInitImports and lint-style clean after the stale-build repair above, and the existing executable regression corpora (CslibTests/S4LoopGuardRegression.lean at 197 lines, plus the probe harnesses under the S4 loop-guard task's artifacts directory) reproducing their recorded verdicts exactly. Expect this task to need expansion into several tasks. The abstraction analysis is now COMPLETE (report 01) and must be REVIEWED AND ACCEPTED in an explicit decision record before any file is moved or split and before any abstraction is implemented.

---

### 554. Cs5 pair seed disjunction property cutfree research
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [554_cs5_pair_seed_disjunction_property_cutfree_research/reports/02_cutfree-literature-grounded.md]
- **Plan**: [554_cs5_pair_seed_disjunction_property_cutfree_research/plans/03_ra-probe-product-model.md]
- **Summary**: [554_cs5_pair_seed_disjunction_property_cutfree_research/summaries/03_ra-probe-summary.md]

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
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 535, Task 561, Task 563, Task 587
- **Research**: [553_s4_loop_guard_soundness_reachability_restriction/reports/06_mint-blocked-redirect-verdict.md]
- **Summary**: [553_s4_loop_guard_soundness_reachability_restriction/summaries/07_p1-p2-mint-blocked-probe-verdict.md]
- **Plan**: [553_s4_loop_guard_soundness_reachability_restriction/plans/08_reformulated-s4-redirect-sound-inv.md]

**Description**: Determine whether the S4 keyed loop-check guard can be made sound, and if so repair it. This task carries EXPLICIT authorization to edit the otherwise-frozen blockingWorldS4Keyed code that the completeness-line task holds constant. FRAMING MATTERS: this is not 'apply the reachability restriction', it is 'determine whether the guard can be narrowed at all without collapsing the termination argument'. THE DEFECT: blockingWorldS4Keyed (LoopChecking.lean approx 469) picks its blocking world by matching birth-content across ALL recorded worlds, with no reachability restriction to the current label. The redirect then adds a bare edge whose soundness needs the two labels to be related in an arbitrary model. Since the S4 frame condition is reflexive and transitive but NOT symmetric, common-ancestor reachability does not yield relatedness, and the S5 precedent relies on symmetry so it does not transfer. As stated, the keyed S4 soundness theorem is likely FALSE. CANDIDATE FIX: restrict candidates to those reachable via ReflTransGen of the accessibility edge relation. CRITICAL PREDICTION TO VERIFY FIRST, derived from hypothesis shapes and NOT yet confirmed: narrowing the guard may break TERMINATION, not merely completeness. The S4 outputs-subset-universe lemma consumes the world-bound lemma, whose hypotheses are exactly the pigeonhole facts that distinct worlds have distinct keys and that keys are contained in the signed subformulas of the root. Key-distinctness is precisely what the UNRESTRICTED guard buys: under a reachability restriction, two mutually-unreachable worlds with the same birth content could both be born, breaking key-distinctness, the world bound, and hence the termination line. Verify this before committing to any fix; if it holds, the guard cannot simply be narrowed and a different soundness route is required. DOWNSTREAM CONSUMERS deferred here from the completeness-line task: the keyed S4 soundness theorem, its successor phase, and the decidability half of the S4 validity decidability instance, which needs BOTH the soundness and completeness lines and is therefore not achievable until this lands. Evidence: the completeness-line task's report on remaining work and the Phase 9 obstruction, plus the carry-forward risk section of its rescope plan.

---

### 551. Cs5 native hilbert pair lindenbaum completeness
- **Effort**: large
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 554
- **Research**:
  - [551_cs5_native_hilbert_pair_lindenbaum_completeness/reports/01_route-b-native-hilbert-cs5-research.md]
  - [551_cs5_native_hilbert_pair_lindenbaum_completeness/reports/03_remaining-obligations-and-path.md]
- **Probe**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/probes/cs5-pair-combined-atomsum.lean]
- **Summary**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/summaries/01_native-hilbert-cs5-completeness-summary.md]
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
- **Dependencies**: Task 531, Task 553, Task 563, Task 564, Task 566, Task 567, Task 586

**Description**: COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree (instDecidableFiveValid/instDecidableKb5Valid, FrameCompleteness.lean) is delivered via the KB5/S5 equivalence route, which leans on a full-equivalence closure. This task delivers genuine pure-K5 / pure-5 (Euclidean without full equivalence, no Mathlib closure operator) tableau soundness + completeness + decidability - the one modal-cube corner explicitly deferred out of the completed KB5/Euclidean task. Mirror the existing Five/KB5 development but over the bare Euclidean frame condition. Zero sorry, zero new axioms; keep the frozen equivalence-route deliverables untouched.

---

### 511. S4 loop checking termination
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 535, Task 553, Task 563, Task 564, Task 565, Task 566, Task 567, Task 586
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
- **Dependencies**: Task 511, Task 553, Task 563, Task 564, Task 565, Task 566, Task 567, Task 586
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

### 430. Prove atom persistence upward closure for intexpan
- **Effort**: 2-3 hours
- **Status**: [COMPLETED]
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
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/11_gap1-fixpoint-completeness.md]
- **Plan**:
  - [430_prove_atom_persistence_upward_closure_for_intexpan/plans/04_positive-formula-persistence-augmented.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/plans/06_gate-b2-then-origin-tracing-export.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/plans/12_terminal-refutation-and-annotation-closeout.md]
- **Lean_source**:
  - [Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean]
  - [Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean]
- **Handoff**:
  - [430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/07_post-reuse-closure-verdict.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/09_forestcomparable-export-phase10-continuation.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/10_origin-tracing-scoping-and-new-blocker.md]
- **Scratch**: [430_prove_atom_persistence_upward_closure_for_intexpan/scratch/BetaSplitRefutation.lean]
- **Summary**: [430_prove_atom_persistence_upward_closure_for_intexpan/summaries/12_terminal-refutation-and-annotation-closeout-summary.md]

**Description**: Prove **positive-formula persistence along the augmented accessibility relation** for open branches produced by `intExpandBranches`, and use it to discharge three sorries at once: `truthLemma`'s T-implication case and both validity bridges.

## The statement

```
∀ φ w w', w ≤ w' → T(φ)@w ∈ b → T(φ)@w' ∈ b
```

where `≤` is `intAccessPreorder edges` over the **augmented** edge list returned by `intExpandBranches_openBranch_sat` (witness `augSets`, carrying task 574's loop-back edges) — NOT the algorithm's raw `edgeSets`.

## Why this scope, not atom-persistence

`propagatePersistence` (`Rules.lean:144-146`, called from `intFImpRule`) copies every positive formula from `w` to a fresh child `w'` **at creation time**. The structural hole is the opposite order: positive formulas arriving at `w` **after** `w'` was already minted are never re-propagated. That single hole surfaces at two formula shapes:

| φ shape | Manifestation | Sorry |
|---|---|---|
| `φ = atom p` | late `T(atom p)@w` never reaches an older child → monotonicity bridge | DP-3 (`Intuitionistic/Completeness.lean:140`), DP-4 (`Minimal/Completeness.lean:128`) |
| `φ = φ'→ψ'` | copy never arrives at `w'`, so reflexive `sat_timp` cannot fire → Gap 1 | DP-5 (`Scheme.lean:633`) |

Three reasons this must be one task:
- Closing either sorry alone has **zero public payoff** — both public completeness theorems carry independent sorries and both delegate to `truthLemma`. Only the union yields a sorry-free public theorem.
- `truthLemma`'s frame is `intAccessPreorder` over the augmented list, deliberately decoupled from the raw edges. Any copy channel filters on raw edges and is strictly weaker, so no algorithm-level, shape-specific patch can close it. The fix is at the **invariant** level, where the general statement costs no more than the atom-only one.
- The unification is pre-recorded in-source: `Scheme.lean:431-434` recommends stating monotonicity "as a NEW field/hypothesis threaded alongside `sat_timp`"; `:413-420` records the same co-inductive diagnosis.

Task 317's Route (a) frame plumbing has landed: `truthLemma` installs `intAccessPreorder edges`, and both `Completeness.lean` bridges already accept `edges` as an argument. The prior coordination gate is discharged.

## Structure: two hard gates, then build-out

**Gate B comes before any calculus change** — it can kill the whole approach and is statable against the tree as it stands.

- **Gate A (probe)**: re-run task 574's variant-selection methodology against the post-Phase-6 tree for V1 (self-copy reinstated verbatim) and V4 (generalize the channel to copy *every* positive formula). Success: saturation on `φ0` at `fuel ≥ 120` and all `TableauConformance.lean` propositional rows matching. V4 is higher-value but **not** assumed safe — positives feed `intApplyRuleFull`'s `.pos,.imp` BETA arm, which yields a world-minting `F(antecedent)@w'`, the original divergence feed. Fall back to V1.
- **Gate B (Lean prototype, GATING, no algorithm change)**: prototype `∀ φ w w', isAccessible augEdges w w' = true → T(φ)@w ∈ b → T(φ)@w' ∈ b` restricted to a single loop-back hop `(x, l)`, using the `Sfor`-containment available at the blocking site. Known risk (flagged UNVERIFIED): the containment is established against `bPers` (the branch at blocking time), not the final branch `b`, and is consumed locally rather than exported. Whether it survives to the final branch is the largest unretired risk. **If Gate B fails, the approach collapses and permanent deferral is the terminal answer for all three sorries at once — escalation to the quotient/blocking-frame route is prohibited.**
- **Then**: revert `a70187dd`'s three hunks (mechanical; `Expansion.lean`, `Scheme.lean`, `Soundness.lean`, all green at the parent commit); prove copy-completeness at a genuine `applyAllTImpRules` fixpoint over raw edges (`filterMap`/`countP`, sketched at `Scheme.lean:508-513`, mirroring `applyAllTImpRules_count_drop`); thread the containment invariant alongside `IAllAccessConsistent` and export it in `openBranch_sat`'s conclusion; discharge the T-imp case and instantiate at atoms for DP-3/DP-4.

## Cross-task coordination

Reverting `a70187dd` touches task 574's settled work. It does not re-open 574's design: 574 settled *termination* (ancestor blocking) and *the reuse-witness route* (loop-back edges, not quotient), and its own D3 verdict records the copy channel as termination-orthogonal, with the removal described in its own commit message as "hygiene" explicitly not addressing Gap 1. Gate A is what makes the revert non-speculative.

## Excluded

- **Quotient / blocking-frame reconstruction**: NO-GO, with an in-repo refutation (`intBlockRep` is non-monotone under branch growth, so it cannot carry the forward induction) and a published one (a filtration relation in the interval may be nontransitive even when `R` is transitive).
- **A T-imp-only or atom-only phase**: zero public payoff either way.
- **Route C (containment preorder) and `≤`-on-ℕ upward closure**: both empirically refuted.
- The pre-repair "no world bound of any size exists" finding is **superseded, not contradicted** — post-repair, `WBound φ0`/`intUniverseExt` exist and `applyPersistenceFixpoint_genuine_of_count_le_fuel` is landed sorry-free.

## Sorry ownership

DP-5 (`Scheme.lean:633`), DP-3 (`Intuitionistic/Completeness.lean:140`) and DP-4 (`Minimal/Completeness.lean:128`) are owned by this task. DP-2 (`intFreshMint_preserves_nw`, `Scheme.lean:2605`) is owned by task 585 and must not be touched. Line numbers are current as of commit `8a36eba9`; re-locate by content if shifted.

## Verification

- `grep -n sorry` on both `Completeness.lean` files returns no bare `sorry`; `Scheme.lean:633` closed; `Scheme.lean:2605` (DP-2) unchanged.
- `lean_verify` on `intuitionisticTableau_complete`, `minimalTableau_complete`, `truthLemma`, `intExpandBranches_closed_unsat`: no new axioms.
- `Soundness.lean` remains sorry-free; full CI green (`lake build`, `checkInitImports`, `lint-style`, `shake`, `lake test`); `TableauConformance.lean` green.

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

### 409. Literal ⊥-rule-free base ND inductive (option B): split MinDerivation + Explosion; re-cut Curry-Howard & normalization
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 407
- **Research**: [409_bot_rule_free_nd_option_b/reports/01_bot-free-nd-option-b-research.md]

**Description**: SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- OPTIONAL / advanced. Task 407 adopts option C (re-frame the task-398 gated efq constructor as the explosion property module; the base relation is ⊥-rule-free UP TO the IsIntuitionistic gate). Option B is the LITERAL structure-first ND: split Theory.Derivation into a genuinely ⊥-rule-free base inductive MinDerivation (no efq constructor) plus an Explosion extension, prove all structural metatheory once on the base, and recover IPL-ND by adjoining efq. TRIGGER CONDITION: only pursue if a concrete downstream consumer needs a physically ⊥-free derivation object (e.g. a minimal-ND normalization theorem, or a lambda-calculus without an abort/efq combinator). COST/RISK: re-opens the single genuinely hard point from task 398 -- the subformula property under efq -- and forces re-cutting Curry-Howard (Theory.Term mirror) and Prawitz normalization (Basic/Reduction/Termination/SubformulaProperty) against the split. Reuse the task-398 decided strategy (atomic restriction + permutation conversions); treat any non-green proof as [BLOCKED], never sorry. HIGH effort -- use --hard. Depends on 407 (and ideally 408). Source: task 407 report 01 §5 option B / §7 W6, report 02 §5. ALIGNMENT NOTE: this two-inductive split is the Design-B-flavored route that the universal-algebra approach (task 407 option C) deliberately AVOIDS, because it duplicates derivation structure (exclude-then-add at the derivation level). Default remains task 407 option C: ONE derivation type with explosion as a property module. Pursue 409 ONLY if the trigger condition above fires.

---

### 400. Unbundle connective typeclasses; reconcile with fmontesi PR #607 (Waring's flag a)
- **Status**: [NOT STARTED]
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

## LINE NUMBERS ARE STALE (repo-wide lint/CI audit)

The line numbers in the body above are dated 2026-07-26 and have since moved -- the repo-wide lint-hygiene pass rewrapped long lines, deleted blank lines inside single-command blocks, and narrowed blanket linter suppressions to declaration scope across these files. RE-DERIVE EVERY LINE NUMBER LIVE (`grep -n sorry <file>`) before acting; do not trust the recorded positions.

The FILE-LEVEL scope and the sorry COUNTS per file are unchanged and remain accurate. The sorries in these files are currently hidden from `lake build --wfail --iofail` by `set_option warn.sorry false in` markers; filling them must also DELETE the corresponding marker, so the suppression count drops with the sorry count. A suppression ratchet is being added under a separate task to enforce exactly that.

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
