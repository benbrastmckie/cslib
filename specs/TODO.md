---
next_project_number: 614
---

# TODO

## Task Order

*Updated 2026-08-10. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,300,400,409,425,534,554,568,569,590,594,599,600,607,608,610,612,613 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,450,497,537,551,571,576,588,589,595,611 | 36,37,181,400,425,534,554,568,594,610 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41 | 39,40 | foundations |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

400 [NOT STARTED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/
  └─ 497 [NOT STARTED] — Reconcile 'imp' vs 'impl' naming in Cslib/Logics/Propositional (P
409 [BLOCKED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O

### Modal Logic

300 [BLOCKED] — Umbrella task for modal frame extensions T/S4/S5 (and the derived
534 [NOT STARTED] — COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree 
  └─ 588 [NOT STARTED] — Resolve the five import-reachability duplicate families in Cslib/
554 [BLOCKED] — [RESCOPED 2026-07-26 by explicit user decision, adopting report 0
  └─ 537 [BLOCKED] — Prove the general labelled SOUNDNESS direction nik_TS5_soundness 
  └─ 551 [BLOCKED] — Deliver NATIVE Hilbert canonical-model completeness for construct
590 [NOT STARTED] — Re-establish the six out-of-tree probe verdicts under a dedicated
599 [NOT STARTED] — Prototype the Euclidean rule combinator identified as an open, un
600 [NOT STARTED] — Retire the unordered S4 stepper stack at Cslib/Logics/Modal/Table
610 [NOT STARTED] — Wire the D (serial) corner through to a `Decidable` instance. The
  └─ 611 [NOT STARTED] — Correct the decidability-matrix documentation block in `Cslib/Log

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

### Code Hygiene

613 [NOT STARTED] — Fix the two unusedDecidableInType lint warnings in Cslib/Logics/P
589 [NOT STARTED] — Fix repo-wide unusedArguments lint findings across the Lean sourc

### Agent System

594 [NOT STARTED] — METATASK. Bring all open task records in specs/state.json into ag
  └─ 595 [NOT STARTED] — Build the validation gate that would have caught the task-graph f
608 [NOT STARTED] — Discovered during task 596's ROADMAP realignment (2026-08-09; see
612 [NOT STARTED] — Batch of small, independent corrections surfaced by the 2026-08-0

### Bimodal Metalogic

607 [NOT STARTED] — Tracked decision (created by task 596's ROADMAP realignment, per 

## Tasks

### 613. Fix unuseddecidableintype lint warnings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Fix the two unusedDecidableInType lint warnings in Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean:159 and Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean:173. Both are pre-existing and were surfaced while verifying the propositional tableau TFAE fold. Verify with lake lint after the fix.

---

### 612. Metadata and hygiene batch from the 2026-08-09 review
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: None

**Description**: Batch of small, independent corrections surfaced by the 2026-08-09 review. Each is self-contained; none requires research.

1. RE-TIGHTEN THE SORRY RATCHET. `bash scripts/check-sorry-suppressions.sh` reports `sorries: 26 (baseline ceiling 28)` and prints an ACTION REQUIRED block. The un-ratcheted file is `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (baseline `0 1`, actual `0 0`) -- the S4 redirect lemma deleted during the ancestor-redirect refutation. Run `bash scripts/check-sorry-suppressions.sh --update` and commit the updated baseline. One command.

2. REFRESH TASK 606's STALE SITE LIST. Its description enumerates "THE FOUR SITES" including `DP-5: truthLemma, Scheme.lean:693, sorry at :768`. DP-5 was discharged by task 604 and `truthLemma` is now sorry-free. All four cited line numbers are stale (the file has grown past 8,000 lines). Correct to the three live sites: `Intuitionistic/Scheme.lean:8034` (DP-6, the open existential), `Intuitionistic/Completeness.lean:170` (DP-3), `Minimal/Completeness.lean:166` (DP-4).

3. UNBLOCK TASK 554. It carries `status: blocked` with `dependencies: []` and nothing actually blocking it, while gating tasks 537 and 551 -- the entire constructive CS5 line, which the 2026-08-09 scope decision KEPT IN SCOPE. Either transition it to `not_started` or record what it is blocked on.

4. BACKFILL `file_scope` ON 497 AND 589. Both are absent. 497 is the `imp`->`impl` rename (~271 files); 589 is the repo-wide `unusedArguments` lint (33 files across five trees). Both are invisible to any clash check. 497 is now transitively serialized behind the propositional chain via 375, but remains unscoped against everything else.

5. RE-BASELINE THE ROADMAP COVERAGE COUNT. `specs/ROADMAP.md` instructs the next audit to "use the 46-task, fully-covered baseline". Thirteen tasks were archived on 2026-08-09, leaving 36 open. Coverage itself is intact -- all 36 open tasks are named in the roadmap, verified mechanically -- so only the number needs updating.

NOT IN SCOPE: the `file_scope` read/write distinction (that is task 595's charter, and it needs a schema decision first).

SOURCE: specs/reviews/review-2026-08-09.md findings H2, M1, M3, L1, L2.

---

### 611. Correct the stale decidability-matrix documentation and record the 10-of-15 scope decision
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 610

**Description**: Correct the decidability-matrix documentation block in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (currently around lines 9110-9185), which is stale relative to what landed on 2026-08-09.

THREE STALE CLAIMS TO FIX:
1. The block names "serial-rule spec shape" as a live gate blocking D, DB, D4, D5 and D45. That gate is DISCHARGED -- its founding premise was machine-checked false, `DDriver.lean` was built with the full twelve-field witness, and the top-loop `...At` retype landed `modalExpandBranchesD_hintikka`.
2. It prices D at "~1,700 lines once ungated". The 1,327-line driver is already built; only the sound/complete/instance wiring remains.
3. The "Covered (8/15)" table must move D into the covered set once the wiring task lands, and the "Out of scope, with named gates" list must drop D and re-state DB's gate (its serial gate is discharged; only the SymmGen closure plus serial repair remain).

ALSO RECORD THE SCOPE DECISION (made 2026-08-09, see ROADMAP.md): the target is 10 of 15 corners. D and DB are IN scope. K45, D5 and D45 remain in scope but sequenced behind the Euclidean rule-combinator prototype. K4 and D4 are DELIBERATELY EXCLUDED at Tier C (~13,500 lines each, ~27,000 combined) -- the matrix stays intentionally incomplete there, and the block should say so as a decision rather than as an unmet gate.

CONSTRAINT: documentation-only in the Lean source -- do not change any proof, definition or instance. This task exists separately from the wiring task specifically so the two do not write `FrameCompleteness.lean` concurrently.

SOURCE: specs/reviews/review-2026-08-09.md finding C1.

---

### 610. Wire the D (serial) corner through to instDecidableDValid
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Wire the D (serial) corner through to a `Decidable` instance. The expensive machinery already exists and is green; only the final soundness/completeness/instance chain is missing.

WHAT EXISTS (landed 2026-08-09, verified): `Cslib/Logics/Modal/Tableau/DDriver.lean` (1,327 lines, registered in Cslib.lean) carrying `modalDualAugment`, the D driver triple, the complete twelve-field witness `modalApplyOneD_specAt`, `modalTableauD_eq`, and `modalExpandBranchesD_hintikka`. Build green at 3325 jobs, zero sorry in all touched files, `#print axioms modalApplyOneD_specAt = [propext, Classical.choice, Quot.sound]`.

WHAT IS MISSING (verified absent by grep): `dValid`, `modalTableauD_sound`, `modalTableauD_complete`, `instDecidableDValid`. Every covered corner (K, T, B, TB, K5, KB5, S4, S5) has all four; D has none.

SCOPE: follow the T corner end-to-end as the pattern -- `tValid` (FrameSoundness.lean), `modalTableauT_sound`/`modalTableauT_complete`, `instDecidableTValid` (FrameCompleteness.lean) -- and produce the D analogues. The serial-rule spec-shape gate that previously blocked this is DISCHARGED: research machine-checked that its founding premise was false (`modalApplyOneD` already satisfies `boxPosNotExpanding`; only `outputsSubsetUniverse` failed, for a universe reason, and that was narrowed via the additive `RuleApplicationSpecCoreAt`/`RuleApplicationSpecAt` siblings). The top-loop chain was retyped to the `...At` interface, landing `modalExpandBranchesD_hintikka` and explicitly unblocking D/DB/D4/D5/D45.

NOTE: do NOT re-litigate the per-regime driver split. That decision is settled -- each corner gets its own bespoke driver file rather than a generic traversal rung parameterised over frame conditions (see the "Settled decisions" block in FrameCompleteness.lean).

Zero new sorries, zero new axioms. Verify `lake build` green and `#print axioms instDecidableDValid` before completion.

SOURCE: specs/reviews/review-2026-08-09.md finding C1.

---

### 609. Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 604
- **Research**: [609_revalidate_intfimpreuse_witness_anc_loopback_containment/reports/01_loopback-revalidation-repair.md]
- **Plan**: [609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md]
- **Summary**: [609_revalidate_intfimpreuse_witness_anc_loopback_containment/summaries/01_beta-priority-repair-summary.md]

**Description**: `intFImpReuseWitnessAnc?` (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`) records a loop-back edge on a `Sfor`-containment check at the moment the branch reuses an ancestor world -- but it never re-validates that containment as the branch continues to grow afterward. This is the root cause both the intuitionistic tableau completeness `truthLemma` restructure and the frame-adequacy analysis that preceded it converged on: it is why the AUGMENTED frame (`augSets`, threaded by `intExpandBranches_openBranch_sat`) carries `IFimpAccess` but REFUTES positive persistence (`CslibTests/BetaSplitRefutation.lean`, `firstViolation = some (2,1,2)`), and why the RAW frame (`rawEdges`) carries positive persistence (`IPosPersistRaw`, sorry-free) but REFUTES `IFimpAccess` at the blocked worlds pruning strands.

WHY IT MATTERS: re-validating the loop-back containment as the branch grows is what would let the augmented frame carry positive persistence too, giving ONE frame with BOTH `IFimpAccess` and persistence simultaneously. That would collapse `openBranch_countermodel`'s remaining existential (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`, the sole live sorry in that file) into a direct `truthLemma` instantiation, since `truthLemma` itself is already sorry-free and parametric over any frame carrying both facts.

EXCLUDED CONSTRUCTIONS (established by machine evidence, do not re-attempt without new evidence): rawEdges itself (fails IFimpAccess and is refuted as a conjunct-2 witness for phiRef1/phiRef3 -- CslibTests/WitnessProbe.lean, CslibTests/BetaSplitRefutation.lean); pruning at blocked worlds (fails dblNeg/peirce, where the loop-back is a self-reuse and cutting the world destroys the falsifying world); pruning at strictly-blocked worlds (fails phiRef3, which needs the self-reuse world cut -- the two pruning rules contradict each other on the same syntactic signal); and the greatest IFimpAccess-supported fixpoint (collapses to K = empty for phiRef1/phiRef2/phiRef3, since the unsupported blocked world strands its parent up to world 0). The maximal atom-inclusion frame was excluded even earlier.

SCOPE: this is calculus-level work in Expansion.lean, explicitly OUT OF SCOPE for Scheme.lean-only dispatches. Do not attempt this inside a Scheme.lean-scoped task.

SOURCE: specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/reports/01_conjunct2-frame-adequacy.md (sections 3, 4, 6) and specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/plans/01_dp5-discharge-honest-restructure.md.

---

### 608. Fix lean-sorry-census.sh double-counting set_option warn.sorry false in as a sorry
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: None

**Description**: Discovered during task 596's ROADMAP realignment (2026-08-09; see specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md section 1 for the full evidence trail, independently re-verified by team-lead with a corrected-regex re-run). The deployed .claude/scripts/lean-sorry-census.sh strips comments/strings correctly, then matches `\bsorry\b` on the stripped text. It does NOT exclude `set_option warn.sorry false in` -- because `.` is a non-word character, `\bsorry\b` also matches the "sorry" substring inside "warn.sorry", so every suppression-annotation line is counted as an extra phantom sorry on top of the real sorry it annotates.

Verified for every Cslib/Logics/Bimodal file carrying sorries: script count 41 = 23 real sorry occurrences + 18 warn.sorry annotation lines double-counted (repo-wide: 45 = 27 + 18). The 27/23 figures independently match the pre-existing ROADMAP.md census and task 215's own hand-audited scope (12 + 1 = 13 for the BXCanonical files specifically). Team-lead independently reproduced repo-wide 45->27, Bimodal 41->23 using the corrected regex `(?<![.\w])sorry\b` substituted into the script's own strip_lean_comments pipeline, and confirmed a naive grep-style count that skips the block-comment/docstring stripper gives 152 repo-wide -- the stripper itself is correct and valuable; the `\bsorry\b` regex is the only broken piece.

CRITICAL -- fix target is the SOURCE STORE, NOT the deployed .claude/ copy: this repo's .claude/ tree is a gitignored deploy artifact regenerated from the source store (see .claude/rules/source-store-deploy-boundary.md). A hand-edit to .claude/scripts/lean-sorry-census.sh is silently wiped on the next regeneration. The actual fix target is the source-store copy at agent-system/extensions/lean/scripts/lean-sorry-census.sh (found on this machine at /home/benjamin/.config/nvim/agent-system/extensions/lean/scripts/lean-sorry-census.sh -- confirm the correct source-store root for whichever environment this task is executed in; it is a sibling extensions tree outside this repository, not a path under cslib/).

Fix: exclude lines that are exactly (or contain only) the `set_option warn.sorry false in` directive from the `\bsorry\b` match -- e.g. use the negative-lookbehind regex `(?<![.\w])sorry\b` in place of `\bsorry\b` (verified to work by both the task-596 implementer and team-lead independently), or line-level pre-filter any line whose stripped content is exactly the set_option directive. Preserve the comment/string stripper (`strip_lean_comments`) unchanged -- it is correct and is the script's valuable part; only the final regex match needs to change. Add a regression fixture (a file with N suppression annotations and M real sorries, asserting the census reports M, not M+N) so this cannot silently regress. Cross-check against `lake build`'s compiler-backed "declaration uses 'sorry'" warning count (the script's own --cross-check flag) as part of the fix's verification, since that count is comment/annotation-immune by construction.

---

### 607. Decide: complete BXCanonical/dense or abandon it for the algebraic pipeline
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Bimodal Metalogic
- **Dependencies**: None

**Description**: Tracked decision (created by task 596's ROADMAP realignment, per specs/ROADMAP.md Section B "Open decision"). The bimodal completeness layer has three constructions: `Algebraic` and `Bundle` form the wired, actively-used completeness pipeline; `BXCanonical` is a separate, incomplete leaf that nothing downstream imports.

Measured 2026-08-09 (bash .claude/scripts/lean-sorry-census.sh, hand-verified against the raw `sorry` occurrences to exclude the script's warn.sorry-substring double-counting bug -- see specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md section 1): BXCanonical carries 13 live sorries (ChronicleToCountermodel.lean: 12, Frame.lean: 1), all gated on the WeakCanonical discrete-completeness port. Task 215 already owns filling these specific sorries once that port lands.

This task is NOT about filling the sorries -- it is the prior architectural decision: (A) complete BXCanonical/dense once its blocking port lands (in which case task 215 delivers it), or (B) abandon BXCanonical/dense as dead weight and consolidate the bimodal completeness story onto the Algebraic+Bundle pipeline alone, retiring the file. Neither option should be taken autonomously by an implementer -- this task exists to hold the decision until a maintainer makes the call, at which point it should be re-scoped into either a completion task (if A) or a retirement/consolidation task (if B).

---

### 606. Discharge or restate the four propositional tableau completeness theorems and verify the TFAE fold
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 603, Task 604, Task 605, Task 609
- **Research**: [606_discharge_propositional_tableau_completeness_and_verify_tfae/reports/01_tableau-completeness-ground-truth.md]
- **Plan**: [606_discharge_propositional_tableau_completeness_and_verify_tfae/plans/01_tfae-fold-and-annotation-closeout.md]
- **Summary**: [606_discharge_propositional_tableau_completeness_and_verify_tfae/summaries/01_tfae-fold-and-annotation-closeout-summary.md]

**Description**: Consume the frame construction and forcing proof from the predecessor tasks, then discharge or restate the four propositional tableau completeness sorries, repair every call site, and verify the TFAE instantiation.

THE FOUR SITES (line numbers current as of the annotation-correction landing; re-verify before editing):
- DP-3: intuitionisticTableau_complete, Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:154, sorry at :164
- DP-4: minimalTableau_complete, Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:150, sorry at :160
- DP-5: truthLemma, Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:693, sorry at :768 (the T(phi prime -> psi prime) implication case)
- DP-6: openBranch_countermodel, Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:7891, sorry at :7965 (the exists edges upward-closure conjunct)

SCOPE: (a) discharge each sorry, or -- where the landed construction supports only a weaker statement -- restate the theorem to what is actually provable; (b) repair every call site the restatement affects; (c) update the docstrings so they describe the landed statement rather than an abandoned one, replacing the current open / augmented-frame-route-known-bad / admissible-space-characterised annotations with the resolved wording.

HARD CONSTRAINT -- THE TFAE FOLD: any restated theorem must still be strong enough to fold the tableau nodes into cplProofSystemsTfae / iplProofSystemsTfae / mplProofSystemsTfae in Cslib/Logics/Propositional/ProofSystemEquivalence.lean. A restatement that discharges a sorry but is too weak to serve the TFAE has NOT solved the problem. Verify the TFAE instantiation type-checks before declaring completion.

EXPLICITLY OUT OF BOUNDS: laundering a sorry via a weakened statement. In particular the in-source prohibition at the DP-3 site stands -- do NOT discharge it with exact h Nat (intExtractValuation _b) _huc 0; that type-checks but only launders an undischarged conjunct through the file without resolving it.

PRECEDENT TO FOLLOW: intExpandBranches_openBranch_sat was in exactly this position (a refuted fuel = 0 base case with a Lean-verified counter-instance) and was repaired by the R1 restatement adding hUniv / hNW / hFuel preconditions (plus hLBS / hWH / hWHC / hNC). It is now sorry-free at Scheme.lean:6815, its fuel = 0 arm discharged via hFuel giving intWork ... < 0, absurd by omega. The counter-instance record survives near :6805 and :6999 as the durable explanation of why the R1 hypotheses exist -- preserve that kind of durable record here too.

Zero new sorries, zero new axioms. If the predecessor tasks landed a negative or narrowing result rather than a proof, this task narrows to updating the annotations to the resolved wording and recording what remains open -- that is a legitimate completion, not a failure.

---

### 605. Establish upward-closure of minBranchBotForces at the bot formula shape
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 603, Task 604
- **Research**: [605_establish_minbranchbotforces_upward_closure_at_bot/reports/01_minbranchbotforces-upward-closure.md]
- **Plan**: [605_establish_minbranchbotforces_upward_closure_at_bot/plans/01_statement-shape-fix.md]
- **Summary**: [605_establish_minbranchbotforces_upward_closure_at_bot/summaries/01_statement-shape-fix-summary.md]

**Description**: Establish upward-closure of `minBranchBotForces b` at the `bot` formula shape -- the second, genuinely separate obligation at the DP-4 site (minimalTableau_complete, Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:150, sorry at :160).

WHY THIS IS SEPARATE: DP-4 needs TWO upward-closure premises -- the valuation's AND minBranchBotForces b's, which is a distinct fact at the bot formula shape -- where only one is supplied. This is not a restatement of the openBranch_countermodel conjunct; it is an independent obligation that must be discharged before DP-4 can close.

CURRENT STATUS (machine-checked): the property HOLDS at the [(1,0)] witness under minScheme, where that edge set discharges BOTH upward-closure obligations and still falsifies phiRef1 at world 0. It is NOT established in general. The former claim that DP-4 was refuted independently of the DP-3 site has been retracted; the site is open, not refuted.

SCOPE: prove upward-closure of minBranchBotForces b in general over the frame the frame-construction task produces, or determine and document precisely what additional precondition it needs -- following the R1 precedent (find the precondition that makes the statement true, add it, repair call sites, discharge) established by intExpandBranches_openBranch_sat, now sorry-free at Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:6815.

A documented negative or narrowing result is a legitimate outcome, recorded in-source with the same honesty discipline as the current annotations. Zero new sorries, zero new axioms.

---

### 600. Unordered s4 stepper stack retirement
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Retire the unordered S4 stepper stack at Cslib/Logics/Modal/Tableau/LoopChecking.lean:192 (the 'Phase 15' marker). Research on the eight-corner decidability gap measured 152 live references still pointing at it, making this a real migration rather than a deletion. The keyed-ordered S4 path that supersedes it already landed (modalTableauS4KeyedOrdered_sound / _complete, instDecidableS4Valid in FrameCompleteness.lean). WORK: migrate the live references to the keyed-ordered path and remove the unordered stack. HARD PREREQUISITE for the K4 and D4 modal-cube corners per the tableau driver abstraction decision (section 9). Independent of the serial-rule spec decision and the Euclidean rule-combinator prototype. Zero sorry, zero new axioms; keep frozen deliverables from task 300 and task 506 untouched.

---

### 599. Euclidean rule combinator prototype
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prototype the Euclidean rule combinator identified as an open, unowned gate by the tableau driver abstraction decision (section 7.2). WORK: build the combinator on Kb5''-from-Five and measure it -- derive the KB5 rule set from the existing Five (K5) rule set via the combinator rather than restating it, and report the measured cost against the bespoke alternative. Deliverable is a measured prototype plus decision report. GATES: K45, D5, D45 in the modal-cube decidability matrix. Independent of the serial-rule spec decision and the S4 stepper-stack retirement -- all three can run in parallel. Zero sorry, zero new axioms; keep frozen deliverables from task 300 and task 506 untouched.

---

### 595. Add a dependency-integrity validation gate so task-graph staleness cannot recur silently
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: Task 594

**Description**: Build the validation gate that would have caught the task-graph findings automatically. Created by the 2026-08-07 codebase review (specs/reviews/review-2026-08-07.md, finding H5 and recommendation 3).

WHY THIS EXISTS -- the loop is not closing: specs/ROADMAP-alignment-audit.md:15 ALREADY recorded "the dependency graph is materially broken" with "one circular edge, five edges pointing at archived tasks, and a recurring completed-but-doesn't-unblock pattern that makes several [blocked] labels stale". Its recommendations were never applied, and on 2026-08-07 the same findings recurred at roughly three times the scale: 37 stale edges, 6 stale-blocked tasks, 20 tasks absent from the roadmap. A one-time cleanup (the reconciliation metatask) will regress again without a gate. There is no dependency-integrity check anywhere in .claude/scripts/ today.

CHECKS TO IMPLEMENT (each must exit non-zero with an actionable message):
(A) STALE BLOCK -- any task with status `blocked` whose dependencies are all satisfied (completed/abandoned in either specs/state.json or specs/archive/state.json) AND which carries no `blocked_reason`. This is the check that would have caught all six.
(B) DANGLING EDGE -- any dependency naming a task number absent from both the active and archived sets.
(C) CYCLE -- any directed cycle in the dependency graph. The prior audit found a 512<->517 cycle; none exists today, so this check guards a real historical failure mode.
(D) PROSE/STATUS DISAGREEMENT -- any task whose description contains "BLOCKED" while its status is not `blocked`, or the converse. Currently fires on 497 and 548.
(E) HUSK -- any task whose entire remaining scope is delegated to a single dependent task, surfaced as a warning rather than a failure (this one needs human judgement; 506 is the worked example).

CRITICAL SCOPING CONSTRAINT -- READ BEFORE STARTING: this repository has NO `agent-system/` source store. Verified 2026-08-07: only two files under `.claude/` are git-tracked, and .claude/rules/source-store-deploy-boundary.md states that `.claude/**` is a disposable deploy artifact regenerated from `agent-system/extensions/**`. A script written into `.claude/scripts/` HERE will be silently wiped by the next deployment. The script must therefore be authored in the upstream source store repository that owns `agent-system/extensions/core/scripts/`, then deployed. FIRST STEP: locate that source store and confirm the correct write target. If it cannot be located, land the checker under this repository's own root-level `scripts/` directory (which IS tracked and IS the home of check-axiom-census.sh, check-sorry-suppressions.sh, check-shake-residue.sh and the other project gates) and record the deviation -- do NOT write into `.claude/scripts/` and call it done.

WIRING: follow the existing project-gate convention in scripts/ and add it to the same gate set the other check-*.sh scripts belong to. Include a self-test with fixture inputs, matching the pattern used by check-runtime-file-tracking.sh (which uses synthetic `000_probe` / `sess_0000000000_probe` fixtures).

SEQUENCING: the reconciliation metatask performs the one-time cleanup; this task prevents recurrence. Running this gate against the pre-cleanup state should reproduce all six stale-blocked findings -- use that as the acceptance test.

---

### 594. Metatask: reconcile all open task records against verified repository state
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: None

**Description**: METATASK. Bring all open task records in specs/state.json into agreement with verified repository state. Created by the 2026-08-07 codebase review (specs/reviews/review-2026-08-07.md, findings H1-H3, M4) at explicit user request for a metatask covering revisions to incomplete tasks.

EVERY ITEM BELOW WAS VERIFIED ON 2026-08-07. Re-verify before acting -- do not act on this list blind.

(1) SIX TASKS MARKED [BLOCKED] HAVE ZERO UNMET DEPENDENCIES. Resolving each edge against specs/state.json and specs/archive/state.json: 511, 554, 568, 583, 409, 37. specs/TODO.md's generated wave table places 511/554/568/583/409 in Wave 1 ("no active dependencies") while the tree entries immediately below render them [BLOCKED] -- the file contradicts itself within one section. Set 511, 554 and 568 to not_started (554's own description says its research is COMPLETE and the remaining work is "LAND NOW (mechanical, no research risk)"). Unblocking 511 and 554 cascades to release 506, 300, 537 and 551.

(2) CLOSE 583 AS SUPERSEDED. Its target `intExpandBranches_openBranch_sat` was restated per its own SCOPE and is now SORRY-FREE at Scheme.lean:6806. Its cited lines are stale: :2583/:2623/:2598-2622 today hold `intUniverseExt_length_le`, `mem_intUniverseExt_of` and neighbours, with no sorry in that region. Its own VERIFY BEFORE STARTING clause mandates this: "if the divergence repair has already restated the lemma, close this task as superseded rather than duplicating the work."

(3) CLOSE 506 AS EXPANDED/PARTIAL AND RE-POINT 300. 506 landed Phases 1-7 green (zero sorry/axiom) and its entire remaining scope IS 511. The graph currently reads 300 -> 506 -> 511, so the umbrella cannot close until an empty intermediate does. Record 506's landed phases in its completion summary, then set 300's dependencies to [511].

(4) THIRTY-SEVEN DEPENDENCY EDGES POINT AT ARCHIVED TASKS. generate-task-order.sh silently treats these as satisfied, which is exactly what makes the staleness invisible. Retarget or drop each. Known live retargets: 375's dependency on archived 317 should become [593] (its real gate is the propositional tableau sorries); 548's dependencies should add [597] (the driver-abstraction decision must precede its 8-corner expansion).

(5) ADD A `blocked_reason` FIELD. There is currently no way to distinguish a genuine external gate from stale graph state. Genuine external gates to record: 37 ("upstream BimodalLogic continuous frame development, not started upstream"), 497 ("external PR leanprover/cslib#607 not yet merged"), 409 ("parked behind an explicit trigger condition, not a dependency"). Note 497 and 548 currently say "BLOCKED" in their description prose while carrying status not_started -- the prose and the status disagree in both directions across the task set.

(6) REFRESH STALE DESCRIPTION TEXT. 375 names only the CPL and IPL TFAEs when `mplProofSystemsTfae` now also exists in ProofSystemEquivalence.lean; 571 qualifies its line numbers with "as of"; 548 says "BLOCKED on 511/535 landing" while 535 is archived.

(7) REWRITE `active_goal`. Handled directly by the review that created this task -- verify it still reads correctly and reflects any status changes made above.

CONSTRAINT: this task changes task METADATA only. No .lean file may be created, edited or deleted. All state.json writes go through .claude/scripts/state-write.sh (the single mutex-guarded writer); regenerate TODO.md via generate-todo.sh afterwards, never by hand.

---

### 593. Find a uniform frame construction for openBranch_countermodel, then discharge the four propositional tableau completeness sorries
- **Status**: [EXPANDED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 591, Task 592

**Description**: Find a uniform frame construction that discharges the `exists edges` conjunct of `openBranch_countermodel`, then discharge or restate the four propositional tableau completeness sorries that depend on it. Originating finding: specs/reviews/review-2026-08-07.md, finding C1. RE-SCOPED 2026-08-09 after the disposition verdict in specs/591_decide_openbranch_countermodel_disposition/reports/01_openbranch-countermodel-disposition.md.

THE FOUR SITES (line numbers current as of the annotation-correction landing):
- DP-3: `intuitionisticTableau_complete`, Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:154, sorry at :164
- DP-4: `minimalTableau_complete`, Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:150, sorry at :160
- DP-5: `truthLemma`, Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:693, sorry at :768 (the `T(phi' -> psi')` implication case)
- DP-6: `openBranch_countermodel`, Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:7891, sorry at :7965 (the `exists edges` upward-closure conjunct)

WHAT IS NOW SETTLED (machine-checked; treat as ground truth):
1. The `exists edges` conjunct is NOT refuted. The `[UNVERIFIED]` inference that the former "PERMANENTLY DEFERRED / unprovable as stated / refuted" annotations rested on is itself machine-REFUTED. Those annotation strings no longer occur anywhere under `Cslib/`.
2. Witness evidence: on the branch the real `intuitionisticTableau` returns for `phiRef1`, `edges = [(1, 0)]` satisfies BOTH conjuncts. Exhaustive enumeration over the complete admissible edge-set space finds 40 witnesses for `phiRef1` under `intScheme`, plus witnesses for `phiRef2`, `phiRef3`, `exMiddle`, `dblNeg`, `peirce`, `deMorgan`, and `dummett`. Under `minScheme`, `[(1, 0)]` discharges BOTH upward-closure obligations (the valuation's and `minBranchBotForces b`'s) and still falsifies `phiRef1` at world 0 -- retracting DP-4's former claim of an independent refutation.
3. Structural characterisation: with `A(w) = { p | T(atom p)@w in b }` and `w <= w'` iff `A(w) subseteq A(w')`, the admissible edge sets are EXACTLY the subsets of that atom-set inclusion preorder, and every such subset is automatically upward-closed. Consequence: conjunct 1 needs NO fact about the tableau algorithm -- no persistence, `genCopies`, or augmented-edge invariant. Instantiating `edges` with any sub-inclusion edge list discharges it by transitivity of `subseteq` on atom sets.
4. The structural argument (independent of any computation): `IValid phi` quantifies over every preorder and every upward-closed valuation, so any refutation of `openBranch_countermodel` would have to exhibit an IPC-valid `phi` on which the algorithm returns `.openBranch`. `phiRef1` is not even classically valid, so it was never such a candidate.
5. Prerequisites already satisfied -- do NOT re-do them: (a) the disposition verdict is delivered and all four in-source annotations are already corrected to "open, augmented-frame route known-bad, admissible edge space characterised"; the four sorries deliberately remain; (b) the evidentiary repair is done -- `CslibTests/BetaSplitRefutation.lean` is present (22 KB, `#guard_msgs`-asserted, CI-protected), contrary to the earlier claim that it was cited but absent.

HONESTY BOUND -- what is NOT established: `openBranch_countermodel` is a `forall phi` statement and remains UNPROVED. The evidence above covers eight formulas under `intScheme` and two under `minScheme`; it constructs no general witness. The maximal inclusion frame is NOT a uniform witness -- it fails at `phiRef1` and `phiRef3`. Per the structural argument, proving the general statement is equivalent to proving the tableau procedure complete. This is substantial open mathematical work, not a mechanical restatement and not a small residual.

THE REAL OPEN OBLIGATION (this task's scope):
(a) Construct `edges` uniformly from the branch `b` -- e.g. `inclEdges b : IEdges`, or a tuned sub-preorder, or a per-formula construction accompanied by a proof that it always exists. Conjunct 1 then falls out of transitivity of `subseteq` on atom sets, independently of every algorithm invariant.
(b) Prove conjunct 2 (`not IForces ... 0 phi`) over THAT frame. This requires a truth lemma over the chosen frame and is the hard part -- it is where the completeness content actually lives. Note that switching the witness away from the augmented frame does not eliminate this work, it relocates it: the existing conjunct-2 argument is tied to the `augSets` witness threaded by `intExpandBranches_openBranch_sat`.
(c) Only once (a) and (b) exist: discharge or restate DP-3/DP-4/DP-5/DP-6, repair every call site, and update the docstrings to describe the landed statement rather than an abandoned one.
Known starting point, unverified: a "raw edges pruned at reuse/blocking sites" construction matches the `phiRef1` witness and is the most promising candidate. Ruled out: the maximal inclusion frame (see the honesty bound). Alternative route: the underlying algorithm defect is real and unfixed -- `intFImpReuseWitnessAnc?` records a loop-back edge on a containment check it never re-validates as the branch grows, which is exactly what makes the augmented frame unusable; fixing it is a second path to a workable frame.
Genuinely separate residual to keep named: upward-closure of `minBranchBotForces b` at the `bot` formula shape is a second obligation at the DP-4 site. It holds at the `[(1, 0)]` witness but is not established in general.

THE PRECEDENT TO FOLLOW -- this route is already proven in this very file. `intExpandBranches_openBranch_sat` was in exactly this position (a refuted `fuel = 0` base case with a Lean-verified counter-instance) and was successfully repaired by the R1 restatement, which added `hUniv`/`hNW`/`hFuel` preconditions (plus `hLBS`/`hWH`/`hWHC`/`hNC`). It is now SORRY-FREE at Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:6815, and its `fuel = 0` arm is discharged via `hFuel` giving `intWork ... < 0`, absurd by `omega`. The counter-instance record survives near :6805 and :6999 as the durable explanation of why the R1 hypotheses exist. The methodological discipline still applies -- find the precondition (here: the frame construction) that makes the statement true, add it, repair call sites, discharge -- with one difference from the R1 case: there, the needed precondition was already identifiable from the counter-instance; here, the needed construction is not yet known and finding it is the research content of the task.

CONSTRAINT: any restated theorem must still be strong enough for the TFAE fold -- folding the tableau nodes into `cplProofSystemsTfae` / `iplProofSystemsTfae` / `mplProofSystemsTfae` in Cslib/Logics/Propositional/ProofSystemEquivalence.lean. A restatement that discharges a sorry but is too weak to serve the TFAE has not solved the problem; verify the TFAE instantiation type-checks before declaring completion.

Zero new sorries, zero new axioms. The four existing sorries stay until (a) and (b) actually land -- laundering them via a weakened statement is explicitly out of bounds, and the existing in-source prohibition on `exact h Nat (intExtractValuation _b) _huc 0` at the DP-3 site stands (it launders an undischarged conjunct).

REALISTIC OUTCOME -- the former success metric ("propositional bare-sorry count drops from 4 to 0") is NOT honestly achievable as a single task and is retired. Since (b) is equivalent to tableau completeness, no sorry-count reduction can be promised in advance. Success is instead: EITHER a uniform frame construction is found and proved (in which case the four sorries follow and the 4-to-0 outcome is reached), OR a documented negative/narrowing result that further constrains the admissible construction space, recorded in-source with the same honesty discipline the current annotations use. Either outcome is a legitimate completion. Consider `/task --expand` to split the frame-construction search from the downstream discharge/restatement work.

EXISTING EVIDENCE TO REUSE (do not re-derive): the machine-checked probes `WitnessProbe.lean`, `WitnessSearch2.lean`, `WitnessSearch3.lean`, and `MinProbe.lean` are preserved at specs/591_decide_openbranch_countermodel_disposition/scratch/ and run via `lake env lean <file>` from the repo root. They are not yet CI-protected; promoting them into `CslibTests/`, mirroring `BetaSplitRefutation.lean`, is a recommended low-cost first step. Reuse-first check already done: `intAccessPreorder` (Scheme.lean:268), `intExtractValuation` (Soundness.lean:1129), `IEdges`/`isAccessible` (Rules.lean:85,92), and `IForces`/`IValid`/`iforces_persistence` (Kripke.lean:81,145,128) cover everything needed; `Mathlib.Relation.ReflTransGen` is already the closure mechanism in use. The only candidate new definition is the frame construction itself.

---

### 590. Reestablish out of tree probe verdicts
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Re-establish the six out-of-tree probe verdicts under a dedicated multi-hour budget: s4probe.lean, s4boxed.lean, s4ancestor.lean, s4subtractive.lean, s4subtractive2.lean, s4subtractive3.lean. These probes are expensive to run and their recorded verdicts have drifted from the current tree. Two specific record defects must be corrected as part of this work, folded in here rather than tracked separately because re-running the probes supersedes them: (a) the S4 loop-guard report 01 describes an s4probe.lean harness from a superseded revision -- eight identifiers it names (dfsR, classify, statsL, badL, hasCountermodel, notS4Valid, def sat, def isS4) have zero matches in the current on-disk file; (b) s4subtractive3.lean carries pre-split LoopChecking.lean:NNNN line citations that no longer resolve -- the declarations still exist under the same names in S4/Hintikka.lean, S4/HintikkaInvariant.lean and S4/Driver.lean, so these should be replaced with declaration names rather than re-numbered. If the multi-hour re-run budget never materialises, split (a) and (b) out as a standalone documentation-only task: they have independent value as a stopgap, because the stale records actively mislead every reader until corrected.

---

### 589. Repo wide unusedarguments lint hygiene
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 534, Task 548, Task 593

**Description**: Fix repo-wide unusedArguments lint findings across the Lean sources: 145 sites in 27 modules, 10 of them in Cslib/Logics/Modal/Tableau/. The uniform pattern is an unused [Hashable Atom] (or analogous) section-level instance binder; the idiomatic fix is `omit [Hashable Atom] in` before the affected block. Distinct from the existing blanket file-scoped lint-suppression ratchet: these are live lint findings, not suppressions, so the ratchet baseline does not cover them.

---

### 588. Tableau import reachability duplicate families
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 511, Task 534, Task 597

**Description**: Resolve the five import-reachability duplicate families in Cslib/Logics/Modal/Tableau/: accFreshInv_append, hasEdge_addEdge_mono, modalApplyOne_boxPos_acc_eq, modalApplyOne_diamondNeg_acc_eq, not_shape_of_not_or. These are privacy-caused duplicates that de-privatization alone cannot resolve: three consumer files cannot reach Soundness.lean where the largest family originates. This is a module-graph problem (new Support module or import restructure), not a statement-equivalence adjudication. The Support-module extraction audit supplies no verdict bearing on these, and the duplicate-family adjudication that followed it explicitly left this class untouched.

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

### 554. Cs5 pair seed disjunction property cutfree research
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [554_cs5_pair_seed_disjunction_property_cutfree_research/reports/02_cutfree-literature-grounded.md]
  - [554_cs5_pair_seed_disjunction_property_cutfree_research/reports/04_route-closure-reverification.md]
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
- **Dependencies**: Task 511, Task 531, Task 553, Task 563, Task 564, Task 566, Task 567, Task 586

**Description**: COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree (instDecidableFiveValid/instDecidableKb5Valid, FrameCompleteness.lean) is delivered via the KB5/S5 equivalence route, which leans on a full-equivalence closure. This task delivers genuine pure-K5 / pure-5 (Euclidean without full equivalence, no Mathlib closure operator) tableau soundness + completeness + decidability - the one modal-cube corner explicitly deferred out of the completed KB5/Euclidean task. Mirror the existing Five/KB5 development but over the bare Euclidean frame condition. Zero sorry, zero new axioms; keep the frozen equivalence-route deliverables untouched.

---

### 497. Reconcile imp naming
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 375, Task 393, Task 400, Task 425, Task 449, Task 535, Task 542

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
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 593
- **Research**: [375_proof_system_equivalence_tableau_sequent_edges/reports/01_tableau-tfae-fold-already-landed.md]

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
- **Dependencies**: Task 511
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
