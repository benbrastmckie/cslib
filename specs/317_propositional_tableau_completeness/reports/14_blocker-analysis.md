# Blocker Analysis: Task #317

**Parent Task**: #317 - propositional_tableau_completeness (Fill the remaining propositional/intuitionistic tableau completeness sorries)
**Generated**: 2026-07-26
**Blocker**: The four remaining `sorry`s cannot be closed by assembly. Report
`reports/13_blocker-root-cause-and-correct-approach.md` Lean-verified that
`intExpandBranches` DIVERGES (does not terminate) on a complexity-9 formula, refuting the world
bound that twelve consecutive plan versions were trying to prove, and refuting the goal at the
remaining `Scheme.lean:2578` `sorry` outright (a false statement, not a hard one).

## Root Cause

Full derivation: `reports/13_blocker-root-cause-and-correct-approach.md`; the falsified proof
strategy that triggered the escalation: `handoffs/12_world-bound-decision.md`.

**The divergence.** For `phi0 = (((a->b)->c) /\ ((d->e)->f)) -> ((u1->v1) \/ (u2->v2))`
(complexity 9, Lean-confirmed), `intExpandBranches [[F(phi0)@0]] [[]] [1] [[]] fuel
isIntuitionisticallyClosed` on the unmodified library produces branch lengths / max labels /
distinct-label counts of 27/4/5, 59/7/8, 100/10/11, 167/14/15 at fuel 10/20/30/40 (Lean `#eval`,
not merely the Python probe harness, which was validated against this data before use). Growth
continues linearly with no saturation through fuel 260 (87 distinct labels). From world 3 onward,
every world is an exact structural duplicate of its grandparent (identical T-set and F-set,
period 2) -- the loop is genuinely periodic, not merely slow.

**Consequence 1 -- the world bound is false, and so is any bound.**
`intApplyRuleFull_outputs_subset`'s `hnw : nextWorld <= phi0.complexity + 1` (`Scheme.lean:1813`)
and the label range `List.range (phi.complexity + 2)` baked into `intUniverse`
(`Scheme.lean:1575-1577`) are refuted by direct counterexample. No replacement bound of any size
exists, because the world count is unbounded in fuel on this input.

**Consequence 2 -- `Scheme.lean:2578`'s sorry is a false goal.** Lean-verified counter-instance:
at `branches = [[F(p/\q)@0]]`, `expandedSets = [[]]`, `nextWorlds = [1]`, `edgeSets = [[]]`, every
hypothesis of `intExpandBranches_openBranch_sat` holds, the loop returns exactly this branch, and
`IBranchSaturation.sat_fand`'s premise evaluates `true` while both disjuncts evaluate `false`. No
proof can close this statement as written.

**The named structural conflict.** The "Deliverable 6" T-implication copy channel in
`applyAllTImpRules` (`Expansion.lean:136-143`), added specifically to make `sat_timp` provable,
is in direct conflict with `intFImpRule`'s `propagatePersistence` (`Rules.lean:154-159`). Each
copy of a `T(phi->psi)` formula placed at a fresh sibling world BETA-resolves to a fresh
`F(antecedent)` at that world, which -- if the antecedent is itself `.imp`-shaped -- mints another
world, which receives another copy. Twelve plan versions each fixed one side of this conflict and
silently broke the other, because each dispatch inherited the prior dispatch's docstring claims as
fact rather than re-verifying them against the executable code.

**Why the existing loop-check cannot cut it.** `intFImpReuseWitness?` (`Expansion.lean:283-311`)
searches only worlds reachable FROM the creation site (descendants, via `isAccessible edges w x`).
In a standard Fitting-style (`Fitting1983` Ch. 4) loop-check, the blocking world is always an
ANCESTOR -- the forced-set `Sfor` at the blocking world already contains what the new world would
force, and `Sfor` grows monotonically along accessibility. Searching descendants is structurally
the wrong direction; fixing this is a calculus/completeness-side redesign (the standard
blocking/quotient countermodel construction), not a predicate tweak.

**Two positive findings preserved by this decomposition.** (1) Two historically-stale docstrings
(`Scheme.lean:3020-3041`'s "determinacy remains BLOCKED" claim, and `Scheme.lean:527`'s "`sat_timp`
is not a field" claim) are both refuted by the current code (`sat_timp` is a live field at
`Scheme.lean:105-108`, discharging `truthLemma`'s T-imp case with no converse needed). (2) The
`IAtomPersist` premise-narrowing route for the two `Completeness.lean` bridges was audited across
five formulas and both closure predicates in report 13 and holds in every case -- an empirical,
medium-confidence but viable route for task 317's eventual remaining assembly work.

**User decision.** The user explicitly selected report 13's Option A (repair the calculus) over
Option B (re-scope/document only) and Option C (retire the tableau-completeness route), and
approved the exact three-task decomposition below.

## Proposed New Tasks

### New Task 1: Correct stale tableau docstrings and record divergence findings
- **Effort**: 1-2 hours
- **Task Type**: cslib
- **Rationale**: Documentation-only fix that removes the exact trap (three stale docstrings) that
  misled twelve prior dispatches, and records the F1 divergence witness and the `Scheme.lean:2578`
  refutation in-code so no future dispatch re-attempts either. Zero proof risk; must land first
  because every downstream agent in this programme reads these docstrings.
- **Depends on**: None

### New Task 2: Spike -- verify blocking-quotient sat_fimp survives intExpandBranches_closed_unsat
- **Effort**: 3-5 hours
- **Task Type**: cslib
- **Rationale**: Report 13 names the quotient-frame `sat_fimp` restatement's interaction with
  `intExpandBranches_closed_unsat` as "the single largest unretired risk" (never prototyped in
  Lean; an earlier related fix died at exactly this obligation). A small, gated, NO-library-write
  spike de-risks the large repair task before 2500-4000 lines are committed to a possibly-unsound
  design.
- **Depends on**: New Task 1, because Task 2's dispatch reads (and must not re-derive) the
  corrected docstrings and the recorded refutations from Task 1 -- without them, a spike dispatch
  risks re-deriving the same false world-bound premise that misled twelve prior plans, wasting the
  spike's time-box on a question Task 1 already closed.

### New Task 3: Repair intuitionistic tableau calculus (self-copy bound, ancestor blocking, quotient sat_fimp)
- **Effort**: 2500-4000 lines; multi-dispatch, recommend `--hard` with phase-sized dispatches
- **Task Type**: cslib
- **Rationale**: Implements report 13's Option A steps 1-3 (bound the self-copy channel, replace
  the descendant-searching loop-check with an ancestor-directed one, restate `sat_fimp` over the
  blocking quotient). This is the actual calculus repair; task 317's four remaining sorries cannot
  be closed until it lands.
- **Depends on**: New Task 2, because Task 3's Step 3 (restating `sat_fimp` over the quotient and
  rewriting `truthLemma`'s F-imp case) is the exact soundness obligation Task 2 was dispatched to
  de-risk against `intExpandBranches_closed_unsat`. If Task 2 reports NO-GO or uncertain, Task 3's
  shape must change before dispatch (Task 2's own instructions require it to say so explicitly);
  Task 3 cannot be safely started without reading Task 2's decision record first.

## Dependency Reasoning

- **Task 2 depends on Task 1**: implementation detail, not mere completion order -- Task 2's
  research dispatch must read the corrected docstrings (in particular the accurate termination
  claim and the recorded F1 divergence witness) so it does not spend its time-box re-verifying
  facts Task 1 already settled and documented in-code.
- **Task 3 depends on Task 2**: Task 3's Step 3 is literally the construction Task 2 prototypes a
  GO/NO-GO answer for. Task 2's decision record's content (GO with documented approach, vs.
  NO-GO requiring re-scope) determines whether Task 3 can proceed as scoped or must first be
  revised -- this is a genuine implementation-detail dependency, not just sequencing.
- No pair of these three tasks is independent: the chain is strictly sequential by construction
  (hygiene -> spike -> repair), matching the user's explicitly approved dependency order.
- **File-footprint overlap (Component 4a)**: all three tasks list
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/` in `file_scope` (Task 1 writes to it, Tasks
  2 and 3 read/prototype against it, per the explicit spawn instructions), and Task 3 additionally
  covers `Cslib/Logics/Propositional/Tableau/Minimal/` and `CslibTests/TableauConformance.lean`.
  Every pairwise overlap on `Intuitionistic/` is already covered by the explicit dependency chain
  above (0->1, 1->2); no additional auto-added edge was needed.

## Required Follow-Ups (NOT performed by this spawn)

1. **Task 456's dependency direction is backwards.** Task 456 (`shared_tableau_containment_blocking`,
   `[NOT STARTED]`) currently states `"dependencies": [317]` and its description says it "DEPENDS
   ON task 317 landing first (so the `(psi not in forced(x))` side-condition shape is settled)".
   That is now backwards: 456 provides the exponential world bound (`Tableau.distinctTypes_le_pow`,
   `(b.labels.map b.typeAt).eraseDups.length <= 2^U.length` for a subformula-closed universe U)
   that the *repaired* calculus (New Task 3 above) needs before task 317's four assembly sorries
   can close. The correct edges are: **New Task 3 (calculus repair) -> task 456 -> task 317**.
   This state.json edit is left for the user/orchestrator to apply; this spawn does not edit
   `specs/state.json`.
2. **Task 317's description must be rewritten via `/revise 317`.** Its current description
   describes the old (refuted) linear-bound assembly-only scope. The rescoped remaining work is
   report 13's Option A step 5: the four sorries as genuine assembly, using the (empirically
   viable, not-yet-a-theorem) `IAtomPersist` premise-narrowing route for the two `Completeness.lean`
   bridges, blocked on task 456 landing. This spawn does not perform the rewrite.
3. **references.bib overlap flag.** Task 456's description already lists "add missing
   references.bib entries GargGenoveseNegri2012 and DershowitzManna1979". New Task 1 above also
   adds `GargGenoveseNegri2012` (plus a Dyckhoff-1992 key, which 456 does not mention). Whichever
   of New Task 1 or task 456 lands first should leave a note for the other to avoid a duplicate or
   conflicting BibTeX entry for `GargGenoveseNegri2012`.

## After Completion

Once all three spawned tasks are complete (in order: docstring hygiene, quotient-soundness spike,
calculus repair), and the two required follow-up state edits above have been applied (re-pointing
task 456's dependency and revising task 317's description), resume the parent task with
`/implement 456` followed by `/implement 317`, or drive the chain with `/orchestrate`.

The blocker will be resolved because: the calculus repair (New Task 3) removes the structural
conflict between the self-copy channel and persistence propagation that makes `intExpandBranches`
diverge, replacing the unbounded linear world-creation behavior with one bounded by task 456's
exponential blocking argument -- at which point task 317's four sorries become genuine assembly
work rather than attempts to prove or use a refuted invariant.

## Adversarial Self-Verification

**Verification date**: 2026-07-28, session `sess_1785275816_a84520_317` (H4 pass, `--hard`,
focus: divergence audit). Reports 13/14 were written BEFORE the spawned chain executed. Since
then: the quotient-soundness spike (`specs/archive/573_tableau_quotient_soundness_spike`,
completed), the calculus repair (task 574, completed), and the shared blocking module (task
456, completed, landing `Cslib/Foundations/Logic/Tableau/Blocking.lean`) have ALL landed, and
task 583's post-repair research
(`specs/583_restate_intexpandbranches_openbranch_sat/reports/01_restate-openbranch-sat.md`)
mechanically re-verified the fuel-0 refutation against the repaired code. Each load-bearing
claim of reports 13/14 was re-checked against that new reality, with evidence gathered by
direct grep/read of current sources plus two fresh `lean_verify` runs.

### Claim Verification Table

| Claim | Source/Counterexample | Verdict | Current evidence (file:line) |
|-------|----------------------|---------|------------------------------|
| Four sorries remain in scope; assembly cannot close them | Report 13 §Context; report 14 preamble | VERIFIED (line drift) | Bare sorries now at `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:617` (was 599), `Scheme.lean:2551` (was 2578), `Intuitionistic/Completeness.lean:133`, `Minimal/Completeness.lean:125` — confirmed by grep 2026-07-28 |
| `Scheme.lean:2578` fuel-0 goal is FALSE as stated (counter-instance `[[F(p∧q)@0]]`) | Report 13 F-summary bullet 3 / Decision 2 | VERIFIED (post-repair) | Refutation survives the 574 repair: 583's report re-ran the `#eval` counter-instance on current code (its Verification Log); refutation recorded in-proof at `Scheme.lean:2526-2550`, sorry at `Scheme.lean:2551` |
| No world bound of any size exists for the calculus (F1/F2 divergence) | Report 13 F1/F2 | VERIFIED for the RETIRED calculus; superseded for current code | In-code divergence note + `intUniverse` warning at `Scheme.lean:1591-1605`; regression row 20 in `CslibTests/TableauConformance.lean:67-72,338-350`. The ancestor-blocked calculus (574) empirically terminates on the witness, but NO post-blocking termination theorem exists — the bound question is re-OPEN (unproven), not re-refuted |
| Loop-check searches descendants; must become ancestor-directed (F5) | Report 13 F5; report 14 "named structural conflict" | DISCHARGED-BY-574 | `intFImpReuseWitnessAnc?` landed at `Expansion.lean:260`, spec lemma `Expansion.lean:~290`; descendant-directed `intFImpReuseWitness?` deleted (per docstring `Expansion.lean:253-259`) |
| `sat_fimp` must be restated over the blocking QUOTIENT frame; "single largest unretired risk" vs `intExpandBranches_closed_unsat` | Report 13 F5/Option A step 3; report 14 New Task 2 rationale | DISCHARGED-BY-574 (prediction REFUTED in detail) | Spike 573 completed; the landed design instead DROPPED the numeric `w ≤ w'` conjunct from `sat_fimp` (decision D8, docstring `Scheme.lean:100-106`) and kept the explicit `F(ψ)@x` conjunct with ancestor direction (`Expansion.lean:273-282`). No quotient restatement of `sat_fimp` exists or is needed; the risk is retired |
| Task 456 provides `(b.labels.map b.typeAt).eraseDups.length ≤ 2^U.length` (report 14 Follow-Up 1's stated form) | Report 14 "Required Follow-Ups" item 1 | REFUTED — corrected form DISCHARGED-BY-456 | 456's own research refuted this exact statement (sign doubling: 5 distinct type-lists over `U = [p,q]` vs bound 4; two independent falsity sources — `specs/456_shared_tableau_containment_blocking/reports/01_blocking-module-research.md:68-78,248`). The landed, corrected form is signed and Finset-valued: `Cslib.Logic.Tableau.distinctTypes_le_pow` over `V : Finset (Sign × F)` with bound `2 ^ V.card` (`Blocking.lean:150-158`); `lean_verify` 2026-07-28: axioms `{propext, Classical.choice, Quot.sound}`, no sorryAx |
| Dependency direction must be re-pointed: repair → 456 → 317 | Report 14 "Required Follow-Ups" item 1 | VERIFIED (applied) | `specs/state.json`: 456 `dependencies: [574]` (completed), 317 `dependencies: [456, 552]` (both completed); 574 `dependencies: [573]` (completed) |
| Three-task decomposition (hygiene → spike → repair) | Report 14 Proposed New Tasks | VERIFIED (executed) | 573 `tableau_quotient_soundness_spike` completed (archive); 574 `tableau_calculus_repair_ancestor_blocking` completed; docstring corrections in-code (stale "determinacy remains BLOCKED" block gone — only a benign GAP-2 mention survives at `Scheme.lean:2326`; `sat_timp` live field at `Scheme.lean:115`) |
| D3/D4 dangling BibKeys (`GargGenoveseNegri2012`, Dyckhoff) | Report 13 F7 defects | DISCHARGED | `references.bib:211` (`Fitting1983`), `:218` (`Dyckhoff1992`), `:239` (`GargGenoveseNegri2012`), `:1041` (`Massacci2000`) — all resolve |
| FMP decidability already sorry-free (F8) | Report 13 F8 | VERIFIED (re-run) | `lean_verify Cslib.Logic.PL.decidableDerivableIntPropAxiomFMP` re-run 2026-07-28 post-upstream-merge (`d5b6da26`): axioms `{propext, Classical.choice, Quot.sound}` |
| `IAtomPersist` premise-narrowing route viable for the two Completeness bridges | Report 13 F7 (medium confidence, empirical) | UNCERTAIN (unchanged) | Still empirical, not a theorem; now has a dedicated planned task in the queue (430 `prove_atom_persistence_upward_closure_for_intexpan`, status planned) |
| "After completion ... task 317's four sorries become genuine assembly work" | Report 14 closing paragraph | REFUTED as stated | 583's F3 equivalence result: with the sole call site `openBranch_countermodel` at `intFuel φ`, ANY provable restatement of the fuel-0 lemma is equivalent to the fuel-sufficiency theorem, which is NOT provable today — the landed measure engine (`Scheme.lean:1913-2487`, sorry-free, unused) is blocked on the refuted/unproven universe-containment invariant, and no post-blocking replacement bound has been proven. The repair made termination empirical, not theorematic; the sorries are NOT yet assembly |
| Plan 04 Phase 5.1's `intExpandBranches_world_bound_dedup` / `intExpandBranches_fuel_sufficient` obligations | plans/04, Phase 5.1/5.x | VERIFIED still open (never landed) | 0 grep hits for either name in `Cslib/` or `CslibTests/`. These are the same obligation 583's F5 names as the missing prerequisite (post-blocking `WBound φ` + `intUniverseExt`/`intExpMeasureExt` re-target + `intFuel` resize + threading invariants) |

### Additional freshness findings (not claims of reports 13/14)

1. **Blocking.lean is NOT yet consumed by the propositional tableau.** Only
   `Cslib/Logics/Temporal/Tableau/Branch.lean:9` imports
   `Cslib.Foundations.Logic.Tableau.Blocking` (its `timeType`/`isSubsetBlocked` are `rfl`-equal
   wrappers, `Branch.lean:126-134`). The intuitionistic ancestor check uses a LOCAL
   `posFormulasAt` with inline containment (`Expansion.lean:268-282`), not
   `Branch.posTypeAt`/`containmentBlocked`. Consuming the counting layer therefore needs a
   small bridge (local `posFormulasAt` ↔ `Branch.posTypeAt`, `Blocking.lean:77`) or direct use
   of the projection-agnostic helper `card_image_le_pow_of_forall_subset` (`Blocking.lean:130`).
2. **Territory collision with task 583.** Task 583 (status blocked) owns the restatement of the
   `Scheme.lean:2551` sorry — one of 317's four. Its report specifies the target restatement
   (form R1: `hUniv`/`hNW`/`hFuel` hypothesis threading) and the prerequisite's acceptance
   gate. A 317 plan that also schedules that sorry duplicates 583's scope; the overlap must be
   resolved explicitly (subsume 583 or defer to it) before dispatch.
3. **No task in the queue covers the fuel-sufficiency prerequisite.** The only related queue
   entries are the S4 analogues (511, 506 — both blocked, corroborating the difficulty) and
   430 (atom persistence, planned). 583's recommended `/spawn` of the prerequisite has not
   happened.

### Analysis-Paralysis Verdict

**Not analysis-paralysis — but now stale.** Reports 13/14 produced a concrete, executed
decomposition: three tasks were spawned and ALL completed (573 spike, 574 repair, 456 blocking
module), the dependency re-point was applied, and the in-code refutation/divergence notes
landed. That is the opposite of analysis-only output. However, reports 13/14 are no longer
accurate as planning inputs: their description of what 456 would provide is the refuted
pre-correction bound form, their quotient-`sat_fimp` prediction was superseded by the D8
design, and their closing claim that the four sorries "become genuine assembly" after the chain
lands is refuted by 583's post-repair equivalence result. The load-bearing current ground truth
is: this section, 583's report 01, and the in-code notes (`Scheme.lean:1591-1605`,
`Scheme.lean:2526-2550`, `Expansion.lean`'s divergence-witness note).

### Planning Readiness

The next plan version (v13) for task 317 must be built on the post-456/574 reality, not on
reports 13/14's pre-repair scoping. Concretely, it must **consume from
`Cslib/Foundations/Logic/Tableau/Blocking.lean`** (namespace `Cslib.Logic.Tableau`; all
sorry-free, `lean_verify`-clean): `Branch.posTypeAt` (`:77`, the Sfor projection) with
`mem_typeAt_iff` (`:91`), the projection-agnostic counting helper
`card_image_le_pow_of_forall_subset` (`:130`), `toFinset_eraseDups` (`:142`),
`distinctTypes_le_pow` (`:150`, SIGNED form: bound `2 ^ V.card` over `V : Finset (Sign × F)`;
instantiate `V = S ×ˢ {pos, neg}` for `2 ^ (2·|S|)`, or use `posTypeAt` over `U : Finset F`
for `2 ^ U.card` — the old `eraseDups.length ≤ 2^U.length` form is FALSE and must not be
planned against), `exists_typeAt_eq_of_card_lt` (`:163`, pigeonhole), and
`strictChain_le_card` (`:185`, the chain bound matching "Sfor strictly grows past every
unblocked ancestor ⇒ chain length ≤ |Sub(φ)|" — the natural discharge shape for plan 04 Phase
5.1's never-landed `intExpandBranches_world_bound_dedup`). The genuinely open obligations are:
(a) the **fuel-sufficiency development** — post-blocking world bound `WBound φ`, enlarged
`intUniverseExt`/`intExpMeasureExt`, `intFuel` resize, and `hUniv`/`hNW` threading invariants
per 583's F5 acceptance gate — on which BOTH `Scheme.lean:2551` (via 583's F3 equivalence) and
`Scheme.lean:617` (via `applyPersistenceFixpoint_genuine_of_count_le_fuel`, `Scheme.lean:2424`,
whose `hb` premise is the same containment invariant; the in-file STOP-gate directs both be
closed in one pass) directly depend; and (b) the two Completeness bridges
(`Intuitionistic/Completeness.lean:133`, `Minimal/Completeness.lean:125`) via the `IAtomPersist`
route (task 430's scope), which itself presupposes saturated branches and therefore also sits
downstream of (a). **All four remaining sorries depend on the fuel-sufficiency gap 583
identified**; no queued task covers it, so the plan must either open with it as its own
phase-block (consuming Blocking.lean's counting layer plus the already-landed, currently-unused
measure engine at `Scheme.lean:1913-2487`) or direct a `/spawn` for it first — and must resolve
the `Scheme.lean:2551` territory overlap with blocked task 583 explicitly before any dispatch
touches that sorry.
