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
