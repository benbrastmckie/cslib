# Research Report: Blocker Re-Assessment and Remaining Obligations

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Started**: 2026-07-24
- **Completed**: 2026-07-24
- **Type**: cslib (research dispatch — findings only, no implementation)
- **Inputs (machine-verified this dispatch)**:
  - Prior artifacts: `reports/02_validity-notion-fmp-grounding.md`,
    `plans/04_completeness-front-rescope.md`, `summaries/04_completeness-front-rescope-summary.md`
  - Source: `Cslib/Logics/Temporal/Tableau/Completeness.lean`, `Soundness.lean`, `Saturation.lean`,
    `Closure.lean`, `Branch.lean`
  - State: `specs/state.json`, `specs/archive/state.json`, `specs/TODO.md`
  - Precedent: task 317 (`317_propositional_tableau_completeness/reports/04_fuel-sufficiency-measure.md`)
- **Artifacts**: this report

## Executive Summary

- **The `[BLOCKED]` dependencies (426, 542) are STALE and both resolved.** Task 426
  (`temporal_tableau_ordconstraints_redesign`) is in `specs/archive/` — completed; it landed the
  `instant` field, `InstantStrict`, and the ordering-constraint machinery this task consumes. Task
  542 (docstring hygiene) is `completed`. Neither was ever the theoretical blocker. **Recommendation:
  clear `dependencies: [426, 542]` in state.json.**
- **BUT the task is NOT freely unblockable.** A *different*, genuine structural gap surfaced during
  the plan-04 implementation dispatch and is documented in `Completeness.lean`'s module docstring
  ("Blocked (FMP Existence Argument)"). Flipping the status to "ready to implement" would be wrong:
  the completeness front (Phases 5-7) is gated on a **fuel-sufficiency/pigeonhole theorem that is not
  yet formalized anywhere in the codebase**, plus an **`EventualityTracker` registration defect**.
- **Current source is zero-debt green.** Scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness`
  succeeds (1249 jobs). There are **no `sorry`/`admit`** in the entire `Cslib/Logics/Temporal/` tree.
  The remaining work is *missing declarations*, not broken proofs — the unfinished lemmas were simply
  never added (correct zero-debt discipline).
- **The smallest remaining obligation set is two prerequisites, not five lemmas.** Before any of
  `temporalTruthLemma_untl/_snce`, `openBranch_branchSat`, `temporalTableau_complete`,
  `temporalTableau_sound`, `instDecidableValid` can be attempted, two infrastructure questions must
  be settled: (P1) fuel-sufficiency, and (P2) the `.branching` eventuality-registration gap.
- **Strong external precedent that P1 is hard.** Sibling task 317 hit the *same class* of
  fuel-sufficiency wall for the propositional tableau and is currently `[BLOCKED]`: its report 04
  found the FMP bound the fuel was sized for assumes a *world/type deduplication the code does not
  perform*, and the true step count exceeds the fuel. The temporal tableau has the identical shape of
  gap. This is architectural, not tactic-effort.
- **Recommended path: `/spawn 425`** to create the two prerequisite subtasks the plan-04 already
  names, then `/revise 425` once they land. A single `/research 425 --hard` pass could alternatively
  resolve the strategic question below first (whether the periodic model is even needed).

## 1. Blocker Re-Assessment (deps 426, 542)

| Dep | Identity | Actual status | Was it the real blocker? |
|-----|----------|---------------|--------------------------|
| 426 | `temporal_tableau_ordconstraints_redesign` | **archived / completed** (`specs/archive/426_.../`) | No. It delivered `TimeOrdering.instant`, `InstantStrict`, and the constraint edges. Its work is already *consumed* by this task's landed Phase 1/2/4 assets (`extractModelℤ` keys on `ord.instant`; `instantStrict_constraint_lt` uses `InstantStrict`). |
| 542 | `strip_task_provenance_stale_claims_docstrings` | **completed** | No. Pure docstring hygiene; it even left a one-line pointer at the live gap in `Completeness.lean` explicitly *for* this task. Never a theoretical dependency. |

Both dependencies predate the plan-03/plan-04 re-scoping and reflect an earlier decomposition where
this task waited on the ordering redesign (426) and a coordination hold with the docstring sweep
(542). Neither holds now. The recent commit history confirms 426's successor work (task 439:
"complete (426 phase 3 — run-level InstantStrict threaded and wired)") landed on `main`, and Phase
1/2 of *this* task built on top of it.

**Verdict:** the `[BLOCKED]` status is stale *with respect to its recorded dependencies*, but the
task should not become "unblocked → implement." The genuine blocker (Section 3) is unrelated to 426/542
and was recorded in the task's own `blockers` field and in `Completeness.lean`'s docstring, not in the
dependency list.

## 2. Current State (source + build, verified this dispatch)

- **Build**: `lake build Cslib.Logics.Temporal.Tableau.Completeness` → *Build completed successfully
  (1249 jobs)*. (A bare `lake build` is red on the unrelated `Cslib/Logics/Modal/Tableau/LoopChecking.lean`,
  a different task's territory; scoped build is the correct gate, per plan-04's verification note.)
- **Sorries/admits in `Cslib/Logics/Temporal/`**: **zero** (the only `grep` hit is the prose string
  "None use `sorry`"). The propositional truth-lemma `sorry` that older artifacts reference
  (`Completeness.lean:433`, imp case, formerly owned by task 427) is **resolved** —
  `temporalTruthLemma_propositional_aux`/`temporalTruthLemma_propositional` are landed
  (`Completeness.lean:668`, `:1189`).
- **Target public lemmas — NOT yet declared** (this is the remaining work, held as absence, not sorry):
  - `temporalTruthLemma_untl`, `temporalTruthLemma_snce` — not present.
  - `openBranch_branchSat`, `temporalTableau_complete` — not present.
  - `temporalTableau_sound` — not present (appears only in a docstring at `Soundness.lean:49`).
  - `eventualityDefect_unsat` — **only a docstring sketch** inside a `BlockedObligations` section
    (`Soundness.lean:~208`, fenced in a ```lean illustration), *not* a real declaration.
  - `instDecidableValid` — not present.
- **Landed reusable assets** (all zero-debt, `lean_verify` clean per prior summaries):
  - Phase 1: `satisfiableDiscrete`, `validDiscrete_iff_not_satisfiableDiscrete_neg`
    (`Semantics/Validity.lean`); `branchSat` domain restricted to the discrete-serial frame class
    (`NoMaxOrder`+`NoMinOrder`+`SuccOrder`+`PredOrder`+`IsSuccArchimedean`) in `Soundness.lean`.
  - Phase 2: `TrackerBranchFaithful` + run-level threading
    (`temporalTableau_trackerBranchFaithful`, `Saturation.lean`).
  - Phase 4a (partial): `instantStrict_constraint_lt` (constraint-edge → `hL : instant t_anc < instant t_new`).
  - Phase 4b (full): `periodicReduce`/`periodicReducePast` (+ `_mem_Ico_of_gt`/`_of_lt`),
    `extractModelℤPeriodic`/`extractModelℤPeriodicPast` + 3 property lemmas each — the bi-lasso
    countermodel *definitions*, parameterized by an explicit loop witness.
  - Order preservation: `temporalTableau_instantStrict` (`Saturation.lean`).
  - Island model: `extractModelℤ` + `extractModelℤ_atomPos_sat`/`_bot_false`/`_atom_neg_notSat`.

## 3. The Genuine Blocker (what actually remains)

Two compounding facts, both re-verified against current source:

### P1 — Fuel-sufficiency / loop-witness existence (the real gate)

The bi-lasso periodic model (Phase 4a/4b spikes) needs a genuine `isSubsetBlocked` loop witness
`(t_anc, t_new)` derived from an *arbitrary* `temporalTableau φ = .openBranch b ord`. Tracing the
call graph shows this does not hold generically:

1. `isTemporalClosed` (`Closure.lean:106`) — hence eventuality-defect closure — is re-checked at
   *every* worklist step. A branch that ever satisfies `isSubsetBlocked` *with a pending eventuality*
   closes immediately (`findEventualityDefect` returns `some t` when `tracker.hasPending` and
   `findBlockedTime = some t`, `Closure.lean:88`). So it can never survive to be returned open with
   that witness intact. A *genuinely-saturated* open branch (`temporalStepBranch = none`) therefore
   has an **empty tracker**, for which the plain island `extractModelℤ` already suffices.
2. The periodic construction is thus only relevant to *fuel-exhausted* open branches
   (`temporalExpandBranches`'s `fuel = 0` fallback). But such a branch may have **no internal loop
   witness at all** — it was cut off mid-expansion. Proving one *must* exist requires an independent
   **fuel-sufficiency theorem**: that `temporalFuel φ = (4n+4)(n+2)+2` with `n = subformulaCount φ`
   (`Saturation.lean:76`, informally the `2^n`-distinct-time-types bound) guarantees `isSubsetBlocked`
   must already hold among the branch's labels whenever fuel exhausts with pending eventualities open.
   **This theorem is not formalized anywhere in the codebase.**

### P2 — `EventualityTracker` `.branching`-arm registration gap

`temporalStepBranch`'s `.branching` arm (`Saturation.lean:156-158`) passes `tracker` through
**unchanged** — `registerEventualities`/`fulfillEventualities` fire only on `.linear`/`.persistent`
arms (`:150-165`). Since `untlPos`/`sncePos` are branching rules (`Rules.lean`), a positive
Until/Since formula's *primary recurring copy* (`untlPos`'s `branch2`) is never registered into
`EventualityTracker.pending` by that call site. Consequently `tracker.hasPending` may not reflect the
"some Until copy is still live" fact that both the defect-detection soundness argument *and* the
fuel-sufficiency pigeonhole need. This must be assessed/fixed before P1 can be stated correctly.

### Strategic question these two raise (worth settling first)

The calculus has two candidate countermodels. `isTemporallyBlocked` (`Branch.lean:160`) fires only
when `isSubsetBlocked` **and** `allEventualitiesFulfilledOrDuplicated` (`Branch.lean:145`) — i.e. the
current defect semantics conflate "fulfilled-in-loop" and "unfulfilled-in-loop" loops in a way that,
combined with P2's under-registration, is not yet proven to match the intended accept/reject split.
The open question a research/revise pass should answer up front: **is the periodic bi-lasso model
actually required, or does the landed island `extractModelℤ` suffice for every open branch once
fuel-sufficiency guarantees genuine saturation (empty tracker)?** If the latter, the Phase 4a/4b
periodic spike is not on the critical path and Phases 5-7 can be proved over the *island* model —
substantially cheaper. This should be resolved before more model-construction is planned.

## 4. Reuse-First Findings (CSLib Foundations / precedent)

- **Task 317 is the load-bearing precedent for P1** (`reports/04_fuel-sufficiency-measure.md`, status
  `[BLOCKED]`): for the *propositional* tableau, fuel-sufficiency at the coded bound was found **not
  achievable** without either raising the fuel formula or adding world/type deduplication — because the
  FMP `2^σ` bound assumes an identification the procedure does not perform, and the true step count is
  `2^Θ(c²)` vs fuel `2^Θ(c)`. The temporal `temporalFuel` has the same `2^n`-time-types justification
  and the same `timeType` structure (`Branch.lean:112`, `eraseDups` over `(Sign × Formula)` pairs) with
  **no time-type deduplication of the branch itself** — expect the identical wall. Any P1 plan must
  budget for a possible `temporalFuel` bump or a `timeType`-dedup step in the saturation loop, and
  should reuse task 317's measure-design method and its `Finset` pigeonhole approach.
- **Task 421 (`min_fmp_decidability`)** is the reuse template named in the task description for the
  *final* `Decidable`-via-FMP wiring, but it decided a logic via finite-model *enumeration*, not a
  tableau loop-witness — so it transfers only at the `decidable_of_iff` assembly step
  (`validDiscrete φ ↔ temporalTableau (¬φ) = .closed`, routing through the landed
  `validDiscrete_iff_not_satisfiableDiscrete_neg`), not for the FMP construction itself.
- No existing `Cslib.Foundations.*` abstraction covers the fuel-sufficiency/pigeonhole lemma; it is
  genuinely new infrastructure (confirmed absent by search of the Temporal and Foundations trees).

## 5. Recommended Path (ordered, most tractable first)

**Step 0 (status correction, do regardless):** Clear the stale `dependencies: [426, 542]` in
state.json. Do **not** mark the task ready-to-implement — the P1/P2 gap remains.

**Step 1 (preferred — `/spawn 425`):** Create the two prerequisite subtasks plan-04 already names, in
this order (P2 first, it is smaller and may change P1's statement):

- **Subtask A — `EventualityTracker` `.branching` registration fix.** Extend
  `temporalStepBranch`'s `.branching` arm (`Saturation.lean:156-158`) to call
  `registerEventualities` on the branching outputs (mirroring the `.linear`/`.persistent` arms), and
  re-verify the Phase-2 `TrackerBranchFaithful` threading still holds. Scoped, self-contained, likely
  small. This is a calculus-correctness fix, not just plumbing — it also affects defect-detection
  soundness.
- **Subtask B — Fuel-sufficiency / pigeonhole theorem.** Target shape:
  `temporalExpandBranches … = .openBranch b ord → temporalStepBranch b _ ord tracker = none`
  (every returned open branch is genuinely saturated, never fuel-cut-off-with-pending). Proof strategy:
  pigeonhole over `timeType b : List (Sign × Formula Atom)` — at most `2 ^ subformulaCount φ` distinct
  time-types, so among `> 2^n` created labels two share a type, forcing `isSubsetBlocked` before fuel
  exhausts. **Mathlib API**: `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` (or
  `Fintype.exists_ne_map_eq_of_card_lt`) for the pigeonhole; `Order.SuccPred.Archimedean`
  (`IsSuccArchimedean`) for the finite successor-distance bounding the loop window; `List.Nodup` /
  `eraseDups` cardinality facts for the time-type count. **Carry task 317's finding**: first confirm
  the current `temporalFuel` constant is large enough, or plan a monotone `temporalFuel` bump / a
  `timeType`-dedup step in the loop. Budget this as the crux; it may itself land `[BLOCKED]` with a
  documented goal state if the bound is insufficient (as task 317 did).

**Step 2 (`/revise 425`):** Once A and B land, revise plan-04 to either (i) prove Phases 5-7 over the
**island** `extractModelℤ` if fuel-sufficiency shows open branches are always genuinely saturated
(cheapest; retire the periodic spike as unused), or (ii) wire `extractModelℤPeriodic`/`Past` in as the
real `extractModelℤ` (Phase 4c/4d) if fulfilled-in-loop branches must be accepted. The strategic
question in Section 3 decides which.

**Step 3 (deferred soundness half — separate research task, per plan-04 "Deferred Deliverable"):**
`temporalTableau_sound : temporalTableau φ = .closed → ¬ satisfiableDiscrete φ` via a **run-level,
model-guided contrapositive induction** (`temporalStepBranch_preserves_sat`), consuming the Phase-2
`TrackerBranchFaithful` asset and `IsSuccArchimedean` least-witness bounding. `eventualityDefect_unsat`
as a *local* `branchSat → False` fact is **not** the right target (it is false as a standalone; see
plan-04's preserved Phase-3 analysis).

**Alternative to Step 1 (`/research 425 --hard`):** If preferred over spawning, a single hard-mode
research pass should (a) settle the island-vs-periodic strategic question, (b) estimate P1's
provability at the current fuel bound against task 317's precedent, and (c) decide whether P2's fix
changes P1's statement — producing a plan-ready decomposition without creating separate task rows.

## 6. Risks / Caveats

- The strategic island-vs-periodic question is *not fully settled* by this dispatch — it requires
  reasoning about the calculus's accept/reject semantics for loops
  (`allEventualitiesFulfilledOrDuplicated` + the P2 under-registration interaction), which is exactly
  what Subtask A / the `--hard` research pass must pin down. Treat "island model suffices" as a strong
  hypothesis, not a proven fact.
- Task 317's precedent means Subtask B has a real chance of concluding the current `temporalFuel` bound
  is insufficient, forcing an architectural decision (raise fuel or add dedup). Plan for that branch.
- No `sorry`/axiom/vacuous-def workaround is acceptable for any of these (zero-debt gate); a documented
  `[BLOCKED]` goal state is the sanctioned outcome if a bound does not close, mirroring tasks 317/506.
