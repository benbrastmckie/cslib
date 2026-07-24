# Implementation Summary: PTL Temporal Tableau — Completeness Front (bi-lasso FMP), round 04

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Plan**: plans/04_completeness-front-rescope.md
- **Status**: [PARTIAL] — Phase 4 partial (4a conversion half + 4b in full landed, zero-debt,
  verified); Phases 5-7 blocked (chained on Phase 4's 4c/4d, which are blocked on a genuine,
  precisely-documented structural gap). Phases 1-2 (completed assets from prior rounds) untouched
  and reused as-is. Phase 3/8 remain out of scope per this plan's re-scope decision (deferred to a
  separate soundness research task, not attempted here).

## Scope of This Dispatch

Delegated scope was Phases 4-7 only (Phases 1-2 preserved assets, Phase 3/8 explicitly out of
scope per the plan's Re-Scope Decision). Territory: `Cslib/Logics/Temporal/Tableau/Completeness.lean`
only; `Cslib/Logics/Modal/**` was not touched (per the concurrent-territory warning — task 535 was
mid-edit on `LoopChecking.lean`, confirmed still red at dispatch end via a bare `lake exe
checkInitImports`/`lake lint` attempt, unrelated to this work).

## What Was Done

### Phase 4: Complete the bi-lasso countermodel [PARTIAL]

**Landed (zero-debt, verified)**:

- **(4a, partial)** `instantStrict_constraint_lt`: converts a recorded ordering-constraint edge
  `(t_anc, t_new) ∈ ord.constraints` plus `InstantStrict ord` into `hL : ord.instant t_anc <
  ord.instant t_new`, the conversion half of deriving the periodic reductions' loop-witness
  hypothesis from tableau-level facts rather than a free parameter.
- **(4b, full)** The symmetric backward (past-tail) periodic reduction: `periodicReducePast` +
  `periodicReducePast_mem_Ico_of_lt` (mirroring `periodicReduce`/`periodicReduce_mem_Ico_of_gt`
  exactly — same `toIcoMod` formula, flipped guard direction), plus `extractModelℤPeriodicPast`
  and its three property lemmas (`extractModelℤPeriodicPast_atom_sat_iff_of_ge`,
  `extractModelℤPeriodicPast_atomPos_sat_of_ge`, `extractModelℤPeriodicPast_bot_false`), mirroring
  the already-landed forward spike's `extractModelℤPeriodic` + 3 lemmas.
- Updated `Completeness.lean`'s module docstring ("Main Results", "Blocked Obligations",
  "Remaining Work") to reflect the propositional truth lemma's completion (previously listed as
  blocked; it was already landed in an earlier round), the new Phase 4a/4b declarations, and the
  precise structural finding below.
- Verification: scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness` green;
  `lean_verify` on `periodicReducePast_mem_Ico_of_lt` and `instantStrict_constraint_lt` report
  only `propext`/`Classical.choice`/`Quot.sound` (the former) and no axioms at all (the latter,
  a direct application); `grep -rn "\bsorry\b"` over the file returns zero hits;
  `lake exe lint-style` on the file returns clean (no output).

**Not landed (4c, 4d) — see BLOCKER below, marked in the plan file**:

- 4c (wire `extractModelℤPeriodic`/`extractModelℤPeriodicPast` in as the real `extractModelℤ` at
  call sites, re-proving the existing `extractModelℤ_*` property lemmas against it) was not
  attempted: it requires the *existence* half of the loop-witness derivation (deriving a genuine
  `isSubsetBlocked` witness from an *arbitrary* `temporalTableau φ = .openBranch b ord` result),
  which the trace below found does not hold generically as stated.
- 4d (the "every instant carries a complete Hintikka time-type" helper) depends on 4c's wiring and
  was not attempted.

### The BLOCKER (full trace in `Completeness.lean`'s module docstring and the plan file)

Tracing `isTemporalClosed`/`findEventualityDefect`/`findBlockedTime`/`isSubsetBlocked`
(`Closure.lean`, `Branch.lean`) against `temporalStepBranch`/`processNext`/`temporalExpandBranches`
(`Saturation.lean`) found two compounding structural facts that break Phase 4c/4d's premise:

1. **Genuinely-saturated open branches never need the periodic construction.** `isTemporalClosed`
   is re-checked at every worklist step, so a branch whose content ever satisfies
   `isSubsetBlocked` with a pending eventuality closes *immediately* — it cannot survive to be
   returned open with that witness intact. Conversely, genuine saturation
   (`temporalStepBranch = none`) requires every live Until/Since copy to have already resolved
   (empty tracker), for which the plain "island" `extractModel`/`extractModelℤ` already suffices.
2. **Fuel-exhausted open branches may carry no internal loop witness at all.** The periodic
   construction is only relevant for the *other* source of `.openBranch` results — the
   `temporalExpandBranches` `fuel = 0` fallback — but that same `isTemporalClosed` check applies
   there too, so a fuel-exhausted branch with pending eventualities may genuinely have no
   `isSubsetBlocked` pair among its own labels at the moment fuel ran out (it was simply
   mid-expansion, not looped). Proving one must exist requires an independent, currently
   unformalized **fuel-sufficiency/pigeonhole theorem**: that `temporalFuel`'s `2^n`-distinct-
   time-types bound (`Saturation.lean:76`) guarantees blocking must already have triggered before
   fuel exhausts whenever pending eventualities remain. This is the actual mathematical content of
   the tableau's termination argument and is not yet formalized anywhere in the codebase.
3. A secondary, narrower finding: `temporalStepBranch`'s `.branching` arm (used by
   `untlPos`/`sncePos`/all branching rules) passes the `EventualityTracker` through *unchanged* —
   `registerEventualities`/`fulfillEventualities` only fire on `.linear`/`.persistent` outputs. So
   a positive Until/Since formula's primary recurring copy (`untlPos`'s `branch2`) is never itself
   registered as pending by that call site. This means `tracker.hasPending` may not even reflect
   the fact the pigeonhole argument needs, independent of the pigeonhole question itself.

This is a genuine mathematical gap, not a proof-complexity issue solvable by more tactic effort —
it requires new infrastructure (the fuel-sufficiency theorem) not yet present in the codebase.

### Phases 5, 6, 7 [BLOCKED]

All three chain from Phase 4c/4d and were not attempted. Phase headers marked `[BLOCKED]` in the
plan file with a one-line cross-reference to the Phase 4 BLOCKER; the phases' original task
checklists are preserved (HTML-comment-fenced) for the eventual follow-on plan.

## Plan Deviations

- **Phase 4, task 4a**: altered — landed only the conversion half (`instantStrict_constraint_lt`);
  the existence half was found not to hold generically and is documented as the BLOCKER rather
  than attempted with a weaker/narrowed statement.
- **Phase 4, task 4c**: skipped — blocked on 4a's existence half (see BLOCKER).
- **Phase 4, task 4d**: skipped — blocked on 4c.
- **Phases 5, 6, 7**: skipped in full — chained on Phase 4c/4d.
- Plan-level `Status` field updated from `[IMPLEMENTING]` to `[PARTIAL]`; Phase 4 heading updated
  from `[IN PROGRESS]` to `[PARTIAL]`; Phase 5/6/7 headings updated from `[NOT STARTED]` to
  `[BLOCKED]`.

No `sorry`, no new axioms, no vacuous definitions were introduced at any point.

## Verification Results

- Scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness`: **green**.
- Full-project `lake build`/`lake lint`/`lake exe checkInitImports`: **not run** — confirmed still
  red on the unrelated concurrent `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (task 535's
  territory), consistent with the delegation's stated caveat. Not gated on.
- `lake exe lint-style` on the modified file: clean (no output).
- `grep -rn "\bsorry\b" Cslib/Logics/Temporal/Tableau/Completeness.lean`: 0 hits (excluding the
  prose string "sorry-free").
- `lean_verify` on new declarations: no `sorryAx`, no axioms beyond `propext`/`Classical.choice`/
  `Quot.sound` (all three already used pervasively throughout Mathlib-backed CSLib proofs).
- New axiom count: 0.
- Vacuous-definition count: 0.

## Recommended Next Action

Per the plan's own Rollback/Contingency section: Phase 4's *tractable* increment (4a-conversion +
4b in full) is a valid landable milestone on its own. The path to Phase 4c/4d/5/6/7 requires either:

1. A dedicated research pass to attempt the fuel-sufficiency/pigeonhole theorem identified above
   (estimate size, confirm/refute provability, decide whether `EventualityTracker` registration
   needs extending to `.branching` outputs), or
2. The plan's own named fallback: the `Fin`-indexed cyclic-quotient domain route (report 02
   §recs.7), which changes the `branchSat`/countermodel interface shape and would need its own
   scoping pass against the now-landed `extractModelℤPeriodic`/`extractModelℤPeriodicPast` spike
   assets.

Recommend `/spawn 425` or a fresh `/research 425 --hard` pass targeting exactly the open goal
above before the next `/revise 425` / `/implement 425`.

## Files Touched

- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — Phase 4a (partial)/4b (full) declarations
  and updated module docstring.
- `specs/425_temporal_tableau_ptl_fmp_decidability/plans/04_completeness-front-rescope.md` — phase
  status markers, BLOCKER writeup, plan-level Status field.
- `specs/425_temporal_tableau_ptl_fmp_decidability/summaries/04_completeness-front-rescope-summary.md`
  — this file.
- `specs/425_temporal_tableau_ptl_fmp_decidability/.return-meta.json`,
  `specs/425_temporal_tableau_ptl_fmp_decidability/.orchestrator-handoff.json` — final metadata.
