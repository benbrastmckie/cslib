# Implementation Summary: Task 553, Phase 2 (Decision Gate)

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Plan**: `plans/03_ancestor-only-blocking.md` (v3), Phase 2 only
- **Status**: BLOCKED (route does not close; escalation to user required)
- **Session**: sess_1785084826_a33d36

## What Was Done

Phase 2 was the ancestor-only-blocking route's decision gate: prove, standalone and with no
driver dependency, that adding a back-edge `src -> a` (where `a` is a spine ancestor whose
recorded key matches the prospective mint's birth content) preserves `branchSatisfiableIn s4FC`.

Landed in `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`:

- `hasEdge_addEdge_cases_anc` (line ~1198): local re-derivation of `Soundness.lean`'s private
  `hasEdge_addEdge_cases`, following this file's existing per-section re-derivation pattern.
- `branchSatisfiableIn_s4FC_ancestor_redirect` (line 1220): the decision-gate lemma itself,
  stated over abstract hypotheses (`hanc : acc.hasEdge a src`, plus `hboxback`/`hdianeg` standing
  in for `S4LoopInv.keyLowerBd`'s semantic payoff with no reference to `keys`/
  `successorBirthContent`/`spine`). Contains one documented `sorry` at line 1244, landed as a
  deliberate strategic skeleton per this dispatch's Recovery Discipline instruction.

`lake build Cslib.Logics.Modal.Tableau.FrameSoundness` is clean apart from the single expected
`declaration uses 'sorry'` warning. `lake exe checkInitImports` passes. A repo-wide grep confirms
this is the only real `sorry` under `Cslib/Logics/Modal/Tableau/`.

## Verdict

**BLOCKED.** The proof reaches an unresolvable obligation (exact `lean_goal` state recorded in
the plan's `#### Phase 2 Verdict` section and in
`handoffs/phase-2-blocked-handoff-20260726.md`). The predicted failure mode (boxed vs. unwrapped
`keyLowerBd` content) never materialized — the proof stalls one step earlier:
`branchSatisfiableIn`'s witness model is existentially arbitrary (not required to equal `acc`'s
transitive closure), so justifying the new edge requires transitively closing the model relation
over *every* ambient predecessor of `src`, a family no standalone, driver-independent hypothesis
set can name. This is the same obstruction already documented in this file's own
`branchPropAdequateIn` module comment for Route P's identical redirect-to-an-existing-world shape.

The two `NOT-YET-VERIFIED — Phase 2 gate` mapping-table rows are resolved: "an ancestor back-edge
is model-justifiable" is **REFUTED** (as a standalone lemma); "the route closes without boxed
birth content" is **MOOT** (the boxed refinement would not fix the actual obstruction, so no
Phase 2b was added).

Per the phase's own done-condition, this **BLOCKED verdict means the route does not close and
must be escalated to the user before Phase 3.** Phases 3-14 are not sequenced around this gate.
The `Gore1999` literature-acquisition escalation branch does not apply — the blocker is a
structural fact about how `branchSatisfiableIn` is encoded in this codebase, not a literature gap.

## Plan Deviations

- Stated the lemma for the **single-hop** ancestor case (`acc.hasEdge a src` directly) rather than
  a full multi-hop spine chain via `Relation.ReflTransGen`. This is a legitimate simplification,
  not scope-narrowing: the multi-hop case is a strict generalization (more edges needing the same
  unavailable justification), so the single-hop base case blocking is sufficient to block the
  general case *a fortiori*. Documented in the plan's task checklist and the handoff.
- Did not add a Phase 2b (boxed-birth-content refinement) since its trigger condition (the
  predicted unwrapped-vs-boxed failure mode) was not the actual obstruction encountered.
- Landed a `sorry`-marked skeleton rather than fully reverting the scratch lemma (as this task's
  own Phase 10 precedent did) — this dispatch's explicit Recovery Discipline instruction called
  for the documented-skeleton approach instead.

## Artifacts

- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (modified: +2 declarations, 1 sorry)
- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/03_ancestor-only-blocking.md`
  (Phase 2 heading -> `[BLOCKED]`, top-level Status -> `BLOCKED`, new `#### Phase 2 Verdict`
  subsection)
- `specs/553_s4_loop_guard_soundness_reachability_restriction/handoffs/phase-2-blocked-handoff-20260726.md`
- `specs/553_s4_loop_guard_soundness_reachability_restriction/.orchestrator-handoff.json`

## sorry_inventory

- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1244` — documented strategic sorry in
  `branchSatisfiableIn_s4FC_ancestor_redirect`, see verdict above.
