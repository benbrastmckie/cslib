# Implementation Summary: Phase 8.0 + Phase 8 — intFuel doubling and intExpMeasure_init_le_fuel

- **Task**: 317 - Propositional Tableau Completeness (Wave B)
- **Status**: [COMPLETED] (Phase 8.0 and Phase 8 of 11 total phases)
- **Started**: 2026-07-13T00:00:00Z
- **Completed**: 2026-07-13T00:00:00Z
- **Artifacts**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`,
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
  `specs/317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md`
- **Dependencies**: Prior handoff `blockers[0]` (verified-false `intExpMeasure_init_le_fuel` goal
  against the un-doubled `intFuel`, discovered in the Phase 7.2 dispatch, commit `b5d2fc86`)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, summary-format.md

## Overview

The prior dispatch left Phase 8 BLOCKED: `intExpMeasure_init_le_fuel` was verified FALSE as
stated because `intFuel`'s exponent (set in Phase 5) was not doubled the way Modal-K's
`modalFuel` is, so the initial worklist measure `3^(2|U|-1)` vastly exceeded `intFuel = 3^|U|`.
This dispatch resolves that blocker in two commits: doubling `intFuel`'s exponent
(`Expansion.lean`, Phase 8.0), then proving `intExpMeasure_init_le_fuel` against the corrected
fuel (`Scheme.lean`, Phase 8).

## What Changed

- `Expansion.lean:462-463` — `intFuel`'s exponent changed from
  `2 * (2 * φ.complexity + 1) * (φ.complexity + 2)` to
  `4 * (2 * φ.complexity + 1) * (φ.complexity + 2)`, mirroring Modal-K's `modalFuel` factor-of-2
  (`FmpMeasure.lean:232-233`). Commit `41d30054`.
- `Scheme.lean` — new lemma `intExpMeasure_init_le_fuel`, inserted before `end Cslib.Logic.PL`
  (~48 lines), mirroring `modalExpMeasure_entry_le_fuel` (`FmpMeasure.lean:208-251`). Sorry-free,
  additive-only. Commit `e2c9bf3b`.
- Plan file `06_route-a-frame-plumbing.md` — Phase 8 heading changed `[BLOCKED]` -> `[COMPLETED]`,
  resolution note added, checklist items checked off.
- `.orchestrator-handoff.json` — overwritten: `phases_completed` 6 -> 7, `blockers` cleared,
  `continuation_context` updated to point at Phase 9, world-bound necessity finding re-confirmed.

## Decisions

- Doubled the exponent exactly (`4 * (2c+1) * (c+2)`) rather than deriving a tighter closed form
  for the exact `2|U|-1` value — matches the plan's own suggestion and the Modal-K precedent, and
  the resulting arithmetic closes with EQUALITY (no slack needed), simpler than modal's own
  `modalWorldBound`-dependent formula.
- Did not touch `intExpandBranches_world_bound` (Phase 6's deferred fact) — re-confirmed it is
  unnecessary for this proof, consistent with two prior independent findings (Phase 7, Phase 7.2).
- Did not edit `Soundness.lean` or `DecisionProcedure.lean` — the re-audit (full `lake build`)
  showed all fuel-pinned callers unaffected by the larger fuel value.
- Fixed an `omega` atomization snag in the `intWork` bound proof by using `rw` (defeq-aware
  rewriting) instead of independently-stated `have` facts fed to `omega` (which failed to
  recognize the countP terms as syntactically identical atoms despite `lean_goal` showing them
  as textually identical) — see Follow-ups.

## Impacts

- Phase 9 (T-imp truthLemma sorry closure) and Phase 10 (measure-bound-supplied countermodel
  lemmas, STOP-gate R4) can now proceed; Phase 10's sole dependency (this Phase 8) is complete.
- No downstream consumer outside `Expansion.lean`/`Scheme.lean` required changes.
- Four task-317 inventory sorries remain exactly where they were (line numbers unchanged):
  `Scheme.lean:535`, `Scheme.lean:1388`, `Completeness.lean:133`, `Minimal/Completeness.lean:125`.

## Follow-ups

- Minor tooling note: `lean_verify` (MCP) reported `sorryAx` for `intExpMeasure_init_le_fuel` on
  first check; direct `#print axioms` via `lake env lean` showed only `[propext, Quot.sound]`
  (sorry-free, no new axioms) — the MCP tool result was spurious. No owner assigned; flagged for
  awareness in future dispatches on this task.
- Phase 9 dispatcher: re-grep for the literal `sorry` keyword at `Scheme.lean` before editing,
  since this dispatch's ~48-line addition at end-of-file may have shifted the exact byte offset
  reported by some tools (though `grep -n` confirmed the sorry's line number, 1388, is unchanged).

## References

- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json`
- `specs/317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md`
- `specs/317_propositional_tableau_completeness/summaries/07_expmeasure-phase7_2-and-phase8-blocked-summary.md`
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean:208-251` (reused proof template)
