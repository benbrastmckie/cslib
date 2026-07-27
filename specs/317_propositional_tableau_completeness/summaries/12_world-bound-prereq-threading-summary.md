# Summary: World-Bound Prerequisite Threading (Plan v12)

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Status**: [PARTIAL]
- **Started**: 2026-07-26
- **Completed**: 2026-07-26
- **Effort**: ~2.5 hours (this dispatch)
- **Dependencies**: 552 (completed)
- **Artifacts**:
  - plans/12_world-bound-prereq-threading.md (Phase 2 marked [COMPLETED], Phase 3 marked [BLOCKED])
  - handoffs/12_world-bound-decision.md (Phase 3 counterexample and evidence)
  - .orchestrator-handoff.json
- **Standards**: summary-format.md, status-markers.md, artifact-management.md

## Overview

This dispatch resumed plan v12 at Phase 2 (Phases 0-1 were already `[COMPLETED]` from prior
dispatches). It completed Phase 2 (pure code relocation) and began Phase 3 (the world-budget
accounting invariant), whose own mandated timeboxed alternative check produced a decisive,
evidence-backed finding that the plan's stated proof strategy for the load-bearing
`intExpandBranches_world_bound` lemma does not work as described.

## What Changed

- **Phase 2 (`[COMPLETED]`)**: Relocated the ~1,060-line universe/measure/persistence block
  (`intUniverse`, `intExpMeasure`, `applyPersistenceFixpoint_genuine_of_count_le_fuel`, and
  supporting lemmas) in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` from
  after `tableau_complete` to before `intExpandBranches_openBranch_sat`'s docstring, removing
  the forward reference that blocked v11's Phase 2. Executed via a verified pure line-slice
  splice (Python), not manual editing, given the scale (1,060 of 3,045 lines). Purity of the
  motion was verified by an **exact sorted-multiset-of-lines identity** between the pre- and
  post-move file — the strongest available confirmation that no character-level content changed,
  only position. Scoped builds green (`Intuitionistic.Scheme`, `Intuitionistic.Completeness`,
  `Minimal.Completeness`); committed at `49fbfe3c`.
- **Phase 3 (`[BLOCKED]`)**: No Lean file was edited for this phase. Its own mandated 30-minute
  timeboxed alternative check (required before committing to the injection strategy) was executed
  by directly computing against the real, unmodified `intuitionisticTableau`/`intApplyRuleFull`
  functions via `lean_run_code`, rather than hand-proving. This produced a concrete, reproducible
  counterexample: for `φ0 = ((p→q)→r ∧ (s→t)) → ((u1→v1)∨(u2→v2)∨(u3→v3))` (complexity 10), the
  single static `.imp`-node position `p→q` fires the world-creating rule at **8** distinct labels,
  not 1 — refuting the plan's (and three pre-existing in-file docstrings') claim that "each world
  created ... can be injected into a DISTINCT `.imp`-node position of φ0's own parse tree." Full
  derivation in `handoffs/12_world-bound-decision.md`. Committed at `59c889b7`.

## Decisions

- Used a verified line-slice splice for Phase 2's relocation rather than the Edit tool, matching
  the plan's own guidance to avoid whole-file reads/manual edits at this scale, and verified
  correctness via a stronger check than `git diff --stat` alone (exact sorted-line-multiset
  equality).
- Escalated Phase 3's timeboxed check into a full computational falsification rather than a
  30-minute "checked, proceed" formality, because an initial hand-trace of the proposed injection
  argument surfaced a plausible gap (T-signed persistence copying of a shared antecedent into
  sibling worlds) that warranted direct verification against the real functions before investing
  further proof-engineering effort.
- Did not write any speculative Lean toward the accounting invariant once the injection strategy
  was confirmed false — writing proof code against a strategy already known unsound would violate
  both the plan's zero-debt standard and the task's "do not weaken the bound to something vacuous"
  constraint.
- Marked Phase 3 `[BLOCKED]` rather than `[PARTIAL]`: there is no green Lean sub-step to resume
  from, only a decisive negative finding about the plan's own stated route.

## Impacts

- Phases 4 through 9 are transitively blocked (Phase 4 depends on Phase 3; Phases 5-9 depend on
  Phase 4). No further phases were attempted this dispatch.
- The task-tree sorry count is unchanged at 4 (`Intuitionistic/Scheme.lean:599,2578`,
  `Intuitionistic/Completeness.lean:133`, `Minimal/Completeness.lean:125`); repo-wide unchanged at
  29. Neither regressed.
- Whether the target numeric bound (`nextWorld ≤ φ0.complexity + 1`) itself holds remains
  **unresolved** — the counterexample formula still satisfies it (8 events vs. bound 11) with
  margin 3. Two follow-on stress tests designed to compound the effect (nesting the shared
  position inside a deeper implication chain) timed out in the `#eval` sandbox before returning a
  conclusive result; this is reported as genuinely open, not resolved in either direction.
- This task requires **re-planning** before Phase 3/4 can be attempted again. The handoff records
  three candidate directions (an amortized/multiset argument, a potential-function argument tied
  to the already-proven `intExpMeasure` machinery, or independent reverification of the bound via
  a faster instrumented harness) without committing to one, since evaluating them is plan-level
  work, not implementation-level work.

## Follow-ups

- Re-plan Phases 3 onward against the refuted-injection finding in
  `handoffs/12_world-bound-decision.md` before further implementation dispatches on this task.
- If a future dispatch wants to determine definitively whether `nextWorld ≤ φ0.complexity + 1` is
  even true, build a faster instrumented test harness (native-compiled, or hand-traced inside a
  copy of `intExpandBranches`) rather than continuing to push `#eval`-based stress tests, which hit
  a sandbox timeout at chain depth 2 before resolving the question.

## References

- `specs/317_propositional_tableau_completeness/plans/12_world-bound-prereq-threading.md`
- `specs/317_propositional_tableau_completeness/handoffs/12_world-bound-decision.md`
- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json`
