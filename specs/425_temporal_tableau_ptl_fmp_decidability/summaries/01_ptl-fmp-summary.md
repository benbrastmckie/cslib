# Implementation Summary: PTL Finite Model Property and Temporal Tableau Decidability

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Status**: [BLOCKED] (partial — 0/6 phases completed)
- **Plan**: plans/01_ptl-fmp-decidability-plan.md

## Outcome

No phases were completed. Phase A (soundness half: `eventualityDefect_unsat` +
`temporalTableau_sound`) was blocked during pre-implementation analysis, before any `.lean` file
was edited. `Cslib/Logics/Temporal/Tableau/` is unchanged from before this dispatch.

## What Was Done

Rather than transcribing the plan's Phase A task list directly into Lean, I first traced the
precise semantics of every predicate the proof would need (`findEventualityDefect`,
`isSubsetBlocked`, `allEventualitiesFulfilledOrDuplicated`, `ancestorTimes`,
`EventualityTracker`) against `branchSat`'s definition and the `untl_iff`/`snce_iff` semantics, to
confirm the report's §3 "pumping" argument sketch would actually discharge the goal before
committing Lean code. It does not, for three independent, cross-checked reasons documented in full
in the plan file's Phase A `[BLOCKED]` annotation and in
`handoffs/01_phase-a-blocker-handoff.md`:

1. The lemma's bare hypotheses don't tie `tracker` entries back to actual branch members (that
   link only holds by construction during a live run, not statically).
2. A single subset-blocked ancestor/descendant pair is provably insufficient to derive a
   contradiction from `branchSat` (an explicit non-contradictory witness assignment was
   constructed by hand).
3. A deeper mismatch: `branchSat`'s domain is fully general (`LinearOrder`/`Nontrivial`, no
   seriality/discreteness), but the `untlPos` rule's `branch1` case is only sound under a
   discreteness/successor assumption, and the rest of the Temporal metalogic layer
   (`Metalogic/Soundness.lean`, `Metalogic/Completeness.lean`) targets `Temporal.validSerial`, not
   the fully general `Temporal.valid` this plan's Phase F specifies. `valid`/`validSerial`/
   `validDiscrete` are a documented incomparable hierarchy
   (`Semantics/Validity.lean:19-39`), and the tableau's ℤ/successor `TimeOrdering` design most
   plausibly corresponds to `validDiscrete`.

## Plan Deviations

- **Phase A**: *(deviation: blocked — see plan file's Phase A `[BLOCKED]` section and
  `handoffs/01_phase-a-blocker-handoff.md` for the full three-part technical finding)*. No Lean
  code was written; the finding was made analytically to avoid landing an unsound or
  incorrectly-scoped lemma.
- **Phases B–F**: *(deviation: not started — blocked transitively; Phase B additionally
  cross-referenced with a note about the same validity-quantifier question, since Phase F's target
  choice affects what `openBranch_branchSat`'s existential witness needs to establish)*.

## Recommendation

Run a dedicated research pass (`/research 425 --lit --hard`, grounding against the cited
[Reynolds1994] source and a close read of `Metalogic/Completeness.lean` /
`Metalogic/Soundness.lean`'s exact frame-class hypotheses) to settle: (a) which validity notion
this tableau actually decides; (b) whether `branchSat`'s domain hypothesis needs a discreteness
correction; (c) the run-level tracker/branch-faithfulness invariant needed for
`eventualityDefect_unsat`; (d) the corresponding correction to Phase F's target (likely
`Temporal.validDiscrete`). Then `/revise 425` before the next `/implement 425`.

## Verification

- `Cslib/Logics/Temporal/Tableau/*.lean`: unchanged (verified via `git status --short`).
- No `sorry`, no vacuous definitions, no new axioms — no code was written.
- CSLib CI pipeline not run (no code changes to verify; nothing to build beyond the pre-existing
  green baseline).

## AI Tools Used

This task's implementation dispatch was carried out by the CSLib implementation agent (Claude
Code, Anthropic), which performed the semantic analysis above and authored this summary, the
handoff document, and the plan-file blocker annotation.
