# Summary: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries

## Metadata

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Status**: [PARTIAL]
- **Started**: 2026-07-26T00:00:00Z
- **Completed**: 2026-07-26T00:00:00Z
- **Effort**: ~3 hours (hard-mode dispatch)
- **Dependencies**: 552 (completed)
- **Artifacts**:
  - `plans/11_tableau-completeness-assembly.md` (updated: Status → [PARTIAL], Phase 0/1 →
    [COMPLETED], Phase 2 → [BLOCKED])
  - `handoffs/11_phase0-spike-decisions.md` (Phase 0 verification spike decision record)
  - `handoffs/11_phase2-blocker-findings.md` (Phase 2 blocker — full findings and evidence)
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (modified: Phase 1)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, summary-format.md

## Overview

This dispatch executed the hard-mode implementation plan v7 for task 317 starting from Phase 0.
Phases 0 and 1 completed cleanly and are committed. Phase 2 (universe/measure invariant
threading) was attempted and hit two compounding, concretely-verified obstacles not accounted
for in the plan's sizing; the broken in-progress attempt was reverted, and the finding was
documented in full rather than forced through with a shortcut. Phases 3-7 were not attempted
(transitively blocked on Phase 2's infrastructure).

## What Changed

- **Phase 0 (verification spike)**: confirmed via `lean_goal` and source inspection that (a)
  the T-imp case at `Scheme.lean:592` (now `:599`) closes by forward-only disjunction
  elimination once `sat_timp`/`ITimpAccess` exist, and (b) `tableau_complete`'s `hvalid` premise
  is genuinely unprovable at its current arbitrary-`edges`/`b` quantification, confirming Phase
  7's premise-narrowing is required (not optional). R1 pinned-SHA and R8 single-construction-site
  checks both passed. Decision record: `handoffs/11_phase0-spike-decisions.md`.
- **Phase 1 (`sat_timp` field)**: added the reflexive `sat_timp` field to `IBranchSaturation`
  (`Scheme.lean`, after `sat_fimp`) and discharged it mechanically at `IExpandedConsistent_sat`
  (the sole construction site), using the exact same `compound_sat`/`intStepBranch_none_compound_mem`
  pattern the five existing fields use, against `sfSatisfied`'s already-landed `.pos, .imp`
  clause. Scoped builds of `Intuitionistic.Scheme`, `Intuitionistic.Completeness`, and
  `Minimal.Completeness` are all green; sorry count in the task tree is unchanged at 4 (this
  phase closes none, as scoped).
- **Phase 2 (blocked, no code changes retained)**: attempted to add a `φ0` parameter plus
  universe-membership and measure-bound hypotheses to `intExpandBranches_openBranch_sat`.
  Discovered (1) `intUniverse`/`intExpMeasure` are declared ~450-950 lines *after* this lemma in
  the file, a genuine forward-reference (verified via a real build error) requiring a large
  relocation of already-landed code; and (2) maintaining the universe-membership invariant
  across the F-imp world-creating step needs a `nextWorld ≤ φ0.complexity + 1` bound
  (`intExpandBranches_world_bound`) that the file itself documents in three places
  (`Scheme.lean:2025-2038`, `:2052-2055`, `:2536-2538`) as a known, unbuilt "continuation" —
  not a mechanical assembly step. The broken attempt was reverted with `git checkout --`; the
  file is back to the Phase-1-committed green state. Full findings, including a genuine positive
  discovery (Phase 3's zero case is actually easy once the invariant exists — a short
  contradiction from `intExpMeasure ≤ 0` forcing `branches = []`), are in
  `handoffs/11_phase2-blocker-findings.md`.

## Decisions

- Did not force Phase 2 through with a weakened invariant, a `sorry`, or a vacuous restatement;
  reverted the broken attempt instead, per the postmortem's "no sorry, no vacuous closure" rule
  and the plan's own R4-style stopping discipline (applied one phase earlier than R4 anticipated).
- Recorded the zero-case simplification (Phase 3 is easier than described, *given* the
  invariant) so a future dispatch does not re-derive it.
- Did not attempt to relocate the `intUniverse`/`intExpMeasure` block or invent
  `intExpandBranches_world_bound` within this dispatch: both are substantial, separately-sized
  units of work, not slack inside Phase 2/3's stated budget, and inventing a new combinatorial
  lemma under time pressure risked exactly the kind of unverified shortcut the postmortem
  constraints prohibit.

## Impacts

- `IBranchSaturation` now has 6 fields instead of 5; every existing consumer (`Intuitionistic/
  Completeness.lean`, `Minimal/Completeness.lean`) still builds unchanged since `sat_timp` is
  additive and mechanically discharged at the sole construction site.
- Phases 3-7 of plan v11 cannot proceed until Phase 2's prerequisite (either the file
  relocation, or an alternative invariant shape that avoids the forward-reference, plus the new
  `intExpandBranches_world_bound` lemma) is planned and built. This is a genuine scope
  correction to the plan, not a re-litigation of any settled design decision.
- Sorry count: task-tree scan unchanged at 4 (`Intuitionistic/Scheme.lean:599`,
  `Intuitionistic/Scheme.lean:1517`, `Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`); repo-wide strict scan unchanged at 29. Neither went down
  this dispatch — expected and disclosed, since Phases 1-2 as scoped do not close any sorry.

## Follow-ups

- Re-plan Phases 2-7 as a new plan round (v8), budgeting explicitly for: (1) relocating the
  `intUniverse`/`intExpMeasure`/`intSubfmls`/`intWork` block before
  `intExpandBranches_openBranch_sat`; (2) a new `intExpandBranches_world_bound` lemma bounding
  the running `nextWorld` counter by `φ0.complexity + 1`, using the already-proven
  `intSubfmls_impCount_le` as its combinatorial ingredient. Owner: next `/plan 317 --hard`
  dispatch.
- Unrelated, pre-existing full-build failure discovered during CI verification: `Cslib/Logics/
  Modal/Metalogic/Constructive/Nested/Soundness.lean` fails `lake build` with a missing-cases
  error (`NestedProof.cut (InputCtx.mk _ _ _)`), committed by task 554 (`88b198bf`, 2026-07-26
  07:47:11), unrelated to task 317's files (verified: `git status --short Cslib/Logics/Modal/`
  is clean, so this is committed, not a concurrent-session artifact of this dispatch). Not fixed
  here (out of territory); flagged for whoever owns task 554.

## CI Status (this dispatch)

- Scoped `lake build` of `Intuitionistic.Scheme`, `Intuitionistic.Completeness`,
  `Minimal.Completeness`: **PASS** (green, unchanged sorry count).
- Scoped `lake build CslibTests.TableauConformance` (the 43-row regression guard): **PASS**.
- Full `lake build`: **FAIL**, but due to the unrelated pre-existing task-554 breakage noted
  above, not task 317's changes.
- `lake exe checkInitImports`: **FAIL** (transitively, only because the full build fails on the
  unrelated module; not evaluable independently of the full build).
- `lake lint` / `lake exe lint-style` / `lake shake`: not run (full pipeline blocked by the
  unrelated pre-existing failure above; the scoped build of `Scheme.lean` showed no new lint
  warnings beyond pre-existing ones already present before this dispatch).

## References

- `specs/317_propositional_tableau_completeness/plans/11_tableau-completeness-assembly.md`
- `specs/317_propositional_tableau_completeness/handoffs/11_phase0-spike-decisions.md`
- `specs/317_propositional_tableau_completeness/handoffs/11_phase2-blocker-findings.md`
- `specs/317_propositional_tableau_completeness/reports/11_team-research.md` and teammate
  findings (a-d)
