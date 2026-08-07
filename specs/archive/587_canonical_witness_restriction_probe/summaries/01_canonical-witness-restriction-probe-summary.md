# Implementation Summary: canonical_witness_restriction_probe

**Task**: 587
**Status**: COMPLETED
**Started**: 2026-08-05
**Completed**: 2026-08-05
**Artifacts**: `specs/587_canonical_witness_restriction_probe/plans/01_canonical-witness-restriction-probe.md`; `specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`
**Standards**: `.claude/rules/artifact-formats.md`; `.claude/rules/lean4.md`; CSLib CONTRIBUTING.md

## Overview

A machine-checked micro-probe of the canonical-witness carrier restriction for the parent task's
redirect-preservation agreement lemma, plus a priced verdict for a follow-on plan. No large Lean
construction was scaffolded ahead of the probe verdict, per the plan's front-loaded kill-gate
discipline.

### Outcome

**CONDITIONAL GO.** All 5 plan phases completed (Phase 4 excluded by its own gate outcome, closed
`[COMPLETED WITH EXCLUSIONS]`). Full verdict, method, and pricing are in
`specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`.

## What Changed

### What Happened, Phase by Phase

- **Phase 1** (Restriction A, `W := WorldIndex`, `f := id`): machine-checked stuck at both
  `box.mp.inr` and `diamond.mpr` -- the escape to non-known-label points persists even after
  fixing the carrier, exactly as this plan's own "Planning-run correction" section anticipated.
  Probe code appended, goal states captured, reverted (did not close sorry-free).
- **Phase 2** (Restriction B1, carrier restricted to the known-branch-labels subtype): both cases
  close sorry-free, but only modulo two assumed hypothesis groups -- Decision Gate B's own
  conclusion (out of this task's scope) and a genuine truth-lemma direction (the central finding:
  NOT free from an arbitrary pinned witness, requires a canonical/term model). The lemma
  `canonicalWitnessRestrictionProbe_agreementConditional`
  (`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:5422`) was retained, sorry-free, axioms
  `propext`/`Classical.choice`/`Quot.sound` only.
- **Phase 3** (pricing): field-by-field classification of `branchSatisfiablePinnedIn`'s four
  conjuncts -- three collapse to near-free consequences of the canonical choice, one (the branch
  conjunct) re-shapes into the truth lemma. `branchSatisfiablePinnedIn_redirect_mechanical`'s
  proof survives verbatim (no re-derivation needed for a v6 plan). A v6 plan is priced at 5-7
  phases / 13.5-17.5 hours, decomposed by workstream, with a recommended front-loaded Gate 0 to
  de-risk the truth lemma's box-positive case.
- **Phase 4**: excluded -- entry condition (a NO-GO gate outcome) was never satisfied.
- **Phase 5**: verdict report written; task 553's blocker record
  (`specs/553_.../reports/05_gate-a-canonical-witness-blocker-analysis.md`) updated with a
  cross-reference and next-step pointer (`/plan 553` to produce a v6 plan against this pricing).

### Files Touched

- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` -- one retained lemma
  (`canonicalWitnessRestrictionProbe_agreementConditional`) appended below the existing
  `branchSatisfiablePinnedIn_redirect_mechanical`; all other content byte-identical to the
  pre-task state (confirmed by `git diff` showing no hunk above the appended section). The
  standing `sorry` at `:1251` is untouched.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` -- read-only reference; zero diff.
- `specs/587_canonical_witness_restriction_probe/plans/01_canonical-witness-restriction-probe.md`
  -- phase status markers and per-phase verdict sections.
- `specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`
  -- the task's deliverable (new file).
- `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/05_gate-a-canonical-witness-blocker-analysis.md`
  -- cross-reference addendum (new section, no existing content altered).

## Decisions

### Plan Deviations

None. All phases executed per the plan's own task lists and kill-criteria tables; Phase 4's
exclusion was the plan's own pre-declared outcome, not a deviation.

## Impacts

### Verification

- Sorry census over `Cslib/Logics/Modal/Tableau/` (authoritative command): exactly 1 (the standing
  `:1251` sorry only) -- confirmed at every phase boundary.
- `accPinnedBy`, `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical`:
  byte-identical to pre-task state (re-located by grep at `:5323`, `:5332`, `:5356`).
- `lake build` (full project): clean, `Cslib` and `CslibTests` both build.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint`: pre-existing repo-wide warnings unrelated to this task; zero warnings reference the
  new declaration or its line range.
- `lake shake --add-public --keep-implied --keep-prefix`: no import change suggested for
  `FrameSoundness.lean`.
- `lake exe mk_all --module`: no update necessary.
- `lake test`: full `CslibTests/` suite passes.
- `lean_verify` on `canonicalWitnessRestrictionProbe_agreementConditional`: axioms `propext`,
  `Classical.choice`, `Quot.sound` only.
- New sorries introduced by this task: 0. New axioms introduced: 0 (repo-wide axiom count
  unchanged at 26). Vacuous definitions introduced: 0.

## Follow-ups

### Next Steps

Resume task 553 with `/plan 553` to produce a v6 plan against this task's Phase 3 pricing
(5-7 phases / 13.5-17.5 hours), then `/implement 553`.

## References

- Verdict report: `specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`
- Plan: `specs/587_canonical_witness_restriction_probe/plans/01_canonical-witness-restriction-probe.md`
- Parent blocker record: `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/05_gate-a-canonical-witness-blocker-analysis.md`
- Prior verdict this task prices: `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/05_pinned-witness-truth-lemma.md` (`#### Phase 1 Verdict`)
