# Implementation Summary: Phase 2 -- Decision Gate A, `modalTruthLemmaS4Sub`

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Status**: [IN PROGRESS] (task-level; Phase 2 of 12 is [COMPLETED])
- **Started**: 2026-07-26T19:06:49Z
- **Completed**: 2026-07-26T20:05:00Z
- **Effort**: ~1 hour
- **Dependencies**: Phase 1 (`modalHintikkaSetS4Sub`, `accWithReds`, `Reds`)
- **Artifacts**: plans/04_subtractive-blocking-red-channel.md (Phase 2 section, plus new
  `#### Phase 2 Verdict` subsection)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, this file

## Overview

Phase 2 (Decision Gate A) proves, standalone and with no driver dependency, that Phase 1's
bifurcated `modalHintikkaSetS4Sub` predicate feeds a truth lemma over
`ReflTransGen (accWithReds acc red)` -- report 04 §9's mandatory viability condition for route
(3). This is one of the plan's two front-loaded decision gates; a negative verdict here would
have killed route (3) outright (honest fallback: route (1), not route (2')). The verdict is
**PASS**.

## What Changed

`Cslib/Logics/Modal/Tableau/LoopChecking.lean`:

- Added `def modalS4Saturated` -- the bare saturation conjunct (conjunct 2), named so it can be
  shared verbatim by `modalHintikkaSetS4` and `modalHintikkaSetS4Sub`.
- Added `theorem modalHintikkaSetS4_saturated` / `theorem modalHintikkaSetS4Sub_saturated` --
  one-line `.2.1` projection bridges from either full predicate to `modalS4Saturated`.
- Re-stated the hypothesis of the six bridges `hintikkaS4_box_pos_self`/`_step`/`_reflTransGen`,
  `hintikkaS4_dia_neg_self`/`_step`/`_reflTransGen` from `modalHintikkaSetS4 φ₀ b acc` to
  `modalS4Saturated φ₀ b acc` (strictly weaker), removing the now-unneeded
  `obtain ⟨_, hrule, _⟩ := hH` destructuring step in each proof body.
- Added `lemma reflTransGen_accWithReds_first_red` -- the path-decomposition lemma: a
  `ReflTransGen (accWithReds acc red)`-path either stays entirely inside `acc.hasEdge`, or
  splits at its first `red`-hop into an `acc`-only prefix, a recorded redirect, and a residual
  union-relation suffix. Proved by `Relation.ReflTransGen.head_induction_on` plus
  `hasEdge_accWithReds_iff`.
- Added `lemma hintikkaS4_box_pos_reflTransGen_boxed` / `lemma
  hintikkaS4_dia_neg_reflTransGen_boxed` -- new box/diamond-*preserving* path bridges (see Plan
  Deviations).

`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`:

- Adjusted `modalTruthLemmaS4`'s two `hintikkaS4_{box_pos,dia_neg}_reflTransGen` call sites to
  project `hH` via `modalHintikkaSetS4_saturated φ₀ b acc hH`, accommodating the weakened bridge
  signatures with zero change to `modalTruthLemmaS4`'s own statement or any other case.
- Added `lemma modalTruthLemmaS4Sub` -- the full complexity induction over
  `extractModelS4 b (accWithReds acc red)`, transcribing `modalTruthLemmaS4` verbatim for every
  case except box-positive/diamond-negative, which case-split on
  `reflTransGen_accWithReds_first_red` and close via the boxed bridges plus conjuncts 5/6.
- Added `theorem modalOpenBranchS4Sub_countermodel` -- verbatim ~9-line transcription of
  `modalOpenBranchS4_countermodel` at `accWithReds acc red`.

`specs/553_.../plans/04_subtractive-blocking-red-channel.md`:

- Checked off all five Phase 2 task-list bullets, moved the phase heading to `[COMPLETED]`, and
  recorded the full verdict (declarations landed, verification results, the full-project-build
  caveat) under a new `#### Phase 2 Verdict` subsection.

## Decisions

- **`modalS4Saturated` indirection instead of editing `modalHintikkaSetS4`'s body** -- see Plan
  Deviations. Named the shared conjunct rather than either (a) editing the landed
  `modalHintikkaSetS4` definition in place (risking its `rfl`-based bridge
  `modalHintikkaSetS4_eq` and any defeq-sensitive downstream use), or (b) duplicating the
  saturation Prop inline in each of the six bridge signatures (poor DRY, and it is already
  duplicated once between `modalHintikkaSetS4` and `modalHintikkaSetS4Sub`).
- **Two new "boxed" path bridges**, not anticipated by the plan's literal task text -- see Plan
  Deviations. Required because `modalHintikkaSetS4Sub`'s forward-cone conjuncts 5/6
  (`redBoxForwardCone`/`redDiaForwardCone`) demand the *wrapped* antecedent
  `T(□χ)@src ∈ b`/`F(◇χ)@src ∈ b` at the `red`-hop's source, but the existing
  `hintikkaS4_box_pos_reflTransGen`/`hintikkaS4_dia_neg_reflTransGen` bridges *unwrap* the
  formula at the path's endpoint (their entire purpose in the `acc`-only case). The fix mirrors
  those bridges' own induction, with the `refl` case returning the wrapped hypothesis unchanged
  instead of invoking `hintikkaS4_box_pos_self`/`hintikkaS4_dia_neg_self`.
- **Full-project `lake build` caveat, not treated as a phase failure**: the only build error in
  the whole project is in `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`,
  explicitly declared out-of-scope by this plan's Overview and currently under active repair by
  a concurrent session (task 554, phase 14). Both files this phase touched build clean in
  isolation (`lake build Cslib.Logics.Modal.Tableau.{LoopChecking,FrameCompleteness}`), and a
  tree-wide grep confirms no caller outside those two files references the six weakened bridges.
  `lake exe checkInitImports` and `lake shake` require a fully up-to-date project build and could
  not be run to completion this dispatch as a consequence; `lake exe lint-style`, which does not
  have that dependency, was run directly on both touched files and is clean.

## Impacts

- **Gate A does not kill route (3).** Phase 3 (Gate B, establishment: can the forward-cone
  clauses be *proved* from branch-level facts at a blocked step?) remains independently gated
  and is now unblocked for a separate wave-2 dispatch, per the plan's "Gates A and B are
  independent" design.
- Sorry count in `Cslib/Logics/Modal/Tableau/` unchanged at exactly 1
  (`FrameSoundness.lean:1244`, untouched, per the user's retained-marker decision).
- No landed declaration was edited in place except the sanctioned six-bridge hypothesis
  weakening (strictly weaker, confirmed safe by scoped rebuild) and the two accommodating
  caller-side projections in `modalTruthLemmaS4`.
- No phase after Phase 2 was scaffolded around this positive outcome, per the plan's risk
  mitigation.

## Follow-ups

- Dispatch Phase 3 (Gate B) as a separate, standalone dispatch (do not compress into this one,
  per the plan's postmortem "Do NOT compress Phases 2 and 3" rule).
- Once the concurrent Nested/Soundness fix lands, re-run `lake exe checkInitImports` and
  `lake shake` to complete this phase's CI-pipeline verification retroactively.

## Plan Deviations

- **`modalS4Saturated` named indirection** instead of literally editing `modalHintikkaSetS4`'s
  body -- see Decisions above. The six bridges' hypotheses were weakened exactly as specified;
  the deviation is in *how* the weaker Prop is expressed (a new named `def` plus two projection
  bridges, rather than an in-place edit to the existing predicate's structure), which is
  strictly safer for the landed `rfl`-based `modalHintikkaSetS4_eq` bridge.
- **Two new box/diamond-preserving path bridges**
  (`hintikkaS4_box_pos_reflTransGen_boxed`/`hintikkaS4_dia_neg_reflTransGen_boxed`) -- not named
  in the plan's task list, but required by the mathematics: conjuncts 5/6 need the wrapped
  formula at the `red`-hop's source, and no existing lemma supplied that. Added as straightforward
  mirrors of the existing (unwrapping) bridges' own induction structure -- no new proof
  technique, no change to any statement's semantic content.
- All five Phase 2 task-list bullets were otherwise completed exactly as specified: the six
  bridges were weakened, the path-decomposition lemma matches the plan's stated shape verbatim,
  `modalTruthLemmaS4Sub` and `modalOpenBranchS4Sub_countermodel` match their specified
  signatures verbatim, and the forbidden wrapped-at-target form was never used to close either
  case.

## References

- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/04_subtractive-blocking-red-channel.md`
  (Phase 2 section; `#### Phase 2 Verdict`)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`modalS4Saturated`, the six weakened bridges,
  `reflTransGen_accWithReds_first_red`, the two new boxed path bridges)
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (`modalTruthLemmaS4Sub`,
  `modalOpenBranchS4Sub_countermodel`)
- `specs/553_s4_loop_guard_soundness_reachability_restriction/.orchestrator-handoff.json`
