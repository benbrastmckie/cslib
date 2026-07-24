# Implementation Summary: Phase 7 Recovered and Landed (Interim, Task Continues)

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `plans/02_keyed-s4-driver-restructured.md`
- **Status**: `[IMPLEMENTING]` (interim summary; Phases 8-11 remain)
- **Date**: 2026-07-24
- **Session**: sess_1784905751_756cda_535

## What Was Done This Dispatch

This was a session-limit-kill recovery dispatch. A prior (hard-mode) agent had been killed
mid-Phase-7, leaving ~376 uncommitted lines in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
that did not build (the repo-wide red spot at dispatch start). This dispatch:

1. Inspected the uncommitted diff (`modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`'s
   full case-split skeleton, essentially complete in design).
2. Diagnosed and fixed three distinct build-blocking bugs (none in previously-landed code; see
   the plan file's Phase 7 "Completed" note and
   `handoffs/04_phase8-11-assessment-and-continuation.md` for full technical detail):
   - A redundant `clear hnbd` after an already-consuming `obtain`.
   - A helper lemma (`keysMatch_eq_keys_of_not_mint`) whose stated hypothesis triggered Lean's
     equation-compiler auto-revert, making it permanently non-defeq to its call sites. Deleted as
     dead code; replaced at all 4 call sites with the SAME `rcases`+`dsimp` idiom already proven
     to work elsewhere in this file.
   - Two `hinveq` `have`s stated with bare `sf` instead of the eta-equal exposed structure
     literal, blocking a later `rw [hff] at hinveq` step.
3. Ran the full CSLib CI pipeline and confirmed green.
4. Committed Phase 7 (`1ce152b6`).
5. Wrote the required Phase 9/10/11 viability assessment (re-confirming the prior dispatch's own
   "Phases 7-8 do not depend on 9" note is still accurate) and a Phase 8 technical map, both in
   `handoffs/04_phase8-11-assessment-and-continuation.md`.

Commit: `1ce152b6` (task 535 phase 7), touching
`Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive, +381/-6 net including the deleted dead
lemma) and the plan file's Phase 7 section (now `[COMPLETED]`).

**New declaration** (`lean_verify`-clean: `propext`/`Classical.choice`/`Quot.sound` only, zero
`sorry`, zero new lint warnings):

- `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` — every `modalStepBranchS4Keyed` step
  preserves the Phase 6 `S4KeyedHintikkaInv` bundle, given the ambient `S4LoopInv` (consumed for
  `keyLowerBd`'s blocked-witness argument via the already-landed
  `modalStepBranchS4Keyed_blocked_witness_mem`).

## Plan Deviations

- **Task 7.2** *(altered)*: the theorem consumes the ambient `S4LoopInv φ₀ b e acc keys`
  hypothesis directly (for `keyLowerBd`), rather than re-deriving `keysWorldsKnown`/
  `worldsContiguousS4` inline as a separate triple — those are already carried unchanged inside
  the frozen `S4LoopInv` structure.
- **Task 7.3** *(altered)*: no separate `_none_saturated` analogue lemma was needed. The
  three-way mint-unblocked/mint-blocked/non-mint case split, combined with `findSome?_eq_some`'s
  `some`-witness and `split_ifs at hsf with hexp` (which already rules out the saturated case at
  selection time), covers every reachable branch without a dedicated lemma.

## What Remains

Phase 8 (top-loop induction, `modalExpandBranchesS4Keyed_hintikka`) was assessed but NOT
attempted this dispatch — after Phase 7's recovery work, remaining budget did not leave enough
runway to safely attempt Phase 8's estimated 250-400 lines of genuinely new induction without
risking another incomplete hand-off. A full technical map (template, substitution table,
line-by-line correspondences to the generic `modalExpandBranchesHintikka`) is recorded in
`handoffs/04_phase8-11-assessment-and-continuation.md`.

Phase 9 remains `[BLOCKED]` (S4's non-symmetric frame lacks the reachability invariant its
soundness argument needs — confirmed again this dispatch, unchanged from commit `a2d9d836`).
Phases 10-11 are transitively blocked via Phase 9 and should not be attempted until Phase 9 is
either resolved (likely requiring a frozen-code change to `blockingWorldS4Keyed`, out of this
plan's stated scope) or the task is formally re-planned around the obstruction. Phase 8 is
independent of Phase 9 and remains fully worth pursuing regardless of that resolution's timeline.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: green, 847 jobs, zero new warnings.
- `lake exe checkInitImports`: clean.
- `lake lint`: no new warnings on this file.
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no new findings.
- `lake exe mk_all --module`: no update necessary.
- `grep -n "\bsorry\b"`: one hit, a pre-existing docstring prose mention (not code).
- `lean_verify` on the new theorem: `propext`/`Classical.choice`/`Quot.sound` only.
- Regression: Phase 1-6 declarations unchanged (confirmed via reading the diff before editing;
  all fixes were localized to the killed agent's own uncommitted Phase 7 material).

## Next Steps

See `handoffs/04_phase8-11-assessment-and-continuation.md` for the full Phase 8 technical map and
the required Phase 9-11 viability assessment. Recommended: dispatch Phase 8 fresh (ideally
`--hard` for phase-sizing discipline, given Phase 7's own experience that even a mostly-complete
skeleton needed non-trivial debugging before it built).
