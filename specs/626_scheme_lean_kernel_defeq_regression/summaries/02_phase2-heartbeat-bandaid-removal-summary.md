# Phase 2 Summary: Remove the LoopChecking Heartbeat Band-Aid

- **Task**: 626
- **Phase**: 2 of 4
- **Session**: sess_1786462543_b0741b
- **Status**: COMPLETED
- **Branch**: `task-619-phase8-wip` (live worktree at scratchpad `wt/`)
- **Commit**: `c331c9e5` — `task 626 phase 2: remove LoopChecking maxHeartbeats band-aid`

## What Was Done

The `set_option maxHeartbeats 1000000 in` block and its 4-line comment in
`Cslib/Logics/Modal/Tableau/LoopChecking.lean` (branch lines 1209-1213, immediately above the
keyed top-loop Hintikka lemma) were deleted and the deletion committed. The comment was deleted,
not rewritten: it misattributed the elaboration cost to a typeclass-projection layer that
`isDefEq` must unfold, while the true cause (report 02) was the scoped-notation precedence
collision fixed in phase 1 (commit `128c42ee`).

Per phase 1's report, the deletion already existed as an uncommitted working-tree change in the
worktree; this phase verified it byte-for-byte and committed it rather than recreating it
(anti-analysis contract: verify-then-commit path, no contingency recipe needed).

## Verification (Done-When Gates)

1. **Diff exactness**: `git diff` showed exactly 5 deletions, hunk `@@ -1206,11 +1206,6 @@` —
   the `set_option` line plus the 4 comment lines, nothing added.
2. **No heartbeat override remains**: `grep -c maxHeartbeats` on the file returns 0. No
   override was re-added anywhere.
3. **Green at default budget**: `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeded
   (0.87s — trace replay from the phase-1 sentinel build of identical content). Because a
   replay alone is weak evidence, a fresh full elaboration was forced via
   `lake env lean Cslib/Logics/Modal/Tableau/LoopChecking.lean` at default options: green in
   6.2s wall / 13.6s CPU, matching report 02 E12's 13.5s measurement. Well under the 10-minute
   regression-signal threshold.
4. **Commit + clean tree**: commit `c331c9e5` contains only `LoopChecking.lean` (5 deletions);
   `git status` clean afterward.
5. **Sorry inventory**: empty. The single `grep` hit for `sorry` in the module is pre-existing
   prose ("sorry/axiom counts" in the census documentation at line 120), not a proof hole.

## Plan Deviations

None. The phase executed exactly as planned via the primary (verify-then-commit) path; the
contingency recipe for a missing deletion was not needed. One verification step was added
beyond the plan's letter (the `lake env lean` fresh elaboration) because the scoped `lake build`
completed as a cache replay, which by itself would not have proven elaboration at the default
budget.

## Scope Compliance

- Only `Cslib/Logics/Modal/Tableau/LoopChecking.lean` touched in the worktree (H7 territory).
- No Scheme.lean or Operators.lean edits; no rebase/merge/cherry-pick/push; no destructive git.
- Phases 3-4 untouched (single-phase dispatch).
- Full-library gate deliberately deferred to phase 4 per the plan (this phase's verification
  tier is `local`).
