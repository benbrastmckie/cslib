# Task 626 Phase 1 Summary: Commit the Precedence Fix on the wip Branch

## What Was Done

Phase 1 of `plans/01_precedence-collision-fix.md` — commit-and-verify of the already-verified
2-line precedence fix in the live worktree.

- **Worktree verified live**: `/tmp/claude-1000/-home-benjamin-Projects-cslib/622a4407-4dc9-4cb5-b6f8-f7c190e5bbfe/scratchpad/wt`,
  branch `task-619-phase8-wip` @ `1e88ad3e`, warm `.lake`. Contingency recipe not needed.
- **Diff verified content-anchored**: `Cslib/Foundations/Logic/Operators.lean` carried exactly
  `scoped infixr:31 " ∨ " => HasOr.or` (was `:30`, line 38) and
  `scoped infixr:26 " → " => HasImp.imp` (was `:25`, line 45) — the report 02 §5 recipe,
  breaking the exact token+precedence+associativity collision with core notation that caused
  Θ(2^n) parser choice-node backtracking.
- **Sentinel build green**: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`
  exited 0 in ~1s real (933 jobs, fully warm cache built from this exact fixed content) — far
  inside the 10-minute regression bound; the non-termination is gone.
- **Committed**: `128c42ee` on `task-619-phase8-wip`, staging ONLY `Operators.lean`
  (1 file, 2 insertions, 2 deletions). Message:
  `task 626 phase 1: offset scoped ∨/→ precedences to break core-notation collision` + Session line.
- **Post-commit state**: `Operators.lean` clean; `LoopChecking.lean` still dirty — expected,
  it is phase 2 territory and stays uncommitted.

## Done-When Criteria (all met)

| Criterion | Result |
|-----------|--------|
| Sentinel build exits 0 in bounded time | Yes — ~1s real, exit 0 |
| `git log -1` shows commit with exactly the 2-line change | Yes — `128c42ee`, 2 insertions / 2 deletions, 1 file |
| `git status` shows `Operators.lean` clean (LoopChecking.lean dirty OK) | Yes |

## Plan Deviations

None. The worktree was live as the dispatch asserted, so the contingency recipe was not
exercised. The sentinel build completed in ~1s rather than the estimated ~29s because the warm
`.lake` cache had been built from exactly the fixed file content during prior verification;
lake's up-to-date hash check against the dirty working tree constitutes proof the fixed content
builds green.

## Sorry Inventory

Empty. No Lean source was authored in this phase (2-digit edit pre-existed and was committed);
no `sorry`, no vacuous definitions, no new axioms.

## Scope Notes

- No `Scheme.lean` edits (prohibited).
- No `maxHeartbeats` added anywhere (prohibited; removal of the existing band-aid is phase 2).
- No rebase/merge/cherry-pick/push (merge-to-main is deliberately deferred to task 619 phase 8).
- Full CI pipeline (lint, shake, mk_all, test) deliberately deferred to the plan's later
  verification phase; phase 1's declared Verification Tier is `local` (sentinel build only).

## Next

Phase 2: remove the LoopChecking `maxHeartbeats 1000000` band-aid and its misattributing
comment, rebuild at default budget, commit only `LoopChecking.lean`.
