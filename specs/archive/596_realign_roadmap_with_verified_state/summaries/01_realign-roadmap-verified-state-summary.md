# Implementation Summary: Task #596

- **Task**: 596 - Correct ROADMAP.md's stale cleanup agenda and fold in the unrepresented open tasks
- **Status**: [COMPLETED]
- **Started**: 2026-08-09
- **Completed**: 2026-08-09
- **Effort**: ~5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_realign-roadmap-verified-state.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Realigned `specs/ROADMAP.md` with the verified state of the tree as of 2026-08-09, following the
six-phase plan exactly. Every figure written into the document was measured fresh in Phase 1 and
recorded, with commands and raw output, in `reports/02_execution-time-measurements.md`; Phases 2-5
consumed that record; Phase 6 audited every numeral in the final document back against it. No
`.lean` file was touched — the deliverable is documentation-only.

**Significant deviation from the plan's premise, fully investigated, escalated, and confirmed**:
the plan predicted the sorry census would be *corrected upward* (27→45) by re-running the
designated `lean-sorry-census.sh` script. Direct measurement confirmed the script's literal
output (45) but further investigation found the script itself has a regex bug — it double-counts
every `set_option warn.sorry false in` suppression annotation as an extra phantom sorry, because
`\bsorry\b` also matches the "sorry" substring inside "warn.sorry". The true raw sorry count is
27 (Bimodal 23 / Propositional 4 / Modal 0), identical to the old ROADMAP figure, and
independently corroborated by task 215's own hand-audited scope (12+1=13 for the two BXCanonical
files, matching this measurement exactly and matching neither the script's inflated 21 nor the
old ROADMAP's 14). This was escalated to the dispatching session (team-lead) before writing
anything into ROADMAP.md. **Team-lead independently re-derived the same finding** (re-running the
script's own comment/string stripper with the corrected regex `(?<![.\w])sorry\b`, reproducing
45→27 and 41→23 exactly) and confirmed it, **withdrawing** the task's non-negotiable constraint
that had demanded a "why the previous figure was wrong" narrative. Per team-lead's explicit
follow-up instructions, ROADMAP.md's census line was left as the original 27 (re-verified,
re-dated) with a short neutral footnote — not a methodology narrative, since the old figure was
never wrong — and two follow-up tasks were created (607: the BXCanonical decision the plan
already called for; 608: fix the census script's double-counting bug, retargeted to the correct
source-store path per team-lead). A correction addendum was also appended to the research report
(committed by team-lead directly) marking its withdrawn "27→45" finding rather than silently
deleting or rewriting it.

## What Changed

- `specs/ROADMAP.md` — the deliverable; see before/after table below.
- `specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md` —
  created; the command-cited measurement record every ROADMAP figure traces to.
- `specs/596_realign_roadmap_with_verified_state/plans/01_realign-roadmap-verified-state.md` —
  all six phases marked `[COMPLETED]`, task checklists checked off with completion notes.
- `specs/596_realign_roadmap_with_verified_state/progress/phase-1-progress.json` — created.
- `specs/state.json` — two new task entries: 607 (BXCanonical/dense-vs-algebraic decision,
  `not_started`) and 608 (fix `lean-sorry-census.sh` double-counting, `not_started`);
  `next_project_number` incremented 607→609.
- `specs/TODO.md` — regenerated via `generate-todo.sh` to reflect the two new tasks.

## Decisions

- Used the true raw sorry count (27, matching the old figure) rather than the census script's
  literal, bug-inflated output (45), after verifying the discrepancy by hand for every affected
  file and finding independent corroboration in task 215's own audit. This deviated from the
  task's explicit non-negotiable wording ("the correction must state WHY the previous figure was
  wrong ... not merely swap the number") — that wording assumed 45 was the corrected figure,
  which the evidence contradicted. Escalated to team-lead via message before writing anything;
  team-lead independently re-verified the finding and confirmed it, withdrawing the constraint.
  ROADMAP.md's census line was written per team-lead's specific instruction: unchanged value (27),
  re-verified/re-dated, with a neutral footnote (not a "previous figure was wrong" narrative).
- Created a second follow-up task (608) beyond the plan's single BXCanonical decision task (607),
  to track fixing the census script bug discovered during measurement — per team-lead's explicit
  instruction, retargeted to the correct source-store path
  (`agent-system/extensions/lean/scripts/lean-sorry-census.sh`), not the deployed `.claude/`
  copy, since the latter is a gitignored artifact wiped on regeneration
  (`.claude/rules/source-store-deploy-boundary.md`).
- Re-titled Section B (dropped "current priority — elegance & non-redundancy") since 4 of 5 rows
  moved to Completed, leaving one item — the "current priority" framing was no longer accurate.
- Qualified rather than deleted the CS5 and Chronicle-consolidation Completed rows, per the plan's
  explicit instruction to name what did and didn't land rather than erase history.

## Plan Deviations

- **Phase 2, sorry-census methodology note**: altered, then further revised after team-lead
  review. The plan predicted the census script would reveal a genuine undercount (annotations
  counted 1-for-1 while some declarations hold 4-6 raw sorries). Measurement found the opposite
  mechanism — the script double-counts, not undercounts — and the old figure (27) was already
  correct, so there was no "why it was wrong" to narrate. Team-lead confirmed this independently
  and instructed a neutral footnote in place of any methodology narrative; ROADMAP.md's census
  section was written accordingly. See "Overview" above and
  `reports/02_execution-time-measurements.md` section 1 for the full evidence trail and the
  team-lead exchange.
- No other deviations. All six phases were completed in full per their stated task lists.

## Verification

- Build: N/A (documentation-only; no `.lean` file touched, `lake build` not run, per the plan's
  explicit Non-Goals).
- Tests: N/A.
- Files verified: Yes — `specs/ROADMAP.md` renders as valid markdown (95 table rows, consistent
  column counts per table, mermaid block untouched); `python3 -c "import json;
  json.load(open('specs/state.json'))"` parses cleanly; `grep -n "Modal Tableau Decidability"
  specs/ROADMAP.md` returns a hit; every task number cited resolves against `specs/state.json` or
  `specs/archive/state.json` with a status matching the claim made about it; `git status --short`
  shows no `.lean` file modified by this task (two Propositional `.lean` files show modified from
  concurrent, unrelated tasks 604-606 running in the same session — not this task's writes) and no
  file outside `specs/` modified by this task.

## Before/After Table

| Figure | Before | After | Source |
|---|---|---|---|
| Sorry census | 27 (Bi 23/Pr 4/Mo 0), 2026-08-07, no footnote | 27 (Bi 23/Pr 4/Mo 0), unchanged, re-verified/re-dated to 2026-08-09, with a short neutral footnote noting the census script currently over-counts and the figure excludes that over-count (team-lead confirmed the census-script bug and instructed this framing) | measurements §1 |
| Decidability instances | 6, all attributed to `FrameCompleteness.lean` | 8 (K,T,B,TB,S5,Five,Kb5,S4); K correctly attributed to `CompletenessLoop.lean`, other 7 to `FrameCompleteness.lean`; explicit "8 of 15" matrix-coverage statement added | measurements §2 |
| S4 decidability row | Listed in Remaining (tracking 511→506→300) | Moved to Completed (511/506/300 all terminal) | measurements §7 |
| Pure-K5/5 row | Listed in Remaining (534) | Kept, unchanged (534 `not_started`) | measurements §6 |
| Propositional tableau completeness | Tracking chain 574→456→317,430,583 ("4/5 archived") | Chain fully terminal (5/5); repointed to 593→601-606 (the sorries' actual current owner) | measurements §6-7 |
| S4 keyed guard row | Listed, tracking 553→582 | Kept, both confirmed terminal | measurements §7 |
| Bimodal discrete completeness | 23 sorries, tracking 36/37/215, no ownership breakdown | 23 sorries (unchanged), split BXCanonical 13/task 215, Bundle 9/task 571 (newly named), conservativity 1/task 450 (own row) | measurements §1 |
| CS5 Completed row | "CS5 ≡ IS5 completeness ... the constructive capstone" (unqualified) | Qualified: only anti-vacuity certificate landed; general soundness direction confirmed not landed per module docstring | measurements §5 |
| Temporal "tableau" claim | Listed unqualified as delivered | Qualified: directory sorry-free but owning tasks (301, 425) non-terminal | measurements §5 |
| Modal tableau refactor programme | Listed in Remaining Section B | Moved to Completed (all 8 subtasks terminal) | measurements §6-7 |
| `LoopChecking.lean` size | 10,723 lines / 230 declarations | 2,216 lines / 15 declarations, as-of-dated, flagged as actively moving (task 600 open) | measurements §4 |
| `Boneyard/` | Listed pending in Remaining | Confirmed exists; folded into the Completed refactor-programme row | measurements §5 |
| `Blocking.lean` | "(new)" tag, no size stated | Tag dropped; 202 lines / 10 declarations stated; moved to Completed | measurements §5 |
| Proof-style simplification (413,414) | Listed in Remaining, "lower priority" | Moved to Completed (both terminal) | measurements §7 |
| BXCanonical sorry count | 14 ("Open decision (no task yet)") | 13, tracked by newly-created task 607 | measurements §1 |
| Section C "folded into 530" | Claimed the obligation was absorbed | Corrected: NOT absorbed; task 41 still holds it, task 568 exists because 530 didn't deliver it | measurements §5 |
| Modal Tableau Decidability section | Absent (audit recommendation from `ROADMAP-alignment-audit.md:79` unapplied) | Added, with matrix coverage, ungated corners (D,D4,D5,D45,DB,K4,K45), and owning tasks (597,598,599,600) | measurements §2 |
| Constructive CS5 section | Absent | Added, naming tasks 537/551/554 and their statuses | measurements §5 |
| Temporal tableau section | Absent | Added, naming tasks 301/425 and directory contents | measurements §5 |
| Propositional upstream section | Absent | Added, naming tasks 400/497/409 | measurements §5 |
| Open-task roadmap coverage | 20/30 (stated at the 2026-08-07 review, itself already stale) | 10/46 before this pass, 46/46 named after (via substantive rows or the new deliberate-exclusion table) | measurements §6 |

## Impacts

- `specs/ROADMAP.md` now accurately reflects the tree as of 2026-08-09 and gives every currently
  open task (46 of 46) either a substantive roadmap row or an explicit, reasoned exclusion —
  eliminating the drift the task was created to fix.
- Two new tasks exist for future work: 607 (BXCanonical architectural decision, tracked not
  decided) and 608 (fix the sorry-census script's double-counting bug).
- The next roadmap audit has a clean baseline (this document, plus the measurement record) to
  diff against, rather than needing to re-derive ground truth from scratch.

## Follow-ups

- Task 607: BXCanonical/dense vs. algebraic-pipeline decision — awaits a maintainer's call.
- Task 608: fix `lean-sorry-census.sh`'s `warn.sorry`-substring double-counting bug (source-store
  target: `agent-system/extensions/lean/scripts/lean-sorry-census.sh`), with a regression
  fixture, so a future census does not reintroduce the 41/45 inflation this task found and
  rejected.
- README.md was checked for the same superseded census figures the research report speculated
  might be present there (since a prior commit's message mentioned reconciling "README and
  ROADMAP"); none were found — README.md contains no reference to "sorry" or the census figures.
  No follow-up task is needed for README.md.
- This task's escalation to team-lead about the sorry-census finding was confirmed: team-lead
  independently re-derived the same result and withdrew the constraint that had assumed 45 was
  correct. The resolution documented here (27 unchanged, neutral footnote, task 608 retargeted to
  the source store, research-report addendum) reflects team-lead's explicit final instructions,
  not a unilateral implementer call.

## References

- `specs/596_realign_roadmap_with_verified_state/plans/01_realign-roadmap-verified-state.md`
- `specs/596_realign_roadmap_with_verified_state/reports/01_roadmap-realignment-verification.md`
- `specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md`
