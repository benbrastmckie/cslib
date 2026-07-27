# Research Report: Task #578

**Task**: 578 - Untrack and gitignore the ephemeral orchestrator runtime files currently committed in this repository
**Started**: 2026-07-27T17:00:00Z
**Completed**: 2026-07-27T17:18:46Z
**Effort**: small (mechanical: one `.gitignore` edit + a batch of `git rm --cached` invocations)
**Dependencies**: None
**Sources/Inputs**:
- `.claude/context/standards/orchestrator-runtime-files.md` (policy source of truth)
- `.claude/scripts/check-runtime-file-tracking.sh` (executed directly, output captured verbatim)
- Root `/.gitignore` (read directly)
- `git ls-files`, `git status --porcelain`, `git check-ignore -v` (executed directly)
**Artifacts**: this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Ran `bash .claude/scripts/check-runtime-file-tracking.sh` directly (not inferred). Check A and
  Check B both FAIL; Check C already PASSES. This confirms the task's problem statement exactly,
  with one small correction to the tallies (34 tracked ephemeral files observed, not 35 — see
  "Corrected Tallies" below; the category breakdown differs slightly from the task description
  but the remediation is identical).
- Root `/.gitignore` currently has **zero** orchestrator/runtime lines (19 lines total, all
  Lean/docs/`.DS_Store`/`.claude/settings.local.json` related). The verbatim ephemeral-class block
  from the standard's "Consumer Repo Setup" section is captured below and is ready to append
  as-is.
- No ordering hazard exists between editing `.gitignore` and running `git rm --cached`: this
  orchestration run's own `specs/578_.../` directory (including its own live
  `.orchestrator-loop-guard` and `.lock/holder.json`) is entirely **untracked** (`git ls-files`
  returns nothing for it) and pre-fix `git check-ignore` on its loop-guard exits 1 (not yet
  ignored). Editing `.gitignore` first is safe and is the standard's own documented order
  (Consumer Repo Setup precedes Untracking Already-Committed Ephemeral Files in the source doc).
  This run's own ephemeral files will become newly ignored the moment `.gitignore` is written,
  which is the intended effect, not a hazard.
- Recommended implementation order: (1) append the verbatim block to root `.gitignore`, (2) run
  the 34 `git rm --cached` / `git rm -r --cached` commands the script itself prints, staging only
  `.gitignore` plus those 34 removals — never a wholesale `git add -A` or `git add specs/578_.../`
  — (3) re-run the check script to confirm all three checks pass.

## Context & Scope

Task 578 asks for a mechanical remediation already fully specified by
`.claude/context/standards/orchestrator-runtime-files.md`: add the documented ephemeral-class
`.gitignore` block to this repo's root, and `git rm --cached` every already-tracked ephemeral-class
file, without touching the durable class (`.orchestrator-handoff.json`, `.return-meta.json` bare
form) and without deleting anything from disk. This report exists to pin down exact, verified
ground truth (not inference) so implementation is a pure execution of already-printed commands.

## Findings

### Verbatim `.gitignore` block (source: "Consumer Repo Setup" section, lines 108–124 of the standard)

```gitignore
# Ephemeral orchestrator runtime state: per-dispatch scratch, mutex directories, and loop
# guards. Ignored because these have no freshness gate on read — a git-restored copy would
# silently corrupt in-flight cycle/churn state. See
# agent-system/extensions/core/context/standards/orchestrator-runtime-files.md for the full
# two-class policy and rationale. Deliberately does NOT include .orchestrator-handoff.json or
# .return-meta.json — those are durable, freshness-gated provenance and MUST stay tracked.
**/.lock/
**/.orchestrator-loop-guard
**/.continuation-loop-guard
**/.orchestrator-churn-state.json
**/.postflight-loop-guard
**/.orchestrator-multi-state.json
**/.drift-inspection.json
**/.return-meta-*.json
**/.events.lock
```

This is copied character-for-character from the standard doc; no adaptation is needed or wanted
(the doc explicitly says a `specs/*` pattern authored inside `.claude/` would resolve relative to
`.claude/` and silently match nothing — hence the requirement to paste this at repo root by hand).

### Current root `/.gitignore` (verified via `Read`, 19 lines total)

Confirmed zero orchestrator/runtime-related lines exist today:
```
/.lake
/docs/doc-data
/docs/doc
/docs/Init-manifest.json
/docs/Init-manifest.json.hash
/docs/Init-manifest.json.trace
/docs/Lake-manifest.json
/docs/Lake-manifest.json.hash
/docs/Lake-manifest.json.trace
/docs/Lean-manifest.json
/docs/Lean-manifest.json.hash
/docs/Lean-manifest.json.trace
/docs/Std-manifest.json
/docs/Std-manifest.json.hash
/docs/Std-manifest.json.trace
**/specs/tmp/
.DS_Store
# .claude tracked files are allowed; ignore only generated/local state
.claude/settings.local.json
```
The new block should be appended after the existing content (a blank line separator, then the
6-line comment header, then the 9 glob lines above). No existing line collides with or
duplicates any of the 9 new patterns.

### Exact `check-runtime-file-tracking.sh` output (executed directly, not inferred)

**Check A (ignore coverage) — FAILED.** All 9 ephemeral-class representative probes report
"NOT ignored" (as expected, since `.gitignore` currently has no matching lines):
```
FAIL specs/000_probe/.orchestrator-loop-guard is NOT ignored
FAIL specs/000_probe/.orchestrator-churn-state.json is NOT ignored
FAIL specs/000_probe/.drift-inspection.json is NOT ignored
FAIL specs/000_probe/.lock/holder.json is NOT ignored
FAIL specs/000_probe/.continuation-loop-guard is NOT ignored
FAIL specs/000_probe/.postflight-loop-guard is NOT ignored
FAIL specs/.orchestrator-multi-state.json is NOT ignored
FAIL specs/000_probe/.return-meta-orchestrate.json is NOT ignored
FAIL specs/.events.lock is NOT ignored
```

**Check B (no ephemeral file tracked) — FAILED.** 34 tracked ephemeral-class paths were found
(see "Corrected Tallies" below for the exact breakdown and the full path list). The script prints
the exact remediation command per file/directory; every line was captured and is reproduced in
full in the Appendix.

**Check C (durable provenance not over-ignored) — PASSED** (already, pre-fix):
```
OK   specs/000_probe/.orchestrator-handoff.json is not ignored
OK   specs/000_probe/.return-meta.json is not ignored
```
This must still pass after the fix — the verbatim block's `**/.return-meta-*.json` pattern
(suffixed form only, note the trailing `-*`) does not match the bare `.return-meta.json` or
`.orchestrator-handoff.json`, so Check C is structurally unaffected by adding the block.

### Corrected Tallies (verified via `grep -c` on the script's own captured output)

The task description's tallies were close but not exact; the verified breakdown is:

| Pattern class | Task description said | Verified count |
|---|---|---|
| `.orchestrator-loop-guard` | 18 | **17** |
| `.orchestrator-churn-state.json` | 7 | **7** (matches) |
| `.return-meta-{research,teammate-a,lit-05,orchestrate}.json` variants | 5 | **5** (matches, but only 3 distinct suffixes appear: `-lit-05`, `-research`, `-teammate-a`; no `-orchestrate` variant is currently tracked) |
| `.drift-inspection.json` | 2 | **2** (matches) |
| `.return-meta-multi*.json` | 2 | **2** (matches: `specs/.return-meta-multi.json` and `specs/.return-meta-multi.sess_1782893182_f5e27d.json`) |
| `.orchestrator-multi-state.json` | 1 | **1** (matches) |
| `.lock/` directory | 1 (`specs/557_.../.lock/`) | **1** (matches exactly: `specs/557_modal_tableau_refactor_abstractions_boneyard/.lock/holder.json`) |
| `specs/.events.lock` | 1 | **1** (matches) |
| **Total** | **35** | **34** |

The only discrepancy is the loop-guard count (17 vs. the stated 18); this does not change the
remediation approach in any way — the implementer should use the exact list the script prints at
execution time (or the full list reproduced in the Appendix below), not a hardcoded count.

### Full list of tracked ephemeral files (verified via `git ls-files` + pattern match, sorted)

```
specs/317_propositional_tableau_completeness/.orchestrator-churn-state.json
specs/317_propositional_tableau_completeness/.orchestrator-loop-guard
specs/317_propositional_tableau_completeness/.return-meta-lit-05.json
specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-churn-state.json
specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-loop-guard
specs/553_s4_loop_guard_soundness_reachability_restriction/.orchestrator-churn-state.json
specs/554_cs5_pair_seed_disjunction_property_cutfree_research/.orchestrator-churn-state.json
specs/557_modal_tableau_refactor_abstractions_boneyard/.lock/holder.json
specs/557_modal_tableau_refactor_abstractions_boneyard/.orchestrator-churn-state.json
specs/557_modal_tableau_refactor_abstractions_boneyard/.orchestrator-loop-guard
specs/archive/038_temporal_dense_completeness/.orchestrator-loop-guard
specs/archive/073_propositional_shared_sublogic/.orchestrator-loop-guard
specs/archive/091_pr_1_5_propositional_hilbert_submission/.orchestrator-loop-guard
specs/archive/169_recreate_modal_primitives_pr_upstream/.orchestrator-loop-guard
specs/archive/170_submit_subpr_3_1_3_2_temporal_syntax/.orchestrator-loop-guard
specs/archive/199_review_pr_citations/.orchestrator-loop-guard
specs/archive/200_fix_literature_directory_quality/.orchestrator-loop-guard
specs/archive/232_rebase_pr649_onto_pr648/.orchestrator-loop-guard
specs/archive/266_research_propositional_and_foundations_improvements/.orchestrator-loop-guard
specs/archive/322_mpl_conservative_extension_chain/.orchestrator-loop-guard
specs/archive/332_normalization_termination_proof/.return-meta-research.json
specs/archive/345_reconcile_logic_encodings_isminimal/reports/.return-meta-teammate-a.json
specs/archive/385_complete_parked_tableau_interpolation_fmp/.orchestrator-loop-guard
specs/archive/404_forall2_mathlib_cleanup_soundness/.orchestrator-loop-guard
specs/archive/477_refactor_pr_662_stack_on_607/.orchestrator-loop-guard
specs/archive/515_s5_universal_rule_termination_unblock_504/.drift-inspection.json
specs/archive/515_s5_universal_rule_termination_unblock_504/.orchestrator-churn-state.json
specs/archive/515_s5_universal_rule_termination_unblock_504/.orchestrator-loop-guard
specs/archive/517_labelled_bounded_context_cs5_completeness/.orchestrator-churn-state.json
specs/archive/552_tableau_calculus_conformance_rule_completeness_repair/.drift-inspection.json
specs/.events.lock
specs/.orchestrator-multi-state.json
specs/.return-meta-multi.json
specs/.return-meta-multi.sess_1782893182_f5e27d.json
```

Remediation commands: `git rm --cached "<path>"` for every entry above except the `.lock/`
directory entry, which uses `git rm -r --cached "specs/557_modal_tableau_refactor_abstractions_boneyard/.lock"`.
All 34 files remain on disk after these commands (index-only removal).

### Durable class confirmation (must remain tracked and un-ignored)

- `.orchestrator-handoff.json` (any path) — durable, freshness-gated by mtime vs.
  `dispatch_start_ts` per `docs/architecture/handoff-schema.md`.
- Bare `.return-meta.json` (any path, **not** the suffixed `.return-meta-*.json` variants) —
  durable, freshness-gated by `meta_mtime` vs. `window_start_ts` per
  `orchestrate-recover-outcome.sh`.

Check C already passes today (both probes report "not ignored") because the current
`.gitignore` has no orchestrator lines at all. The verbatim block above is written to preserve
this: it uses `**/.return-meta-*.json` (suffixed form, note the `-*.json` after the literal
`-meta`), which does not match bare `.return-meta.json`, and it contains no pattern at all for
`.orchestrator-handoff.json`. Verify this stays true after editing — Check C must still pass.

### Ordering hazard analysis

The task description explicitly flagged a possible hazard: this very orchestration run is
creating its own ephemeral files under `specs/578_.../`. Verified directly:

```
$ find specs/578_untrack_ephemeral_orchestrator_runtime_files -maxdepth 2
specs/578_untrack_ephemeral_orchestrator_runtime_files
specs/578_untrack_ephemeral_orchestrator_runtime_files/.orchestrator-loop-guard
specs/578_untrack_ephemeral_orchestrator_runtime_files/.return-meta.json
specs/578_untrack_ephemeral_orchestrator_runtime_files/reports
specs/578_untrack_ephemeral_orchestrator_runtime_files/.lock
specs/578_untrack_ephemeral_orchestrator_runtime_files/.lock/holder.json

$ git ls-files specs/578_untrack_ephemeral_orchestrator_runtime_files
(empty — nothing tracked yet)

$ git status --porcelain specs/578_untrack_ephemeral_orchestrator_runtime_files
?? specs/578_untrack_ephemeral_orchestrator_runtime_files/

$ git check-ignore -v specs/578_untrack_ephemeral_orchestrator_runtime_files/.orchestrator-loop-guard
(exit 1 — not ignored, pre-fix, as expected)
```

**Conclusion: no hazard.** This run's own `.orchestrator-loop-guard` and `.lock/holder.json` are
entirely untracked right now (the whole task directory is a fresh `??` in `git status`), so
`git rm --cached` is never applicable to them — there is nothing to untrack. The only interaction
with the `.gitignore` edit is that, the instant the new block is written, `git check-ignore` on
these two paths will flip from exit 1 to exit 0 (silently ignored), which is exactly the desired
effect and requires no special sequencing. The standard document's own section order (Consumer
Repo Setup, i.e. the `.gitignore` edit, is presented before Untracking Already-Committed
Ephemeral Files) is the natural and safe order to follow: write `.gitignore` first, then run the
`git rm --cached` batch. There is no case where doing it in the other order would break anything
either (git rm --cached does not consult `.gitignore` to decide whether removal is allowed), but
gitignore-first avoids a transient window where the just-untracked copies show up as new
unignored `??` untracked files in `git status` between the two steps.

One related caution for the implementer: `specs/553_.../.orchestrator-loop-guard` and
`specs/575_.../.orchestrator-loop-guard` (visible as pre-existing `??` untracked entries in the
broader repo `git status` at session start) are likewise untracked already and require no
`git rm --cached` — only the 34 paths in the Appendix/Findings list above are currently tracked
and need remediation.

### Staging discipline for the eventual commit

Per `.claude/rules/git-workflow.md` and `.claude/context/standards/git-staging-scope.md`, the
implementation commit must stage `.gitignore` plus exactly the 34 `git rm --cached` / one
`git rm -r --cached` removals (git records these as deletions from the index) — never
`git add -A` and never a wholesale `git add specs/578_.../`, since the latter would newly track
this task's own `.orchestrator-loop-guard`/`.lock/holder.json` (harmless in isolation, but exactly
the anti-pattern this task exists to reverse, and avoidable entirely since `.gitignore` now covers
them).

## Recommendations

1. Append the verbatim 15-line block (6-line comment + 9 glob patterns) to root `/.gitignore`.
2. Run `git rm --cached` for each of the 33 file paths and `git rm -r --cached` for the one
   `.lock/` directory listed above (or re-run the check script immediately before remediating and
   use its freshly-printed list/commands, in case new ephemeral files appeared in the interim from
   concurrent orchestration activity).
3. Stage only `.gitignore` and the 34 removed index entries; commit.
4. Re-run `bash .claude/scripts/check-runtime-file-tracking.sh` and confirm exit code 0 with all
   three checks passing.
5. Do not touch `.orchestrator-handoff.json` or bare `.return-meta.json` anywhere in the repo.
6. Do not delete any file from disk — `git rm --cached` (and its `-r` form) is index-only by
   design; verify with `ls` on a sample path or two after the commit if desired, but this is
   guaranteed by the command itself, not something to second-guess.

## Decisions

- Use the verbatim block from the standard doc with no modification (per explicit task
  instruction and per the standard's own rationale for why it must be hand-applied here).
- Treat the task description's "35 files" tally as approximate; the implementer should drive off
  the script's live output (or the Appendix list in this report) rather than a fixed count, since
  the exact count can drift slightly between task authorship and execution (e.g., new
  `.orchestrator-loop-guard` files from concurrent in-flight orchestrations could be committed by
  another process before this fix lands — unlikely but the live-list approach is robust to it
  regardless).

## Risks & Mitigations

- **Risk**: A concurrent `/orchestrate` run on another task commits a new ephemeral file between
  this research report and the implementation step, making the fixed 34-item list stale.
  **Mitigation**: implementer re-runs `check-runtime-file-tracking.sh` immediately before
  remediating and drives off its live Check B output, not a hardcoded list.
- **Risk**: Accidentally matching or ignoring `.orchestrator-handoff.json` / bare
  `.return-meta.json` via an overly broad glob.
  **Mitigation**: use the verbatim block only (already verified not to match either durable
  filename); confirm with Check C after the edit.
- **Risk**: Wholesale `git add` on the task's own directory tracks this run's own ephemeral
  loop-guard/lock, re-creating the exact problem being fixed.
  **Mitigation**: stage `.gitignore` and the 34 removals explicitly; never `git add -A` or
  `git add specs/578_.../`.

## Context Extension Recommendations

None — the standard document (`orchestrator-runtime-files.md`) and its verification script
already fully and correctly document this exact remediation; no gap was found.

## Appendix

### Commands executed for this research (all run directly, no inference)

```bash
bash .claude/scripts/check-runtime-file-tracking.sh
cat .gitignore
git ls-files | grep -E '(pattern)'   # per check script's own b_patterns array
git status --porcelain specs/578_untrack_ephemeral_orchestrator_runtime_files
git ls-files specs/578_untrack_ephemeral_orchestrator_runtime_files
git check-ignore -v specs/578_untrack_ephemeral_orchestrator_runtime_files/.orchestrator-loop-guard
find specs/578_untrack_ephemeral_orchestrator_runtime_files -maxdepth 2
```

### Full exact remediation commands (as would be printed per-file by the script; reproduced here for implementation convenience)

```bash
git rm --cached "specs/317_propositional_tableau_completeness/.orchestrator-loop-guard"
git rm --cached "specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-loop-guard"
git rm --cached "specs/557_modal_tableau_refactor_abstractions_boneyard/.orchestrator-loop-guard"
git rm --cached "specs/archive/038_temporal_dense_completeness/.orchestrator-loop-guard"
git rm --cached "specs/archive/073_propositional_shared_sublogic/.orchestrator-loop-guard"
git rm --cached "specs/archive/091_pr_1_5_propositional_hilbert_submission/.orchestrator-loop-guard"
git rm --cached "specs/archive/169_recreate_modal_primitives_pr_upstream/.orchestrator-loop-guard"
git rm --cached "specs/archive/170_submit_subpr_3_1_3_2_temporal_syntax/.orchestrator-loop-guard"
git rm --cached "specs/archive/199_review_pr_citations/.orchestrator-loop-guard"
git rm --cached "specs/archive/200_fix_literature_directory_quality/.orchestrator-loop-guard"
git rm --cached "specs/archive/232_rebase_pr649_onto_pr648/.orchestrator-loop-guard"
git rm --cached "specs/archive/266_research_propositional_and_foundations_improvements/.orchestrator-loop-guard"
git rm --cached "specs/archive/322_mpl_conservative_extension_chain/.orchestrator-loop-guard"
git rm --cached "specs/archive/385_complete_parked_tableau_interpolation_fmp/.orchestrator-loop-guard"
git rm --cached "specs/archive/404_forall2_mathlib_cleanup_soundness/.orchestrator-loop-guard"
git rm --cached "specs/archive/477_refactor_pr_662_stack_on_607/.orchestrator-loop-guard"
git rm --cached "specs/archive/515_s5_universal_rule_termination_unblock_504/.orchestrator-loop-guard"
git rm --cached "specs/317_propositional_tableau_completeness/.orchestrator-churn-state.json"
git rm --cached "specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-churn-state.json"
git rm --cached "specs/553_s4_loop_guard_soundness_reachability_restriction/.orchestrator-churn-state.json"
git rm --cached "specs/554_cs5_pair_seed_disjunction_property_cutfree_research/.orchestrator-churn-state.json"
git rm --cached "specs/557_modal_tableau_refactor_abstractions_boneyard/.orchestrator-churn-state.json"
git rm --cached "specs/archive/515_s5_universal_rule_termination_unblock_504/.orchestrator-churn-state.json"
git rm --cached "specs/archive/517_labelled_bounded_context_cs5_completeness/.orchestrator-churn-state.json"
git rm --cached "specs/archive/515_s5_universal_rule_termination_unblock_504/.drift-inspection.json"
git rm --cached "specs/archive/552_tableau_calculus_conformance_rule_completeness_repair/.drift-inspection.json"
git rm -r --cached "specs/557_modal_tableau_refactor_abstractions_boneyard/.lock"
git rm --cached "specs/.orchestrator-multi-state.json"
git rm --cached "specs/.return-meta-multi.json"
git rm --cached "specs/.return-meta-multi.sess_1782893182_f5e27d.json"
git rm --cached "specs/317_propositional_tableau_completeness/.return-meta-lit-05.json"
git rm --cached "specs/archive/332_normalization_termination_proof/.return-meta-research.json"
git rm --cached "specs/archive/345_reconcile_logic_encodings_isminimal/reports/.return-meta-teammate-a.json"
git rm --cached "specs/.events.lock"
```

Post-remediation, `bash .claude/scripts/check-runtime-file-tracking.sh` should exit 0 with all
three checks reporting `passed`.
