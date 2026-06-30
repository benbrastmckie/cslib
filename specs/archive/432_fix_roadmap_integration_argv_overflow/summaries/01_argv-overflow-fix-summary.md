# Implementation Summary: Task #432

**Completed**: 2026-06-30
**Duration**: ~30 min

## Overview

Fixed three shell scripts (`.claude/scripts/roadmap-integration.sh`, `issue-grouping.sh`, and `tier-selection.sh`) that passed large shell-variable contents as `sys.argv` positional arguments to inline Python heredocs — a pattern that aborts with `E2BIG` when the data exceeds the OS kernel's `ARG_MAX` limit (~2 MB on Linux). Site 2 in `roadmap-integration.sh` was the actual trigger, passing the full 92 KB `state.json` blob as an argv argument during `/review`. All six Python invocations across the three scripts were converted to temp-file path-passing using `mktemp`/`printf '%s'`/`json.load`/`rm -f`.

## What Changed

- `.claude/scripts/roadmap-integration.sh` — Site 1 (line ~113): removed `ROADMAP_CONTENT=$(cat ...)` and switched Python invocation to pass `$ROADMAP_PATH` directly, reading with `open(sys.argv[1], encoding='utf-8')`. Site 2 (line ~238): write `$ROADMAP_STATE` and `$ALL_COMPLETED` to `mktemp` temp files, pass paths to Python, load with `json.load()`, `rm -f` after.
- `.claude/scripts/issue-grouping.sh` — Two Python invocations (clustering at line ~160, post-processing at line ~214): both now write the JSON blob to a `mktemp` file, pass the path, load with `json.load()`, and `rm -f` after.
- `.claude/scripts/tier-selection.sh` — Two Python invocations (tier2 at line ~188, tier3 at line ~242): the `$GROUPED_ISSUES` blob is written to a `mktemp` file and passed as a path; `$SELECTED_GROUPS` (a short comma-separated index string) remains as `sys.argv[2]` unchanged.

## Decisions

- `$SELECTED_GROUPS` in `tier-selection.sh` was left as argv[2] (not temp-filed) because it is a short string of comma-separated integers, never approaching `ARG_MAX`.
- `printf '%s'` is used (not `echo`) to write JSON to temp files, avoiding spurious trailing-newline corruption risk.
- `encoding='utf-8'` is passed to all `open()` calls to match the shell default.
- Temp file variable names are script-scoped (`_RI_TMP_*`, `_IG_TMP*`, `_TS_TMP*`) to avoid collisions across scripts.

## Plan Deviations

- None (implementation followed plan)

## Verification

- Build: N/A
- Tests: `bash -n` parses all three scripts without syntax error; `roadmap-integration.sh` runs against the real 94 KB `specs/state.json` + `specs/ROADMAP.md` with exit 0 and valid JSON output; `issue-grouping.sh` functional smoke test passes; no stray `mktemp` temp files left after run.
- Files verified: Yes

## Notes

- The E2BIG fix is immediately effective: no remaining `json.loads(sys.argv` pattern exists in any of the three scripts.
- Future growth of `state.json` or `ROADMAP.md` will not trigger E2BIG since content is never passed through the OS execve argument vector.
