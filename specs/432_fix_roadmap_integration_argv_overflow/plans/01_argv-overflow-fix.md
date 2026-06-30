# Implementation Plan: Fix roadmap-integration.sh argv overflow

- **Task**: 432 - Fix roadmap-integration.sh argv overflow
- **Status**: [NOT STARTED]
- **Effort**: 1.25 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_argv-overflow-fix.md
- **Artifacts**: plans/01_argv-overflow-fix.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

`.claude/scripts/roadmap-integration.sh` aborts with `python3: Argument list too long`
(E2BIG) at line 352 during `/review`, because two inline-Python heredoc invocations pass
large shell-variable contents as `sys.argv` positional arguments. Site 1 (line 115) passes
the full ROADMAP.md text; site 2 (line 238) passes two JSON blobs, the second derived from
the 92 KB `state.json` — this is the actual overflow trigger. The fix never passes file
content or large blobs as argv: site 1 passes the file path directly (`open(sys.argv[1])`),
and site 2 writes both blobs to `mktemp` temp files and passes their paths. The same
anti-pattern in two sibling scripts (`issue-grouping.sh`, `tier-selection.sh`) is fixed for
consistency. Definition of done: `roadmap-integration.sh` runs against the real large
`state.json` without E2BIG and produces valid roadmap-match output.

### Research Integration

The research report (`reports/01_argv-overflow-fix.md`) identifies the fix concretely:
- Site 1 (lines 113-115): delete the `ROADMAP_CONTENT=$(cat ...)` line and pass `$ROADMAP_PATH`
  to Python, reading it with `open(sys.argv[1], encoding='utf-8')`. `$ROADMAP_CONTENT` is used
  nowhere else, so the `cat` line is safe to delete.
- Site 2 (lines 238-352): write `$ROADMAP_STATE` and `$ALL_COMPLETED` to `mktemp` temp files
  with `printf '%s'`, pass the two paths, load with `json.load(open(...))`, then `rm -f` the
  temp files.
- stdin is NOT viable: the heredoc `<< 'PYEOF'` already occupies stdin with the Python source.
- Sibling scripts `issue-grouping.sh` (lines 160, 214) and `tier-selection.sh` (lines 188, 242)
  share the pattern; data is small today but fixed for prevention.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md roadmap item targeted by this task; the fix restores ROADMAP.md auto-annotation
tooling itself. No roadmap phases requested (roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Eliminate the E2BIG abort in `roadmap-integration.sh` so `/review` roadmap auto-annotation
  works against the current and future (growing) `state.json`.
- Replace all argv-content passing in `roadmap-integration.sh` with path-passthrough (site 1)
  and temp-file paths (site 2), preserving existing Python logic and output format.
- Apply the same temp-file pattern to `issue-grouping.sh` and `tier-selection.sh` for
  consistency and future-proofing.
- Verify the fix against the real large `state.json` (not a synthetic small input).

**Non-Goals**:
- No change to the matching logic, output schema, or callers of these scripts.
- No new context/documentation file (the research's `shell-argv-limits.md` suggestion is out
  of scope for this fix task).
- No refactor of the heredoc-Python embedding approach beyond the argv fix.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Temp files left behind on error exit | L | L | Place `rm -f` immediately after the command substitution; optionally add `trap` cleanup. Verify no stray files after a run. |
| `printf '%s'` vs `echo` newline corrupts JSON | M | L | Use `printf '%s'`; `json.load` tolerates a trailing newline regardless. |
| `$ROADMAP_CONTENT` used elsewhere | M | L | Research confirms it is only used at line 115; grep the file to re-confirm before deleting. |
| Encoding mismatch (`cat` vs Python `open`) | L | L | Pass `encoding='utf-8'` to `open()` to match shell default. |
| Sibling-script edits break `/review` issue grouping | M | L | Keep Python bodies byte-identical except the input-loading lines; data is small so behavior is unchanged. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. Phases 1-2 touch the same file
(`roadmap-integration.sh`) and are therefore sequential.

### Phase 1: Fix roadmap-integration.sh site 1 (path passthrough) [COMPLETED]

- **Goal:** Stop passing ROADMAP.md content as argv[1]; pass the path and read it in Python.
- **Tasks:**
  - [ ] Grep `roadmap-integration.sh` to re-confirm `$ROADMAP_CONTENT` is used only at the
    site-1 invocation (line ~115).
  - [ ] Delete the `ROADMAP_CONTENT=$(cat "$ROADMAP_PATH")` line (~line 113).
  - [ ] Change the invocation to `python3 - "$ROADMAP_PATH" << 'PYEOF'`.
  - [ ] Replace `content = sys.argv[1]` with
    `with open(sys.argv[1], encoding='utf-8') as _f:` / `    content = _f.read()`.
  - [ ] Confirm the rest of the site-1 Python body is unchanged.
- **Timing:** ~15 min
- **Depends on:** none
- **Files to modify:**
  - `.claude/scripts/roadmap-integration.sh` (lines ~113-115) - remove `cat`, pass path, read in Python
- **Verification:**
  - `bash -n .claude/scripts/roadmap-integration.sh` parses without syntax error.
  - Grep confirms no remaining `$ROADMAP_CONTENT` reference.

### Phase 2: Fix roadmap-integration.sh site 2 (mktemp temp files) [COMPLETED]

- **Goal:** Stop passing the two JSON blobs as argv[1]/argv[2]; write them to temp files and
  pass the paths. This is the actual E2BIG trigger.
- **Tasks:**
  - [ ] Before the site-2 invocation (~line 238), add:
    `_RI_TMP_STATE=$(mktemp)` and `_RI_TMP_ALL=$(mktemp)`.
  - [ ] Write blobs with `printf '%s' "$ROADMAP_STATE" > "$_RI_TMP_STATE"` and
    `printf '%s' "$ALL_COMPLETED" > "$_RI_TMP_ALL"`.
  - [ ] Change the invocation to `python3 - "$_RI_TMP_STATE" "$_RI_TMP_ALL" << 'PYEOF'`.
  - [ ] Replace `roadmap_state = json.loads(sys.argv[1])` with
    `with open(sys.argv[1]) as _f: roadmap_state = json.load(_f)` and the analogous change for
    `all_completed` / `sys.argv[2]`.
  - [ ] After the closing `)` of the command substitution (~line 352), add
    `rm -f "$_RI_TMP_STATE" "$_RI_TMP_ALL"`.
  - [ ] Confirm the rest of the site-2 Python body (matching logic, `print(json.dumps(matches))`)
    is unchanged.
- **Timing:** ~20 min
- **Depends on:** 1
- **Files to modify:**
  - `.claude/scripts/roadmap-integration.sh` (lines ~238-352) - mktemp temp files, path args, json.load, cleanup
- **Verification:**
  - `bash -n .claude/scripts/roadmap-integration.sh` parses without syntax error.
  - Grep confirms no remaining `json.loads(sys.argv` in the file.

### Phase 3: Verify against the real large state.json [COMPLETED]

- **Goal:** Confirm the E2BIG no longer occurs and the script produces valid output when run
  against the real (large) `state.json`.
- **Tasks:**
  - [ ] Identify how `roadmap-integration.sh` is invoked by `/review` (read the script's
    argument contract / header) and run it directly against `specs/ROADMAP.md` and the real
    `specs/state.json`.
  - [ ] Confirm no `Argument list too long` error appears.
  - [ ] Confirm the script exits 0 and the roadmap-match output is valid JSON (pipe through
    `jq .` or `python3 -m json.tool`).
  - [ ] Confirm no stray temp files remain (e.g. check `$TMPDIR`/`/tmp` for leftover `mktemp`
    files after the run).
- **Timing:** ~15 min
- **Depends on:** 1, 2
- **Files to modify:** none (verification only)
- **Verification:**
  - Script run completes without E2BIG and emits parseable JSON.
  - No leftover temp files.

### Phase 4: Apply temp-file pattern to sibling scripts [COMPLETED]

- **Goal:** Fix the identical anti-pattern in `issue-grouping.sh` and `tier-selection.sh` for
  consistency and future-proofing.
- **Tasks:**
  - [ ] `issue-grouping.sh` line ~160: write `$ENRICHED` to a `mktemp` file, pass the path,
    load with `json.load(open(...))`, `rm -f` after.
  - [ ] `issue-grouping.sh` line ~214: same treatment for `$GROUPED`.
  - [ ] `tier-selection.sh` line ~188: write `$GROUPED_ISSUES` to a temp file and pass its
    path; `$SELECTED_GROUPS` is a short string and may remain an argv string (or also use a
    temp file for uniformity) — keep `selected_str = sys.argv[2]` working accordingly.
  - [ ] `tier-selection.sh` line ~242: same treatment as line 188.
  - [ ] Keep each Python body byte-identical except the input-loading lines.
- **Timing:** ~20 min
- **Depends on:** 3
- **Files to modify:**
  - `.claude/scripts/issue-grouping.sh` (lines ~160, ~214) - mktemp + path + json.load + cleanup
  - `.claude/scripts/tier-selection.sh` (lines ~188, ~242) - mktemp + path for the JSON blob arg
- **Verification:**
  - `bash -n` parses both scripts without syntax error.
  - Grep confirms no remaining `json.loads(sys.argv` in either file.

## Testing & Validation

- [ ] `bash -n .claude/scripts/roadmap-integration.sh` (and the two sibling scripts) parse cleanly.
- [ ] `roadmap-integration.sh` run against the real `specs/state.json` + `specs/ROADMAP.md`
  completes with no `Argument list too long` and exits 0.
- [ ] Roadmap-match output is valid JSON.
- [ ] No `json.loads(sys.argv` remains in any of the three scripts.
- [ ] No stray `mktemp` temp files remain after a run.

## Artifacts & Outputs

- `.claude/scripts/roadmap-integration.sh` (modified - sites 1 and 2 fixed)
- `.claude/scripts/issue-grouping.sh` (modified - 2 sites fixed)
- `.claude/scripts/tier-selection.sh` (modified - 2 sites fixed)
- `specs/432_fix_roadmap_integration_argv_overflow/summaries/01_argv-overflow-fix-summary.md`
  (on completion)

## Rollback/Contingency

All changes are localized to three shell scripts. Revert with
`git checkout -- .claude/scripts/roadmap-integration.sh .claude/scripts/issue-grouping.sh .claude/scripts/tier-selection.sh`.
If only Phase 4 (siblings) causes regression, revert just those two files and keep the
`roadmap-integration.sh` fix, since Phases 1-3 are independently verified.
