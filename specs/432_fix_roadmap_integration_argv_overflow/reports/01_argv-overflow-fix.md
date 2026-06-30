# Research Report: Task #432

**Task**: 432 - Fix roadmap-integration.sh argv overflow
**Started**: 2026-06-30T00:00:00Z
**Completed**: 2026-06-30T00:00:00Z
**Effort**: 0.5h
**Dependencies**: None
**Sources/Inputs**: Codebase — `.claude/scripts/roadmap-integration.sh`, `specs/reviews/review-2026-06-30.md`, sibling scripts
**Artifacts**: `specs/432_fix_roadmap_integration_argv_overflow/reports/01_argv-overflow-fix.md`
**Standards**: report-format.md

## Executive Summary

- Two invocation sites in `roadmap-integration.sh` pass large shell variable contents as `sys.argv` arguments to `python3`, causing `E2BIG` ("Argument list too long") when the combined argv + environment exceeds the kernel limit.
- **Site 1 (line 115)**: passes ROADMAP.md file content (~9 KB currently) as `argv[1]` — fixable by passing the already-available `$ROADMAP_PATH` directly and reading the file inside Python.
- **Site 2 (line 238)**: passes two JSON blobs (`$ROADMAP_STATE` + `$ALL_COMPLETED`, the latter derived from the 92 KB `state.json`) as `argv[1]` and `argv[2]` — fixable by writing both blobs to `mktemp` temp files and passing the paths instead.
- Three sibling scripts (`issue-grouping.sh`, `tier-selection.sh`) use the same anti-pattern; they handle smaller data today but should be fixed for consistency and future-proofing.

## Context and Scope

`roadmap-integration.sh` is called by `/review` to cross-reference `ROADMAP.md` against completed tasks in `state.json` and annotate roadmap items. The script embeds two inline Python heredoc invocations that receive their input data as positional argv strings. As `state.json` grows (currently 92 KB, 430+ tasks), the argv string for the second invocation overflows the kernel `E2BIG` limit (`ARG_MAX = 2097152` bytes on this system, but environment variables compete for that budget).

The review report (`specs/reviews/review-2026-06-30.md`, line 83–88) confirmed the abort at line 352 during the 2026-06-30 review run.

## Findings

### Codebase Patterns

#### roadmap-integration.sh — offending site 1 (lines 113–198)

```bash
# Line 113 — file content read into a shell variable
ROADMAP_CONTENT=$(cat "$ROADMAP_PATH")

# Line 115 — content passed as argv[1] to Python
ROADMAP_STATE=$(python3 - "$ROADMAP_CONTENT" << 'PYEOF'
import sys, re, json
content = sys.argv[1]          # receives entire ROADMAP.md text
...
PYEOF
)
```

The file is already available at `$ROADMAP_PATH`. There is no need to read it into a shell variable first; Python can open the path directly.

**Current data size**: ROADMAP.md is ~9 KB. Not the trigger today, but the same anti-pattern.

#### roadmap-integration.sh — offending site 2 (lines 238–352)

```bash
# Line 238 — two large JSON blobs passed as argv[1] and argv[2]
ROADMAP_MATCHES=$(python3 - "$ROADMAP_STATE" "$ALL_COMPLETED" << 'PYEOF'
import sys, re, json
roadmap_state  = json.loads(sys.argv[1])   # JSON from site-1 output
all_completed  = json.loads(sys.argv[2])   # JSON extracted from 92 KB state.json
...
print(json.dumps(matches))
PYEOF
)   # <-- line 352: bash reports E2BIG here
```

`$ALL_COMPLETED` is built by piping completed entries from `state.json` through two `jq` calls and optionally merging with `archive/state.json`. With 430+ tasks, the completed-task subset easily runs 30–50 KB as a JSON array. The bash error is reported at line 352 (the closing `)` of the command substitution) because that is where the shell attempts to `execve()` the python3 process.

#### issue-grouping.sh — same pattern (lines 160 and 214)

```bash
# Line 160
GROUPED=$(python3 - "$ENRICHED" << 'PYEOF'
enriched = json.loads(sys.argv[1])
...

# Line 214
POST_PROCESSED=$(python3 - "$GROUPED" << 'PYEOF'
groups = json.loads(sys.argv[1])
```

`$ENRICHED` and `$GROUPED` are JSON blobs representing code-review issues. Current sizes are modest (typically < 10 KB during `/review`) but subject to the same overflow if the issue list grows.

#### tier-selection.sh — same pattern (lines 188 and 242)

```bash
# Line 188
TOTAL_ISSUES=$(python3 - "$GROUPED_ISSUES" "$SELECTED_GROUPS" << 'PYEOF'
groups = json.loads(sys.argv[1])
selected_str = sys.argv[2]

# Line 242
OPTIONS=$(python3 - "$GROUPED_ISSUES" "$SELECTED_GROUPS" << 'PYEOF'
groups = json.loads(sys.argv[1])
selected_str = sys.argv[2]
```

Same pattern; data is small today but structurally identical.

#### roadmap-sync.sh — not affected (line 315)

```bash
python3 "$py_script" "$roadmap_path" "$old_str" "$new_str"
```

Passes file paths and short replacement strings — not file content. Safe.

#### vault-operation.sh — partially affected (line 201)

```bash
python3 - "$TODO_FILE" "$comment" <<'PYEOF' 2>/dev/null || true
```

Passes a file *path* (`$TODO_FILE`) not content, plus a short `$comment` string. Safe as written.

### Recommended Fix Pattern

**Principle**: never pass file content or large JSON blobs as `sys.argv`; always pass file *paths* or use temp files with `mktemp`.

#### Fix for site 1 (lines 113–198) — pass path directly

Remove the `cat` line and pass `$ROADMAP_PATH` instead of `$ROADMAP_CONTENT`:

```bash
# BEFORE
ROADMAP_CONTENT=$(cat "$ROADMAP_PATH")
ROADMAP_STATE=$(python3 - "$ROADMAP_CONTENT" << 'PYEOF'
content = sys.argv[1]

# AFTER — delete the cat line, pass the path
ROADMAP_STATE=$(python3 - "$ROADMAP_PATH" << 'PYEOF'
with open(sys.argv[1], encoding='utf-8') as _f:
    content = _f.read()
```

`$ROADMAP_CONTENT` is not used anywhere else after line 115, so the `cat` line can be deleted entirely.

#### Fix for site 2 (lines 238–352) — write to mktemp files

```bash
# AFTER — write blobs to temp files, pass paths
_RI_TMP_STATE=$(mktemp)
_RI_TMP_ALL=$(mktemp)
printf '%s' "$ROADMAP_STATE"   > "$_RI_TMP_STATE"
printf '%s' "$ALL_COMPLETED"   > "$_RI_TMP_ALL"

ROADMAP_MATCHES=$(python3 - "$_RI_TMP_STATE" "$_RI_TMP_ALL" << 'PYEOF'
import sys, re, json
with open(sys.argv[1]) as _f:
    roadmap_state = json.load(_f)
with open(sys.argv[2]) as _f:
    all_completed = json.load(_f)
# ... body unchanged ...
print(json.dumps(matches))
PYEOF
)
rm -f "$_RI_TMP_STATE" "$_RI_TMP_ALL"
```

Use `printf '%s'` rather than `echo` to avoid the trailing newline issue with large JSON. The `rm -f` cleanup should appear both after normal completion and in a `trap ERR EXIT` if the script is expanded in the future.

#### Fix for issue-grouping.sh and tier-selection.sh (same approach)

Apply the mktemp pattern identically to all four sites in those two files. Since this data is currently small, these fixes are for consistency and prevention rather than immediate correctness.

### Why stdin is not viable here

`python3 -` already consumes stdin for the Python script source via the heredoc (`<< 'PYEOF'`). A process can only have one stdin, so piping data via stdin is not possible without restructuring the call (e.g., using a process substitution for the script source). The temp-file approach is simpler and correct.

## Decisions

- Use temp files (`mktemp`) for site 2 and for sibling scripts — avoids restructuring the heredoc pattern.
- Use direct path pass-through for site 1 — simpler and cheaper than `mktemp` because the path is already available.
- Use `printf '%s'` not `echo` when writing JSON blobs to temp files (avoids spurious trailing newline that could corrupt JSON in edge cases, though `json.load` tolerates it).
- Apply fixes to `issue-grouping.sh` and `tier-selection.sh` in the same implementation task for consistency, even though they do not fail today.

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Temp file left behind on error exit | Add `trap 'rm -f "$_RI_TMP_STATE" "$_RI_TMP_ALL"' EXIT` before the mktemp calls, or ensure `set -euo pipefail` terminates before the rm line and test manually |
| `mktemp` unavailable on some systems | `mktemp` is POSIX.1-2008 and present on NixOS; not a concern here |
| `$ROADMAP_CONTENT` used later | Confirmed: variable is only used as argv[1] at line 115 and nowhere else; safe to delete |
| Python `open()` encoding vs shell `cat` | Add `encoding='utf-8'` to `open()` calls to match shell behavior |

## Context Extension Recommendations

- **Topic**: Shell scripting — argv size limits and mitigation patterns
- **Gap**: No existing context file documents E2BIG mitigation strategies for bash scripts that embed Python heredocs
- **Recommendation**: Add a short note to `.claude/context/patterns/` (e.g., `shell-argv-limits.md`) describing the temp-file and path-passthrough patterns to prevent recurrence in future scripts.

## Appendix

### File sizes at time of research
| File | Size |
|------|------|
| `specs/ROADMAP.md` | ~9 KB |
| `specs/state.json` | ~92 KB |
| System `ARG_MAX` | 2,097,152 bytes |

### Affected files summary

| File | Lines | Pattern | Fix |
|------|-------|---------|-----|
| `.claude/scripts/roadmap-integration.sh` | 115 | pass path content as argv[1] | pass path directly |
| `.claude/scripts/roadmap-integration.sh` | 238 | pass two JSON blobs as argv[1,2] | mktemp + path |
| `.claude/scripts/issue-grouping.sh` | 160, 214 | pass JSON blob as argv[1] | mktemp + path |
| `.claude/scripts/tier-selection.sh` | 188, 242 | pass two JSON blobs as argv[1,2] | mktemp + path |
