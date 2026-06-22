---
name: skill-cslib-vet
description: Vet completed CSLib tasks against library standards. Invoke for /vet command.
allowed-tools: Agent, Bash, Edit, Read, Write
---

# CSLib Vet Skill

Thin wrapper that validates CSLib task inputs, identifies changed Lean files via git history,
prepares delegation context, and delegates vetting to `cslib-vet-agent` subagent. The agent
reads changed files, runs the CI pipeline, checks against all four standards documents, and
creates fix tasks interactively.

## Trigger Conditions

This skill activates when:
- `/vet` command is invoked with task numbers
- CSLib tasks need to be vetted against contribution standards
- Quality gate check before a PR submission

## Execution Flow

### Stage 1: Input Validation

Validate that task numbers exist in state.json:

```bash
cd /home/benjamin/Projects/cslib

for task_num in $TASK_NUMBERS; do
  task_entry=$(jq --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num)' \
    specs/state.json 2>/dev/null)

  if [ -z "$task_entry" ]; then
    echo "Error: Task $task_num not found in specs/state.json"
    # Return failed status
  fi

  task_name=$(echo "$task_entry" | jq -r '.project_name')
  task_type=$(echo "$task_entry" | jq -r '.task_type')
  task_status=$(echo "$task_entry" | jq -r '.status')
  echo "Task $task_num: $task_name (type=$task_type, status=$task_status)"
done
```

### Stage 2: Preflight

Generate a session ID if not passed from the command:

```bash
session_id="${session_id:-sess_$(date +%s)_$(od -An -N3 -tx1 /dev/urandom | tr -d ' ')}"
```

**Note**: The vet skill does NOT change task status. Vetting is orthogonal to the task
lifecycle (`not_started` -> `researching` -> `researched` -> `planned` -> `implementing`
-> `pr_ready` -> `completed`). Vet operates on tasks in ANY status.

### Stage 2b: Identify Changed Files

For each task number, identify Lean files changed by that task using git history:

```bash
cd /home/benjamin/Projects/cslib

CHANGED_FILES_MAP="{}"

for task_num in $TASK_NUMBERS; do
  echo "Finding files changed by task $task_num..."

  # Primary: git history via commit messages matching "task N:"
  lean_files=$(git log --all --format="%H" --grep="task ${task_num}:" \
    | xargs -I{} git show --name-only --format="" {} \
    | grep "^Cslib/" \
    | sort -u 2>/dev/null)

  # Fallback: uncommitted changes if no commits found
  if [ -z "$lean_files" ]; then
    echo "  No commits found for task $task_num — checking uncommitted changes..."
    lean_files=$(git diff --name-only HEAD -- Cslib/ 2>/dev/null)
    if [ -z "$lean_files" ]; then
      lean_files=$(git diff --cached --name-only -- Cslib/ 2>/dev/null)
    fi
    if [ -z "$lean_files" ]; then
      lean_files=$(git status --porcelain -- Cslib/ 2>/dev/null | awk '{print $2}' | grep "^Cslib/")
    fi
  fi

  if [ -z "$lean_files" ]; then
    echo "  Warning: No Lean files found for task $task_num (no commits matching 'task ${task_num}:' and no uncommitted changes)."
  else
    file_count=$(echo "$lean_files" | grep -c "." 2>/dev/null || echo 0)
    echo "  Found $file_count Lean file(s) for task $task_num"
    echo "$lean_files" | while read -r f; do
      echo "    - $f"
    done
  fi

  # Store as newline-separated list per task
  CHANGED_FILES_MAP="${CHANGED_FILES_MAP}|${task_num}:${lean_files}"
done
```

### Stage 3: Prepare Delegation Context

Build the delegation context for `cslib-vet-agent`:

```json
{
  "session_id": "{session_id}",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "vet", "skill-cslib-vet"],
  "timeout": 3600,
  "task_context": {
    "task_numbers": [{task_numbers_array}],
    "task_names": [{task_names_array}],
    "task_types": [{task_types_array}]
  },
  "changed_files": {
    "{task_num_1}": ["{file_1}", "{file_2}"],
    "{task_num_2}": ["{file_3}"]
  },
  "focus_prompt": "{optional focus from user}",
  "cslib_dir": "/home/benjamin/Projects/cslib",
  "standards_paths": {
    "contributing": "CONTRIBUTING.md",
    "notation": "NOTATION.md",
    "organisation": "ORGANISATION.md",
    "code_of_conduct": "CODE_OF_CONDUCT.md"
  },
  "metadata_file_path": "specs/270_create_vet_command_skill_agent/.return-meta.json"
}
```

**Note on metadata_file_path**: Use the actual task directory for the vetted tasks. For the
vet operation itself, the metadata path should be `specs/{NNN}_{SLUG}/.return-meta.json` where
`NNN`/`SLUG` refer to the vet invocation context (if any). Since `/vet` is a standalone command
(not tied to a specific task number), the agent writes metadata to the cslib-vet-agent's own
working directory. The skill should set this to a temp path under `.claude/tmp/` or use the
first task's directory:

```bash
# Use the first task's directory as the metadata home for this vet run
first_task_num=$(echo "$TASK_NUMBERS" | awk '{print $1}')
task_name=$(jq -r --argjson num "$first_task_num" \
  '.active_projects[] | select(.project_number == $num) | .project_name' \
  /home/benjamin/Projects/cslib/specs/state.json)
task_num_padded=$(printf '%03d' "$first_task_num")
task_dir="/home/benjamin/Projects/cslib/specs/${task_num_padded}_${task_name}"
mkdir -p "$task_dir"
metadata_file_path="specs/${task_num_padded}_${task_name}/.vet-meta.json"
```

### Stage 4: Invoke Subagent

Use Agent tool with `subagent_type: "cslib-vet-agent"` and pass the delegation context
as a JSON string in the prompt. The agent will:
1. Read all changed Lean files
2. Read the four standards documents
3. Run the CSLib CI pipeline
4. Analyze files against all standards
5. Present violations to the user interactively
6. Create fix tasks for user-selected violations
7. Write final metadata to the metadata_file_path

### Stage 4b: Self-Execution Fallback

**CRITICAL**: If you performed the work above WITHOUT using the Agent tool (i.e., you read
files, analyzed violations, or created tasks directly instead of spawning a subagent), you
MUST write a `.return-meta.json` file now before proceeding to postflight. Use the appropriate
status value.

If you DID use the Agent tool, skip this stage — the subagent already wrote the metadata.

## Postflight (ALWAYS EXECUTE)

The following stages MUST execute after work is complete, whether done by a subagent or inline.
Do NOT skip these stages for any reason.

### Stage 5: Parse Subagent Return

Read the metadata file from the path set in Stage 3:

```bash
if [ -f "$task_dir/.vet-meta.json" ]; then
  return_status=$(jq -r '.status' "$task_dir/.vet-meta.json" 2>/dev/null)
  fix_tasks_created=$(jq -r '.fix_tasks_created // 0' "$task_dir/.vet-meta.json" 2>/dev/null)
  summary=$(jq -r '.summary // "Vet completed"' "$task_dir/.vet-meta.json" 2>/dev/null)
  echo "Vet status: $return_status"
  echo "Fix tasks created: $fix_tasks_created"
else
  echo "Warning: Metadata file not found at $task_dir/.vet-meta.json"
  return_status="partial"
fi
```

### Stage 6: Git Commit (if fix tasks were created)

If any fix tasks were created, commit the state changes:

```bash
cd /home/benjamin/Projects/cslib

# Check if there are any state changes from fix task creation
if git status --porcelain specs/state.json specs/TODO.md | grep -q .; then
  git add specs/state.json specs/TODO.md
  git commit -m "vet task(s) $TASK_NUMBERS: create fix tasks

Session: $session_id"
  echo "Fix tasks committed."
else
  echo "No state changes to commit (no fix tasks created)."
fi
```

### Stage 7: Return Brief Summary

Return a brief text summary (3-6 bullets):

- Tasks vetted: {comma-separated task numbers}
- Files analyzed: {count} Lean files
- Violations found: {count} (Critical: N, High: N, Medium: N, Low: N)
- Fix tasks created: {count}
- CI pipeline: PASSED/FAILED
- Next step: {guidance based on outcome}

## MUST NOT (Postflight Boundary)

After the agent returns, this skill MUST NOT:

1. **Edit .lean files** — All CSLib code work is done by the agent
2. **Run lake build/test/lint** — CI verification is done by the agent
3. **Use lean-lsp MCP tools** — Domain tools are for agent use only
4. **Analyze standards compliance** — Compliance analysis is agent work
5. **Change vetted task status** — Vet is orthogonal to task lifecycle

The postflight phase is LIMITED TO:
- Reading agent metadata file
- Committing fix task state changes (if any)
- Git commit of state.json/TODO.md updates
- Returning brief summary

## Return Format

Brief text summary (NOT JSON).
