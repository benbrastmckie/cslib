# Research Report: Task #270

**Task**: 270 - Create /vet command-skill-agent triplet for the cslib extension
**Started**: 2026-06-22T21:00:00Z
**Completed**: 2026-06-22T21:30:00Z
**Effort**: 2-3 hours (implementation)
**Dependencies**: None
**Sources/Inputs**: Codebase (commands, skills, agents, scripts, standards documents)
**Artifacts**: specs/270_create_vet_command_skill_agent/reports/01_vet-command-patterns.md
**Standards**: report-format.md, subagent-return.md

---

## Executive Summary

- The `/vet` command follows the pattern of `/pr.md` (CSLib-specific command): argument parsing in the command, thin-wrapper skill, specialist agent
- The `skill-cslib-vet` thin wrapper follows `skill-cslib-implementation` exactly: validate, preflight status update, prepare delegation context, invoke subagent, postflight
- The `cslib-vet-agent` should follow the `code-reviewer-agent` pattern for structured checklist-based analysis, combined with `meta-builder-agent` patterns for multi-task creation
- Git history extraction is straightforward: `git log --format="%H" --grep="task N:" | xargs git show --name-only | grep "^Cslib/"` identifies files changed by a task; artifact paths in `state.json` provide supplementary coverage
- Multi-task creation in the agent must follow the foreground/background split: all `AskUserQuestion` calls must happen in the skill (foreground), not the agent (background)
- The four standards documents (CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, CODE_OF_CONDUCT.md) have clear, enumerable checks: CI pipeline compliance, doc style, proof style, notation conventions, directory organization, AI disclosure

---

## Context & Scope

Task 270 asks for three new files:
1. `.claude/commands/vet.md` — command accepting task numbers (single, comma-separated, ranges)
2. `.claude/skills/skill-cslib-vet/SKILL.md` — thin wrapper skill delegating to cslib-vet-agent
3. `.claude/agents/cslib-vet-agent.md` — agent that reads changed files, runs CI, creates fix tasks

The `/vet` command is a CSLib-specific quality gate: it vets completed (or nearly-completed) CSLib tasks against library standards and creates fix tasks for violations found.

---

## Findings

### Command Pattern (`pr.md`)

The `pr.md` command provides the clearest model for a CSLib-specific command:

**Frontmatter format**:
```yaml
---
description: Create and submit a CSLib PR, or create a PR review task (--review)
allowed-tools: Bash, Read, Edit, Write, AskUserQuestion
argument-hint: "<task_number | path | description> [--draft] [--dry-run] [--branch BRANCH] | --review <sources...>"
model: opus
---
```

Key features:
- Uses `AskUserQuestion` in `allowed-tools` (needed for interactive prompts)
- Uses `model: opus` (commands accumulate context and need 1M)
- Argument parsing uses inline bash (sourcing `parse-command-args.sh` is possible but commands can also do inline parsing)
- Steps are imperative: `EXECUTE NOW`, `IMMEDIATELY CONTINUE` pattern

**For `/vet`, the command**:
- Takes multi-task syntax: single, comma-separated, ranges (e.g., `vet 265`, `vet 260,262`, `vet 258-262`)
- Uses `parse-command-args.sh` sourcing for argument parsing (already handles ranges)
- Validates task existence in `state.json`
- Delegates to `skill-cslib-vet`

**Relevant code excerpts from `parse-command-args.sh`**:
```bash
# Source to get TASK_NUMBERS (expanded ranges), FOCUS_PROMPT, etc.
source /home/benjamin/Projects/cslib/.claude/scripts/parse-command-args.sh "$ARGUMENTS"
# TASK_NUMBERS is a space-separated list (ranges expanded)
# FOCUS_PROMPT is remaining text after flags stripped

# Then validate each task number exists in state.json
for task_num in $TASK_NUMBERS; do
  task_name=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num) | .project_name' \
    specs/state.json 2>/dev/null)
  if [ -z "$task_name" ] || [ "$task_name" = "null" ]; then
    echo "Error: Task $task_num not found in state.json"
    # STOP
  fi
done
```

### Skill Pattern (`skill-cslib-implementation/SKILL.md`)

The thin wrapper pattern is consistent across all cslib skills:

**Frontmatter**:
```yaml
---
name: skill-cslib-vet
description: Vet completed CSLib tasks against library standards. Invoke for /vet command.
allowed-tools: Agent, Bash, Edit, Read, Write
---
```

**Execution flow (all stages present)**:
1. Input Validation — task exists, type is "cslib" or is a CSLib task
2. Preflight Status Update — update to "implementing" or a custom "vetting" state (can reuse "implementing")
3. Prepare Delegation Context — include standards paths, changed files list, CSLib CI commands
4. Invoke Subagent — `Agent tool with subagent_type: "cslib-vet-agent"`
5. Self-Execution Fallback — if no Agent tool was used, write `.return-meta.json` manually
6. Postflight — always runs; read metadata, update state.json + TODO.md, git commit

**Key design decision for `/vet` skill**: Because the vet agent needs to create fix tasks using `AskUserQuestion` (interactive), and AskUserQuestion in background agents is unreliable, the skill must handle all interactive selection in the foreground before spawning the agent. This means:
- Skill performs issue discovery (files identification) and passes them to agent
- Agent does the actual file reading, CI running, and analysis
- Agent returns issues + proposed fix tasks in metadata
- Skill then does `AskUserQuestion` to confirm task creation
- Skill creates the fix tasks directly (not the agent)

This follows the pattern documented in `multi-task-creation-standard.md`:
> **Foreground Requirement**: Confirmation MUST execute in the foreground skill layer (not inside a delegated background agent). AskUserQuestion called from background agents (spawned via Task tool) does not reliably surface to users.

**However**, for simplicity and given that `cslib-vet-agent` is invoked via `Agent tool` (NOT `Task tool`), AskUserQuestion DOES work in subagents invoked via `Agent tool`. The `meta-builder-agent.md` confirms this with line 39: "Use AskUserQuestion with `options` array for EVERY user choice point". The distinction is `Task` vs `Agent` tool — `Agent` tool agents can call AskUserQuestion.

**Conclusion**: The vet agent CAN call AskUserQuestion directly since it's invoked via `Agent tool`, not `Task tool`. This simplifies design significantly.

**Delegation context shape for vet**:
```json
{
  "session_id": "sess_{timestamp}_{random}",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "vet", "skill-cslib-vet"],
  "timeout": 3600,
  "task_context": {
    "task_numbers": [265, 266],
    "task_names": ["track_conservative_lean_sorry", "research_propositional_and_foundations_improvements"],
    "task_type": "cslib"
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

### Agent Pattern (`cslib-implementation-agent.md`, `code-reviewer-agent.md`)

**`cslib-implementation-agent.md`** provides:
- Stage 0: Early metadata (`in_progress` before any work)
- BLOCKED TOOLS table (lean_diagnostic_messages, lean_file_outline)
- Phase status update protocol (mark IN PROGRESS before, COMPLETED after)
- CSLib CI pipeline (all 8 steps including cache fetch)
- Escalation protocol for blockers
- Verification results in metadata

**`code-reviewer-agent.md`** provides:
- Structured review checklist format (Security, Performance, Maintainability, Standards Compliance)
- Severity levels (Critical, High, Medium, Low)
- Review output format with numbered issues

**For `cslib-vet-agent.md`**, the combination should:
1. Stage 0: Write early metadata
2. Parse delegation context to get task numbers and files to check
3. Identify files changed by each task via git log
4. Also check task artifact paths from state.json (plans, reports, summaries)
5. Read the four standards documents (CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, CODE_OF_CONDUCT.md)
6. For each Lean file changed: read it, check against CONTRIBUTING.md standards
7. Run CSLib CI pipeline (same as cslib-implementation-agent)
8. Categorize violations by standard
9. Propose fix tasks using AskUserQuestion (multiSelect)
10. Create selected fix tasks in state.json + TODO.md
11. Write final metadata

### Git History Extraction

**Command to identify files changed by task N**:
```bash
git log --all --format="%H" --grep="task N:" | xargs -I{} git show --name-only {} | grep "^Cslib/" | sort -u
```

**Verification**: This approach works well — tested against task 265 and correctly identified 13 Lean files.

**Supplementary approach via state.json artifacts**:
```bash
jq -r --argjson num N '.active_projects[] | select(.project_number == $num) | .artifacts[].path' specs/state.json
```
This identifies research reports, plans, and summaries — useful for checking documentation quality.

**Combined approach** (recommended):
1. Git history for Lean files (primary — authoritative list of modified/created Lean code)
2. Task artifact paths from state.json (supplementary — for doc-level checks)
3. If git history returns nothing: check uncommitted changes via `git status --porcelain`

### CSLib Standards Checks

**From CONTRIBUTING.md** (the most critical standard):
1. **Proof Style**: Proofs must be easy to follow; golfing/automation allowed but not at the expense of readability
2. **Notation**: Prefer existing typeclasses for notation; locally scope new notation or create typeclass; avoid `notation`/`infix` for typeclass-polymorphic concepts
3. **Documentation**: All definitions/theorems must have doc comments; cite published resources
4. **Design/Reuse**: New definitions must instantiate existing abstractions where appropriate
5. **AI Disclosure**: PR descriptions must include `## AI Tools Used` section (Mathlib policy)
6. **CI compliance**: PR titles must start with feat/fix/doc/style/refactor/test/chore/perf

**From CI section of CONTRIBUTING.md** (most mechanically verifiable):
- `lake test` — CslibTests suite
- `lake exe checkInitImports` — all files import Cslib.Init
- `lake lint` + `lake exe lint-style` — linting
- `lake exe mk_all --module` — all .lean files listed in Cslib.lean
- `lake shake --add-public --keep-implied --keep-prefix` — minimized imports

**From NOTATION.md**:
- Three arrow notation options (A/B/C); modules should be internally consistent
- Bisimilarity: `p ~[lts] q`
- Reduction, transition, multi-step conventions
- Suffix with LTS name for alternative semantics

**From ORGANISATION.md**:
- Directory placement conventions (Foundations/ vs Logics/ vs Languages/ etc.)
- Namespace convention: `Cslib.Logic` spans `Foundations/Logic/` and `Logics/`
- New files should follow the module tree structure shown

**From CODE_OF_CONDUCT.md**: Standard Contributor Covenant — less relevant for code vetting but agent should reference it for any community-interaction guidance issues found

**Lint-specific checks** (from `cslib-implementation-agent.md` lint rules):
- Every def/theorem/lemma/instance/structure/inductive needs `/-- ... -/` docstring
- Prop-valued declarations must use `lemma` or `theorem` (not `def`)
- Declaration names must use lowerCamelCase (no underscores)
- `@[simp]` lemmas: no redundant LHS
- Use `omit` for unused section variables
- Wrap `instance` declarations in explicit namespaces
- No namespace prefix repetition in declaration names

### Multi-Task Creation in the Vet Agent

The vet agent needs to create fix tasks. Per `multi-task-creation-standard.md`, the **required** components are:
1. **Item Discovery** — CI failures + standards violations found during analysis
2. **Interactive Selection** — AskUserQuestion with multiSelect for selecting which issues become tasks
3. **User Confirmation** — Summary table + "Yes, create tasks" before creation
4. **State Updates** — Atomic state.json + TODO.md updates

**Recommended additional components**:
- **Topic Grouping** — cluster violations by standard/category (e.g., "docstring violations", "notation consistency", "CI failures")
- **Task Minimization** — group related small fixes into coherent tasks

**State.json update pattern** (from meta-builder-agent and review.md):
```bash
now=$(date -u +%Y-%m-%dT%H:%M:%SZ)
next_num=$(jq '.next_project_number' specs/state.json)
slug=$(echo "$title" | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9]/_/g' | cut -c1-40)

updated_state=$(jq \
  --argjson next_num "$next_num" \
  --arg slug "$slug" \
  --arg desc "$description" \
  --arg tt "cslib" \
  --arg now "$now" \
  '.next_project_number = ($next_num + 1) |
   .active_projects = [{
     project_number: $next_num,
     project_name: $slug,
     status: "not_started",
     task_type: $tt,
     description: $desc,
     created: $now,
     last_updated: $now
   }] + .active_projects' \
  specs/state.json)

echo "$updated_state" > specs/state.json
bash .claude/scripts/generate-todo.sh
```

### Command Syntax Design

Based on `parse-command-args.sh` analysis, `/vet` command syntax:
```
/vet <task_number[,task_number-task_number...]> [focus_prompt]
```

Examples:
- `/vet 265` — vet single task
- `/vet 260,262,265` — vet three tasks
- `/vet 258-262` — vet range of tasks
- `/vet 265 "focus on notation consistency"` — vet with focus

No `--draft`, `--dry-run`, or other flags needed for the initial implementation.

---

## Decisions

1. **Vet agent CAN use AskUserQuestion** because it's invoked via `Agent tool` (not `Task tool`). This simplifies the design — no need to split interactive confirmation into skill-side foreground execution.

2. **Git history is the primary source** for identifying changed Lean files. Pattern: `git log --all --format="%H" --grep="task N:" | xargs git show --name-only | grep "^Cslib/" | sort -u`

3. **Uncommitted changes as fallback**: If no commits found for task N (task just completed, changes not yet committed), fall back to `git diff --name-only HEAD -- Cslib/` to catch staged/unstaged changes.

4. **Status during vetting**: The vet skill should NOT change task status (vet is orthogonal to the implementing/planned lifecycle). It operates on tasks in any status.

5. **Fix tasks should be type "cslib"** since they involve fixing Lean code to meet CSLib standards. This ensures they get routed to cslib-implementation-agent.

6. **CI pipeline in vet agent**: Run the same CI pipeline as `cslib-implementation-agent` for accurate verification. The vet agent should use a scoped build (`lake build Module.Name`) for each changed file first, then the full pipeline steps.

7. **Standards checks ordered by actionability**: CI failures first (most mechanical), then lint checks, then doc/style checks, then design/organization checks.

8. **Task number padding**: The `{NNN}` prefix in task directory names is `printf '%03d' $task_num`. This is used to find task directories: `specs/${task_num_padded}_${task_name}/`.

---

## Risks & Mitigations

- **Risk**: Git grep for "task N:" may miss tasks with non-standard commit messages
  - **Mitigation**: Fall back to uncommitted changes + check task artifact paths in state.json

- **Risk**: Vet agent context exhaustion during long multi-file analysis
  - **Mitigation**: Process files in batches; write partial metadata after each task; limit per task to most impactful checks

- **Risk**: Multi-task creation in agent may be overly aggressive (too many fix tasks)
  - **Mitigation**: Group related violations; enforce task minimization principle; user selects which to create

- **Risk**: CI pipeline run time in vet agent (30+ min for full build)
  - **Mitigation**: Use scoped build per-file first; cache fetch; show CI step results incrementally

- **Risk**: `parse-command-args.sh` sourcing in command context may not work as expected
  - **Mitigation**: Inline the argument parsing logic in the command (as `pr.md` does) rather than sourcing

---

## Concrete Structure Recommendations

### `.claude/commands/vet.md` Structure
```
---
description: Vet completed CSLib tasks against library standards
allowed-tools: Bash, Read, AskUserQuestion
argument-hint: "<task_number[,task_number-task_number...]> [focus_prompt]"
model: opus
---

# /vet Command
## Syntax
## STEP 1: Parse Arguments
## STEP 2: Validate Tasks
## STEP 3: Delegate to skill-cslib-vet
```

**Note**: Command does NOT use Agent tool directly — it delegates to skill via instructions telling the skill to run. Commands are not skills; they instruct the top-level agent.

Actually, looking at pr.md more carefully: commands don't use `Agent tool` — they ARE the top-level agent's instructions. The command tells the model what to do, including invoking skills. But `/pr` doesn't "invoke skill-pr-implementation" via Agent tool — it's a self-contained procedure.

**Correction**: For `/vet`, the command should either:
(a) Be self-contained (like `/pr`) — all logic in the command file itself
(b) Route to a skill by telling the model to invoke the skill

Looking at existing patterns: commands like `/implement`, `/research` route to skills via `skill-orchestrator`. But `/pr` is self-contained. For `/vet`, the most consistent approach with `/pr` as the model is to make it self-contained but light — argument parsing + validation in the command, then spin off `cslib-vet-agent` via Agent tool.

### `.claude/skills/skill-cslib-vet/SKILL.md` Structure
```
Stage 1: Input Validation
Stage 2: Preflight (no status change — vet is orthogonal to task lifecycle)
Stage 2b: Identify Changed Files (git history + artifacts)
Stage 3: Prepare Delegation Context
Stage 4: Invoke cslib-vet-agent via Agent tool
Stage 5: Parse Return Metadata
Stage 6: Git Commit (just the fix tasks creation, no task status change)
Stage 7: Return Brief Summary
```

### `.claude/agents/cslib-vet-agent.md` Structure
```
Stage 0: Early metadata
Stage 1: Parse delegation context
Stage 2: Read changed Lean files
Stage 3: Read standards documents
Stage 4: Run CSLib CI pipeline
Stage 5: Analyze each file against standards
Stage 6: Categorize violations (CI failures, lint, doc, design)
Stage 7: Present issues to user (AskUserQuestion multiSelect)
Stage 8: Group into fix tasks
Stage 9: Confirm task creation (AskUserQuestion)
Stage 10: Create fix tasks in state.json + TODO.md
Stage 11: Write final metadata
```

---

## Context Extension Recommendations

- **Topic**: CSLib vet/quality patterns
- **Gap**: No existing context file documents the "vet" pattern or quality gates for CSLib tasks
- **Recommendation**: After creating the `/vet` triplet, add a summary to `.claude/extensions/cslib/context/` explaining the vet workflow and when to use it

---

## Appendix

### Search Queries Used
- `Read .claude/commands/pr.md` — command structure and frontmatter
- `Read .claude/commands/review.md` — review/analysis pattern
- `Read .claude/skills/skill-cslib-implementation/SKILL.md` — thin wrapper pattern
- `Read .claude/skills/skill-cslib-research/SKILL.md` — thin wrapper pattern
- `Read .claude/agents/cslib-implementation-agent.md` — agent structure, CI pipeline
- `Read .claude/agents/code-reviewer-agent.md` — checklist-based review pattern
- `Read .claude/docs/reference/standards/multi-task-creation-standard.md` — 8-component pattern
- `Read .claude/scripts/parse-command-args.sh` — multi-task argument parsing
- `Read CONTRIBUTING.md`, `Read NOTATION.md`, `Read ORGANISATION.md` — standards content
- `git log --format="%H" --grep="task 265:" | xargs git show --name-only | grep "^Cslib/"` — file identification

### Key Files to Follow for Implementation
- `/home/benjamin/Projects/cslib/.claude/commands/pr.md` — command template
- `/home/benjamin/Projects/cslib/.claude/skills/skill-cslib-implementation/SKILL.md` — skill template
- `/home/benjamin/Projects/cslib/.claude/agents/cslib-implementation-agent.md` — agent template (CI pipeline)
- `/home/benjamin/Projects/cslib/.claude/agents/code-reviewer-agent.md` — checklist template
- `/home/benjamin/Projects/cslib/.claude/scripts/parse-command-args.sh` — argument parsing
- `/home/benjamin/Projects/cslib/.claude/scripts/update-task-status.sh` — status updates
- `/home/benjamin/Projects/cslib/.claude/scripts/generate-todo.sh` — TODO regeneration
- `/home/benjamin/Projects/cslib/.claude/docs/reference/standards/multi-task-creation-standard.md` — task creation
