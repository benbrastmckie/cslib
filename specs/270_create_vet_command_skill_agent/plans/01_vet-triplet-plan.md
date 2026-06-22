# Implementation Plan: Create /vet Command-Skill-Agent Triplet

- **Task**: 270 - Create /vet command-skill-agent triplet for the cslib extension
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/270_create_vet_command_skill_agent/reports/01_vet-command-patterns.md
- **Artifacts**: plans/01_vet-triplet-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

Create the `/vet` command-skill-agent triplet for the cslib extension. This adds a quality-gate command that vets completed CSLib tasks against CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, and CODE_OF_CONDUCT.md standards. The command parses multi-task arguments, the skill validates inputs and prepares delegation context, and the agent reads changed files, runs the CSLib CI pipeline, categorizes violations, and creates scoped fix tasks via interactive selection. All three files follow established patterns: `pr.md` for the command, `skill-cslib-implementation/SKILL.md` for the skill, and `cslib-implementation-agent.md` + `meta-builder-agent.md` for the agent.

### Research Integration

Key findings from the research report (01_vet-command-patterns.md):
- The vet agent CAN use AskUserQuestion directly since it is invoked via Agent tool (not Task tool), simplifying the design
- Git history extraction via `git log --grep="task N:"` reliably identifies changed Lean files (verified against task 265)
- The four standards documents have clear, enumerable checks: CI compliance, doc style, proof style, notation conventions, directory organization
- Multi-task creation must follow the 8-component pattern from multi-task-creation-standard.md
- The vet command should NOT change task status since vetting is orthogonal to the implementing/planned lifecycle

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No direct roadmap items advanced. This is a meta/tooling task that supports the broader CSLib porting effort by providing a quality gate for completed work.

## Goals & Non-Goals

**Goals**:
- Create `.claude/commands/vet.md` accepting multi-task syntax with optional focus prompt
- Create `.claude/skills/skill-cslib-vet/SKILL.md` as a thin wrapper that validates tasks, identifies changed files, and delegates to the agent
- Create `.claude/agents/cslib-vet-agent.md` that reads changed files, runs CI, checks against all four standards, categorizes violations, and creates fix tasks with user confirmation
- Follow established command/skill/agent patterns for consistency

**Non-Goals**:
- Registering the vet command in extension manifests or routing tables (separate follow-up)
- Creating hard-mode (`--hard`) variants of the vet skill/agent
- Updating CLAUDE.md merge-sources or documentation (auto-generated from extensions)
- Adding automated CI integration (vet is a manual quality gate)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Agent context exhaustion when vetting many files across multiple tasks | H | M | Process files in batches; limit scope to Lean files changed by the task; recommend vetting 1-3 tasks at a time |
| Git grep for "task N:" misses tasks with non-standard commit messages | M | L | Fall back to uncommitted changes + check task artifact paths in state.json |
| CI pipeline run time (30+ min for full build) slows vet cycle | M | M | Use scoped `lake build Module.Name` per file first; full pipeline only for final verification |
| Fix task creation may be overly granular (too many small tasks) | L | M | Group related violations by category; enforce task minimization principle; user controls selection |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Create Command File [COMPLETED]

**Goal**: Create `.claude/commands/vet.md` following the `pr.md` command pattern.

**Tasks**:
- [ ] Read `.claude/commands/pr.md` in full for command frontmatter and step structure
- [ ] Read `.claude/scripts/parse-command-args.sh` for multi-task argument parsing interface
- [ ] Create `.claude/commands/vet.md` with the following structure:
  - Frontmatter: `description`, `allowed-tools` (Bash, Read, AskUserQuestion), `argument-hint`, `model: opus`
  - STEP 1: Parse arguments using `parse-command-args.sh` sourcing pattern to extract TASK_NUMBERS and FOCUS_PROMPT
  - STEP 2: Validate each task number exists in state.json; verify task type is "cslib" or has Lean file changes
  - STEP 3: Invoke `skill-cslib-vet` via Skill tool with task numbers, focus prompt, and session ID
- [ ] Verify command file has correct frontmatter fields and imperative step structure

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `.claude/commands/vet.md` - Create new command file (~80-120 lines)

**Verification**:
- File exists with valid YAML frontmatter
- Contains STEP 1/2/3 matching the `pr.md` imperative pattern
- Uses `parse-command-args.sh` for argument parsing
- Task validation loop matches existing patterns from `pr.md`

---

### Phase 2: Create Skill File [COMPLETED]

**Goal**: Create `.claude/skills/skill-cslib-vet/SKILL.md` as a thin delegation wrapper following the `skill-cslib-implementation` pattern.

**Tasks**:
- [ ] Read `.claude/skills/skill-cslib-implementation/SKILL.md` in full for the complete stage structure
- [ ] Create directory `.claude/skills/skill-cslib-vet/`
- [ ] Create `.claude/skills/skill-cslib-vet/SKILL.md` with the following stages:
  - Frontmatter: `name: skill-cslib-vet`, `description`, `allowed-tools: Agent, Bash, Edit, Read, Write`
  - Stage 1: Input Validation -- verify task exists, extract task metadata from state.json
  - Stage 2: Preflight -- no status change (vet is orthogonal to task lifecycle), but generate session_id if not passed
  - Stage 2b: Identify Changed Files -- use `git log --all --format="%H" --grep="task N:" | xargs -I{} git show --name-only {} | grep "^Cslib/" | sort -u` for each task number; fall back to `git diff --name-only HEAD -- Cslib/` for uncommitted changes; also extract artifact paths from state.json
  - Stage 3: Prepare Delegation Context -- include session_id, task_numbers, task_names, changed_files map, standards_paths (CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, CODE_OF_CONDUCT.md), focus_prompt, cslib_dir, metadata_file_path
  - Stage 4: Invoke cslib-vet-agent via Agent tool with subagent_type
  - Stage 4b: Self-Execution Fallback -- write .return-meta.json if Agent tool was not used
  - Postflight stages (5-9): Parse metadata, git commit fix task creation if any, return brief summary
- [ ] Ensure postflight does NOT change task status (vet is read-only with respect to the vetted task)
- [ ] Verify SKILL.md matches the thin-wrapper pattern: all domain logic is in the agent

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `.claude/skills/skill-cslib-vet/SKILL.md` - Create new skill file (~150-200 lines)

**Verification**:
- File exists with valid frontmatter matching skill-cslib-implementation pattern
- All stages (1 through 9) are present
- Delegation context includes all four standards paths
- Changed files identification uses git history + fallback
- Postflight does not update vetted task status
- Self-execution fallback (Stage 4b) is present

---

### Phase 3: Create Agent File [COMPLETED]

**Goal**: Create `.claude/agents/cslib-vet-agent.md` that performs standards checking and creates fix tasks with interactive user confirmation.

**Tasks**:
- [ ] Read `.claude/agents/cslib-implementation-agent.md` in full for CI pipeline steps and agent structure
- [ ] Read `.claude/agents/meta-builder-agent.md` for multi-task creation pattern, AskUserQuestion usage, and state.json update pattern
- [ ] Read `.claude/docs/reference/standards/multi-task-creation-standard.md` for the 8-component standard
- [ ] Create `.claude/agents/cslib-vet-agent.md` with the following structure:
  - Frontmatter: `name: cslib-vet-agent`, `description`, `model: sonnet`
  - Overview section explaining the agent's purpose and return format
  - BLOCKED TOOLS table (same as cslib-implementation-agent: lean_diagnostic_messages, lean_file_outline)
  - Allowed Tools section (Read, Write, Edit, Bash, Glob, Grep, AskUserQuestion)
  - Stage 0: Early metadata -- write `in_progress` status to `.return-meta.json`
  - Stage 1: Parse delegation context -- extract task_numbers, changed_files, standards_paths, focus_prompt
  - Stage 2: Read changed Lean files -- batch-read all files identified by the skill
  - Stage 3: Read standards documents -- read CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, CODE_OF_CONDUCT.md
  - Stage 4: Run CSLib CI pipeline -- for each changed file, run scoped `lake build`; then run full pipeline (`lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`)
  - Stage 5: Analyze files against standards -- check each file for:
    - CONTRIBUTING.md: doc comments on all declarations, proof readability, typeclass notation usage, AI disclosure, CI compliance (commit title format)
    - NOTATION.md: arrow notation consistency (A/B/C), bisimilarity format, reduction/transition conventions
    - ORGANISATION.md: correct directory placement per module tree, namespace conventions
    - CODE_OF_CONDUCT.md: community guidelines (light check, mostly for documentation artifacts)
    - Lint rules: lowerCamelCase names, Prop-valued = lemma/theorem, @[simp] LHS check, docstrings, omit for unused vars, instance namespace wrapping
  - Stage 6: Categorize violations -- group issues by category (CI failures, lint violations, documentation gaps, notation inconsistencies, organization issues); assign severity (Critical/High/Medium/Low)
  - Stage 7: Present issues to user -- display categorized issues table; use AskUserQuestion with multiSelect for selecting which issues to create as fix tasks; empty selection = no tasks created
  - Stage 8: Group selected issues into fix tasks -- apply task minimization principle; cluster related violations into coherent tasks (e.g., "fix docstring gaps in Modal/Semantics/" not one task per file); set task_type to "cslib" for all fix tasks
  - Stage 9: Confirm task creation -- show summary table of proposed tasks with descriptions; use AskUserQuestion for final "Yes, create tasks" / "No, cancel" confirmation
  - Stage 10: Create fix tasks -- for each confirmed task: increment next_project_number in state.json, create task entry with slug, description, status "not_started", task_type "cslib"; regenerate TODO.md via generate-todo.sh
  - Stage 11: Write final metadata -- write `.return-meta.json` with status, artifacts (fix tasks created), and metadata
- [ ] Ensure AskUserQuestion usage follows the multi-task creation standard (multiSelect with options array, not text-based choices)
- [ ] Include the MUST NOT constraints section (no direct Lean edits, no status changes to vetted tasks)

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `.claude/agents/cslib-vet-agent.md` - Create new agent file (~300-400 lines)

**Verification**:
- File exists with valid frontmatter (name, description, model)
- All 12 stages (0-11) are present and complete
- BLOCKED TOOLS table matches cslib-implementation-agent
- CI pipeline steps match the CSLib verification pipeline
- Standards checks cover all four documents with specific, enumerable criteria
- Multi-task creation follows the 8-component standard (discovery, selection, confirmation, state updates)
- AskUserQuestion used with options array for all user choices
- Task minimization principle enforced in grouping stage
- Fix tasks set to task_type "cslib"

---

## Testing & Validation

- [ ] All three files exist at correct paths
- [ ] Command frontmatter is valid YAML with required fields
- [ ] Skill frontmatter matches established pattern (name, description, allowed-tools)
- [ ] Agent frontmatter includes model field
- [ ] Cross-references are consistent: command references skill name, skill references agent type, agent references metadata path pattern
- [ ] Git history extraction command is correct: `git log --all --format="%H" --grep="task N:" | xargs -I{} git show --name-only {} | grep "^Cslib/" | sort -u`
- [ ] CI pipeline commands match cslib-implementation-agent: lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake
- [ ] Multi-task creation follows the 8-component standard from multi-task-creation-standard.md

## Artifacts & Outputs

- `.claude/commands/vet.md` - Command file (~80-120 lines)
- `.claude/skills/skill-cslib-vet/SKILL.md` - Skill file (~150-200 lines)
- `.claude/agents/cslib-vet-agent.md` - Agent file (~300-400 lines)

## Rollback/Contingency

All three files are new creations (no existing files modified). Rollback is simply deleting the three files:
```bash
rm -f .claude/commands/vet.md
rm -rf .claude/skills/skill-cslib-vet/
rm -f .claude/agents/cslib-vet-agent.md
```

No state.json changes, no status transitions, no existing code modifications.
