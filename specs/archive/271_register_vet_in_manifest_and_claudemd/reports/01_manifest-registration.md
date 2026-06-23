# Research Report: Task #271

**Task**: 271 - Register /vet command-skill-agent in cslib extension manifest and CLAUDE.md
**Started**: 2026-06-22T00:00:00Z
**Completed**: 2026-06-22T00:05:00Z
**Effort**: ~30 min (straightforward registration edits)
**Dependencies**: Task 270 (completed — files exist)
**Sources/Inputs**: Codebase (manifest.json, CLAUDE.md, vet.md, SKILL.md, cslib-vet-agent.md)
**Artifacts**: - specs/271_register_vet_in_manifest_and_claudemd/reports/01_manifest-registration.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Three files exist from task 270: `.claude/commands/vet.md`, `.claude/skills/skill-cslib-vet/SKILL.md`, `.claude/agents/cslib-vet-agent.md`
- Two files need edits: `.claude/extensions/cslib/manifest.json` and `.claude/CLAUDE.md`
- No routing entry is needed — `/vet` is a standalone command, not routed through `/research`/`/plan`/`/implement`
- Exact insertion points and values are identified below

---

## Context & Scope

Task 270 created the `/vet` command triplet. Task 271 registers it in the extension manifest
and CLAUDE.md so the system knows about the new agent/skill/command. This is a meta-level
registration task — no new functionality is added, just two files updated.

**Note on EXTENSION.md**: The manifest references `EXTENSION.md` as the source for the
`extension_cslib` section in CLAUDE.md (`merge_targets.claudemd.source = "EXTENSION.md"`),
but this file does not exist in `.claude/extensions/cslib/`. The CSLib Extension section in
CLAUDE.md is managed directly. CLAUDE.md is the implementation target.

---

## Findings

### 1. Files Created by Task 270

#### `.claude/commands/vet.md` (frontmatter)
```yaml
description: Vet completed CSLib tasks against library standards (CONTRIBUTING.md, NOTATION.md, ORGANISATION.md, CODE_OF_CONDUCT.md), run the CI pipeline, and create fix tasks for violations found.
allowed-tools: Bash, Read, AskUserQuestion
argument-hint: "<task_number[,task_number-task_number...]> [focus_prompt]"
model: opus
```

**Filename to register**: `vet.md`

#### `.claude/skills/skill-cslib-vet/SKILL.md` (frontmatter)
```yaml
name: skill-cslib-vet
description: Vet completed CSLib tasks against library standards. Invoke for /vet command.
allowed-tools: Agent, Bash, Edit, Read, Write
```

**Skill name to register**: `skill-cslib-vet`

#### `.claude/agents/cslib-vet-agent.md` (frontmatter)
```yaml
name: cslib-vet-agent
description: Vet CSLib tasks against library standards, run CI pipeline, and create fix tasks with interactive user confirmation
model: sonnet
```

**Agent filename to register**: `cslib-vet-agent.md`

---

### 2. manifest.json — Current Structure and Insertion Points

**File**: `.claude/extensions/cslib/manifest.json`

**Current `provides.agents` array (lines 12-19)**:
```json
"agents": [
  "cslib-research-agent.md",
  "cslib-implementation-agent.md",
  "cslib-research-hard-agent.md",
  "cslib-implementation-hard-agent.md",
  "pr-review-research-agent.md",
  "pr-review-implementation-agent.md"
],
```

**Insertion**: Append `"cslib-vet-agent.md"` as the 7th element (after `"pr-review-implementation-agent.md"`).

**Current `provides.skills` array (lines 20-28)**:
```json
"skills": [
  "skill-cslib-research",
  "skill-cslib-implementation",
  "skill-pr-implementation",
  "skill-cslib-research-hard",
  "skill-cslib-implementation-hard",
  "skill-pr-review-research",
  "skill-pr-review-implementation"
],
```

**Insertion**: Append `"skill-cslib-vet"` as the 8th element (after `"skill-pr-review-implementation"`).

**Current `provides.commands` (line 29)**:
```json
"commands": ["pr.md"],
```

**Insertion**: Add `"vet.md"` as the 2nd element, giving `["pr.md", "vet.md"]`.

**No routing entry needed**: `/vet` is invoked directly as a command, not through the
`/research`/`/plan`/`/implement` routing mechanism. The `routing` and `routing_hard` blocks
in manifest.json are for cslib and pr task types only. `/vet` is a standalone command.

---

### 3. CLAUDE.md — Current CSLib Section and Insertion Points

**Section header**: `## CSLib Extension`

#### Skill-Agent Mapping Table

**Current table** (in the CSLib Extension section):

| Skill | Agent | Model | Purpose |
|-------|-------|-------|---------|
| skill-cslib-research | cslib-research-agent | opus | CSLib formalization research with lean-lsp MCP |
| skill-cslib-implementation | cslib-implementation-agent | sonnet | CSLib proof implementation with CI verification |
| skill-pr-implementation | cslib-implementation-agent | sonnet | PR description preparation only -- produces pr-description.md, transitions task to [PR READY]; branch creation and CI handled by /pr |
| skill-cslib-research-hard | cslib-research-hard-agent | opus | Hard-mode CSLib research: adversarial verification (H4), BibKey citation grounding (H3) |
| skill-cslib-implementation-hard | cslib-implementation-hard-agent | sonnet | Hard-mode CSLib proof implementation: anti-analysis (H2), sorry_inventory (H9), territory (H7) |
| skill-pr-review-research | pr-review-research-agent | sonnet | Fetch and synthesize GitHub PR and Zulip discussion for review tasks |
| skill-pr-review-implementation | pr-review-implementation-agent | sonnet | Compose pr-response.md and zulip-response.md for pr-type review tasks; falls back to legacy pr-description workflow when sources are absent |

**Row to append** (after `skill-pr-review-implementation` row):
```
| skill-cslib-vet | cslib-vet-agent | sonnet | Vet CSLib tasks against library standards, run CI pipeline, and create fix tasks with interactive user confirmation |
```

#### Commands Table

**Current table** (at end of CSLib Extension section):

| Command | Usage | Description |
|---------|-------|-------------|
| `/pr` | `/pr <task_number\|path\|description> [--draft] [--dry-run]` | Submit CSLib PR: create branch, run CI, create PR on leanprover/cslib (user-only) |
| `/pr` | `/pr --review <sources...>` | Create pr-type review task from GitHub PR URLs, Zulip URLs, or descriptions |
| `/pr` | `/pr N` (when task is [PR READY] with sources) | Push changes, post GitHub PR comment, optionally send Zulip message |

**Row to append** (after the last `/pr` row):
```
| `/vet` | `/vet <task_number[,task_number-task_number...]> [focus_prompt]` | Vet completed CSLib tasks against library standards and CI; create fix tasks for violations found |
```

---

## Decisions

- **No routing entry in manifest.json**: `/vet` is a standalone command, not a task-type-routed skill. The `routing` block maps task_type strings (cslib, pr) to skills for `/research`/`/plan`/`/implement` commands only. `/vet` invokes `skill-cslib-vet` directly from the command file.
- **Append position**: New entries go at the end of each array/table to preserve existing order.
- **Model for agent**: `sonnet` (confirmed from cslib-vet-agent.md frontmatter).
- **CLAUDE.md is the direct target**: The `EXTENSION.md` merge source referenced in manifest.json does not exist; CLAUDE.md is edited directly.

---

## Exact Edit Specifications

### Edit 1: manifest.json — agents array

**File**: `/home/benjamin/Projects/cslib/.claude/extensions/cslib/manifest.json`

**Old string** (lines 18-19):
```
      "pr-review-implementation-agent.md"
    ],
```

**New string**:
```
      "pr-review-implementation-agent.md",
      "cslib-vet-agent.md"
    ],
```

### Edit 2: manifest.json — skills array

**File**: `/home/benjamin/Projects/cslib/.claude/extensions/cslib/manifest.json`

**Old string** (lines 27-28):
```
      "skill-pr-review-implementation"
    ],
```

**New string**:
```
      "skill-pr-review-implementation",
      "skill-cslib-vet"
    ],
```

### Edit 3: manifest.json — commands array

**File**: `/home/benjamin/Projects/cslib/.claude/extensions/cslib/manifest.json`

**Old string** (line 29):
```
    "commands": ["pr.md"],
```

**New string**:
```
    "commands": ["pr.md", "vet.md"],
```

### Edit 4: CLAUDE.md — Skill-Agent Mapping row

**File**: `/home/benjamin/Projects/cslib/.claude/CLAUDE.md`

**Old string** (last row of cslib Skill-Agent Mapping table):
```
| skill-pr-review-implementation | pr-review-implementation-agent | sonnet | Compose pr-response.md and zulip-response.md for pr-type review tasks; falls back to legacy pr-description workflow when sources are absent |
```

**New string** (append new row):
```
| skill-pr-review-implementation | pr-review-implementation-agent | sonnet | Compose pr-response.md and zulip-response.md for pr-type review tasks; falls back to legacy pr-description workflow when sources are absent |
| skill-cslib-vet | cslib-vet-agent | sonnet | Vet CSLib tasks against library standards, run CI pipeline, and create fix tasks with interactive user confirmation |
```

### Edit 5: CLAUDE.md — Commands table row

**File**: `/home/benjamin/Projects/cslib/.claude/CLAUDE.md`

**Old string** (last row of cslib Commands table):
```
| `/pr` | `/pr N` (when task is [PR READY] with sources) | Push changes, post GitHub PR comment, optionally send Zulip message |
```

**New string** (append new row):
```
| `/pr` | `/pr N` (when task is [PR READY] with sources) | Push changes, post GitHub PR comment, optionally send Zulip message |
| `/vet` | `/vet <task_number[,task_number-task_number...]> [focus_prompt]` | Vet completed CSLib tasks against library standards and CI; create fix tasks for violations found |
```

---

## Risks & Mitigations

- **CLAUDE.md is auto-generated**: The file header warns "Do not edit directly." However, the
  merge source `EXTENSION.md` does not exist for the cslib extension, so the section is managed
  manually. This is consistent with how the `/pr` command and existing cslib entries were added.
  Risk is low — the edit is additive and append-only.
- **Exact match required for Edit tool**: The old_string values above include sufficient context
  to be unique in each file.

---

## Appendix

### Files Read
- `.claude/extensions/cslib/manifest.json`
- `.claude/CLAUDE.md` (via system-reminder context)
- `.claude/commands/vet.md`
- `.claude/skills/skill-cslib-vet/SKILL.md`
- `.claude/agents/cslib-vet-agent.md`

### Key Values Extracted
| Field | Value |
|-------|-------|
| Agent filename | `cslib-vet-agent.md` |
| Agent name | `cslib-vet-agent` |
| Agent model | `sonnet` |
| Skill name | `skill-cslib-vet` |
| Command filename | `vet.md` |
| Command syntax | `/vet <task_number[,task_number-task_number...]> [focus_prompt]` |
