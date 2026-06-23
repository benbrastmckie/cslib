# Implementation Plan: Register /vet in cslib manifest and CLAUDE.md

- **Task**: 271 - Register /vet command-skill-agent in cslib extension manifest and CLAUDE.md
- **Status**: [COMPLETED]
- **Effort**: 0.25 hours
- **Dependencies**: Task 270 (completed -- files exist)
- **Research Inputs**: specs/271_register_vet_in_manifest_and_claudemd/reports/01_manifest-registration.md
- **Artifacts**: plans/01_register-vet-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

Register the existing /vet command-skill-agent triplet (created by task 270) in the cslib extension manifest and CLAUDE.md. This is a purely mechanical registration task: 5 append-only edits across 2 files, with JSON validation as the only verification step.

### Research Integration

The research report at `reports/01_manifest-registration.md` provides exact old_string/new_string pairs for all 5 edits, including verified line numbers and insertion points in both `manifest.json` and `CLAUDE.md`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items are directly advanced by this registration task.

## Goals & Non-Goals

**Goals**:
- Register `cslib-vet-agent.md` in manifest.json `provides.agents`
- Register `skill-cslib-vet` in manifest.json `provides.skills`
- Register `vet.md` in manifest.json `provides.commands`
- Add skill-cslib-vet / cslib-vet-agent row to CLAUDE.md CSLib Skill-Agent Mapping table
- Add /vet row to CLAUDE.md CSLib Commands table

**Non-Goals**:
- Adding routing entries (not needed -- /vet is a standalone command)
- Modifying EXTENSION.md (does not exist for cslib extension)
- Creating or modifying the /vet command, skill, or agent files (already done in task 270)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| manifest.json becomes invalid JSON after edit | H | L | Verify with `jq empty` after edits |
| Edit tool fails on non-unique old_string | M | L | Research report verified uniqueness of all insertion points |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Apply all registration edits [IN PROGRESS]

**Goal**: Register /vet triplet in manifest.json and CLAUDE.md

**Tasks**:
- [ ] Edit 1: Append `"cslib-vet-agent.md"` to `provides.agents` array in manifest.json
- [ ] Edit 2: Append `"skill-cslib-vet"` to `provides.skills` array in manifest.json
- [ ] Edit 3: Add `"vet.md"` to `provides.commands` array in manifest.json
- [ ] Edit 4: Append skill-cslib-vet row to CSLib Skill-Agent Mapping table in CLAUDE.md
- [ ] Edit 5: Append /vet row to CSLib Commands table in CLAUDE.md
- [ ] Verify manifest.json is valid JSON with `jq empty`

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `.claude/extensions/cslib/manifest.json` - Add agent, skill, command to provides arrays
- `.claude/CLAUDE.md` - Add rows to Skill-Agent Mapping and Commands tables

**Verification**:
- `jq empty .claude/extensions/cslib/manifest.json` exits 0 (valid JSON)
- `grep "cslib-vet-agent.md" .claude/extensions/cslib/manifest.json` returns match
- `grep "skill-cslib-vet" .claude/extensions/cslib/manifest.json` returns match
- `grep "vet.md" .claude/extensions/cslib/manifest.json` returns match (in commands array)
- `grep "skill-cslib-vet" .claude/CLAUDE.md` returns match in CSLib section

## Testing & Validation

- [ ] `jq empty .claude/extensions/cslib/manifest.json` succeeds (valid JSON)
- [ ] manifest.json contains `cslib-vet-agent.md` in agents array
- [ ] manifest.json contains `skill-cslib-vet` in skills array
- [ ] manifest.json contains `vet.md` in commands array
- [ ] CLAUDE.md CSLib Skill-Agent Mapping table contains skill-cslib-vet row
- [ ] CLAUDE.md CSLib Commands table contains /vet row

## Artifacts & Outputs

- `plans/01_register-vet-plan.md` (this file)
- Modified: `.claude/extensions/cslib/manifest.json`
- Modified: `.claude/CLAUDE.md`

## Rollback/Contingency

Revert both files with `git checkout -- .claude/extensions/cslib/manifest.json .claude/CLAUDE.md`.
