# Implementation Plan: Document `lake env lean` hazard in CONTRIBUTING.md

- **Task**: 624 - Document that `lake env lean <file>` is unsafe for module-system files and that `lake build <Module.Name>` is the correct single-module build
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/624_document_lake_env_lean_hazard/reports/01_lake-env-lean-hazard-doc-home.md`
- **Artifacts**: plans/01_lake-env-lean-hazard-doc.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: true

## Overview

Add one new `## Building a single file` subsection to `CONTRIBUTING.md`, placed last under
`# Continuous Integration` (immediately after `## Imports`), documenting that bare `lake env lean
<file>` is unsafe on this repository's module-system files and that `lake build <Module.Name>` is
the correct way to build a single module. The same edit must add the matching hand-maintained
Table of Contents entry. This is a documentation-only change confined to one file; definition of
done is the subsection present, the ToC entry present and correctly slugified, and the prose
matching the terse register of the surrounding `## Testing` / `## Imports` subsections.

### Research Integration

The research report confirms the doc home (`CONTRIBUTING.md`'s `# Continuous Integration`
section, lines 97-132), the exact insertion point, the house style, and the required ToC
companion edit. It also supplies the 5-point content shape used verbatim in Phase 1's task list.
All technical claims (the 19+ minute hang, ~101-128% CPU, 1,340,544 KB RSS, the 23.78 s
`--setup` comparison, the dependency-resolution bypass, and the missing-`.olean` artifact) are
sourced from the prior stall investigation's direct measurements and are restated, not re-derived
— the diverging command is never re-run by this task.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (none provided in delegation context).

## Goals & Non-Goals

**Goals**:
- A contributor mid-hang can pattern-match the observed symptom against the doc and immediately
  find the correct command.
- State the rule (`lake env lean <file>` unsafe here; `lake build <Module.Name>` correct) and the
  one-sentence mechanism (`--setup` is never passed by `lake env lean`, always by `lake build`).
- Record the two secondary hazards: stale-`.olean` reuse from bypassed dependency resolution, and
  the fact that a missing `.olean` after such a run is a property of the command line, not
  evidence the module never built.
- Keep `CONTRIBUTING.md` internally consistent by adding the matching ToC entry.

**Non-Goals**:
- Changing any behavior of `lake`, the build scripts, or CI configuration.
- Editing any file other than `CONTRIBUTING.md`.
- Re-running or verifying the diverging command.
- Documenting this caveat in agent-facing context files (out of `file_scope`; noted by research as
  a possible follow-up).
- Reworking the surrounding `# Continuous Integration` subsections.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Subsection over-expands into a warning-banner essay, breaking the file's terse register | M | M | Follow the 5-point content shape below; target 2-4 short paragraphs, comparable in length to `## Imports` |
| ToC companion edit omitted, leaving the file internally inconsistent | M | M | ToC edit is an explicit checklist item in Phase 1 and a Phase 1 verification criterion |
| Implementer cites `scripts/README.md`'s `AxiomCensus.lean` entry as "another instance" of the hazard | M | L | That `lake env lean --run` usage is a distinct, SAFE post-build script invocation; it is explicitly out of scope and must not be referenced |
| Implementer includes the specific hanging invocation as a copy-pasteable "try this" example | M | L | Describe the pattern generically as `lake env lean <file>`; never name a concrete file that hangs |
| ToC anchor mismatch (wrong slugification) makes the new entry a dead link | L | L | Anchor is GitHub-slugified from the heading: `## Building a single file` -> `#building-a-single-file`; verified against the existing sibling entries' pattern |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add `## Building a single file` subsection and ToC entry [NOT STARTED]

**Goal**: `CONTRIBUTING.md` contains a new terse subsection documenting the `lake env lean`
hazard and the correct `lake build <Module.Name>` alternative, with a matching Table of Contents
entry.

**Tasks**:
- [ ] Read `CONTRIBUTING.md` and confirm the current `# Continuous Integration` subsection order
      ends with `## Imports`, and that the ToC `Continuous Integration` block ends with the
      `[Imports](#imports)` line.
- [ ] Insert `  - [Building a single file](#building-a-single-file)` into the ToC immediately
      after the `  - [Imports](#imports)` line, at the same two-space indent as its siblings.
- [ ] Insert a new `## Building a single file` subsection after the final paragraph of
      `## Imports` and before the `# Getting started` heading.
- [ ] Write the subsection following the symptom-first content shape (see Content Shape below),
      in 2-4 short paragraphs matching the register of `## Testing` and `## Imports`.
- [ ] Re-read the edited region to confirm the heading level is `##` (not `###`), commands are in
      inline backticks, and no emoji or warning-banner formatting was introduced.

**Content Shape** (order is load-bearing — symptom first so a contributor mid-hang can match
what they are seeing):

1. **Symptom** — a `lean` process that never finishes and never errors: roughly one core's worth
   of CPU (observed 101-128%), resident memory flat rather than growing (observed pinned at
   ~1.3 GB), no diagnostic output, for many minutes with no observed upper bound (one measured
   run was killed at 19 minutes).
2. **Rule** — name the unsafe command and the correct one in the same sentence: do not run bare
   `lake env lean <file>` on files in this repository; use `lake build <Module.Name>` to build a
   single module.
3. **Mechanism, one sentence** — `lake build` always passes `--setup`; `lake env lean` never
   does, and without it Lean's module system lacks the `module` / `public import` exposure
   configuration, which is what causes elaboration to diverge. For contrast, the same invocation
   with `--setup` completes in well under a minute.
4. **Secondary hazards, briefly** — it bypasses dependency resolution, so it can silently consume
   stale `.olean` files; and without an explicit `-o` it never writes an `.olean` at all, so a
   missing `.olean` after such a run says nothing about whether the module ever built.
5. **Escape hatch, one line (optional)** — if raw `lean` output is genuinely required, the safe
   form is `lake env lean --setup <module>.setup.json <file>`, where the setup JSON lives under
   `.lake/build/ir/` after a build.

**Explicitly do NOT**:
- Cite `scripts/README.md`'s `AxiomCensus.lean` entry or its `lake env lean --run` usage — that is
  a distinct, safe post-build script invocation and must not be conflated with this hazard.
- Include a concrete, copy-pasteable invocation that is known to hang.
- Run any `lake env lean` command as part of implementing or verifying this phase.

**Timing**: 20-30 minutes

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: This phase asserts that `CONTRIBUTING.md` is the only file modified, that
the ToC `Continuous Integration` block currently ends with the `[Imports](#imports)` line, and
that `## Imports` is the last subsection before `# Getting started`. Confirm at implementation
time by reading `CONTRIBUTING.md` before editing; if the surrounding structure has changed,
adjust the insertion point to keep the new subsection last under `# Continuous Integration` and
the ToC entry adjacent to its siblings, and record the deviation in the summary.

**Files to modify**:
- `CONTRIBUTING.md` - add one ToC line in the `Continuous Integration` block; add one new
  `## Building a single file` subsection at the end of the `# Continuous Integration` section

**Verification**:
- `grep -n "^## Building a single file" CONTRIBUTING.md` returns exactly one match, positioned
  after the `## Imports` heading and before the `# Getting started` heading.
- `grep -n "Building a single file" CONTRIBUTING.md` returns exactly two matches: the ToC entry
  and the heading.
- The ToC entry reads `  - [Building a single file](#building-a-single-file)` and sits directly
  after the `  - [Imports](#imports)` line.
- `git diff --stat` shows `CONTRIBUTING.md` as the only modified file.
- Diff read-through confirms every changed hunk is prose/markdown with no compile surface
  (prose-tier check).
- The subsection names both `lake env lean <file>` and `lake build <Module.Name>`, and mentions
  `--setup`.
- The subsection does not mention `AxiomCensus`, and contains no concrete file path that would
  reproduce the hang.

---

## Testing & Validation

- [ ] `CONTRIBUTING.md` is the only file changed.
- [ ] New subsection present, at `##` level, last under `# Continuous Integration`.
- [ ] ToC entry present, correctly indented, correctly slugified as `#building-a-single-file`.
- [ ] Prose covers all five content-shape points in order (symptom, rule, mechanism, secondary
      hazards, optional escape hatch).
- [ ] Length and register comparable to the adjacent `## Testing` / `## Imports` subsections
      (2-4 short paragraphs; no tables, no banners, no emoji).
- [ ] No `lake env lean` command was executed during implementation or verification.
- [ ] No `AxiomCensus.lean` reference introduced.

## Artifacts & Outputs

- `CONTRIBUTING.md` (modified — one new subsection plus one new ToC line)
- `specs/624_document_lake_env_lean_hazard/summaries/01_lake-env-lean-hazard-doc-summary.md`

## Rollback/Contingency

Single-file, additive markdown change. To revert: `git checkout HEAD -- CONTRIBUTING.md` (or
revert the task's commit). No build state, generated file, or downstream artifact depends on this
edit, so rollback has no side effects.
