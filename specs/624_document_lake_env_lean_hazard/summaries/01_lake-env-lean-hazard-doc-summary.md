# Implementation Summary: Task #624

- **Task**: 624 - Document that `lake env lean <file>` is unsafe for module-system files and that `lake build <Module.Name>` is the correct single-module build
- **Status**: [COMPLETED]
- **Started**: 2026-08-10
- **Completed**: 2026-08-10
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_lake-env-lean-hazard-doc.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Added a new `## Building a single file` subsection to `CONTRIBUTING.md`, placed last under the
`# Continuous Integration` section (immediately after `## Imports`), together with the matching
hand-maintained Table of Contents entry. The subsection documents that bare `lake env lean <file>`
is unsafe on this repository's module-system files and that `lake build <Module.Name>` is the
correct way to build a single module.

## What Changed

- `CONTRIBUTING.md` — Added one ToC line (`  - [Building a single file](#building-a-single-file)`)
  after the `[Imports]` entry, and one new `## Building a single file` subsection (3 short
  paragraphs) after `## Imports` and before `# Getting started`.

## Decisions

- Followed the plan's Scope Hypothesis exactly: confirmed before editing that the `# Continuous
  Integration` subsection order ended with `## Imports` and the ToC block ended with
  `[Imports](#imports)` — no deviation needed.
- Content covers all five points from the plan's Content Shape in order: symptom first (flat
  CPU/RSS, no diagnostic output, no observed upper bound), the rule (`lake env lean <file>` unsafe
  / `lake build <Module.Name>` correct), the one-sentence `--setup` mechanism, the two secondary
  hazards (stale `.olean` reuse; missing `.olean` is a property of the command line, not evidence
  the module never built), and the optional one-line safe escape hatch
  (`lake env lean --setup <module>.setup.json <file>`).
- Did not name a concrete file or write a copy-pasteable hanging invocation, per the binding
  "do NOT" items from research/plan.
- Did not reference `scripts/README.md`'s `AxiomCensus.lean` / `lake env lean --run` usage, which
  is a distinct, safe post-build script invocation.
- Did not run any `lake env lean` command during implementation or verification.

## Plan Deviations

- None (implementation followed plan)

## Verification

- Build: N/A (documentation-only change)
- Tests: N/A
- Files verified: Yes — `grep -n "^## Building a single file" CONTRIBUTING.md` returns exactly one
  match; `grep -n "Building a single file" CONTRIBUTING.md` returns exactly two matches (ToC entry
  + heading); `git diff --stat -- CONTRIBUTING.md` confirms the file changed with no other
  unrelated hunks; diff read-through confirms both hunks are prose/markdown only; `grep -n
  AxiomCensus CONTRIBUTING.md` returns no match; subsection names both `lake env lean <file>` and
  `lake build <Module.Name>`, and mentions `--setup`.

## Impacts

- Contributors mid-hang on a `lake env lean <file>` invocation now have a documented,
  symptom-first diagnostic path in `CONTRIBUTING.md` pointing them to `lake build <Module.Name>`.

## Follow-ups

- The research report notes this caveat may also belong in agent-facing Lean/CSLib tooling
  context (out of this task's `file_scope`); left as a possible future task, not created here per
  current context-gap policy.

## References

- `specs/624_document_lake_env_lean_hazard/plans/01_lake-env-lean-hazard-doc.md`
- `specs/624_document_lake_env_lean_hazard/reports/01_lake-env-lean-hazard-doc-home.md`
- `CONTRIBUTING.md`
