# Research Report: Task #624

**Task**: 624 - Document that lake env lean skips --setup and is unsafe for module-system files
**Started**: 2026-08-10
**Completed**: 2026-08-10
**Effort**: Small (single markdown subsection, ~15-25 lines)
**Dependencies**: None
**Sources/Inputs**:
- `CONTRIBUTING.md` (full read, 328 lines)
- `specs/622_investigate_scheme_build_stall/reports/01_scheme-build-stall-root-cause.md` (prior task's direct measurements — the technical source of truth for this task; this report does NOT re-run the diverging command)
- `scripts/README.md` (style precedent for tooling-hazard prose)
- `docs/` directory survey (ruled out as doc home)
**Artifacts**:
- This report
**Standards**: report-format.md, subagent-return.md, no-task-references-in-deliverables.md

## Executive Summary

- **Doc home confirmed**: `CONTRIBUTING.md`'s `# Continuous Integration` section is the right
  home. It already documents every other "how to run CSLib's checks locally" command (`lake
  test`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake exe mk_all`,
  `lake shake`). No other candidate location (`docs/`, `scripts/README.md`, `README.md`) hosts
  contributor build-workflow guidance — `docs/` holds two unrelated deep-dive documents
  (lint-suppression policy, a modal-axiom-schema architecture note), not build-tooling guidance.
- **Insertion point**: a new `##`-level subsection after the existing `## Imports` subsection
  and before `# Getting started` (i.e., the last subsection of `# Continuous Integration`),
  matching the existing subsection list: Pull Request Titles, Testing, Linting, Imports, **+ new
  subsection**.
- **House style**: terse, 2-4 sentence paragraphs, backtick-quoted commands, no headers deeper
  than `##` inside this section, links via `[text](/Path)`-style repo-relative or bare backticks
  for commands — matches the "Testing" and "Imports" subsections' register exactly.
- **Technical claims verified**: every claim in the task description is independently
  corroborated by task 622's direct-measurement report (row-by-row timed reproduction at
  `HEAD=b83ae232`), which is the authoritative source for the numbers. This report does not
  re-run the diverging command (per task instructions) — it cites the prior measurement instead.
  All figures (19+ min hang / 101-128% CPU / 1,340,544 KB RSS / 23.78 s with `--setup`) are the
  ones already published in that report and require no restatement or independent verification
  beyond confirming internal consistency, which holds.
- **Required update alongside the new subsection**: the Table of Contents at the top of
  `CONTRIBUTING.md` is a manually maintained anchor list (lines 3-41) and must gain one new entry
  under the `Continuous Integration` block, or the new subsection will be invisible to the ToC.

## Context & Scope

The task is documentation-only, scoped to `CONTRIBUTING.md` (per `file_scope` in the delegation
context). The job is to place a short, symptom-first subsection stating: (1) the rule (`lake env
lean <file>` is unsafe for module-system files here), (2) the failure signature (what a
contributor mid-hang will observe), and (3) the correct alternative (`lake build
<Module.Name>`). No code changes, no re-running of the diverging command — its behavior is
already established and documented by task 622's report.

## Findings

### Codebase Patterns

**`CONTRIBUTING.md` structure** (328 lines, ToC at top mirrors the heading tree):

```
# Contributing to CSLib
# Contribution model
# The role of AI
# Style and documentation
  ## Variable names
  ## Proof style and golfing :golf:
  ## Notation
  ## Documentation
# Design principles
  ## Reuse
# Continuous Integration
  ## Pull Request Titles
  ## Testing
  ## Linting
  ## Imports
# Getting started
  ...
```

`# Continuous Integration` (lines 97-132) is explicitly introduced as: *"There are a number of
checks that run in continuous integration. Here is a brief guide that includes instructions on
how to run these locally."* This is precisely the genre of content the task needs: a
locally-runnable command with a short explanation of what it does and why it matters. The
`## Testing` and `## Imports` subsections are the closest style matches:

```markdown
## Testing

There is a series of tests that runs for each PR. The components of this are

- running the tests found in [CslibTests](/CslibTests)
- checking that all files import [Cslib.Init](/Cslib/Init.lean), which sets up some default linting
  and tactics

You can run these locally with `lake test` and `lake exe checkInitImports` respectively.
```

```markdown
## Imports

There is also a test that [Cslib.lean](/Cslib.lean) imports all files. You can ensure this by
running `lake exe mk_all` locally, which will make the required changes.

CSLib tests for minimized imports using `lake shake --add-public --keep-implied --keep-prefix`, which also comes with a `--fix` option.
See `lake shake --help` for the special comment syntax used to preserve imports required for tactics or typeclasses.
```

Both subsections: 1-3 short paragraphs, no bullet-heavy formatting for the command itself
(bullets are reserved for "what runs" not "how to run it"), commands always in inline backticks,
occasional `[text](/Path)` repo-relative links. This is the register to match — not a warning
box, not a table, not a multi-paragraph essay.

**Table of Contents maintenance**: `CONTRIBUTING.md` lines 3-41 are a hand-maintained anchor
list generated by GitHub-style slugification (lowercase, spaces to hyphens, punctuation
stripped). The `Continuous Integration` block currently reads:

```
- [Continuous Integration](#continuous-integration)
  - [Pull Request Titles](#pull-request-titles)
  - [Testing](#testing)
  - [Linting](#linting)
  - [Imports](#imports)
```

A new subsection titled, e.g., `## Building a single file` needs a corresponding ToC line
`  - [Building a single file](#building-a-single-file)` inserted after the `[Imports]` line.
This is a required companion edit, not optional — every existing subsection has a ToC entry and
the file's own convention (a hand-written ToC, not an auto-generated one) means omitting the
entry would be a visible inconsistency against the rest of the document.

**No competing/duplicate home found**: `README.md` has no build-workflow section (checked,
`grep -n lake README.md` returns nothing beyond incidental prose, i.e. no existing `lake env
lean` guidance to update); `scripts/README.md` documents utility *scripts*, not raw `lake`/`lean`
invocation guidance, and one entry there (`AxiomCensus.lean`, run via `lake env lean --run
scripts/AxiomCensus.lean`) is itself a *safe* use of `lake env lean` because it runs a script
with `--run` after a full `lake build`, not a bare per-file elaboration — this is a different
usage pattern than the hazard being documented and should not be conflated with it in the new
subsection. `docs/` contains only `lint-suppression-policy.md` and
`modal-axiom-schema-architecture.md`, neither of which is contributor build-workflow guidance.

### External Resources

Not applicable — this is a purely internal, repository-specific tooling caveat (arising from
this repo's Lean 4.33 module-system usage), not a general Lean/Lake documentation gap. No
external search was needed; the technical grounding is task 622's direct local measurement, not
upstream Lake/Lean documentation (which does not need to explain a repo-specific footgun).

### Recommendations

**Subsection heading and placement**: Insert `## Building a single file` as a new `##`-level
subsection immediately after `## Imports` (line 133, before the blank line preceding `#
Getting started`), i.e., as the last subsection under `# Continuous Integration`. Rationale for
this exact slot rather than earlier in the section: the existing four subsections progress
PR-title convention → testing → linting → imports, i.e., broad CI mechanics before narrowing to
one specific tool quirk (`lake shake`'s own flags). A single-file-build caveat is the same
"narrow tool-specific footgun" register as `## Imports`'s `lake shake` discussion, so it belongs
adjacent to it rather than earlier, more general subsections.

**Content shape** (symptom-first, per the task's suggested approach), matching house style:

1. **Signature paragraph first** — what a contributor sees before naming the cause, so a
   contributor mid-hang can pattern-match against the doc while it is happening: a `lean`
   process pinned at roughly one core's worth of CPU, resident memory flat and non-growing, no
   error and no completion, for minutes with no upper bound observed.
2. **Rule statement** — name the unsafe command and the safe alternative in the same sentence so
   the fix is immediately visible: `lake env lean <file>` vs `lake build <Module.Name>`.
3. **One-sentence mechanism** — omitting `--setup` means the module-system exposure
   (`module`/`public import`) configuration Lake normally supplies is absent, which is what
   causes elaboration to diverge on module-system files; `lake build` always passes `--setup`,
   `lake env lean` never does.
4. **Secondary hazards, briefly** — bypasses dependency resolution (can silently reuse stale
   `.olean` files) and never writes an `.olean` without an explicit `-o`, so a missing `.olean`
   after such a run says nothing about whether the module has ever built.
5. **Escape hatch** (optional, one line) — if raw `lean` output is genuinely needed, `lake env
   lean --setup <module>.setup.json <file>` is the safe form; `<module>.setup.json` lives under
   `.lake/build/ir/<path/to/module>.setup.json` after a build.

All five points are already stated, with concrete verified numbers, in task 622's report
sections 1, 2, and 7 (item 2) — this task's job is compression into CONTRIBUTING.md's terse
register, not new fact-finding.

**Do not include** the raw reproduction command that hangs (`lake env lean
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`, unqualified) as a "try this to
see" example — CONTRIBUTING.md is instructional, not a bug report; naming the general pattern
(`lake env lean <file>`) is sufficient and does not invite a contributor to reproduce a 19+
minute hang.

## Decisions

- **Doc home**: `CONTRIBUTING.md`, `# Continuous Integration` section — confirmed, no
  alternative location found.
- **New subsection heading**: `## Building a single file` (placed last under `# Continuous
  Integration`, immediately after `## Imports`).
- **ToC update is in-scope**: the plan/implementation must also add the corresponding ToC entry
  (lines 3-41 block); this is not a separate task, it is part of making the same edit internally
  consistent with the rest of the file's own convention.
- **No re-verification of the hang**: per task instructions, the diverging command was not
  re-run. The technical claims are sourced from task 622's already-published, directly-measured
  report and are accurately restated above.
- **`scripts/AxiomCensus.lean`'s `lake env lean --run`** is a distinct, safe usage pattern (runs
  a script post-build, not raw per-file elaboration) and should not be referenced or conflated in
  the new subsection — flagging this explicitly to avoid an implementer accidentally citing it as
  a counter-example or "another instance of the same hazard."

## Risks & Mitigations

- **Risk**: An implementer might over-expand the new subsection into a multi-paragraph essay
  that reads as a warning banner, inconsistent with the file's terse register.
  **Mitigation**: This report's "Recommendations" section gives an explicit 5-point content
  shape sized to match `## Testing`/`## Imports` (roughly 2-4 short paragraphs total).
- **Risk**: Forgetting the Table of Contents companion edit leaves the file internally
  inconsistent (every other subsection has a ToC entry).
  **Mitigation**: Called out explicitly above as a required companion edit, not optional polish.
- **Risk**: Citing the reproduction command that hangs as a literal "try this" example could
  cause a contributor to intentionally trigger a 19+ minute hang.
  **Mitigation**: Recommend describing the pattern (`lake env lean <file>`) generically rather
  than including the specific hanging invocation as a copy-pasteable example.

## Context Extension Recommendations

- **Topic**: Lean/CSLib tooling context — a general note about Lean 4.33's module-system
  `--setup` requirement for raw `lean` invocations.
- **Gap**: Task 622's report (section 7, item 2) suggested this caveat also belongs in "the
  Lean/CSLib tooling context" more broadly (beyond just CONTRIBUTING.md), e.g. an
  agent-facing context file under a lean/cslib extension's context directory, so agents
  (not just human contributors) avoid the same misdiagnosis pattern when investigating a
  seemingly-stalled build.
- **Recommendation**: Out of scope for this task (`file_scope: ["CONTRIBUTING.md"]`), but worth a
  follow-up task or note if the misdiagnosis pattern recurs in agent-driven investigations. Not
  creating a task for this per current context-gap policy (task creation from context gaps is
  disabled).

## Appendix

### Search queries / commands used

```bash
grep -rn "lake env lean" --include="*.md" .
grep -rn "lake build" --include="*.md" .
ls docs/
grep -n "lake" README.md
grep -rln "lake env" scripts/
```

### Key references

- `CONTRIBUTING.md:97-132` (`# Continuous Integration` section and its four existing
  subsections)
- `CONTRIBUTING.md:3-41` (Table of Contents anchor list)
- `specs/622_investigate_scheme_build_stall/reports/01_scheme-build-stall-root-cause.md`
  sections 1, 2, and 7 (item 2) — authoritative source for all technical claims restated in this
  report
- `scripts/README.md` (`AxiomCensus.lean` entry) — confirms the distinct, safe `lake env lean
  --run` usage pattern that must not be conflated with the hazard
