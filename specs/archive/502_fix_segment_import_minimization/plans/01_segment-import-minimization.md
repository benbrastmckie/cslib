# Implementation Plan: Task #502

- **Task**: 502 - Fix Segment.lean import minimization (replace transitive PrimeTheory import with two direct imports)
- **Status**: [BLOCKED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/502_fix_segment_import_minimization/reports/01_segment-import-minimization.md
- **Artifacts**: plans/01_segment-import-minimization.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` currently `public import`s
`Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` (line 10) but consumes zero
PrimeTheory-local declarations. The research report traced every symbol Segment uses to exactly
two upstream modules. This plan executes a single mechanical edit: replace that one import line
with two direct `public import`s, keep `import Cslib.Init` (line 9) untouched, and verify with
`lake build` plus `lake shake`.

### Research Integration

Key findings encoded from the research report (all confirmed):

- **Replacement**: Segment.lean line 10 (`public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory`)
  is replaced by TWO direct imports, Foundations-before-Logics ordering (matching PrimeTheory's own convention):
  - `public import Cslib.Foundations.Logic.Metalogic.PrimeExclusion`
  - `public import Cslib.Logics.Modal.Metalogic.DerivationTree`
- **Both MUST be `public`**: Segment's declarations sit under an `@[expose] public section` and
  reference these types in their public signatures; dropping `public` would re-break shake /
  downstream visibility.
- **KEEP `import Cslib.Init` (line 9)**: mandated by CONTRIBUTING.md, enforced by
  `lake exe checkInitImports`. Shake's suggestion to drop it is the known systemic out-of-scope
  false positive and is intentionally ignored.
- **Symbol provenance (fully traced, zero PrimeTheory-local symbols consumed)**:
  - `PrimeAdmissible` / `DeductivelyClosed` -> `Foundations/Logic/Metalogic/PrimeExclusion.lean`
  - `DerivationTree` + constructors (`.ax`, `.modus_ponens`, `.weakening`, `.assumption`) +
    `modalDerivationSystem` -> `Logics/Modal/Metalogic/DerivationTree.lean`
  - `Proposition` + `◇`/`□` notation -> `Logics/Modal/Basic.lean` (public-imported by DerivationTree)
  - `DerivationSystem` -> `Foundations/Logic/Metalogic/Consistency.lean` (public-imported by both replacements)
- **Target module paths verified to exist** (both are already in PrimeTheory's own public-import list).
- **Coverage complete**: the union of the two replacements' public-import closures covers everything
  Segment needs; the dropped transitive modules (DeductionTheorem, ListHelpers) contribute nothing.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided). This task advances library-hygiene / import
minimization surfaced by the vet of a prior CSLib task.

## Goals & Non-Goals

**Goals**:
- Replace the single transitive `public import ...PrimeTheory` line with two direct `public import`s.
- Preserve `import Cslib.Init` exactly as-is.
- Confirm `lake build` succeeds and `lake shake` no longer flags Segment.lean line 10.

**Non-Goals**:
- No new definitions, abstractions, axioms, or `sorry` — pure import reduction.
- No notation changes; the file's existing scoped `◇`/`□` usage is unaffected.
- No re-derivation of scope; do not touch other imports or other files.
- Do NOT act on shake's remaining project-wide `import Cslib.Init` flag (out of scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| One replacement written as plain (non-`public`) import | M | L | Both lines must be `public`; verified by shake re-flagging if plain |
| Accidentally removing `import Cslib.Init` on shake's advice | M | L | Plan explicitly forbids; `lake exe checkInitImports` enforces |
| Build breakage from missing transitive symbol | H | L | Research traced full public-import closure; `lake build` gates completion |
| Import ordering deviates from convention | L | L | Use Foundations-before-Logics ordering per PrimeTheory precedent |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single phase; no parallelism.

### Phase 1: Replace transitive import and verify [BLOCKED]

**BLOCKER** (Phase 1):
- **What failed**: After replacing Segment.lean's line 10 with the two prescribed direct
  `public import`s (`Cslib.Foundations.Logic.Metalogic.PrimeExclusion` and
  `Cslib.Logics.Modal.Metalogic.DerivationTree`), the scoped build of Segment.lean itself
  succeeded, but `lake shake --add-public --keep-implied --keep-prefix` (which rebuilds the
  whole project to compute the import graph) failed with `error: there are out of date oleans`
  while building `Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum`. A direct
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum` reproduced 6 real
  compile errors: `Unknown identifier 'modalDeductiveClosure'` (4 occurrences, lines 160, 189,
  217, 259) and `Unknown identifier 'deductionTheorem'` (2 occurrences, lines 391, 429).
- **Root cause**: `SegmentLindenbaum.lean` is the *sole* direct importer of `Segment.lean`
  (`import Cslib.Logics.Modal.Metalogic.Constructive.Segment` is its only content import besides
  `Cslib.Init`). It uses `modalDeductiveClosure` (defined at
  `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean:78` -- i.e. it IS
  PrimeTheory-local, contradicting the research report's "zero PrimeTheory-local symbols
  consumed" claim, which was scoped only to Segment.lean's own direct usage, not its
  downstream consumers) and `deductionTheorem` (defined at
  `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean:64` -- one of the two modules, "the
  dropped transitive modules (DeductionTheorem, ListHelpers)", the research report judged to
  "contribute nothing"). SegmentLindenbaum never imports either module directly; it relied
  entirely on Segment.lean's old `public import ...PrimeTheory` transitively re-exporting both
  symbols. Replacing that one line with the two direct imports Segment.lean itself needs
  (PrimeExclusion + DerivationTree) silently drops that re-export path, breaking
  SegmentLindenbaum.lean and everything that transitively imports it
  (`MinExtension.lean`, `MinPrimeTheory.lean`, `CKTruthLemma.lean`, and further downstream).
- **What was tried**: Applied the exact two-import replacement per plan Task 1 (both `public`,
  Foundations-before-Logics order); ran scoped `lake build` on Segment.lean (green); ran
  `lake shake --add-public --keep-implied --keep-prefix` (failed mid-rebuild); ran
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum` directly to isolate
  the failure (confirmed real compile errors, not a flaky/unrelated failure -- ruled out the
  KB5/Five-simplification failure the delegation context flagged as pre-existing/out-of-scope,
  since this is a distinct, reproducible `Unknown identifier` error tied precisely to the
  removed transitive re-export). Per this plan's own Rollback/Contingency section, reverted
  Segment.lean's import block to the original single `public import ...PrimeTheory` line
  (verified via `git diff` showing zero diff against HEAD) and re-confirmed
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum` is green again
  post-revert.
- **Why it's stuck**: The plan's non-goals explicitly forbid touching other imports or other
  files ("No re-derivation of scope; do not touch other imports or other files"), and
  `.claude/rules/plan-compliance.md` requires escalating rather than silently substituting a
  different step for `.lean` files. Fixing this correctly (making SegmentLindenbaum.lean import
  `PrimeTheory.lean` and `Modal/Metalogic/DeductionTheorem.lean` directly, per proper import
  hygiene) is a second file's import list -- outside this plan's declared single-file scope.
- **What is needed**: A follow-up task (or a revised plan for this task, if the user prefers to
  widen scope now) to add `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory`
  and `public import Cslib.Logics.Modal.Metalogic.DeductionTheorem` directly to
  `SegmentLindenbaum.lean`, THEN re-apply this task's Segment.lean two-import replacement, THEN
  re-verify with `lake build` (whole-project or at least the SegmentLindenbaum/CKTruthLemma/
  MinExtension/MinPrimeTheory dependent chain) and `lake shake`.
- **Prohibited workarounds**: Did NOT use `sorry`, `def X := True`, or any vacuous placeholder.
  Did NOT widen scope to edit SegmentLindenbaum.lean without user authorization. Did NOT leave
  Segment.lean in the broken intermediate state -- reverted to the last known-green content.


**Goal**: Swap the one PrimeTheory import line for the two direct public imports, keep Cslib.Init,
and verify the build + shake are clean for Segment.lean.

**Tasks**:
- [ ] Open `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` and confirm line 9 is
      `import Cslib.Init` and line 10 is `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory`.
- [ ] Replace line 10 with two lines (Foundations before Logics):
      `public import Cslib.Foundations.Logic.Metalogic.PrimeExclusion`
      and `public import Cslib.Logics.Modal.Metalogic.DerivationTree`.
- [ ] Leave line 9 (`import Cslib.Init`) exactly as-is; do not remove or reorder it.
- [ ] Run `lake build` (or scoped `lake build Cslib.Logics.Modal.Metalogic.Constructive.Segment`)
      and confirm no errors.
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` and confirm Segment.lean line 10
      is no longer flagged (the remaining project-wide `import Cslib.Init` flag is expected and out of scope).

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` - replace line 10 (one `public import`)
  with two direct `public import`s; keep line 9 unchanged.

**Verification**:
- `lake build` succeeds with no errors.
- `lake shake --add-public --keep-implied --keep-prefix` no longer flags Segment.lean's replaced
  import line.
- The `import Cslib.Init` line remains present and unchanged.

---

## Testing & Validation

- [ ] `lake build` completes with no errors.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports Segment.lean line 10 resolved.
- [ ] `import Cslib.Init` still present (satisfies `lake exe checkInitImports`).
- [ ] Both new imports are `public`.

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` (single import-line change).

## Rollback/Contingency

Single-file, single-line change. If `lake build` fails, revert the import block to the original
`public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` (git checkout of the one
file) and re-investigate the failing symbol before retrying.
