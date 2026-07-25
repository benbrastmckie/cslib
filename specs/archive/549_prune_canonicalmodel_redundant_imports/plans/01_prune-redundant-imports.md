# Implementation Plan: Prune redundant imports from Intuitionistic CanonicalModel.lean

- **Task**: 549 - prune_canonicalmodel_redundant_imports
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_prune-redundant-imports.md
- **Artifacts**: plans/01_prune-redundant-imports.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Remove two unused `public import` lines from
`Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (`MCS` and `Birelational`),
which became redundant after a recent consolidation added `GenericMCSBridge` /
`DerivationCombinators` imports. Because `Birelational` is re-exported through CanonicalModel and
consumed downstream (`BForces` in TruthLemma.lean; `BModel`/`IValid`/`MValid` in Completeness.lean),
its removal must be paired with adding a direct `public import Cslib.Logics.Modal.Semantics.Birelational`
to TruthLemma.lean. `MCS` is genuinely dead across the whole downstream subtree and needs no
compensating change. The two edits form an atomic unit; definition of done is a green
`lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness`.

### Research Integration

Key findings from reports/01_prune-redundant-imports.md, fully integrated:
- Both imports are unused *in CanonicalModel.lean's own code* (all `MCS`/`Birelational`
  identifiers there appear only in docstring prose). `open Cslib.Logic.Metalogic.GenericMCS`
  resolves via `GenericMCSBridge`, not `MCS.lean`.
- `lake shake` confirms: remove both from CanonicalModel, but **add** `Birelational` to
  TruthLemma (a relocation, not a free deletion). `MCS` gets no compensating add anywhere.
- `import Cslib.Init` is flagged for removal by shake in both files — a **false positive** that
  MUST be ignored (`Cslib.Init` is imported for side effects; removing it breaks the
  `lake exe checkInitImports` invariant).
- Do NOT use `lake shake --fix`: it would strip `import Cslib.Init` and touch out-of-scope files
  (`SchemaUnion.lean`, `PrimeTheory.lean`). Use targeted manual edits only.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Remove the two redundant `public import` lines (`MCS`, `Birelational`) from CanonicalModel.lean.
- Relocate the `Birelational` import down to TruthLemma.lean, its true direct consumer.
- Keep the affected subtree building green with no regression in TruthLemma or Completeness.

**Non-Goals**:
- Do NOT run `lake shake --fix` or apply any shake recommendation mechanically.
- Do NOT remove or alter `import Cslib.Init` in any file.
- Do NOT touch out-of-scope files (SchemaUnion.lean, PrimeTheory.lean) or edit Completeness.lean.
- Do NOT rewrite or remove docstring prose that mentions `MCS`/`Birelational` by name (it is
  illustrative, not an import dependency).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing Birelational from CanonicalModel without adding it to TruthLemma breaks the build | H | H (if edits split) | Treat both edits as one atomic unit; verify with the Completeness build before committing |
| Accidentally removing `import Cslib.Init` (shake false positive) | H | M | Explicitly preserve `import Cslib.Init` in both files; never run `lake shake --fix` |
| Scoped build passes but a broader consumer regresses | M | L | Completeness is the terminal downstream consumer of this subtree; its build transitively exercises CanonicalModel and TruthLemma |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Relocate imports and verify build [COMPLETED]

- **Goal:** Remove the two redundant imports from CanonicalModel.lean, add the compensating
  Birelational import to TruthLemma.lean, and confirm the affected subtree builds green.
- **Tasks:**
  - [x] In `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean`, remove the line
        `public import Cslib.Logics.Modal.Metalogic.MCS`.
  - [x] In the same file, remove the line
        `public import Cslib.Logics.Modal.Semantics.Birelational`.
        Keep `import Cslib.Init` and the `PrimeTheory` / `GenericMCSBridge` /
        `DerivationCombinators` imports intact.
  - [x] In `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean`, add
        `public import Cslib.Logics.Modal.Semantics.Birelational` (e.g. immediately after the
        existing `public import ...Intuitionistic.CanonicalModel` line). Keep `import Cslib.Init`.
  - [x] Do NOT edit Completeness.lean; the chain `Completeness -> TruthLemma -> Birelational`
        keeps its names reachable after the relocation.
  - [x] Run `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness` and confirm it
        is green (this transitively builds CanonicalModel and TruthLemma).
  - [x] (Optional) Re-run
        `lake shake --add-public --keep-implied --keep-prefix TruthLemma CanonicalModel` and
        confirm no further remove/add beyond the ignored `import Cslib.Init` false positive.
- **Timing:** ~30 minutes (mostly build time).
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` - remove 2 unused
    `public import` lines (`MCS`, `Birelational`).
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` - add 1 `public import`
    (`Birelational`) to compensate for the lost transitive re-export.
- **Verification:**
  - `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness` exits 0 (green).
  - Both edited files still contain `import Cslib.Init`.

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness` is green.
- [x] `grep -n "import Cslib.Init"` confirms `import Cslib.Init` remains in both edited files.
- [x] CanonicalModel.lean no longer contains `public import Cslib.Logics.Modal.Metalogic.MCS`
      or `public import Cslib.Logics.Modal.Semantics.Birelational`.
- [x] TruthLemma.lean now contains `public import Cslib.Logics.Modal.Semantics.Birelational`.
- [x] No `sorry`, no new axioms introduced (this is a pure import-hygiene change).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (2 lines removed)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (1 line added)
- `specs/549_prune_canonicalmodel_redundant_imports/summaries/01_prune-redundant-imports-summary.md`
  (produced at implementation time)

## Rollback/Contingency

If the Completeness build fails after the edits, revert the three line changes across the two
files (`git checkout -- <files>` after a snapshot, or re-add the removed imports) to restore the
pre-change state, then re-verify with the same Completeness build. The change is 2 removals + 1
addition across 2 files, so rollback is a direct reversal of the diff.
