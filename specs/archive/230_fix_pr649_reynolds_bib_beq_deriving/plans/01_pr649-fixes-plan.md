# Implementation Plan: Fix PR #649 Reynolds Bib Key + BEq Deriving

- **Task**: 230 - Fix PR #649 Reynolds Bib Key + BEq Deriving
- **Status**: [COMPLETED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_pr649-fixes-research.md
- **Artifacts**: plans/01_pr649-fixes-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two single-line edits on the feat/temporal-formula-propositional branch to fix minor issues
identified during PR #649 review. (1) Rename the `Reynolds1994` bib key to `Reynolds1996` in
`references.bib` to match the actual publication year confirmed by DOI. (2) Add `BEq` to the
`Temporal.Formula` deriving clause for consistency with `LTL.Formula`.

### Research Integration

Research report confirmed both issues. The `Reynolds1994` key at line 645 of `references.bib`
has year field `1996` (DOI 10.1093/logcom/6.5.679 confirms 1996). The key is not referenced
anywhere else in the codebase. `Temporal.Formula` derives only `DecidableEq` while
`LTL.Formula` derives both `DecidableEq` and `BEq`. Adding `BEq` is safe -- it defers to
`DecidableEq` with no behavioral change.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Correct the Reynolds bib key from `Reynolds1994` to `Reynolds1996`
- Add `BEq` to `Temporal.Formula` deriving clause for consistency with `LTL.Formula`

**Non-Goals**:
- Auditing other bib keys for year mismatches
- Modifying any other deriving clauses across the codebase

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Bib key referenced elsewhere | L | L | Research confirmed no references exist |
| BEq breaks downstream code | L | L | BEq from DecidableEq is strictly additive |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Apply Both Fixes [COMPLETED]

**Goal**: Make both single-line edits and verify the build passes.

**Tasks**:
- [x] Change `@article{Reynolds1994,` to `@article{Reynolds1996,` on line 645 of `references.bib`
- [x] Change `deriving DecidableEq` to `deriving DecidableEq, BEq` in `Cslib/Logics/Temporal/Syntax/Formula.lean`
- [x] Run `lake build` to verify no regressions

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `references.bib` - Rename bib key from Reynolds1994 to Reynolds1996
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Add BEq to deriving clause

**Verification**:
- `lake build` succeeds with no new errors
- `grep -n Reynolds1996 references.bib` confirms the key rename
- `grep -n 'deriving DecidableEq, BEq' Cslib/Logics/Temporal/Syntax/Formula.lean` confirms the deriving addition

## Testing & Validation

- [ ] `lake build` passes without errors
- [ ] No references to `Reynolds1994` remain in the codebase

## Artifacts & Outputs

- plans/01_pr649-fixes-plan.md (this file)
- Modified: `references.bib`, `Cslib/Logics/Temporal/Syntax/Formula.lean`

## Rollback/Contingency

Both edits are independent single-line changes. Revert either with `git checkout -- <file>`.
