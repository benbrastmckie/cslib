# Implementation Plan: Task #331 - Polish Code from Completed Tasks (310, 312, 322)

- **Task**: 331 - Polish code from recently completed tasks (310, 312, 322)
- **Status**: [COMPLETED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/331_completed_tasks_code_polish/reports/01_code-polish-research.md
- **Artifacts**: plans/01_code-polish-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add cross-reference docstrings between ConservativeChain.lean and MplConservativeChain.lean,
clarify the thin alias `hilbertConjImpConservativeOverImp_direct` with a docstring explaining
its naming-convention purpose, and remove the unused `_hphi` parameter from
`hilbertEmbeddingLemma` in DiegoEmbedding.lean. All changes are docstring additions or a
single parameter removal with no proof logic modifications.

### Research Integration

The research report confirmed:
- MplConservativeChain.lean already references ConservativeChain.lean in several places, but
  ConservativeChain.lean makes zero mention of MplConservativeChain.lean. Cross-references
  need to be added in ConservativeChain.lean and existing references in MplConservativeChain.lean
  should be upgraded to "See also" format for consistency.
- The `_direct` alias is a pure naming-convention artifact with zero callers. Keeping it with
  a clarifying docstring is preferred over removal for API symmetry with `_viaIpl`.
- The `_hphi` parameter in `hilbertEmbeddingLemma` is genuinely unused (confirmed by proof
  inspection) and the lemma has zero callers, making removal a non-breaking change.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly targeted by this polish task.

## Goals & Non-Goals

**Goals**:
- Add "See also" cross-references in ConservativeChain.lean pointing to MplConservativeChain.lean counterparts
- Upgrade existing "Compare with" references in MplConservativeChain.lean to "See also" format
- Add clarifying docstring to `hilbertConjImpConservativeOverImp_direct` explaining it is an API alias
- Remove unused `_hphi` parameter from `hilbertEmbeddingLemma` and update its docstring

**Non-Goals**:
- Changing any proof logic or proof terms
- Refactoring module structure or imports
- Adding tests (these are documentation-only and parameter-removal changes)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `_hphi` removal causes downstream breakage | L | L | Research confirmed zero callers; `lake build` verification |
| Docstring syntax error breaks Lean parser | L | L | Use standard `/-- ... -/` format; verify with `lake build` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Docstring and Signature Edits [COMPLETED]

**Goal**: Apply all three polish items across the three target files.

**Tasks**:
- [ ] Add "See also" cross-reference to `hilbertMplConservativeOverConjImp` docstring in ConservativeChain.lean, pointing to `hilbertMplConservativeOverConjImp_direct` in MplConservativeChain.lean
- [ ] Add "See also" cross-reference to `hilbertMplConservativeOverImp` docstring in ConservativeChain.lean, pointing to `hilbertMplConservativeOverImp_direct` in MplConservativeChain.lean
- [ ] Add "See also" cross-reference to `GHAValid_implies_BrouwerianValid_orBotFree` docstring in ConservativeChain.lean, pointing to `GHAValid_implies_BrouwerianValid_direct` in MplConservativeChain.lean
- [ ] Add a note in the module docstring of ConservativeChain.lean mentioning that MplConservativeChain.lean provides alternative direct-algebraic proofs for the MPL steps
- [ ] Upgrade "Compare with" references in MplConservativeChain.lean to "See also" format for `GHAValid_implies_BrouwerianValid_direct`, `hilbertMplConservativeOverConjImp_direct`, and `hilbertMplConservativeOverImp_direct`
- [ ] Add clarifying docstring to `hilbertConjImpConservativeOverImp_direct` in ConservativeChain.lean stating it is an API naming-convention alias, not an alternative proof route
- [ ] Remove `(_hphi : phi.IsImpTopOnly = true)` parameter from `hilbertEmbeddingLemma` signature in DiegoEmbedding.lean
- [ ] Update `hilbertEmbeddingLemma` docstring to note the biconditional holds for all formulas but is primarily applied to `IsImpTopOnly` formulas in the Diego embedding context

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` - Add cross-references and alias docstring
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` - Upgrade existing references to "See also" format
- `Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean` - Remove unused parameter, update docstring

**Verification**:
- All three files have the expected docstring additions
- `hilbertEmbeddingLemma` signature no longer contains `_hphi`

---

### Phase 2: Build Verification [COMPLETED]

**Goal**: Confirm all edits compile cleanly and pass CI checks.

**Tasks**:
- [ ] Run `lake build` to verify no compilation errors
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Spot-check that `hilbertEmbeddingLemma` compiles without the removed parameter

**Timing**: 0.25 hours

**Depends on**: 1

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` exits with code 0
- `lake exe lint-style` reports no new violations

## Testing & Validation

- [ ] `lake build` compiles successfully with all edits
- [ ] `lake exe lint-style` passes
- [ ] Manual inspection: ConservativeChain.lean contains "See also" references to MplConservativeChain.lean
- [ ] Manual inspection: MplConservativeChain.lean uses consistent "See also" format
- [ ] Manual inspection: `hilbertConjImpConservativeOverImp_direct` has API-alias docstring
- [ ] Manual inspection: `hilbertEmbeddingLemma` signature has no `_hphi` parameter

## Artifacts & Outputs

- `specs/331_completed_tasks_code_polish/plans/01_code-polish-plan.md` (this plan)
- `specs/331_completed_tasks_code_polish/summaries/01_code-polish-summary.md` (after implementation)

## Rollback/Contingency

All changes are docstring additions and a single parameter removal. Rollback is trivial via
`git checkout` on the three affected files. No database migrations, no config changes, no
external dependencies.
