# Implementation Plan: Task #356

- **Task**: 356 - Fix DenseMCS docBlame violations
- **Status**: [COMPLETED]
- **Effort**: 0.3 hours
- **Dependencies**: None (sequence before task 357, which also edits this file)
- **Research Inputs**: specs/356_fix_dense_mcs_docblame_violations/reports/01_dense-mcs-docblame.md
- **Artifacts**: plans/01_dense-mcs-docblame.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CONTRIBUTING.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add a brief `/-- ... -/` docstring immediately above each of six public `theorem`
declarations in `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` to clear the
`docBlame` environment-linter warnings. This is a purely mechanical, zero-debt
documentation change: no proof bodies, signatures, or imports are touched. The
research report supplies exact, ready-to-insert docstring text matching the
file's established local style, so a single implementation phase suffices.

### Research Integration

The report (`reports/01_dense-mcs-docblame.md`) confirmed against the live file that
all six declarations exist at the stated line numbers, are `theorem`s lacking a
member docstring, and trigger `docBlame`. It also provides the exact `/-- ... -/`
text for each and the documented CSLib convention (member doc comment with no
blank line before the declaration; brief single phrase ending in a period;
backtick-quote Lean identifiers). Note that `/-! ... -/` section comments do NOT
satisfy `docBlame` -- only `/-- ... -/` member docs do.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Insert one `/-- ... -/` docstring above each of the six flagged theorems.
- Clear the six `docBlame` warnings for this file under `lake lint`.
- Keep edits limited strictly to docstring insertions so task 357 (linter
  suppression removal) can be sequenced cleanly against the same file.

**Non-Goals**:
- No proof, signature, or import changes.
- No changes to other declarations or to existing docstrings/section comments.
- No removal or alteration of linter suppressions (that is task 357's scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Edit anchor matches a non-unique line | L | L | Anchor each Edit on the unique `theorem <name>` signature line; names are distinct |
| Line numbers shifted since research | L | L | Anchor on declaration text, not line numbers; report verified current positions |
| Docstring form fails to satisfy docBlame | M | L | Use `/-- ... -/` member doc with no blank line before the theorem, per report |
| Edits collide with task 357 region | M | L | Limit edits to docstring insertions only; coordinate ordering at orchestration level |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single phase; no internal parallelism.

### Phase 1: Insert docstrings and verify [COMPLETED]

**Goal**: Add the six docstrings and confirm a clean build with the `docBlame`
warnings gone.

**Tasks**:
- [ ] Insert `/-- Modus ponens for fc-parameterized derivability: from `φ → ψ` and `φ` derive `ψ`. -/` above `theorem mp_deriv_fc` (~line 72).
- [ ] Insert `/-- Weakening for fc-parameterized derivability: enlarging the context preserves derivability. -/` above `theorem weakening_deriv_fc` (~line 80).
- [ ] Insert `/-- Assumption rule for fc-parameterized derivability: any hypothesis in the context is derivable. -/` above `theorem assumption_deriv_fc` (~line 87).
- [ ] Insert `/-- Falsum `⊥` is never a member of an fc-maximal-consistent set. -/` above `theorem mcs_bot_not_mem_fc` (~line 324).
- [ ] Insert `/-- In an fc-MCS, if `φ` is not a member then its negation `¬φ` is (negation completeness). -/` above `theorem mcs_neg_of_not_mem_fc` (~line 334).
- [ ] Insert `/-- In an fc-MCS, if the negation `¬φ` is a member then `φ` is not. -/` above `theorem mcs_not_mem_of_neg_fc` (~line 342).
- [ ] Ensure no blank line separates each new docstring from its theorem keyword.

**Timing**: 0.3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - add six member docstrings; no other changes.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DenseMCS` compiles successfully.
- `lake lint` shows the six `docBlame` warnings for these declarations are gone.
- Manual diff review confirms only docstring lines were added (no proof/signature edits).

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Metalogic.DenseMCS` succeeds.
- [ ] `lake lint` no longer reports `docBlame` for the six theorems.
- [ ] `git diff` shows exactly six added `/-- ... -/` lines and nothing else.
- [ ] Zero-debt compliance preserved (no `sorry`, no new axioms).

## Artifacts & Outputs

- Modified `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` with six new docstrings.
- This plan file.

## Rollback/Contingency

Docstring insertions are isolated and side-effect-free. If the build or lint
regresses unexpectedly, revert the single-file change with `git checkout --
Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` (or remove the six added lines).
If a docstring still fails `docBlame`, confirm it uses `/-- ... -/` (not `/-! ... -/`)
and that no blank line separates it from the theorem keyword.
