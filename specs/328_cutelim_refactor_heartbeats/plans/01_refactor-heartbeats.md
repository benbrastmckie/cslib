# Implementation Plan: Task #328

- **Task**: 328 - Refactor CutElimination.lean to reduce or eliminate the maxHeartbeats 800000 override
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: 327 (completed)
- **Research Inputs**: specs/328_cutelim_refactor_heartbeats/reports/01_refactor-heartbeats.md
- **Artifacts**: plans/01_refactor-heartbeats.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Refactor `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` to reduce elaboration cost from 800000 heartbeats to the default 200000 or at most 400000. The strategy has two independent axes: (1) extract the three purely self-recursive `cutAdm_right_*` helpers from the 739-line mutual block into standalone definitions, shrinking the mutual block from 5 definitions to 2 (~296 lines); (2) replace 35+ duplicated inline Finset subset proof constructions with shared helper lemmas. Together these yield an estimated 60-80% heartbeat reduction. The public API (`cutAdmissibility`, `LKProof.cutElim`, `CutFreeLKProof.mono`) remains unchanged throughout.

### Research Integration

The research report (`reports/01_refactor-heartbeats.md`) provided:
- A complete call-graph analysis proving `cutAdm_right_andR`, `cutAdm_right_orR`, and `cutAdm_right_impR` are purely self-recursive and can be safely extracted from the mutual block.
- Quantitative analysis of 35+ repeated "push through cut formula" patterns and 14 "double-insert weakening" patterns replaceable by two shared helpers (`insert_subset_swap`, `subset_insert2`).
- Verified type-checking of proposed helper lemmas via `lean_run_code`.
- Heartbeat reduction estimate of 60-80% from combined optimizations.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly advance any ROADMAP.md item. It is a code quality / performance refactoring of the propositional sequent calculus module, which supports the broader proof-theory infrastructure used across modal, temporal, and bimodal metalogic modules.

## Goals & Non-Goals

**Goals**:
- Reduce `maxHeartbeats` from 800000 to at most 400000, ideally to default (200000)
- Extract three self-recursive helpers from the mutual block into standalone definitions
- Replace duplicated Finset subset proof patterns with shared helpers
- Maintain the unchanged public API: `cutAdmissibility`, `LKProof.cutElim`, `CutFreeLKProof.mono`
- Each phase builds and passes CI independently

**Non-Goals**:
- Splitting into separate files (CutAdmRight.lean) -- deferred unless needed for heartbeat target
- Converting term-mode proofs to tactic mode
- Changing the proof structure or algorithm of cut elimination
- Optimizing `CutFree.mono` or other pre-mutual-block definitions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Mutual block extraction changes termination checking behavior | H | L | The three helpers are demonstrably self-recursive (no mutual calls); Lean's termination checker handles them independently. Test each extraction individually. |
| Shared helpers change unification behavior in surrounding proofs | M | L | Helpers have been verified via `lean_run_code`. Apply mechanically with `lake build` after each batch of replacements. |
| Heartbeat target not reached after all optimizations | M | L | Research estimates 60-80% reduction; even conservative 50% reaches 400000. File splitting remains available as escalation. |
| Eta-reduction of lambda wrappers causes type mismatch | L | M | Test each replacement; revert to explicit lambda if Lean's expected types require it. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Shared Finset Helpers [COMPLETED]

**Goal**: Define reusable Finset subset proof helpers and one-sided mono wrappers before the mutual block, replacing the most common duplicated patterns.

**Tasks**:
- [ ] Add `private theorem subset_insert2` proving `s <= insert a (insert b s)` from double-transitive subset_insert
- [ ] Add `private theorem insert_subset_swap` proving `insert a s <= insert c (insert a t)` from `s <= insert c t`
- [ ] Add `private def CutFreeLKProof.monoL` (left-side weakening with `Finset.Subset.refl` on right)
- [ ] Add `private def CutFreeLKProof.monoR` (right-side weakening with `Finset.Subset.refl` on left)
- [ ] Verify all helpers type-check with `lake build`
- [ ] Run CI pipeline (`lake test`, `lake exe checkInitImports`, `lake exe lint-style`)

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Add 4 helper definitions before the mutual block (approximately lines 91-110, after `mem_of_ne_head`)

**Verification**:
- `lake build` succeeds with no new errors
- All four helpers are defined and accessible within the file
- No change to public API signatures

---

### Phase 2: Extract cutAdm_right_* Helpers from Mutual Block [COMPLETED]

**Goal**: Move the three purely self-recursive helpers (`cutAdm_right_andR`, `cutAdm_right_orR`, `cutAdm_right_impR`) out of the `mutual` block into standalone recursive definitions, shrinking the mutual block from 5 definitions (~739 lines) to 2 definitions (~296 lines).

**Tasks**:
- [ ] Move `cutAdm_right_andR` (currently ~lines 118-266) out of the mutual block, placing it after the Finset helpers but before the `mutual` keyword
- [ ] Move `cutAdm_right_orR` (currently ~lines 269-410) similarly
- [ ] Move `cutAdm_right_impR` (currently ~lines 413-553) similarly
- [ ] Adjust the `mutual` block to contain only `cutAdm_right` and `cutAdm_left`
- [ ] Verify termination checking passes for each standalone helper
- [ ] Verify the mutual block still elaborates correctly with external calls to the three helpers
- [ ] Run `lake build` to confirm no regressions

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Restructure mutual block: move 3 definitions out (~435 lines moved, mutual block shrinks to ~296 lines)

**Verification**:
- `lake build` succeeds
- Mutual block contains only `cutAdm_right` and `cutAdm_left`
- The three extracted helpers are standalone `def` or `theorem` declarations with explicit `termination_by` if needed
- `cutAdmissibility`, `LKProof.cutElim`, `CutFreeLKProof.mono` signatures unchanged

---

### Phase 3: Replace Duplicated Finset Patterns with Shared Helpers [COMPLETED]

**Goal**: Systematically replace inline Finset subset proof constructions across all five definitions with calls to the shared helpers from Phase 1, reducing code size and elaboration cost.

**Tasks**:
- [ ] Replace ~35 "push through cut formula" inline patterns with `insert_subset_swap h` (and composed `insert_subset_swap (insert_subset_swap h)` for double-insert)
- [ ] Replace ~14 "double-insert weakening" patterns with `subset_insert2 a b s`
- [ ] Replace ~44 eta-reducible `(fun x hx => hsuc hx)` lambdas with direct hypothesis references (`hsuc`)
- [ ] Replace `.mono h (Finset.Subset.refl _)` calls with `monoL h` and `.mono (Finset.Subset.refl _) h` with `monoR h`
- [ ] Work in batches: complete all replacements in one helper function, then `lake build` before moving to the next
- [ ] Run full CI pipeline after all replacements

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Replace inline patterns across `cutAdm_right_andR`, `cutAdm_right_orR`, `cutAdm_right_impR`, `cutAdm_right`, and `cutAdm_left` (estimated ~200+ lines removed)

**Verification**:
- `lake build` succeeds after each batch of replacements
- Net line count reduction of ~150-250 lines
- No change to public API

---

### Phase 4: Measure Heartbeats and Adjust maxHeartbeats Setting [COMPLETED]

**Goal**: Measure actual heartbeat usage after optimizations and set `maxHeartbeats` to the minimum viable value (target: 200000 default or at most 400000).

**Tasks**:
- [ ] Remove `set_option maxHeartbeats 800000` entirely and attempt build with default (200000)
- [ ] If default fails, profile with `lean_profile_proof` on the mutual block to identify remaining hotspots
- [ ] If default fails, try `set_option maxHeartbeats 400000`
- [ ] If 400000 also fails, identify remaining hotspots and consider targeted fixes (remove unused `Tableau.Defs` import, further eta-reductions)
- [ ] If still above 400000, consider file splitting as escalation (move extracted helpers to `CutAdmRight.lean`)
- [ ] Run full CI pipeline: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Remove unused imports if any (research identified `Tableau.Defs` as potentially unused)

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Adjust or remove `set_option maxHeartbeats` line; remove unused imports
- `Cslib.lean` - Only if file splitting is needed (add new module import)

**Verification**:
- `lake build` succeeds with the new heartbeat setting
- Full CI pipeline passes
- `maxHeartbeats` is at most 400000 (ideally removed entirely for default 200000)
- Public API unchanged: `cutAdmissibility`, `LKProof.cutElim`, `CutFreeLKProof.mono`

## Testing & Validation

- [ ] `lake build` succeeds at each phase boundary
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] Public API signatures unchanged (verify with `lean_hover_info` on `cutAdmissibility`, `LKProof.cutElim`, `CutFreeLKProof.mono`)
- [ ] Final `maxHeartbeats` is at most 400000

## Artifacts & Outputs

- `specs/328_cutelim_refactor_heartbeats/plans/01_refactor-heartbeats.md` (this file)
- `specs/328_cutelim_refactor_heartbeats/summaries/01_refactor-heartbeats-summary.md` (after implementation)
- Modified `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean`

## Rollback/Contingency

All changes are within a single file (`CutElimination.lean`). If any phase causes regressions that cannot be resolved:
1. `git checkout` the file to its pre-task state
2. Re-attempt with a more conservative approach (e.g., extract only one helper at a time)
3. If the heartbeat target cannot be reached without file splitting, create a follow-up task for the split
