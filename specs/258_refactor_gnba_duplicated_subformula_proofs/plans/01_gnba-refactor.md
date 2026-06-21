# Implementation Plan: Refactor Duplicated Proof Patterns in GNBA.lean

- **Task**: 258 - Refactor duplicated proof patterns in GNBA.lean
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: 257
- **Research Inputs**: specs/258_refactor_gnba_duplicated_subformula_proofs/reports/01_gnba-refactor.md
- **Artifacts**: plans/01_gnba-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Introduce a single `Formula.subformulas_trans` lemma (subformula transitivity) in GNBA.lean to replace five near-identical inductive proofs with one-liner wrappers. Remove two dead-code closure lemmas (`imp_left_mem_closure`, `imp_right_mem_closure`). The transitivity pattern already exists in Bimodal and Temporal modules, making this a well-precedented refactoring. Net savings: approximately 80 lines with zero API breakage since all affected lemmas are private or intra-file.

### Research Integration

Key findings from report `01_gnba-refactor.md`:
- Five inductive proofs (`subformulas_untl_left`, `subformulas_untl_right`, `subformulas_imp_left`, `subformulas_imp_right`, `subformulas_next_sub`) all share the same structure and differ only in which constructor matches and which child is concluded.
- `Formula.subformulas_trans` unifies all five into a single ~20-line induction, with verified proof code provided in the research report.
- `imp_left_mem_closure` (line 375) and `imp_right_mem_closure` (line 385) are dead code -- never called downstream. The stronger variants `imp_sub_left_mem_closure` (line 423) and `imp_sub_right_mem_closure` (line 433) handle all call sites.
- The one-liner wrappers use `by simp [Formula.subformulas]` to discharge the child-membership subgoal, which was verified to compile.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly reference this refactoring task.

## Goals & Non-Goals

**Goals**:
- Introduce `Formula.subformulas_trans` as a single inductive proof for subformula transitivity
- Replace the four binary-constructor subformula lemmas (lines 236-333) with one-liner wrappers that call `subformulas_trans`
- Replace `subformulas_next_sub` (line 712) with a one-liner wrapper
- Remove dead-code lemmas `imp_left_mem_closure` and `imp_right_mem_closure`
- Ensure `lake build Cslib.Logics.LTL.Semantics.GNBA` passes after all changes

**Non-Goals**:
- Refactoring `untl_left_mem_closure` / `untl_right_mem_closure` (these remain structurally necessary as bridges from closure to subformulas, and their bodies are already short)
- Unifying `subformulas_trans` across modules (Bimodal, Temporal, LTL) into a shared base -- that is a separate task
- Modifying any files other than `Cslib/Logics/LTL/Semantics/GNBA.lean`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `by simp [Formula.subformulas]` fails in wrappers | M | L | Research verified compilation; fall back to explicit `Set.mem_union` terms if needed |
| Dead code removal breaks an undetected caller | M | L | Research grep confirmed zero callers; re-run `lean_local_search` before deletion |
| Transitivity proof does not type-check as written | H | L | Proof code verified in research; test with `lean_multi_attempt` before committing |
| Downstream proofs break due to different definitional unfolding | M | L | The wrappers maintain the exact same signature; callers see no change |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Introduce subformulas_trans and replace Group 1 lemmas [COMPLETED]

**Goal**: Add `Formula.subformulas_trans` and convert the four binary-constructor subformula lemmas to one-liner wrappers.

**Tasks**:
- [ ] Add `Formula.subformulas_trans` lemma immediately before `subformulas_untl_left` (around line 235), using the verified inductive proof from the research report
- [ ] Replace the body of `subformulas_untl_left` (lines 237-258) with: `Formula.subformulas_trans (by simp [Formula.subformulas]) h`
- [ ] Replace the body of `subformulas_untl_right` (lines 262-283) with: `Formula.subformulas_trans (by simp [Formula.subformulas]) h`
- [ ] Replace the body of `subformulas_imp_left` (lines 287-308) with: `Formula.subformulas_trans (by simp [Formula.subformulas]) h`
- [ ] Replace the body of `subformulas_imp_right` (lines 312-333) with: `Formula.subformulas_trans (by simp [Formula.subformulas]) h`
- [ ] Verify with `lean_goal` or `lean_multi_attempt` that the wrappers type-check
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.GNBA` to confirm no regressions

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` - Add `subformulas_trans`, rewrite four lemma bodies

**Verification**:
- All four wrapper lemmas compile
- `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds

---

### Phase 2: Replace subformulas_next_sub and remove dead code [COMPLETED]

**Goal**: Convert `subformulas_next_sub` to a one-liner wrapper and remove the two dead-code `imp_*_mem_closure` lemmas.

**Tasks**:
- [ ] Replace the body of `subformulas_next_sub` (lines 713-733) with: `Formula.subformulas_trans (by simp [Formula.subformulas]) h`
- [ ] Verify `next_sub_mem_closure` (line 742, which calls `subformulas_next_sub`) still compiles
- [ ] Confirm `imp_left_mem_closure` and `imp_right_mem_closure` have zero callers (run `lean_local_search` for both names)
- [ ] Remove `imp_left_mem_closure` (lines 374-382) and `imp_right_mem_closure` (lines 384-391) entirely
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.GNBA` to confirm no regressions

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` - Rewrite `subformulas_next_sub` body, delete two dead lemmas

**Verification**:
- `subformulas_next_sub` and `next_sub_mem_closure` compile
- No build errors after dead code removal
- `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds

---

### Phase 3: Final verification and cleanup [COMPLETED]

**Goal**: Full CI verification and confirm net line savings.

**Tasks**:
- [ ] Run `lake build` (full project) to ensure no cross-file regressions
- [ ] Run `lake exe checkInitImports` to verify import integrity
- [ ] Run `lake exe lint-style` to check style compliance
- [ ] Verify net line reduction is approximately 80 lines compared to pre-refactoring state

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` passes with zero errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- Line count reduction confirms refactoring achieved expected savings

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Semantics.GNBA` passes after each phase
- [ ] `lake build` (full project) passes after all phases
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] All downstream callers of wrapper lemmas continue to compile unchanged
- [ ] No new `sorry` introduced

## Artifacts & Outputs

- `specs/258_refactor_gnba_duplicated_subformula_proofs/plans/01_gnba-refactor.md` (this plan)
- `specs/258_refactor_gnba_duplicated_subformula_proofs/summaries/01_gnba-refactor-summary.md` (post-implementation)
- Modified: `Cslib/Logics/LTL/Semantics/GNBA.lean`

## Rollback/Contingency

All changes are confined to a single file (`GNBA.lean`). If any phase fails:
- `git checkout -- Cslib/Logics/LTL/Semantics/GNBA.lean` restores the original file
- No other files are affected, so rollback is atomic and complete
