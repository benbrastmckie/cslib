# Implementation Plan: Task #236 -- Inline Counter Fix (gnba_language_eq)

- **Task**: 236 - Complete follow-up PRs from PR #649 for Buchi automata and closure of omega-regular languages under boolean operations
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/236_follow_up_prs_buchi_omega_regular/reports/06_team-research.md
- **Artifacts**: plans/07_inline-counter-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan addresses the 3 remaining sorry markers in `Cslib/Logics/LTL/Semantics/GNBA.lean` (lines 1205, 1324, 1359), all located in the completeness direction's counter cycling proof. Team research (report 06) corrected the diagnosis from prior plan 05: the root cause is not a Decidable instance mismatch but rather the need to unfold `ctr` via `Nat.rec_add_one` and case-split the resulting if-then-else chain. Each sorry requires 5-15 lines of proof. The soundness direction is already fully proved (lines 811-1127, no sorry). Definition of done: `lake build` succeeds with zero sorry in GNBA.lean and `lean_verify` confirms `Formula.gnba_language_eq` and `Formula.isRegular` are sorry-free.

### Research Integration

- Report `06_team-research.md`: Corrected root cause diagnosis (not Decidable mismatch), provided verified inline fix strategies for all 3 sorry markers tested via `lean_run_code` reproductions, confirmed soundness is complete, confirmed mathematical correctness of `gnbaNBA` definition, estimated 30-80 lines of new proof code.

### Prior Plan Reference

Plan 05 (`05_gnba-correctness-plan.md`) was based on an incorrect diagnosis and grossly overestimated effort:
- Phase 2 (soundness, 8 hours) requires zero work -- soundness is already complete.
- The "Decidable instance mismatch" diagnosis was wrong -- both `open Classical in` and `classical` tactic use the same `Classical.propDecidable` instance.
- Total effort was estimated at 18 hours; actual remaining work is 1-1.5 hours.
- Estimated 400-500 lines of new proof; actual remaining work is 30-80 lines.
- The phase structure (3 phases, sequential) was appropriate for the incorrectly scoped task but unnecessary for the actual work.

### Roadmap Alignment

No ROADMAP.md items are advanced by this task. The LTL/GNBA module is outside the BimodalLogic porting scope tracked in the roadmap.

## Goals & Non-Goals

**Goals**:
- Fill sorry at line 1205 (`hss_trans` counter condition) with inline proof
- Fill sorry at line 1324 (`hctr_stay_step`) with inline proof
- Fill sorry at line 1359 (`hctr_advance`) with inline proof
- Verify `Formula.gnba_language_eq` is sorry-free via `lean_verify`
- Verify `Formula.isRegular` is transitively sorry-free via `lean_verify`
- Pass full CI pipeline: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`

**Non-Goals**:
- Refactoring `ctr` or `gnbaNBA` definitions (they are correct as-is)
- Extracting `counterStep`/`counterSeq` as standalone definitions (fallback only)
- Modifying soundness direction (already complete)
- Adding new lemmas or restructuring the proof
- General GNBA type refactoring (separate task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `simp` timeout on the 1400-line file | M | L | Use `simp only [...]` with explicit lemma list to limit search; if still slow, fall back to extraction strategy |
| `rename_i` variable names differ from research reproductions | L | M | Match by goal structure rather than exact names; use `lean_goal` if responsive, otherwise `lean_run_code` snippets |
| `lean_goal` / `lean_hover_info` timeout on large file | L | H | Use `lake build` for verification instead of interactive tools; use `lean_run_code` with minimal snippets for tactic testing |
| Proof terms differ due to elaboration context in actual file | M | L | The research tested with structurally matching reproductions (Fin types, Classical scoping, let bindings); fall back to extraction strategy if inline fix fails |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Fill Sorry Markers [COMPLETED]

**Goal**: Replace all 3 sorry markers in GNBA.lean with verified proofs, making `gnba_language_eq` sorry-free.

**Tasks**:
- [ ] Fill sorry at line 1205 (`hss_trans` counter condition): `simp only [Formula.gnbaNBA, ss, ctr, Nat.rec_add_one]` followed by nested `split` to handle `dite (K = 0)`, `dite (i.val < K)`, and `ite (B n in acc)` chain (~10 lines)
- [ ] Fill sorry at line 1324 (`hctr_stay_step`): `simp only [ctr, Nat.rec_add_one]` + `split` + `exfalso` in acceptance branch using `Fin.ext` from `hctr_d'` to contradict `hno_acc_d'` (~12 lines)
- [ ] Fill sorry at line 1359 (`hctr_advance`): `simp only [ctr, Nat.rec_add_one]` + `split` + `exfalso` in non-membership branch using `Fin.ext` from `hctr_t_d_min` to contradict `hd_min_mem` (~12 lines)
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.GNBA` to verify compilation

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- replace sorry at lines 1205, 1324, 1359 with proof terms

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors or sorry warnings

---

### Phase 2: Verification and CI [COMPLETED]

**Goal**: Confirm sorry-free status of `gnba_language_eq` and `isRegular`, and pass the full CI pipeline.

**Tasks**:
- [x] Run `lean_verify` on `Cslib.Logic.LTL.Formula.gnba_language_eq` -- no `sorryAx`
- [x] Run `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular` -- no `sorryAx`
- [x] Run `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular_untl` -- no `sorryAx`
- [x] Run full CI pipeline:
  - `lake build` (full project) -- pass
  - `lake test` -- pre-existing failure (CslibTests.Bisimulation import, unrelated)
  - `lake exe checkInitImports` -- pass
  - `lake exe lint-style` -- pass
- [x] Grep GNBA.lean for remaining `sorry` or `proof_wanted` -- none found

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- None (verification only)

**Verification**:
- All `lean_verify` calls pass with no `sorryAx`
- All CI commands pass
- No `sorry` or `proof_wanted` in GNBA.lean or OmegaRegular.lean

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds after Phase 1
- [ ] `lake build` (full project) succeeds after Phase 2
- [ ] `lean_verify` confirms no `sorryAx` in `gnba_language_eq`, `isRegular`, `isRegular_untl`
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No `sorry` or `proof_wanted` remains in GNBA.lean

## Artifacts & Outputs

- `Cslib/Logics/LTL/Semantics/GNBA.lean` (modified) -- 3 sorry markers filled with proof terms
- `specs/236_follow_up_prs_buchi_omega_regular/plans/07_inline-counter-fix.md` (this file)

## Rollback/Contingency

- **If inline fix fails (simp timeout or elaboration mismatch)**: Fall back to the extraction strategy from research report 06. Extract `counterStep` and `counterSeq` as standalone `noncomputable def`s, prove `counterSeq_succ` (should be `rfl`), and replace `ctr` references. This adds ~30 lines of definition but makes all three sorry locations trivial. Estimated additional time: 1 hour.
- **If extraction also fails**: The existing proof infrastructure is preserved. All sorry markers are isolated to the counter cycling section. Mark phase as [PARTIAL] and document the specific elaboration issue for a targeted follow-up.
- **Overall**: All existing infrastructure (closure, atoms, canonical atoms, GNBA construction, soundness proof) is unaffected regardless of outcome.
