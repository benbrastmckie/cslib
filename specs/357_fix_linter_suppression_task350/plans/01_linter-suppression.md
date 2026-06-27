# Implementation Plan: Task #357

- **Task**: 357 - Fix linter suppressions in task-350 files
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: Task 356 (DenseMCS.lean docstring edits) — sequence, do not run in parallel on DenseMCS.lean
- **Research Inputs**: specs/357_fix_linter_suppression_task350/reports/01_linter-suppression.md
- **Artifacts**: plans/01_linter-suppression.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Five global `set_option linter.* false` directives across four task-350 files were
investigated empirically (each removed, module rebuilt, warnings captured). Most are
unnecessary and can simply be deleted; only three guard real warnings. This plan removes
every global suppression and fixes the genuinely-flagged issues at their source:
`linter.style.emptyLine` (intra-command blank lines in `DeductionTheorem.lean`),
`linter.flexible` (`simp [...]` → `simp only [...]` in `DenseMCS.lean`), and
`linter.dupNamespace` (replace one file-global suppression with four per-declaration
scoped suppressions in `DenseMCS.lean`). All edits are style/structural and
behavior-preserving — no `sorry`, no axioms, no semantic changes.

### Research Integration

Findings from `reports/01_linter-suppression.md` drive every phase: each suppression's
empirical status (UNNECESSARY vs REAL) and the exact fix strategy per file. Key empirical
results integrated:
- All three `maxHeartbeats` overrides are stale — every module builds at the default 200000.
- `@[nolint dupNamespace]` (env linter) and `set_option linter.dupNamespace false`
  (build-time frontend linter) are distinct; DenseMCS needs the scoped `set_option` form
  on its 4 intentionally `Temporal.`-prefixed declarations. Renaming is rejected (established
  sibling-file convention; ~10 external call sites).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Remove every global `set_option linter.* false` directive in the five task-350 suppression sites.
- Fix the genuinely-flagged issues at source (emptyLine, flexible, dupNamespace).
- Keep all four modules building cleanly at default heartbeats with no new lint warnings.
- Sequence DenseMCS.lean edits with task 356 so the two tasks rebase cleanly.

**Non-Goals**:
- Do NOT touch docstrings in DenseMCS.lean (owned by task 356).
- Do NOT rename the 4 `Temporal.`-prefixed declarations (established convention; out of scope).
- Do NOT re-add `maxHeartbeats` overrides unless a CI timeout actually surfaces (fallback only).
- No semantic/proof-logic changes beyond `simp [...]` → `simp only [...]`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `simp only [...]` set is incomplete and proof fails to close | M | M | Use `simp?` to obtain the explicit lemma set per flagged site; verify the goal closes after each change before moving on. |
| Removing `maxHeartbeats` causes a CI-machine timeout | M | L | Research confirmed default builds locally; fallback is a scoped `set_option maxHeartbeats 400000 in` before `deriv_tree_to_list` only (no file-global, no suppression needed). |
| DenseMCS.lean edit collides with task 356 docstring edits | M | M | Sequence the two tasks (either order); whichever runs second rebases. Place `set_option ... in` immediately above the docstring/`@[nolint]`/`def` block: order is `set_option ... in` → docstring → `@[nolint dupNamespace]` → `def`. |
| dupNamespace scoped suppression placed at wrong site | L | L | Apply to exactly the 4 named decls: `Temporal.DerivFc`, `Temporal.ThDerivableFc`, `Temporal.SetConsistentFc`, `Temporal.SetMaximalConsistentFc`. |
| Line numbers drifted from report's restored-file values | L | M | Treat report line numbers as guides; re-enable each linter, rebuild, and act on the actual warning locations. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel (they touch four distinct files).
Phase 4 (DenseMCS.lean) additionally must be sequenced against task 356 — do not run
task 356 and Phase 4 in parallel on that file.

### Phase 1: DeductionTheorem.lean — remove suppressions + fix emptyLine [COMPLETED]

**Goal**: Delete all four header `set_option` lines (43-46) and remove the intra-command
blank lines that `linter.style.emptyLine` genuinely flags.

**Tasks**:
- [ ] Delete the four `set_option` lines (43-46): `style.show`, `style.emptyLine`, `style.setOption`, `flexible`.
- [ ] Re-enable / rebuild to surface the ~11 `linter.style.emptyLine` warnings.
- [ ] Remove each flagged blank line inside the `match` bodies of `deductionWithMem`
      (~lines 92-136) and `deductionTheorem` (~line 168+): the blank line between an arm's
      last tactic and the next `|`, plus the blank line before each `termination_by`.
- [ ] Rebuild and confirm zero emptyLine warnings remain.

**Timing**: ~30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` — delete 4 set_option lines; remove ~11 intra-command blank lines.

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem` succeeds with no lint warnings.

---

### Phase 2: Bimodal GenericMCSBridge.lean — delete three header lines [COMPLETED]

**Goal**: Remove the three unnecessary header directives (lines 64-66).

**Tasks**:
- [ ] Delete `set_option linter.dupNamespace false` (64) — never fires.
- [ ] Delete `set_option linter.style.setOption false` (65) — only fired on `maxHeartbeats`.
- [ ] Delete `set_option maxHeartbeats 400000` (66) — builds at default 200000.
- [ ] Rebuild at default heartbeats.

**Timing**: ~10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — delete lines 64-66.

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` succeeds at default heartbeats with no new warnings.
- Fallback (only if a `maxHeartbeats` timeout surfaces): add scoped `set_option maxHeartbeats 400000 in` immediately before `deriv_tree_to_list`.

---

### Phase 3: Temporal GenericMCSBridge.lean — delete three header lines [COMPLETED]

**Goal**: Remove the three unnecessary header directives (lines 54-56), identical to Phase 2.

**Tasks**:
- [ ] Delete `set_option linter.dupNamespace false` (54).
- [ ] Delete `set_option linter.style.setOption false` (55).
- [ ] Delete `set_option maxHeartbeats 400000` (56).
- [ ] Rebuild at default heartbeats.

**Timing**: ~10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — delete lines 54-56.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` succeeds at default heartbeats with no new warnings.
- Same scoped-`maxHeartbeats` fallback as Phase 2 if needed.

---

### Phase 4: DenseMCS.lean — header cleanup, flexible fix, scoped dupNamespace [COMPLETED]

**Goal**: Remove the unnecessary header directives, convert flagged `simp [...]` to
`simp only [...]`, and replace the file-global `dupNamespace` suppression with four
per-declaration scoped suppressions. Linter fixes ONLY — do not touch docstrings.

**Tasks**:
- [ ] Confirm task 356's DenseMCS.lean edits are landed (or coordinate to run second and rebase). Do not run in parallel with 356 on this file.
- [ ] Delete `set_option linter.style.setOption false` (41) — only fired on `maxHeartbeats`.
- [ ] Delete `set_option maxHeartbeats 3200000` (44) — stale 16x over-allocation; builds at default.
- [ ] Delete `set_option linter.flexible false` (43) after fixing the flagged simp calls below.
- [ ] Re-enable `linter.flexible`, rebuild, and for each flagged `simp [...]` run `simp?`
      to get the explicit lemma set, then replace with `simp only [...]`. Known sites
      (restored-file line numbers, treat as guides): line 245 `simp [List.mem_cons] at this`;
      lines 328 & 356 `simp [temporalDerivationSystemFc, Temporal.DerivFc]`; also check
      line 259 `simp [h1, DerivationTree.height]` and line 327
      `simp [List.mem_cons] at hx`. Convert only those the linter actually flags. Verify the
      proof closes after each change.
- [ ] Replace the file-global `set_option linter.dupNamespace false` (42) with a
      per-declaration `set_option linter.dupNamespace false in` placed immediately above each
      of the 4 declarations: `Temporal.DerivFc`, `Temporal.ThDerivableFc`,
      `Temporal.SetConsistentFc`, `Temporal.SetMaximalConsistentFc`. Keep the existing
      `@[nolint dupNamespace]`. Required ordering: `set_option linter.dupNamespace false in`
      → docstring (task 356) → `@[nolint dupNamespace]` → `def`.
- [ ] Rebuild and confirm no dupNamespace, flexible, setOption, or emptyLine warnings.

**Timing**: ~50 minutes

**Depends on**: none (file-independent of Phases 1-3; externally sequenced against task 356)

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` — delete header lines 41, 43, 44; replace line 42 with 4 per-declaration scoped suppressions; convert flagged `simp [...]` → `simp only [...]`. NO docstring edits.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DenseMCS` succeeds at default heartbeats with no new lint warnings.
- Confirm the 4 scoped `set_option ... in` sit correctly above the docstring/`@[nolint]`/`def` blocks.

---

### Phase 5: Full CI verification [COMPLETED]

**Goal**: Confirm the whole change set passes the CSLib CI pipeline with no new warnings.

**Tasks**:
- [ ] `lake build` (full) — syntax linters run during build; expect no new warnings.
- [ ] `lake exe lint-style`.
- [ ] `lake exe checkInitImports`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `lake test`.
- [ ] Confirm no remaining global `set_option linter.* false` in the five suppression sites
      (grep the four files).

**Timing**: ~20 minutes

**Depends on**: 1, 2, 3, 4

**Files to modify**: none (verification only).

**Verification**:
- All CI commands pass.
- `grep -rn "set_option linter" ` on the four files shows only the 4 scoped
  `set_option linter.dupNamespace false in` lines in DenseMCS.lean and no file-global suppressions.

## Testing & Validation

- [ ] Each affected module builds individually at default heartbeats with no new lint warnings.
- [ ] No `linter.style.emptyLine` warnings in DeductionTheorem.lean.
- [ ] No `linter.flexible` warnings in DenseMCS.lean; all converted `simp only [...]` close their goals.
- [ ] No build-time `linter.dupNamespace` warnings in DenseMCS.lean (scoped suppression covers exactly the 4 decls).
- [ ] Full `lake build`, `lake exe lint-style`, `lake exe checkInitImports`, `lake shake`, `lake test` all pass.
- [ ] No file-global `set_option linter.* false` remains in any of the four files.
- [ ] No docstring changes introduced by this task (task 356 owns docstrings).

## Artifacts & Outputs

- Modified `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`
- Modified `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
- Modified `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
- Modified `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean`
- `specs/357_fix_linter_suppression_task350/summaries/01_*-summary.md` (on completion)

## Rollback/Contingency

- Each phase edits a distinct file; revert that file via `git checkout -- <path>` if a build
  regresses, leaving other phases intact.
- If removing `maxHeartbeats` produces a CI-only timeout, re-add a scoped
  `set_option maxHeartbeats 400000 in` immediately before `deriv_tree_to_list` in the affected
  bridge file (file-global form rejected — it requires the very suppression we are removing).
- If a `simp only [...]` conversion cannot be made to close, restore that single `simp [...]`
  call and keep a narrowly-scoped `set_option linter.flexible false in` on that one declaration
  rather than reinstating the file-global suppression.
- If task 356 has not yet landed on DenseMCS.lean, defer Phase 4 until coordination is resolved
  to avoid a merge conflict; Phases 1-3 and 5 (for those files) are unaffected.
