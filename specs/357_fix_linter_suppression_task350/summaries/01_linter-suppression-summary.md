# Implementation Summary: Task #357 — Fix Linter Suppressions (task-350 files)

- **Task**: 357 - Fix linter suppressions in task-350 files
- **Status**: implemented
- **Phases completed**: 5 / 5
- **Plan**: specs/357_fix_linter_suppression_task350/plans/01_linter-suppression.md

## What Was Done

Removed all five file-global `set_option linter.* false` directives across four task-350
Lean files and fixed the genuinely-flagged issues at source. All edits are style/structural
and behavior-preserving — no semantic changes, no `sorry`, no new axioms.

### Phase 1: DeductionTheorem.lean

Removed 4 file-global `set_option` lines (`linter.style.show`, `linter.style.emptyLine`,
`linter.style.setOption`, `linter.flexible`). Fixed the 11 intra-command blank lines that
`linter.style.emptyLine` genuinely flagged: 7 blank lines between match arms and 1 before
`termination_by` in `deductionWithMem`, plus 3 blank lines between match arms and 1 before
`termination_by` in `deductionTheorem`.

### Phase 2: Bimodal/Metalogic/Core/GenericMCSBridge.lean

Deleted 3 unnecessary header directives: `set_option linter.dupNamespace false`,
`set_option linter.style.setOption false`, `set_option maxHeartbeats 400000`. All three were
empirically confirmed stale by the research phase. The module builds at default heartbeats.

### Phase 3: Temporal/Metalogic/GenericMCSBridge.lean

Identical cleanup to Phase 2 — deleted the same 3 unnecessary header directives at the
Temporal variant of the bridge file.

### Phase 4: Temporal/Metalogic/DenseMCS.lean

Most complex phase. Four changes:

1. Removed `set_option linter.style.setOption false` and `set_option maxHeartbeats 3200000`
   (both stale — module builds at default heartbeats with no style issues).

2. Removed `set_option linter.flexible false` (file-global). Fixed the 5 `simp [...]` calls
   flagged by `linter.flexible`:
   - `simp [List.mem_cons] at this` → `simp only [List.mem_cons, List.mem_nil_iff, or_false] at this`
     (extra lemmas needed because full simp also reduces `x ∈ []` via `List.mem_nil_iff`)
   - `simp [h1, DerivationTree.height]` → `simp only [h1, DerivationTree.height]; omega`
     (simp only reduces but leaves `n < 1 + n` which omega closes)
   - `simp [List.mem_cons] at hx` → `simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx`
   - Two occurrences of `simp [temporalDerivationSystemFc, Temporal.DerivFc]` →
     `simp only [temporalDerivationSystemFc, Temporal.DerivFc]`
   - `unfold temporalDerivationSystemFc Temporal.DerivFc at h ⊢; simp at h ⊢` →
     `simp only [temporalDerivationSystemFc, Temporal.DerivFc] at h ⊢`
     (the simp was doing struct projection beta-reduction only; combining unfold + simp into
     a single `simp only` is equivalent and avoids the flexible lint warning)

3. Removed `set_option linter.dupNamespace false` (file-global). Replaced with 4 scoped
   `set_option linter.dupNamespace false in` directives, one before each of the 4
   intentionally `Temporal.`-prefixed declarations:
   `Temporal.DerivFc`, `Temporal.ThDerivableFc`, `Temporal.SetConsistentFc`,
   `Temporal.SetMaximalConsistentFc`. Ordering per plan: `set_option ... in` → docstring
   (added by task 356) → `@[nolint dupNamespace]` → `def`/`abbrev`.

### Phase 5: CI Verification

- All 4 modules build clean in isolation with zero lint warnings.
- `lake exe lint-style` passes with no issues in modified files.
- `lake shake` finds no import minimization issues for modified files.
- Full `lake build` shows failures only in pre-existing unrelated modules (task-360 scope,
  as documented in the orchestration notes).
- Zero sorries; zero new axioms; no docstring changes.

## Plan Deviations

None. All phases executed as planned.

## Artifacts Modified

- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` — removed 4 set_option lines + 11 blank lines
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — removed 3 header set_option lines
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — removed 3 header set_option lines
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` — removed 4 global set_options; added 4 scoped; fixed 5 simp calls
