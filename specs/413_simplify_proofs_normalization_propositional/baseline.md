# Phase 1 Baseline: Task 413

Captured 2026-07-28. All numbers below are *observed*, not the report's hypotheses; later
phases compare against these.

## Pre-flight checks

- `git status --porcelain Cslib/` before starting: **empty** (confirmed).
- `git apply --check specs/413_simplify_proofs_normalization_propositional/verified-simplification.patch`:
  **succeeds** — patch is not stale.

## Residual-site / unfold counts

- `grep -rn "simp only \[.*\(listImp\|bigconj\|negBigconj\)" Cslib/ | wc -l` -> **20**
  (matches the report's hypothesis of 20 exactly).
- `grep -rn "unfold ListDeriv" Cslib/ | wc -l` -> **24** total occurrences of the substring
  in `Cslib/` today. This is a broader count than the report's "15 accompanying unfolds"
  figure, because the raw grep also counts `unfold ListDeriv` occurrences that are NOT
  paired with a redundant `simp only [listImp_*]` (e.g. `ListDeduction.lean:59,77,93,107`,
  `GenericMCS.lean:255`, and the `«axiom»` arms in the four bridges, which use
  `listImp_axiom_k` for real work and are explicitly out of scope). Counting only the
  lines the verified patch actually deletes: `grep -c "^-.*unfold ListDeriv"` against the
  patch gives **19** removed lines. Neither 19 nor 24 matches the report's "15" figure
  exactly; this is a documentation/counting-convention mismatch in the report (the report
  likely counted distinct restatement *blocks* rather than raw `unfold` line occurrences),
  not evidence of a residual/missed site — the primary scope-defining count (20 `simp only`
  sites, 8 files) matches exactly. Proceeding without blocking on this secondary metric.

## Full `lake build` baseline

- Command: `lake build` (Mathlib cache already warm, per delegation context).
- Result: **green**, **3309 jobs** (matches report's job count exactly).
- Wall time: `1m15.445s` (real), `7m55.440s` (user), `1m19.397s` (sys).
- Full-build `sorry` warning set (5 warnings, 4 files):
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1252:6`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:570:6`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:2583:14`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:124:8`
  - `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118:8`

  **Divergence from report**: the report hypothesized exactly 4 pre-existing `sorry`
  warnings across 3 files (all under `Propositional/Tableau/`). The observed baseline has
  a 5th warning at `Modal/Tableau/FrameSoundness.lean:1252:6`, in a file untouched by this
  task's change set and unrelated to `listImp`/`bigconj`. The in-file docstring
  (`FrameSoundness.lean:1234-1236`) states this sorry is "retained by explicit user
  decision" and propagates into no other result — it predates this task and is not a
  regression introduced by (or discharged by) this work. **Disposition**: not a blocker.
  The 20-site / 8-file scope that actually bounds this patch matches the report exactly;
  this is baseline drift in an unrelated file since the report was written. All downstream
  phases compare against this *observed* 5-warning/4-file set, not the report's 4-warning
  set.

## Per-module baseline build times (from the full-build run above)

| Module | Time |
|--------|------|
| `Cslib.Foundations.Logic.Metalogic.GenericMCS` | 709ms |
| `Cslib.Foundations.Logic.Metalogic.ListDeduction` | 658ms |
| `Cslib.Foundations.Logic.Metalogic.MCSProperties` | 927ms |
| `Cslib.Foundations.Logic.Theorems.BigConj` | 629ms |
| `Cslib.Logics.Propositional.Metalogic.GenericMCSBridge` | 956ms |
| `Cslib.Logics.Modal.Metalogic.GenericMCSBridge` | 982ms |
| `Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` | 1.1s |
| `Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` | 968ms |

## Post-flight check

- `git status --porcelain Cslib/` at phase end: empty (no source edit leaked into this
  measurement-only phase).

## Verdict

Patch is valid and current. Scope hypothesis (20 sites, 8 files) confirmed exactly. Sorry
baseline is the *observed* 5-warning set above (not the report's 4-warning guess), and is
the reference for every later phase's sorry-freeness check. Proceeding to Phase 2.
