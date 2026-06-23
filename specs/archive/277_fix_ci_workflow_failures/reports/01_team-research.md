# Research Report: Task #277

**Task**: Fix recurring CI workflow failures in GitHub Actions
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates)

## Summary

The CI failures stem from **two independent root causes**, not one recurring issue. The first is `sorry` warnings and an unused `simp` argument triggering the `--iofail` build flag, which treats all warnings as errors. The second is a missing repository guard on `lake-update.yml` that causes the "Bump Mathlib to LKG" workflow to fail on every fork. A third, emergent issue — genuine proof errors in `TemporalConservativity.lean` — was discovered in the latest CI run.

## Key Findings

### Failure Mode 1: `--iofail` Build Failures (runs 27984755605, 27983889592)

The CI workflow passes `build-args: "--iofail"` to `lake build`, which causes any warning-level diagnostic to fail the build. Five modules fail consistently:

| Module | Issue | Fix Type |
|--------|-------|----------|
| `GNBA.lean:795` | 2 unused `simp` arguments | Quick: remove unused args |
| `Bundle/UntilSinceCoherence.lean` | 2 `sorry` (blocked task 37) | Proof completion |
| `BXCanonical/Frame.lean` | 1 `sorry` (blocked task 36) | Proof completion |
| `Bundle/SuccRelation.lean` | 7 `sorry` (blocked task 37) | Proof completion |
| `BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 10+ `sorry` (blocked task 36) | Proof completion |

The `--iofail` flag is correct upstream behavior — upstream CSLib uses `--wfail --iofail` and passes because it has no `sorry` stubs. The fork's sorry stubs are intentionally partial proofs blocked on tasks 36 and 37, not regressions.

**Historical context**: CI has **never passed** on this fork (35+ runs all failed). The failure count has been decreasing steadily — from 15+ modules in early June to 5 now — indicating significant progress.

### Failure Mode 2: Missing Repository Guard (run 27986662089)

The `lake-update.yml` workflow requires `MATHLIB_NIGHTLY_TESTING_APP_ID` and `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY` secrets that only exist in the upstream `leanprover/cslib` organization. Error: `[@octokit/auth-app] appId option is required`.

Unlike other upstream workflows (`docs.yml`, `bump_toolchain_nightly-testing.yml`, `weekly-lints.yml`), `lake-update.yml` lacks the `if: github.repository == 'leanprover/cslib'` guard. This is a one-line fix.

### Failure Mode 3: Proof Errors in TemporalConservativity.lean (latest run)

Run 27987390947 reveals a new failure not in the originally listed runs. `TemporalConservativity.lean` has genuine compilation errors (metavariable/rewrite failures) introduced by task 275's PARTIAL completion — distinct from sorry-triggered warnings:

```
error: TemporalConservativity.lean:116:8: Tactic `rewrite` failed
error: TemporalConservativity.lean:108:4: (kernel) declaration has metavariables
```

### Architectural Tension: `--wfail` Drift Pattern

The fork has a recurring cycle where `--wfail` is removed from CI to allow sorry stubs, then restored during upstream merges, then removed again. Git history shows 3 such cycles. This reflects a fundamental tension: upstream mandates `--wfail`, but the fork carries in-progress work with sorry stubs.

### Additional Issues

- **`pre-pr-check.sh` gap**: Script checks only `Modal/`, `Temporal/`, `Foundations/` — not `Bimodal/`, the primary development area
- **No git hooks**: `.git/hooks/` contains only sample files; no pre-push verification
- **Mathlib version drift**: Fork uses older Mathlib pin than upstream (v4.31.0 vs v4.32.0-rc1)

## Synthesis

### Conflicts Resolved

1. **Remove `--iofail` vs. suppress sorry locally**: Teammates B and D disagreed on approach. Teammate B suggested removing `--iofail` as a development-mode option; Teammate D recommended keeping `--iofail` and using `set_option linter.sorry false` per-file. **Resolution**: The `set_option` approach is preferable because it keeps CI honest for non-sorry warnings (like the GNBA unused simp args) while allowing acknowledged sorry stubs. Removing `--iofail` entirely would mask other warnings.

2. **Whether `--iofail` vs `--wfail --iofail` matters**: Teammate B traced that the fork uses `--iofail` only while upstream uses both. Since `--iofail` (fail-level=info) is stricter than `--wfail` (fail-level=warning), both catch sorry warnings equally. The distinction is irrelevant for the current failures but the fork should match upstream exactly to avoid drift.

### Gaps Identified

1. **Task 36 and 37 status unknown**: The sorry stubs reference blocking tasks 36 and 37; their current status is unclear
2. **`set_option linter.sorry false` validity**: Whether this Lean 4 pattern is accepted by CSLib/Mathlib conventions needs verification before adoption
3. **TemporalConservativity proof errors**: These are distinct from sorry issues and need separate diagnosis

### Recommendations

**Immediate fixes (can be done now):**
1. Add `if: github.repository == 'leanprover/cslib'` guard to both jobs in `lake-update.yml` — eliminates Failure Mode 2 entirely
2. Remove the 2 unused `simp` arguments in `GNBA.lean:795` — eliminates one of the 5 build targets
3. Fix proof errors in `TemporalConservativity.lean` — eliminates Failure Mode 3

**Short-term (requires proof work):**
4. Complete sorry stubs in 4 Bimodal files (blocked on tasks 36/37) — eliminates remaining build failures
5. Alternatively, use `set_option linter.sorry false in` scoping for acknowledged sorry stubs to let CI pass on non-sorry warnings while sorry work is in progress

**Medium-term (CI hardening):**
6. Update `scripts/pre-pr-check.sh` to cover `Cslib/Logics/Bimodal/`
7. Install a pre-push git hook running `lake build --wfail --iofail`
8. Restore `--wfail` in CI to match upstream exactly

**Long-term (architectural):**
9. Adopt a branch strategy separating upstream-ready (`main`) from in-progress (`develop`)
10. Track sorry inventory as a first-class metric

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary root cause analysis | completed | high |
| B | Alternative patterns and upstream comparison | completed | high |
| C | Critic — gaps and blind spots | completed | high |
| D | Strategic horizons and long-term CI | completed | high/medium |

## References

- CI runs: 27986662089, 27984755605, 27983889592, 27987390947
- Upstream repo: `leanprover/cslib`
- Lean toolchain: `leanprover/lean4:v4.31.0`, Lake `5.0.0`
- Blocking tasks: 36, 37 (referenced in sorry comments)
- lean-action issue #163 (test-args silently ignored — workaround already in place)
