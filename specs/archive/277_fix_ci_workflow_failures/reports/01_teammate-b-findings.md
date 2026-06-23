# Teammate B Findings: Alternative Patterns and Prior Art for CI Fix

**Task**: 277 — Fix recurring CI workflow failures  
**Focus**: Upstream comparison, caching strategies, workflow divergences, and prior art

---

## Key Findings

### Finding 1: Two Distinct Failure Categories (Different Fixes Required)

The three failing runs break into two completely different problems:

**A. Lean Action CI failures** (runs 27984755605, 27983889592) — `lake build failed`  
Root cause: `sorry` warnings in fork-specific Lean files trigger the `--iofail` flag in `build-args`, causing build failure.

**B. "Bump mathlib to LKG" failure** (run 27986662089) — `[@octokit/auth-app] appId option is required`  
Root cause: `lake-update.yml` tries to use `MATHLIB_NIGHTLY_TESTING_APP_ID` and `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY` GitHub App secrets that only exist in the upstream `leanprover/cslib` organization. This workflow runs on the fork but lacks a repository guard (`if: github.repository == 'leanprover/cslib'`) that other upstream workflows have.

### Finding 2: The Fork's `--iofail` Change Broke CI (Traced via Git History)

The workflow divergence history, traced exactly:

| Commit | Action | Date |
|--------|--------|------|
| `57109904` | Removed `--wfail` from CI to allow sorry during development (task 206) | 2026-06-15 |
| `ed63767d` | Restored upstream config with `--wfail --iofail` (task 206) | 2026-06-15 |
| `849f049b` | "update" commit — changed `--wfail --iofail` back to `--iofail` only | 2026-06-16 |

The current fork state uses `build-args: "--iofail"` while upstream `leanprover/cslib` uses `build-args: "--wfail --iofail"`.

**Why this matters**: `--iofail` sets `--fail-level=info`, meaning the build fails on any message at severity `info` or above. Since `declaration uses sorry` is emitted at severity `warning` (above `info`), the `--iofail` flag catches sorry warnings and fails the build. The upstream `--wfail --iofail` combination has the same effect (since `--iofail` is stricter), but the fork's removal of `--wfail` was supposed to allow sorry. It did not, because `--iofail` still catches warnings.

### Finding 3: Files with `sorry` in the Fork (Not in Upstream)

CI fails on these specific targets:

| File | Sorry count | Failure in runs |
|------|-------------|-----------------|
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 17 | Both Lean Action CI runs |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` | 7 | Both Lean Action CI runs |
| `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` | 6 | (not flagged yet; may not be in build path) |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` | 3 | — |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` | 2 | Both Lean Action CI runs |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` | 2 | Both Lean Action CI runs |
| `Cslib/Logics/LTL/Semantics/GNBA.lean` | 0 real sorry (1 in comment only) | (flagged for simp warnings) |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` | 1 | — |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` | 1 | — |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 1 | — |
| `Cslib/Logics/Bimodal/Metalogic/Algebraic/InteriorOperators.lean` | 1 | — |
| `Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean` | 1 | — |

The GNBA failure in run 27983889592 is from unused `simp` arguments (warnings), not sorry.

### Finding 4: The `lake-update.yml` Runs in Fork Without Required Secrets

Unlike most other upstream workflows (`docs.yml`, `bump_toolchain_nightly-testing.yml`, `weekly-lints.yml`, etc.), `lake-update.yml` lacks a `if: github.repository == 'leanprover/cslib'` guard. The workflow requires:
- `MATHLIB_NIGHTLY_TESTING_APP_ID` secret
- `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY` secret

These are GitHub App credentials owned by the `leanprover` organization. When the workflow runs on the fork (`benbrastmckie/cslib`), step "Generate app token" fails immediately.

### Finding 5: `test-args` in lean-action is Currently Broken (Known Upstream Issue)

There is an open bug in `leanprover/lean-action` (issue #163): the `test-args` input is silently ignored because `lake_test.sh` references `$TEST_ARGS` but the test step in `action.yml` never maps `inputs.test-args` to that environment variable. The workaround already present in the fork's workflow — setting `TEST_ARGS` manually via `echo "TEST_ARGS='--iofail'" >> $GITHUB_ENV` — is the correct approach identified as the workaround in the issue.

### Finding 6: No Cache Miss Issues (Lean Action CI Caching is Working Correctly)

The CI logs show `lake exe cache get` running successfully and downloading Mathlib oleans. The `actions/cache/restore@v5` step correctly sets keys and restore-keys. Cache is not the cause of the failures. The GitHub Actions cache backend was upgraded from legacy (deprecated Feb 2025) and lean-action v1 already uses `actions/cache@v5`.

### Finding 7: Upstream CI Passes Despite Using `--wfail --iofail`

The upstream `leanprover/cslib` uses `build-args: "--wfail --iofail"` (same or stricter than the fork's `--iofail`) and their CI passes. This means upstream has no `sorry` in their Lean files. All the sorry declarations in the failing files are fork-specific additions from task implementations.

---

## Recommended Approach

**Two-track fix** is needed — one for each failure category.

### Track 1: Fix Lean Action CI (sorry-related failures)

**Option A (Preferred): Resolve the sorry declarations**  
Remove `sorry` from the failing files by completing the proofs. This is the upstream-compliant approach. The 5 files that caused actual CI failures in the logged runs contain a total of ~29 sorry instances (excluding files not yet reached in build order).

**Option B (Development mode): Suppress `--iofail` temporarily**  
Change `build-args: "--iofail"` to no build-args at all (or `build-args: ""`) to match a permissive mode while work is in progress. This is explicitly what commit `57109904` did, but it should be reverted once proofs are complete.

**Why Option B is not a complete solution**: Even with no `--wfail`/`--iofail`, the `lint-style-action` step still runs and may catch lint issues. And this only masks the problem temporarily — PRs back to upstream will be blocked by their CI anyway.

**Recommendation**: If submitting PRs to upstream is the goal, resolve the sorry declarations (Track 1 Option A). If this is a development fork where CI should pass without completing all proofs, use Option B but document it clearly.

### Track 2: Fix "Bump mathlib to LKG" failures

Add a repository guard to `lake-update.yml` so it only runs on `leanprover/cslib`:

```yaml
jobs:
  bump:
    runs-on: ubuntu-latest
    if: github.repository == 'leanprover/cslib'
```

This pattern is already used by `docs.yml`, `bump_toolchain_nightly-testing.yml`, `weekly-lints.yml`, `merge_main_into_nightly-testing.yml`, and `release.yml`. The `lake-update.yml` is simply missing this guard.

---

## Evidence / Examples

### Upstream vs. Fork Workflow Diff

```diff
# Upstream leanprover/cslib lean_action_ci.yml
-          echo "TEST_ARGS='--wfail --iofail'" >> $GITHUB_ENV
-          build-args: "--wfail --iofail"
-          test-args: "--wfail --iofail"

# Fork benbrastmckie/cslib (current)
+          echo "TEST_ARGS='--iofail'" >> $GITHUB_ENV
+          build-args: "--iofail"
+          test-args: "--iofail"
```

### CI Log Evidence: sorry warnings triggering `--iofail`

From run 27984755605 (the tail of the log):
```
⚠ [2952/3015] Building Cslib.Logics.Bimodal.Metalogic.Bundle.UntilSinceCoherence
warning: Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean:35:8: declaration uses `sorry`
warning: Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean:39:8: declaration uses `sorry`
...
Some required targets logged failures:
- Cslib.Logics.LTL.Semantics.GNBA
- Cslib.Logics.Bimodal.Metalogic.Bundle.UntilSinceCoherence
- Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
- Cslib.Logics.Bimodal.Metalogic.Bundle.SuccRelation
- Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodel
error: build failed
```

### lake-update.yml Failure Evidence

From run 27986662089:
```
X Generate app token
[@octokit/auth-app] appId option is required
```

All downstream steps skipped because the GitHub App token could not be created (missing secrets).

### Repository Guard Pattern (from working workflows)

```yaml
# lake-update.yml should add this to each job:
jobs:
  bump:
    if: github.repository == 'leanprover/cslib'
```

---

## Confidence Level

| Finding | Confidence | Basis |
|---------|-----------|-------|
| `--iofail` catches sorry warnings | High | Observed in CI logs: "warning: declaration uses sorry" directly precedes "error: build failed"; `--fail-level=info` threshold is below warning severity |
| The `849f049b` "update" commit caused regression | High | Git log confirms this commit changed `--wfail --iofail` to `--iofail` while sorry was already in the files |
| `lake-update.yml` missing repository guard | High | Confirmed by examining all workflow files; `lake-update.yml` is the only workflow with GitHub App token requirements that lacks the guard |
| `test-args` silently ignored (lean-action #163) | High | The manual workaround in the workflow is the exact fix described in the open issue |
| Cache is not the root cause | High | CI logs show successful `lake exe cache get` with packages downloading; cache hits on retry keys |
| Option A (resolve sorry) is the complete fix | Medium | Depends on whether the sorry files are intended to eventually become sorry-free. The 5 failing files belong to Bimodal/BXCanonical work. If these tasks are still open/in-progress, Option B may be the right interim choice. |
