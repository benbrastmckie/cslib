# Teammate A Findings: CI Workflow Failure Analysis

**Date**: 2026-06-22
**Runs analyzed**: 27986662089, 27984755605, 27983889592

---

## Key Findings

Two **distinct failure patterns** exist across the three CI runs:

### Pattern 1: `lake build --iofail` failures (runs 27984755605, 27983889592)

The Lean Action CI workflow (`lean_action_ci.yml`) passes `build-args: "--iofail"` to `lake build`.
The `--iofail` flag in Lake 5.0.0 treats **any warning-level diagnostic as a build failure**.
This causes five modules to be listed under "Some required targets logged failures":

| Module | Failure Type | File | Lines |
|--------|-------------|------|-------|
| `Cslib.Logics.LTL.Semantics.GNBA` | Unused `simp` arguments | `Cslib/Logics/LTL/Semantics/GNBA.lean` | 795:13, 795:52 |
| `Cslib.Logics.Bimodal.Metalogic.Bundle.UntilSinceCoherence` | `sorry` | `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` | 35, 39 |
| `Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame` | `sorry` | `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` | 159 |
| `Cslib.Logics.Bimodal.Metalogic.Bundle.SuccRelation` | `sorry` | `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` | 253, 258, 263, 267, 273, 279, 285 |
| `Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodel` | `sorry` | `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 67, 144-175, 178 |

The 5 modules listed above match exactly between run 27983889592 (commit `4d96487b`) and
run 27984755605 (commit `bcdbf298`). Note: the latter run also includes a 5th target failure
(`ChronicleToCountermodel`) that was present in the earlier run too.

### Pattern 2: Missing GitHub App secrets (run 27986662089)

The "Bump Mathlib to LKG" workflow (`lake-update.yml`) uses a GitHub App for authentication
(`actions/create-github-app-token`) that requires `MATHLIB_NIGHTLY_TESTING_APP_ID` and
`MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY` secrets. These secrets are only configured in the
upstream `leanprover/cslib` repository, **not in this fork** (`benbrastmckie/cslib`).

Error: `[@octokit/auth-app] appId option is required`

This workflow was designed for the upstream mathlib compatibility tracking infrastructure and
is not meaningful in a fork context.

---

## Root Cause Analysis

### Root Cause 1: Pre-existing `sorry` declarations blocked on unresolved tasks

The four `sorry`-containing files were introduced to the codebase in:
- **Task 82** (`7f65f654`): initial sorry annotations on Bimodal/Temporal metalogic
- **Task 234** (`9688c483`): partial convention swap that left 3 files with build errors

The sorry comments in these files explicitly identify blockers:
- `SuccRelation.lean`: "sorry: blocked on task 37"
- `UntilSinceCoherence.lean`: "sorry: blocked on task 37"
- `BXCanonical/Frame.lean`: "sorry: blocked on task 36 (requires irreflexive semantics resolution)"
- `ChronicleToCountermodel.lean`: "sorry: blocked on task 36 (discrete_embed_strictMono)"

An additional file (`TemporalConservativity.lean`) from task 275 also contains 1 sorry, but it
did not appear in the failure list for these specific runs (it was added in commit `92206b88`
which is newer than the commits being run in 27983889592 and 27984755605 — but it will fail in
future runs: the run 27987390947 triggered on commit `f974e301` likely fails on it too).

### Root Cause 2: `--iofail` treats all warnings as errors

The CI workflow uses `build-args: "--iofail"` which is correct and intentional — matching
upstream cslib behavior. The `--iofail` flag in Lake causes any module that produces a warning
(including `sorry` warnings and unused `simp` argument warnings) to be counted as a "required
target failure", which causes `lake build` to exit with code 1.

This is the **correct and expected CI behavior**: the fork simply has outstanding warnings that
need to be fixed before CI will pass.

### Root Cause 3: Unused `simp` arguments in GNBA.lean

`Cslib/Logics/LTL/Semantics/GNBA.lean` line 795 has two unused `simp` arguments:
```lean
simp only [Cslib.Automata.ωAcceptor.mem_language, NA.Buchi.instωAcceptor,
  Formula.gnbaOmegaLanguage, Cslib.ωLanguage.mem_def, Set.mem_setOf_eq]
```
- `Cslib.Automata.ωAcceptor.mem_language` is unused
- `NA.Buchi.instωAcceptor` is unused

These are warning-level linter findings (not errors), but `--iofail` promotes them to build failures.

### Root Cause 4: Scheduled workflow not configured for fork

The `lake-update.yml` workflow runs on a schedule and requires upstream CSLib infrastructure
(GitHub App secrets). It is not useful in a fork and will always fail. This is a workflow
configuration mismatch.

---

## CI History

Checking CI history reveals that **all 35+ available runs on the fork have failed** — the CI
has never passed. The number of failing modules has been decreasing over time (from 15+ in the
June 14 runs to 5 now), indicating steady progress toward a clean build.

The June 14 runs failed on many more modules (e.g., `Separation.Defs`, `Modal.Denotation`,
various `Separation.*` modules). Those have been fixed in subsequent commits.

---

## Evidence / Specific Error Messages

### `lake build --iofail` failure (primary):
```
Some required targets logged failures:
- Cslib.Logics.LTL.Semantics.GNBA
- Cslib.Logics.Bimodal.Metalogic.Bundle.UntilSinceCoherence
- Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
- Cslib.Logics.Bimodal.Metalogic.Bundle.SuccRelation
- Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodel
error: build failed
##[error] lake build failed
##[error]Process completed with exit code 1.
```

### GNBA unused simp warning:
```
warning: Cslib/Logics/LTL/Semantics/GNBA.lean:795:13: This simp argument is unused:
  Cslib.Automata.ωAcceptor.mem_language
warning: Cslib/Logics/LTL/Semantics/GNBA.lean:795:52: This simp argument is unused:
  NA.Buchi.instωAcceptor
```

### Sorry warnings (representative):
```
warning: Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean:35:8: declaration uses `sorry`
warning: Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean:39:8: declaration uses `sorry`
```

### GitHub App missing secrets error:
```
Error: [@octokit/auth-app] appId option is required
##[error][@octokit/auth-app] appId option is required
```

---

## Additional Sorry Files (Not Yet Triggering Failures on These Runs)

The following file also has sorry and will cause future CI failures (introduced in commit `92206b88`):
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` — 1 sorry at line 263, blocked on task 36 (domain mismatch resolution)

---

## Workflow Configuration Details

**`lean_action_ci.yml`** (relevant excerpt):
```yaml
- uses: leanprover/lean-action@v1
  with:
    build-args: "--iofail"
    test-args: "--iofail"
```
**`lakefile.toml`** key options:
```toml
weak.linter.mathlibStandardSet = true
```
This enables the full Mathlib standard linter set, which includes unused simp argument linting.

**Lean version**: `leanprover/lean4:v4.31.0`, Lake `5.0.0`

---

## Confidence Level

**High** for all findings:

1. The specific failing files and line numbers are confirmed from CI logs (identical across two runs).
2. The `--iofail` mechanism is confirmed by seeing ⚠ (warning) markers on all 5 failing modules.
3. The `sorry` annotations include inline comments naming the blocking tasks.
4. The GitHub App secrets issue is a direct error message from the action.
5. The GNBA unused simp arguments are precisely identified at line 795 of the file.

---

## Recommended Fixes (Summary)

1. **GNBA.lean** (quick fix): Remove the two unused simp arguments at line 795.
2. **Four Bimodal sorry files**: These are blocked on tasks 36 and 37. Either complete those tasks or accept that CI will remain red until they are resolved.
3. **TemporalConservativity.lean**: 1 sorry blocked on task 36 — will surface in the most recent CI run.
4. **lake-update.yml**: Either disable/delete this workflow in the fork, or add a condition to skip it (e.g., only run if the secrets are present, or if the repo is the upstream `leanprover/cslib`).
