# Teammate C (Critic) Findings: CI Workflow Failures

**Date**: 2026-06-22
**Role**: Adversarial investigation — gaps, blind spots, conflation risks

---

## Key Findings

### Finding 1: The Three Runs Are NOT Failing for the Same Reason

This is the central blind spot to challenge. There are **two entirely separate failure modes**:

**Failure Mode A — Lean build with `--iofail` flag (Runs 27984755605 and 27983889592)**

These fail because `lake build --iofail` treats warnings as errors. The specific failing targets in BOTH runs are identical:
- `Cslib.Logics.LTL.Semantics.GNBA` — unused `simp` arguments (warnings)
- `Cslib.Logics.Bimodal.Metalogic.Bundle.UntilSinceCoherence` — `sorry` warnings
- `Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame` — `sorry` warning
- `Cslib.Logics.Bimodal.Metalogic.Bundle.SuccRelation` — `sorry` warnings (multiple)
- `Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodel` — `sorry` warnings

The root issue: `--iofail` causes Lean to exit with code 1 when any warnings exist. The `sorry`-containing files **compile successfully** but emit warnings that trigger `--iofail`. The GNBA file has an unused simp argument warning (not a sorry).

**Failure Mode B — `Bump mathlib to LKG` workflow (Run 27986662089)**

This fails with `[@octokit/auth-app] appId option is required` — a completely separate issue caused by missing GitHub App secrets (`MATHLIB_NIGHTLY_TESTING_APP_ID` and `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY`) in this fork repository. This has been failing **every day since at least June 15** and is entirely independent of the Lean code. It requires GitHub App credentials that exist only in the upstream `leanprover/cslib` repo.

### Finding 2: The Lean CI Failure Was Present Before the Listed Runs (Pre-existing)

The June 21 failure (run 27910057382, commit `4d96487b`) shows a **larger** set of failing modules:
- `Cslib.Logics.Propositional.Semantics.Algebra.Conservative`
- `Cslib.Logics.Bimodal.Metalogic.Soundness.DenseSoundness`
- `Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes`
- `Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.*` (multiple)
- Plus the same 5 modules from the listed runs

This means the 272-276 implementation batch (commit `92206b88`) **improved** the situation by fixing 10+ modules but left 5 still failing. The task description framing this as a single "recurring" issue obscures that significant progress was made and only a residual set remains.

### Finding 3: The Latest CI Run (After the Listed Runs) Has a New Failure

Run 27987390947 (`vet: add Glivenko1929 to references.bib`) shows an **additional** failing module not present in the listed runs:
- `Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.TemporalConservativity`

This file was added in commit `92206b88` with acknowledged sorries (6 sorries, task 275 marked PARTIAL). The latest run adds real compilation errors to this file:
```
error: Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean:116:8:
  Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: ...TemporalConservativity.lean:108:4: (kernel) declaration has metavariables
error: ...TemporalConservativity.lean:161:4: unknown metavariable '?_uniq.3570'
```

This is NOT a sorry-warning issue — it is a genuine proof error causing `Lean exited with code 1`. The file also has `--iofail`-triggering warnings. This represents a third failure mode not in the original runs.

### Finding 4: The `--iofail` Flag in the Workflow is the Architectural Decision Causing All Sorry-Related Failures

The CI workflow (`lean_action_ci.yml`) passes `--iofail` to both build and test:
```yaml
build-args: "--iofail"
test-args: "--iofail"
```

This flag means "fail if any IO warning is emitted." In Lean/Lake, `sorry` emits a warning. Therefore, **any sorry in any file that is compiled** causes CI failure. This is correct behavior for an upstream library — but for an active development fork with acknowledged partial work, it creates persistent CI noise.

The git history shows this was previously modified (commit `ed63767d` disabled `--wfail --iofail`, commit `5eb49d96` disabled `lake test`, commit `ed63767d` restored `--wfail --iofail`). This indicates an ongoing tension between strict CI and development workflow.

### Finding 5: The Sorry Files Are Intentionally Partial — Not Broken Code

The sorries in `UntilSinceCoherence.lean`, `SuccRelation.lean`, and `BXCanonical/Frame.lean` all have comments `-- sorry: blocked on task 37` or similar. These are **deliberately unfinished proofs**, not regressions. The `--iofail` flag was inherited from upstream and makes CI fail on any partial work.

---

## Gaps and Blind Spots Identified

1. **Conflation of two independent failure modes**: The task title "recurring CI workflow failures" conflates the Lean build failure (code-related, fixable) with the Bump mathlib app-auth failure (infrastructure/secrets, not fixable without GitHub organization access).

2. **Conflation of sorry-warnings with proof errors**: `TemporalConservativity.lean` has genuine proof errors (metavariables, failed rewrites) that are separate from the sorry-triggered-`--iofail` failures in the other files.

3. **The Bump mathlib workflow is unfixable in the fork**: `MATHLIB_NIGHTLY_TESTING_APP_ID` and `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY` are secrets that exist only in the upstream `leanprover/cslib` repo. A fork cannot set these unless explicitly configured. The workflow has a guard `if: github.repository == 'leanprover/cslib'` in `bump_toolchain_nightly-testing.yml` — but the `lake-update.yml` (`Bump mathlib to LKG`) does NOT have this guard.

4. **The "fix" options may have different scopes**: Fixing CI means either:
   - (a) Remove sorries from the 5 persistent files (proof completion work)
   - (b) Disable `--iofail` in the workflow (weakens CI, bad for upstream PR readiness)
   - (c) Add `if: github.repository == 'leanprover/cslib'` guard to lake-update.yml (fixes Bump mathlib silently)
   - (d) Fix the actual proof errors in `TemporalConservativity.lean` (distinct from sorry removal)
   These are four separate fixes for different problems.

5. **Assumption of transient vs persistent**: None of these failures are transient infrastructure issues. The Lean build failures have been reproducible across commits; the Bump mathlib failure has been happening every single day for at least 8 days.

6. **The GNBA warning is not a sorry**: `GNBA.lean:795` has unused simp arguments — this is different from sorry warnings and may be an unrelated linting issue introduced during implementation of GNBA.

---

## Questions That Need Answers

1. **Is the goal to fix CI for upstream PR submission or for local development tracking?**
   - If upstream PR: removing sorries is the only valid approach; `--iofail` must stay
   - If local tracking: disabling `--iofail` or adding `ci-skip` labels on known-partial files would be acceptable

2. **Is `TemporalConservativity.lean` meant to be submitted as-is (with sorries)?**
   - The file has a proof error (metavariable, failed rewrite) on top of the sorry — these need separate fixes
   - The sorry at line 263 is acknowledged as a "domain mismatch" gap; the metavariable error at line 108/161 is a distinct problem

3. **Should lake-update.yml be disabled or have a fork-guard added?**
   - Every fork of cslib will have this Bump mathlib failure unless they either (a) set up the GitHub App or (b) add a repository guard
   - The fix is trivial: add `if: github.repository == 'leanprover/cslib'` to both jobs in lake-update.yml

4. **What are the sorry-blocked files actually waiting on?**
   - `SuccRelation.lean` and `UntilSinceCoherence.lean` comment `blocked on task 37` — what is task 37?
   - `BXCanonical/Frame.lean` comments `blocked on task 36` — what is task 36?
   - These may be long-standing blockers or may be tasks that have since been created/completed

5. **Is the unused simp argument in GNBA.lean a warning-as-error under `--iofail`?**
   - The log shows it causes a "required target logged failures" for GNBA — confirming yes
   - Was this warning present before the GNBA implementation was committed, or is it a regression?

---

## Confidence Level

**High confidence**:
- The Bump mathlib failure (run 27986662089) is caused by missing GitHub App secrets, is entirely separate from the Lean build failures, and is unfixable without credentials
- The Lean build failures in runs 27984755605 and 27983889592 are caused by `--iofail` treating sorry-warnings as errors
- All three originally-listed runs fail for reasons that were **present before those runs** (pre-existing issues not introduced by those specific commits)

**High confidence**:
- The failing targets in runs 27984755605 and 27983889592 are identical (5 modules)
- The June 21 failure had a larger set of failing modules; the implementation batch reduced the failure count

**Medium confidence**:
- The metavariable/rewrite errors in `TemporalConservativity.lean` (latest run 27987390947) may have been introduced by a vet-operation commit (`f974e301`) modifying `references.bib` but NOT the Lean file itself — this is puzzling and may indicate a Lean caching issue or a pre-existing error that wasn't caught until a clean build
- The `--iofail` tension between upstream norms and fork development workflow may be the core architectural issue to address

**Low confidence**:
- Whether removing `--iofail` is acceptable as a fix (depends on the user's contribution workflow)
- Whether there is a way to selectively exempt known-partial files from `--iofail` in Lean/Lake
