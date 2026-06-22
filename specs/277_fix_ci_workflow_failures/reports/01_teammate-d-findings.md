# Teammate D Findings: Long-Term CI Strategy

**Task 277**: Fix recurring CI workflow failures (runs 27986662089, 27984755605, 27983889592)
**Role**: Horizons — long-term CI strategy alignment for a fork contributing upstream

---

## Key Findings

### 1. Root Cause: Recurring `--wfail` Drift

The fork (`benbrastmckie/cslib`) has experienced a repeating pattern with the `--wfail` flag:

| Commit | Action |
|--------|--------|
| `57109904` (task 206) | Removed `--wfail` to allow development with sorry stubs |
| `ed63767d` (task 206) | Restored `--wfail` to match upstream |
| `c76df599` (merge upstream) | Correctly included `--wfail` |
| `849f049b` ("update", Jun 16) | Removed `--wfail` again |

The June 22 CI failures were triggered by commits pushing new Lean files (tasks 272-276) while the CI was in the "removed --wfail" state. This means the 3 failing runs were catching actual build errors or warnings-treated-as-errors introduced by the batch of new proofs.

**The core tension**: Upstream CSLib (and Mathlib) mandate `--wfail` on all CI runs. The fork carries ~24 `sorry` stubs in in-progress files. `sorry` generates Lean warnings. `--wfail` causes warnings to fail CI. Therefore: restoring `--wfail` would surface sorry-warning failures across 6 files.

### 2. The Fork's CI Posture Is Inherently Unstable

The fork is running the upstream CSLib CI workflow (`lean_action_ci.yml`) against a codebase that contains work-in-progress content that would not pass upstream's own CI. This is a structural mismatch:

- **Upstream CI assumption**: all merged code is sorry-free and warning-clean
- **Fork reality**: code includes sorry stubs gated behind task dependencies (tasks 36, 37)

The fork patches this mismatch by removing `--wfail`, but this removal keeps getting lost during upstream merges, creating a recurring breakage cycle.

### 3. Sorry-Bearing Files (6 files, 24 instances)

Files in the fork's `Cslib/` tree that have sorry stubs:
- `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` (7 sorry, blocked on task 37)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` (2 sorry, blocked on task 37)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` (12 sorry, blocked on task 36)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` (1 sorry, blocked on task 36)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` (1 sorry, blocked on task 36)
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` (1 sorry)

These files exist in the fork's barrel import (`Cslib.lean`) but are NOT in upstream `leanprover/cslib`. They represent work that is not yet ready for upstream submission.

### 4. CI Workflows Are Mostly Appropriate for a Fork

The majority of CI workflows are already correctly scoped:

- **Correctly guarded** (`if: github.repository == 'leanprover/cslib'`): `bump_toolchain_nightly-testing.yml`, `weekly-lints.yml`, `docs.yml`, `release.yml`, `merge_main_into_nightly-testing.yml`, `report_failures_nightly-testing.yml`. These workflows require secrets (`MATHLIB_NIGHTLY_TESTING_APP_ID`, `ZULIP_API_KEY`) that the fork does not have and would correctly no-op.

- **No guard** (runs on all forks): `lean_action_ci.yml`, `shellcheck.yml`, `pr-title.yml`, `todo-issue.yml`. These are appropriate to run on forks.

The primary issue is `lean_action_ci.yml` which is the core build/lint check and is designed to run on forks.

### 5. Mathlib Version Drift

The fork uses mathlib `rev = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"` while upstream uses `rev = "29af524..."` (bumped in upstream's PR #670). The local toolchain is `v4.31.0` while upstream has advanced to `v4.32.0-rc1`. This version drift means:
- The fork may miss breaking changes that upstream has already handled
- New modules added locally are compiled against an older Mathlib, complicating future upstream PRs

### 6. Pre-PR Local Check Script Is Incomplete

`scripts/pre-pr-check.sh` checks only `Cslib/Foundations/Logic/`, `Cslib/Logics/Modal/`, and `Cslib/Logics/Temporal/` — not `Cslib/Logics/Bimodal/`. This gap means new Bimodal files (the primary area of development) are not verified locally before pushing. The script also hardcodes specific build targets rather than running the full `lake build`.

### 7. No Git Hooks Are Active

`/.git/hooks/` contains only `.sample` files. No pre-push or pre-commit hooks are installed. The fork's primary guard against breaking CI is running commands manually, which is error-prone.

---

## Strategic Recommendations

### Short-Term (fixes for task 277)

1. **Restore `--wfail` in the CI workflow** — sync with upstream's `lean_action_ci.yml` exactly. The current divergence (`--iofail` only) is the direct cause of both this CI failure and the recurring drift pattern.

2. **Suppress sorry warnings locally using `set_option`** — rather than removing `--wfail` from CI, add `set_option linter.sorry false` locally in each sorry-bearing file (or scope sorry blocks with `section`/`set_option`). This keeps CI honest while allowing in-progress work. The pattern:
   ```lean
   set_option linter.sorry false in
   theorem foo : P := by sorry
   ```

3. **Alternatively: use `-- nolint sorry`** or the `@[sorry]` attribute if CSLib provides it. Confirm by checking Mathlib's pattern for handling in-progress stubs.

### Medium-Term

4. **Add a pre-push git hook** that runs `lake build --wfail --iofail` before allowing a push to origin. This catches CI failures locally before they appear in GitHub Actions. A minimal hook:
   ```bash
   #!/usr/bin/env bash
   set -e
   echo "Running pre-push CI check..."
   lake build --wfail --iofail
   lake exe checkInitImports
   echo "Pre-push checks passed."
   ```
   Install at `.git/hooks/pre-push` (or provide a `make install-hooks` target in the project).

5. **Update `scripts/pre-pr-check.sh`** to cover all active modules, not just Modal/Temporal. Extend the sorry scan and header check to `Cslib/Logics/Bimodal/` and run `lake build` (full build, not module-scoped) with `--wfail --iofail`.

6. **Bump the Mathlib/toolchain version to match upstream** — reduces the risk of merge-conflict-inducing API changes when upstreaming the in-progress modules. This should be done task-by-task rather than in a single risky bump.

### Long-Term

7. **Adopt a branch strategy that separates upstream-ready from in-progress** code:
   - `main` — mirrors upstream's state plus only upstream-merged content (stays sorry-free)
   - `develop` — carries in-progress sorry stubs; CI here can relax `--wfail` intentionally
   - Feature branches for individual upstream PRs

   This separates "what will be pushed to GitHub" from "what is being worked on locally." In-progress work stays on `develop`; only PR-ready content is rebased to `main` before submission.

8. **Track sorry stubs as a first-class metric** — maintain a `specs/sorry-inventory.md` listing every sorry instance, its blocking task number, and expected resolution. This surfaces progress and prevents sorry accumulation going unnoticed. The `/vet` command could automatically scan for and report this inventory.

9. **Mirror upstream CI updates automatically** — rather than periodic manual merges that lose local patches (like `--wfail`), use a GitHub Actions workflow that automatically opens a PR when the upstream `lean_action_ci.yml` changes. The existing `lake-update.yml` already demonstrates the bump-PR pattern; the same can be applied to CI workflow files.

---

## Long-Term Vision

The fundamental challenge for this fork is that it serves two simultaneous purposes:

1. **Development workspace** — for exploratory, in-progress Lean formalization with sorry stubs
2. **Upstream contribution pipeline** — for staging code that will eventually be PR'd to `leanprover/cslib`

These two purposes have conflicting CI requirements. The cleanest long-term resolution is to separate them by branch:

- Treat `main` as **upstream-tracking**: always sorry-free, always passing `--wfail`, always ready to PR to upstream
- Carry in-progress work on `develop` or topic branches where `--wfail` is known to be relaxed intentionally and documented

The recurring `--wfail` drift is a symptom of this architectural tension, not an independent bug. Each time it's "fixed" by removing the flag, the fix papers over the real issue (sorry stubs in CI-checked code) rather than resolving it.

Additionally, the fork would benefit from **upstream CI visibility**: subscribing to upstream's `nightly-testing` failure notifications (already present as `report_failures_nightly-testing.yml` in the Zulip channel `nightly-testing-cslib`) would make it easy to detect when Mathlib bumps break the code before the fork attempts a merge. The fork currently misses this because the nightly-testing workflows are guarded by `github.repository == 'leanprover/cslib'`.

A practical variant: subscribe locally (via a weekly cron job or Zulip webhook) to upstream CI status, and run `lake update && lake build` locally against the latest upstream Mathlib pin at least once per week. This converts upstream breakage from a surprise (discovered at PR submission time) to a routine catch.

---

## Confidence Level

**High** — on root cause analysis (the `--wfail` drift mechanism is well-evidenced in git history and file diffs).

**Medium** — on strategic recommendations (the branch strategy and pre-push hooks are standard practice, but the right tradeoffs depend on the author's workflow preferences and how aggressively upstream contributions are pursued).

**Low** — on the specific sorry-suppression mechanism (`set_option linter.sorry false`). The correct Lean 4 / CSLib pattern for annotating intentional in-progress stubs should be verified against Mathlib's current conventions before adopting.
