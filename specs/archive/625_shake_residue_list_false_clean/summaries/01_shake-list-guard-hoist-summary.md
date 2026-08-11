# Implementation Summary: Task #625

- **Task**: 625 - shake_residue_list_false_clean
- **Status**: [COMPLETED]
- **Started**: 2026-08-10T23:13:10Z
- **Completed**: 2026-08-11T00:20:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_shake-list-guard-hoist.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`scripts/check-shake-residue.sh --list` could exit 0 with zero output when `lake shake` failed
to complete an analysis (e.g. a stale `Cslib` facade target, which research confirmed makes
`lake shake` exit 1 before it ever reaches its own import-analysis logic) — indistinguishable
from a genuine "nothing flagged" clean result. All five plan phases are implemented and
verified: the two fatal-condition guards are consolidated into one shared validator
(`validate_shake_result()` / `run_and_validate_shake()`, mirroring
`scripts/check-axiom-census.sh`'s `run_and_validate_census()`), all three usage modes
(`--list`, `--update`, bare) are rewired onto it, `--list` now correctly exits 2 on the
stale-target failure mode, a `--self-test` subcommand with four deterministic fixtures locks the
fix in mechanically, and the EXIT-CODE CONTRACT header is reconciled with the implementation.

## What Changed

- `scripts/check-shake-residue.sh` — added `validate_shake_result()` (pure, globals-only) and
  `run_and_validate_shake()` (composes `run_shake()` + `validate_shake_result()`); rewired
  `--update` and the bare verify path onto the shared helper (Phase 1); rewired `--list` onto the
  same helper with a `[ -n "$live" ]`-guarded print so a genuinely clean run still emits zero
  bytes (Phase 2) — this is the defect fix; added a `--self-test` subcommand with four literal
  fixtures (`flagged`, `stale-target`, `clean`, `bad-exit`), a `SHAKE_SELF_TEST_FIXTURE`
  short-circuit in `run_shake()`, a `SHAKE_SELF_TEST_BASELINE` override for `$BASELINE`, and 18
  PASS/FAIL assertions covering in-process validator/parser behavior and end-to-end per-mode
  subprocess re-invocation (Phase 3); reconciled the EXIT-CODE CONTRACT header block to state the
  four rules govern all three modes uniformly, name the two helper functions as the single
  implementation, extend the Usage/Exit lines for `--self-test`, document the two self-test env
  vars, and note that `--self-test` is deliberately not wired into `scripts/pre-pr-check.sh`
  (Phase 4).

## Decisions

- Kept `validate_shake_result()` and `run_and_validate_shake()` as two separate functions (not
  merged, unlike `check-axiom-census.sh`'s single `run_and_validate_census()`) because Phase 3's
  self-test design specifically requires calling the pure validation logic directly against a
  fixture without invoking `run_shake`'s real `lake shake` call.
- Sourced the `stale-target` self-test fixture's transcript directly from the research report's
  reproduction section (the literal "target is out-of-date and needs to be rebuilt" / "out of
  date oleans" error text plus a `Driver.lean:893:100:`-style repo-relative warning line), so the
  fixture is a faithful encoding of the actual reproduced regression, not an invented analogue.
- Verified the self-test has teeth by deliberately reverting the Phase 2 fix in a scratch copy
  and re-running `--self-test` against it: 17 of 18 assertions still passed, and the one failure
  was exactly `stale-target: --list exits 2` (expected 2, actual 0) — the precise regression this
  task exists to close.

## Plan Deviations

- **Phase 1 Verification bullet** (`grep -c 'expected 0 or 1' ... returns 1`): this assertion's
  true satisfaction point is the end of Phase 2, not Phase 1, since Phase 1's own task list only
  rewires `--update` and the bare path, leaving `--list`'s own copy of the guard text in place
  until Phase 2 replaces it. Reconciled per the Scope Hypothesis's "stop and reconcile rather
  than proceeding" guidance: recorded the count as 2 at the end of Phase 1 and confirmed it
  reached 1 at the end of Phase 2 (see `progress/phase-1-progress.json` and
  `progress/phase-2-progress.json`).
- **Phase 5, "Optionally run `bash scripts/pre-pr-check.sh`"**: deliberately skipped — the plan
  explicitly frames this step as optional and instructs skipping with disclosure if the build
  cost is prohibitive. `pre-pr-check.sh` runs a full build-and-verify pipeline; the bare verify
  path it would exercise (step 7) was already run directly against the live repo and verified in
  this same phase, so the skip does not leave that behavior unverified.

## Verification

- Build: N/A (bash script; `bash -n` syntax-checked after every phase)
- Tests: Passed — `bash scripts/check-shake-residue.sh --self-test` reports 18 passed, 0 failed,
  exit 0. Against a scratch copy with the Phase 2 fix reverted, the self-test correctly fails
  (17 passed, 1 failed) on exactly the reproduced regression.
- Files verified: Yes — `--list`, bare verify, and `--self-test` all run live against the
  actually-built repo in Phase 5; output matches the pre-change 12-entry baseline set exactly;
  `scripts/shake-residue-baseline.txt` confirmed byte-unchanged (`git diff --exit-code`)
  throughout, including after `--self-test`.

## Impacts

- `scripts/check-shake-residue.sh --list` (and the underlying shared guard) is now trustworthy:
  a stale/broken `lake shake` run is reported as exit 2, never silently as a false "nothing
  flagged" clean result, in all three usage modes uniformly.
- The `--self-test` subcommand gives this script the same kind of mechanical regression lock
  `check-boneyard-quarantine.sh` has for its own invariants, without requiring a `lake` invocation
  or a built `.olean` tree.

## Follow-ups

- **Wiring `--self-test` into `scripts/pre-pr-check.sh`** (named Non-Goal / Rollback-Contingency
  item in the plan): would run the self-test on every local pre-PR check without needing a full
  `lake build`, alongside that script's existing Boneyard quarantine self-test step. Deliberately
  not done in this task — declared file scope was `scripts/check-shake-residue.sh` plus fixtures
  only.
- Two files unrelated to this task, `.claude/scripts/literature-fidelity-audit.sh` and
  `.claude/scripts/literature-search.sh`, were already modified in the working tree before this
  task began and remain modified; they are out of this task's scope and were left untouched.

## References

- `specs/625_shake_residue_list_false_clean/plans/01_shake-list-guard-hoist.md`
- `specs/625_shake_residue_list_false_clean/reports/01_shake-residue-false-clean.md`
- `specs/625_shake_residue_list_false_clean/progress/phase-1-progress.json` through
  `phase-5-progress.json`
- `scripts/check-axiom-census.sh` (the in-tree template for the shared-validator shape)
- `scripts/check-boneyard-quarantine.sh` (the in-tree `--self-test` naming/exit-contract precedent)
