# Implementation Summary: Task #277

**Completed**: 2026-06-22
**Duration**: ~30 minutes

## Overview

Fixed three independent CI failure modes: added repository guards to `lake-update.yml` to prevent fork secret failures, restored `--wfail` to CI flags alongside `--iofail` while suppressing sorry warnings on intentional sorry stubs using `set_option warn.sorry false`, and expanded `pre-pr-check.sh` to cover Bimodal modules.

## What Changed

- `.github/workflows/lake-update.yml` — Added `if: github.repository == 'leanprover/cslib'` to both `bump` and `open-issue` jobs
- `.github/workflows/lean_action_ci.yml` — Restored `--wfail --iofail` in `build-args`, `test-args`, and `TEST_ARGS` echo (was `--iofail` only)
- `Cslib/Logics/LTL/Semantics/GNBA.lean` — Removed 2 unused simp arguments (`Cslib.Automata.ωAcceptor.mem_language` and `NA.Buchi.instωAcceptor`) from `gnba_language_eq` at line 795
- `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` — Added `set_option warn.sorry false in` before 2 sorry-bearing declarations (`backward_until_reflexive`, `backward_since_reflexive`)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` — Added `set_option warn.sorry false in` before 1 sorry-bearing declaration (`bx_le_refl`)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` — Added `set_option warn.sorry false in` before 7 sorry-bearing declarations (Until/Since step properties and content-subset theorems)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` — Added `set_option warn.sorry false` at section scope (10+ sorries, discrete pipeline blocked on task 36)
- `scripts/pre-pr-check.sh` — Added `Cslib/Logics/Bimodal/` to grep paths for sorry/debug/copyright checks and `lake build Cslib.Logics.Bimodal.Metalogic` to build targets

## Decisions

- Used `set_option warn.sorry false in` (not `linter.sorry false`) — the correct Lean 4 built-in option is `warn.sorry` (declared in `Lean.AddDecl`); `linter.sorry` is not a valid option in Lean v4.31.0
- Used section-scope `set_option warn.sorry false` (no `in`) for `ChronicleToCountermodel.lean` due to the large number (10+) of sorry stubs
- `TemporalConservativity.lean` build errors are pre-existing and out-of-scope per the plan (separate task)

## Plan Deviations

- **Task 2.2-2.5** altered: Used `warn.sorry false` instead of `linter.sorry false` — the option name `linter.sorry` does not exist in Lean v4.31.0; `warn.sorry` is the correct built-in option that controls the "declaration uses sorry" warning

## Verification

- Build (targeted modules with `--wfail --iofail`): Success — all 5 modified Lean files pass
- `lake build --wfail --iofail Cslib.Logics.LTL.Semantics.GNBA`: Success
- `lake build --wfail --iofail Cslib.Logics.Bimodal.Metalogic.Bundle.UntilSinceCoherence`: Success
- `lake build --wfail --iofail Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame`: Success
- `lake build --wfail --iofail Cslib.Logics.Bimodal.Metalogic.Bundle.SuccRelation`: Success
- `lake build --wfail --iofail Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodel`: Success
- `lake exe lint-style`: Pass
- Tests: N/A (no test changes)
- Files verified: Yes

## Notes

The full `lake build` fails on `TemporalConservativity.lean` (a pre-existing unrelated issue, explicitly out-of-scope per the plan). The CI changes we made should produce green builds once the `TemporalConservativity` issue is resolved separately. The `--wfail` restoration keeps CI honest for non-sorry warnings while the `warn.sorry false` annotations acknowledge the intentional stubs blocked on tasks 36/37.
