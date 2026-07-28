# Implementation Summary: Restore `lake shake` to a Green, Alignment-Preserving Disposition

- **Task**: 580 - shake_ci_gate_restore_green
- **Plan**: specs/580_shake_ci_gate_restore_green/plans/01_restore-shake-ci-gate.md
- **Status**: COMPLETED (all 4 phases)

## What changed

1. **`Cslib/Logics/Modal/Basic.lean`** (+1 import): added `public import Mathlib.Order.Notation`,
   shake's own suggested addition for this file.
2. **`Cslib/Foundations/Data/HasFresh.lean`** (-1, +4 imports): removed
   `public import Mathlib.Analysis.Normed.Field.Lemmas`; added `Mathlib.Analysis.Normed.Group.Basic`,
   `Mathlib.Topology.MetricSpace.Bounded`, `Mathlib.Data.EReal.Operations`,
   `Mathlib.Topology.Algebra.InfiniteSum.Order`.
3. **`scripts/check-shake-residue.sh`** (new, executable): exact-set ratchet guard on `lake shake
   --add-public --keep-implied --keep-prefix Cslib`. No-args verifies against the baseline;
   `--update` re-baselines from the live flagged set; `--list` prints the live flagged set; any
   other flag is a usage error (exit 2). Follows `check-lint-suppressions.sh`'s shape: header
   comment, `REPO_ROOT` resolution, `set -uo pipefail` without `-e` (shake legitimately exits 1
   when it has suggestions). Exits 2 whenever shake's own exit code falls outside `{0,1}`, or
   when it exits 1 but no flagged-file line is parseable -- a broken environment (missing
   `.olean`s) can never masquerade as a clean/empty flagged set.
4. **`scripts/shake-residue-baseline.txt`** (new): the frozen, checked-in exact-set baseline.
5. **`scripts/pre-pr-check.sh`**: added step 7, invoking the new guard after the existing build
   steps (4/5), following step 6's `check-lint-suppressions.sh` accumulate-into-`failed` shape.
6. **`scripts/README.md`**: documented the new script and baseline.
7. **`.github/workflows/lean_action_ci.yml`**: commented out the `"lake shake"` CI step, matching
   upstream's own `#`-per-line commenting shape (upstream commit
   `74600063621f66f0dbfbac31963cd1219e0e05ed`, "ci: disable shake again (#397)"). Added an inline
   rationale block above it recording the audit date, the upstream SHA compared against, the
   byte-identical-residue statement, upstream's disabling commit, why selective per-file exemption
   was rejected, and a pointer to the new local guard. No task-number references.

## Deviation from the plan: live residue is 9 files, not 10

The plan (following the research report) predicted the flagged-file count would drop from 12 to
exactly 10 after fixing the two locally-modified files -- the report's 10 IDENTICAL rows. The
live, twice-verified (byte-identical repeat runs) post-edit `lake shake` result is **9 files**:
`Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/LcAt.lean` (report row 11) no longer
appears.

Root cause: `LcAt.lean` imports `Untyped/Basic.lean`, which imports `HasFresh.lean`. With
`--keep-implied`, one of the four Mathlib imports newly added to `HasFresh.lean` in Phase 1 now
transitively supplies the import `LcAt.lean` needed (`Mathlib.Data.Int.ConditionallyCompleteOrder`
per the report), so shake no longer flags it. `LcAt.lean` itself was never edited and is confirmed
byte-identical to `upstream/main` in Phase 4, alongside the other 9 residual files -- this is a
side effect of the sanctioned `HasFresh.lean` edit, not a NON-GOALS violation.

The Phase 2 baseline was seeded from this live 9-file set (via `check-shake-residue.sh --update`),
not from the report's stale 10-file prediction, consistent with the guard's own
live-output-is-authoritative design. Every deviation point is annotated inline in the plan file
(`specs/580_shake_ci_gate_restore_green/plans/01_restore-shake-ci-gate.md`).

## Verification results

- **Phase 1**: both edited modules build clean individually and in a full `lake build`
  (3309/3309 jobs). Pre-edit and post-edit build-warning sets are byte-identical (same 5
  pre-existing `sorry` warnings) -- no new warnings introduced.
- **Phase 2 (guard)**:
  - Clean path: `bash scripts/check-shake-residue.sh` -> exit 0, "OK: shake-flagged set matches
    the baseline exactly."
  - Regression path (proven, not assumed): deleted `TimeM.lean`'s line from a `.bak`-backed
    baseline copy -> `FAIL` + exit 1 naming the file; restored via `mv` (never `git
    checkout`/`git restore`).
  - Improvement path (proven): appended a fabricated path to a `.bak`-backed baseline copy ->
    `IMPROVED` + exit 0 + re-baseline note; restored via `mv`.
  - `--list` prints the 9-path live set, exit 0; an unrecognized flag exits 2.
- **Phase 3 (workflow)**: file parses as valid YAML (`python3 -c "import yaml..."`); `git diff`
  confined to the shake step + its new comment block -- `TEST_ARGS`, `lean-action`, `mk_all`,
  `checkInitImports`, and the `lint-style-action` pin are byte-unchanged. Comment block contains
  the literal strings `2026-07-28`, `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`,
  `74600063621f66f0dbfbac31963cd1219e0e05ed`, and `scripts/check-shake-residue.sh`.
- **Phase 4 (final re-verification)**:
  - Resolved `upstream/main` SHA: `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1` -- unchanged from the
    audit SHA, no drift (R7 non-issue).
  - All 9 residual files, plus `LcAt.lean` separately, confirmed `git diff --quiet upstream/main`
    exit 0 (byte-identical).
  - `lake test` -> exit 0 (same 5 pre-existing warnings: 4 `sorry` declarations plus the
    `privateInPublic` warning in `CslibTests/FreeMonad.lean`; nothing new).
  - `lake exe mk_all --check` -> exit 0 ("No update necessary").
  - `lake exe checkInitImports` -> exit 0.
  - `lake exe lint-style` -> exit 0.
  - `bash scripts/check-shake-residue.sh` -> exit 0.
  - `bash scripts/check-lint-suppressions.sh` -> exit 0 (19 blanket suppressions, baseline ceiling
    19 -- unchanged, confirming no collateral).
  - `lake build --wfail --iofail` (the sorry gate) confirmed still RED as expected -- fails on the
    same 4 pre-existing sorry-bearing modules (`Modal/Tableau/FrameSoundness.lean`,
    `Propositional/Tableau/Intuitionistic/{Scheme,Completeness}.lean`,
    `Propositional/Tableau/Minimal/Completeness.lean`). Build args untouched. This is explicitly
    out of scope for this task and was not modified.
  - `git status --short`: the five task files (`Cslib/Logics/Modal/Basic.lean`,
    `Cslib/Foundations/Data/HasFresh.lean`, `.github/workflows/lean_action_ci.yml`,
    `scripts/check-shake-residue.sh`, `scripts/shake-residue-baseline.txt`,
    `scripts/pre-pr-check.sh`, `scripts/README.md`) were all already committed by Phase 3; no
    file outside the intended set was modified. Pre-existing unrelated dirty files
    (`.claude/scripts/literature-*.sh`, `specs/TODO.md`, `specs/state.json`, etc.) were dirty
    before this task began and are outside its scope.
  - Zero sorries, zero vacuous definitions introduced in either edited file (grep checks empty).
  - Axiom count unchanged: 26 before this task's commits, 26 after -- no new axioms.

## Definition of Done -- checklist

- [x] Locally-modified bucket (`Modal/Basic.lean`, `HasFresh.lean`) shake-clean (verified via
      individual scoped builds; the files no longer appear in shake's flagged-file list).
- [x] Upstream-identical bucket untouched and still byte-identical (all 9 residual files plus
      `LcAt.lean` confirmed via `git diff --quiet upstream/main`).
- [x] Shake gate disabled with audit date and upstream SHA recorded inline.
- [x] Local guard (`check-shake-residue.sh` + baseline) pinning the exact residue, proven working
      on all four code paths (clean/regression/improvement/bad-flag).
- [x] Four other non-build CI steps (`lake test`, `mk_all --check`, `checkInitImports`,
      `lint-style`) re-verified exit 0.
- [x] `--wfail --iofail` build args untouched; sorry gate confirmed still red and explicitly
      out of scope.

## Plan Deviations

One deviation throughout, all stemming from a single root cause, documented inline at each
occurrence in the plan file:

- **Live shake residue is 9 files, not the predicted 10** (Phase 1 task checklist, Phase 2 task
  checklist and Verification, Phase 4 task checklist and Verification). `LcAt.lean` (report row
  11) dropped out of the flagged set as a `--keep-implied` transitive-import side effect of the
  sanctioned `HasFresh.lean` edit -- it was never itself touched, and its byte-identity to
  upstream was separately confirmed in Phase 4. This is a genuine improvement (fewer files need
  tracking as debt), reproduced twice via consecutive `lake shake` runs before being accepted as
  ground truth, and does not violate any NON-GOALS. All references to "10" elsewhere in the plan
  document (task instructions and phase text predating this discovery) are superseded by this
  correction; the checked-in baseline and this summary use the live-verified 9-file set as the
  authoritative record.

No other deviations. All FILE SCOPE, NON-GOALS, and Phase 2-gates-Phase-3 constraints from the
task delegation were honored: no blanket `lake shake --fix`, no upstream-identical file modified,
no proof/definition/theorem touched, `--wfail --iofail` args unchanged, no destructive git
operation used (all guard verification used `.bak` copies + `cp`/`mv`), no task-number reference
in any deliverable outside `specs/**`.

## Out of scope (confirmed, not attempted)

`lake build --wfail --iofail` (the sorry gate) remains red, as it was before this task and as the
task explicitly scoped out. No sorry, proof, definition, or theorem statement was touched.

## Next steps

This task's implementation is complete. Per the PR/push prohibition, no branch was created and no
PR was submitted -- the user may invoke `/pr 580` (or the standard `/merge` flow, depending on
this task's `task_type` routing) to submit these changes for review.
