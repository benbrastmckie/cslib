# Implementation Summary: Scope pre-pr-check step 1's sorry gate

- **Task**: 584 - scope_pre_pr_check_sorry_gate
- **Status**: [COMPLETED]
- **Plan**: `specs/584_scope_pre_pr_check_sorry_gate/plans/01_scope-sorry-gate-delegation.md`

## What Changed

All five plan phases completed, one commit per phase:

1. **`scripts/check-sorry-suppressions.sh`** gained `--scope PATH...`: a real argument loop
   replaces the single-token `case` dispatch; a new `sweep_files()` helper routes all three
   `find "$SCAN_ROOT" -name '*.lean'` call sites (verified exactly three exist before
   refactoring) through one path; `--update` combined with `--scope`/`--changed` is refused with
   `exit 2` before any write to the baseline; a mistyped `--scope` path stays a fatal `exit 2`;
   the displayed ceiling total is restricted to swept paths on scoped runs (comparison arrays
   stay whole-baseline-keyed and untouched); the improvement remediation message keeps the bare
   `--update` command plus a scoped-run caveat.
2. The same script gained opt-in `--changed [--base REF]`: merge-base resolution happens in the
   main script body (never inside a pipe subshell, so a resolution failure's `exit 2` actually
   terminates the script) via `resolve_merge_base()`; the changed set is the union of
   `--diff-filter=d` diffs against the merge-base, unstaged, staged, plus untracked files,
   filtered to `*.lean` under `Cslib/`, intersected with `--scope` when both are given, and
   dropping paths no longer on disk; an empty `--changed` result is `exit 0` with an explicit
   "nothing to check" line — a distinct branch from the `--scope` zero-file `exit 2` case.
3. **`scripts/pre-pr-check.sh`** step 1's inline `perl`/`sed`/`grep` sorry-detection pipeline was
   deleted and replaced with a scoped delegation:
   `check-sorry-suppressions.sh --scope Cslib/Foundations/Logic Cslib/Logics/Modal
   Cslib/Logics/Temporal Cslib/Logics/Bimodal`. The announcement line, the four-tree comment (now
   marked as a stale, non-authoritative artifact), the steps 8/9 rationale block, and the
   file-top "steps 1-3 are advisory greps" comment were all corrected to describe the actual
   delegation relationship and to preserve the step-1-vs-step-5 scope distinction. Step numbering
   (1-9) and step 5's `lake build --wfail --iofail` were left untouched.
4. **`scripts/check-sorry-suppressions.sh`**'s header (Usage block, EXIT-CODE CONTRACT, new
   `--update`-refusal rationale subsection, stale "can run as step 1" claim) and
   **`scripts/README.md`**'s "Sorry/suppression volume ratchet" section were updated to document
   the new flags and the dual step-1/step-8 wiring. All edits confirmed to lie inside comment
   blocks only (no executable line touched by this phase); README step citations (7, 8, 9)
   unchanged.
5. Full verification sweep: baseline invariance proven byte-identical and by matching exact
   figures (`markers: 18 (baseline ceiling 18); sorries: 28 (baseline ceiling 28)`); step 1 green
   on the unmodified tree via a full `bash scripts/pre-pr-check.sh` run (step 5 red as declared
   non-goal, steps 6-9 all green); scratch-probe regression test confirmed step 1 goes red on a
   new in-scope sorry and green again after cleanup; scope-asymmetry probe confirmed step 1 stays
   green while step 8 goes red on an out-of-scope (`Propositional/`) sorry; `--update --scope` and
   `--update --changed` both refused with `exit 2`, baseline byte- and mtime-identical afterward;
   the two zero-file conditions (`--scope` mistyped path vs. empty `--changed` set) confirmed
   distinct (`exit 2` vs. `exit 0`); doc step-citation grep confirmed no renumbering-driven edits
   were needed; final tree confirmed clean under `Cslib/` with only the three `file_scope` files
   modified.

## Plan Deviations

None. All five phases were implemented exactly as specified; every "Scope Hypothesis" assertion
(three `find "$SCAN_ROOT"` call sites in Phase 1; seven external step-N citations in Phase 3;
one README section in Phase 4; the exact 18/18, 28/28, 24-hit/6-file figures in Phase 5) was
confirmed by direct `grep`/script execution before proceeding, and matched in every case.

## Hard Guardrails Verified

- Step 5 (`lake build --wfail --iofail`) untouched: confirmed via `grep -n` and by observing it
  still fails on the tree's known 4 bare-sorry files during the Phase 5 full-script run.
- Zero files under `Cslib/` were modified by this task: `git diff --stat 2e4148d7..HEAD --
  Cslib/` is empty across all four implementation-phase commits; the two scratch-probe files
  created during Phase 5 regression testing were deleted before the phase concluded (`git status
  --porcelain Cslib/` empty both times).
- No existing sorry was resolved.
- `scripts/sorry-suppression-baseline.txt` is byte-identical: `git diff --stat` empty at every
  phase boundary, and both attempted scoped `--update` invocations were refused before any write
  (confirmed via SHA-256 hash and mtime comparison in Phase 5).
- Step numbering preserved (still 1-9, confirmed via
  `grep -cE '^echo "[0-9]\.' scripts/pre-pr-check.sh`).
- `--update` refusal guard fires before any write, for both `--scope` and `--changed`.
- The two zero-file conditions stay on separate branches (`exit 2` vs. `exit 0`).
- Scoped runs restrict the *displayed* ceiling to swept paths only, without touching the
  whole-baseline-keyed comparison arrays.
- Step 1's announcement and comments now describe the actual baseline-relative delegation
  behavior rather than the prior misleading "PR scope" framing.

## CI / Verification Notes

This task's `file_scope` is `scripts/pre-pr-check.sh`, `scripts/check-sorry-suppressions.sh`,
`scripts/README.md` only — no `Cslib/` Lean source was modified. The plan's own "Testing &
Validation" section (fully executed in Phase 5, see above) is the authoritative acceptance
criterion for a shell-script-scoped task and subsumes the Lean-build-relevant portions of the
standard CI pipeline: a full `bash scripts/pre-pr-check.sh` run was executed twice (Phase 3 and
Phase 5), exercising `lake build` (step 4), `lake build --wfail --iofail` (step 5), the blanket
linter-suppression ratchet (step 6), the shake import-debt ratchet (step 7), the sorry-suppression
ratchet (steps 1 and 8), and the axiom-census ratchet (step 9) — all green except step 5, which is
red by design on the tree's 4 pre-existing bare-sorry files (a declared non-goal, not introduced
by this task). `lake exe checkInitImports` was additionally run standalone and passed (exit 0, no
output). Since no Lean file was touched, `sorry_count`, `vacuous_count`, and `axiom_count` for
this task's own modified files are trivially 0; the repo-wide baseline figures (28 sorries, 26
top-level `axiom` declarations) are pre-existing and unchanged, confirmed via the byte-identical
`sorry-suppression-baseline.txt` and the empty `Cslib/` diff noted above. `shellcheck` is
unavailable in this environment (consistent with prior tasks' findings); the path-triggered
`shellcheck.yml` workflow will sweep the changed shell scripts on push.

## Files Modified

- `scripts/check-sorry-suppressions.sh`
- `scripts/pre-pr-check.sh`
- `scripts/README.md`
- `specs/584_scope_pre_pr_check_sorry_gate/plans/01_scope-sorry-gate-delegation.md` (phase status
  markers and Scope Hypothesis confirmations)

## Commits

- `task 584 phase 1: add --scope PATH... to check-sorry-suppressions.sh`
- `task 584 phase 2: add opt-in --changed [--base REF] narrowing`
- `task 584 phase 3: rewire pre-pr-check.sh step 1 to a scoped ratchet delegation`
- `task 584 phase 4: document --scope/--changed and fix stale cross-references`
