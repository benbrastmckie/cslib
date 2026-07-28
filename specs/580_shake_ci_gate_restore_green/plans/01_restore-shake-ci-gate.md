# Implementation Plan: Restore `lake shake` to a Green, Alignment-Preserving Disposition

- **Task**: 580 - shake_ci_gate_restore_green
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/580_shake_ci_gate_restore_green/reports/01_shake_ci_gate_restore_green.md
- **Artifacts**: plans/01_restore-shake-ci-gate.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`lake shake --add-public --keep-implied --keep-prefix Cslib` currently exits 1 on 12 files, making
CI red for a reason independent of the sorry gate. The research report re-derived the split live:
2 of the 12 flagged files already diverge from `upstream/main` and are freely fixable at zero
alignment cost; the other 10 are byte-identical to upstream and represent upstream's own unresolved
import debt. This plan fixes the 2 locally-modified files, disables the CI step with the alignment
rationale recorded inline, and replaces the lost enforcement with a checked-in-baseline local guard
that fails whenever this fork introduces import debt of its own. Definition of done: locally-modified
bucket shake-clean, upstream-identical bucket untouched and still byte-identical, shake gate disabled
with audit date and upstream SHA inline, local guard pinning the exact residue, and the four other
non-build CI steps re-verified exit 0.

### Research Integration

Findings carried directly into the phases below:

- **The 12/2/10 split is live-confirmed** (report §1) against upstream SHA
  `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`, audit date 2026-07-28. The 2 fixable files are
  `Cslib/Logics/Modal/Basic.lean` and `Cslib/Foundations/Data/HasFresh.lean`; the exact suggested
  import deltas are recorded in report §2 and reproduced in Phase 1.
- **Item 3 is resolved, do not re-litigate** (report §3). The per-file annotation mechanism
  (`-- shake: keep`, `module -- shake: keep-all`, `keep-downstream`) *does* exist and is already
  used 12 times in this repo — the audit's literal "no mechanism exists" claim is refuted. But it
  is unusable for the residue for two independent reasons: (a) applying it requires editing the
  flagged file, forking a pristine upstream file, which this task's NON-GOALS prohibit; (b)
  `keep-all` suppresses only *removal* reports, never *addition* reports, and 9 of the 10 residual
  files need an `add` — so even if editing pristine files were permitted it would silence at most
  1 of 10. Module-scoping via positional `[<MODULE>...]` args is equally unusable: shake visits
  every module sharing the given root, and the residue contains import hubs with fan-in up to 7.
  Disabling + local guard is the only approach consistent with both NON-GOALS.
- **Disabling reduces, not increases, divergence** (report §4). Upstream's own
  `lean_action_ci.yml` has the `lake shake` step commented out (upstream commit
  `74600063621f66f0dbfbac31963cd1219e0e05ed`, "ci: disable shake again (#397)"). This fork's copy
  of the file already diverges (local `TEST_ARGS`) and already has the step *enabled* where
  upstream has it disabled, so re-commenting it shrinks that hunk.
- **`lake shake` needs built `.olean` files** (report §5). This is why the guard cannot join the
  build-free `lint-hygiene.yml` workflow, and why the guard must distinguish "shake ran and found
  nothing" from "shake failed to run" — see Phase 2's exit-2 requirement.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and no ROADMAP.md consultation was
requested; this plan proceeds without roadmap alignment.

## Goals & Non-Goals

**Goals**:
- Make `Cslib/Logics/Modal/Basic.lean` and `Cslib/Foundations/Data/HasFresh.lean` shake-clean by
  applying shake's own suggested import deltas, with no new build warnings.
- Comment out the `lake shake` step in `.github/workflows/lean_action_ci.yml`, recording inline:
  audit date `2026-07-28`, upstream SHA `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`, the explicit
  statement that the remaining flagged files are byte-identical to upstream, upstream's own
  disabling commit, and a pointer to the local guard.
- Add `scripts/check-shake-residue.sh` plus a checked-in `scripts/shake-residue-baseline.txt`
  seeded with exactly the 10 upstream-identical paths, doing exact-set comparison with exit 0/1,
  modeled on `scripts/check-lint-suppressions.sh`.
- Re-verify `lake test`, `lake exe mk_all --check`, `lake exe checkInitImports`, and
  `lake exe lint-style` all exit 0, and that all 10 residual files remain byte-identical to
  `upstream/main`.

**Non-Goals**:
- No blanket `lake shake --fix`.
- No modification of any upstream-identical file — including no `-- shake: keep` /
  `module -- shake: keep-all` annotations added to them (report §3 explains why this is off-limits
  even though the mechanism exists).
- No changes to any `sorry`, proof, definition, or theorem statement.
- No change to the `--wfail --iofail` build args; the sorry gate stays red and is out of scope.
- No new step added to `.github/workflows/lean_action_ci.yml` and no new workflow file — the guard
  is local-only this round (see Risk R5 for the rationale and the deferred option).
- No `git push`, no PR creation.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: Removing `Mathlib.Analysis.Normed.Field.Lemmas` from `HasFresh.lean` breaks a downstream module that relied on the transitive import | H | M | Full `lake build` (not just the two modules) after the edit; if a downstream file breaks, revert to the pre-edit import line, re-run shake, and report — do NOT "fix" the downstream file, that widens scope | 
| R2: The two edits introduce new build warnings, violating "no new warnings" | M | M | Capture a full pre-edit `lake build` warning snapshot in Phase 1 before touching anything, diff against the post-edit snapshot; only pre-existing warnings (the known sorries + `privateInPublic` in `CslibTests/FreeMonad.lean`) may remain |
| R3: The guard silently reports "clean" because `lake shake` failed to run (missing `.olean`s), turning a broken environment into a false pass | H | M | Guard MUST exit 2 (environment error, distinct from 0/1) when shake's exit code is outside `{0,1}` or its output is unparseable; never treat a failed run as an empty flagged set |
| R4: `lake shake` exits 1 by design when it has suggestions, so a naive `set -e` in the guard aborts before comparison | M | H | Follow `check-lint-suppressions.sh`'s pattern: `set -uo pipefail` without `-e`, capture shake's exit code explicitly |
| R5: Adding the guard as a CI step would add a fresh divergence hunk to a shared workflow file | M | H | Deliberately NOT wiring it into CI this round. `lint-hygiene.yml`'s own header states the rule (a new step in a shared workflow adds a conflict hunk to every sync), and the guard cannot join `lint-hygiene.yml` because that job is deliberately Lean-free while shake needs built `.olean`s. Wire into `scripts/pre-pr-check.sh` (already a local-only file) instead; record the deferred CI option in the workflow comment |
| R6: A task-number reference leaks into a deliverable | L | M | `.claude/rules/no-task-references-in-deliverables.md` — the workflow comment, the guard script, the baseline header, and `pre-pr-check.sh` MUST cite durable anchors (audit date, upstream SHA, upstream commit, sibling filenames) and never "task 580" |
| R7: `upstream/main` ref is stale or absent locally, making the byte-identity re-verification vacuous | M | L | Phase 4 fetches `upstream main` first and asserts the resolved SHA equals `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`; if it has moved, report the new SHA rather than silently comparing against a different tree |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel. Phases 2 and 3 touch disjoint files
(`scripts/` vs `.github/workflows/`) and may be done in either order or concurrently; both need
Phase 1's post-fix residue to be established first.

---

### Phase 1: Fix the two locally-modified files [COMPLETED]

**Goal**: Apply shake's own suggested import deltas to the two files that already diverge from
upstream, so the flagged set drops from 12 to exactly the 10 upstream-identical residue, with no
new build warnings.

**Tasks**:
- [x] Snapshot the pre-edit state before touching anything:
  - [x] `lake build 2>&1 | tee /tmp/shake-pre-build.log` (plain `lake build` — NOT
        `--wfail --iofail`, the sorry gate is out of scope and would abort the run)
  - [x] `lake shake --add-public --keep-implied --keep-prefix Cslib 2>&1 | tee /tmp/shake-pre.log`
        (expect exit 1, 12 files) *(confirmed: exit 1, 12 files, matching report §1 exactly)*
- [x] Read the import headers of both target files and note the exact syntax convention in use
      (`public import X` vs `import X`, ordering, any existing `-- shake: keep` annotations). Match
      the file's existing convention when adding lines; do not reformat unrelated lines.
- [x] `Cslib/Logics/Modal/Basic.lean`: add `public import Mathlib.Order.Notation`.
- [x] `Cslib/Foundations/Data/HasFresh.lean`:
  - [x] remove `public import Mathlib.Analysis.Normed.Field.Lemmas`
  - [x] add `public import Mathlib.Analysis.Normed.Group.Basic`
  - [x] add `public import Mathlib.Topology.MetricSpace.Bounded`
  - [x] add `public import Mathlib.Data.EReal.Operations`
  - [x] add `public import Mathlib.Topology.Algebra.InfiniteSum.Order`
- [x] `lake build Cslib.Logics.Modal.Basic Cslib.Foundations.Data.HasFresh` — both must compile.
      *(both built clean)*
- [x] Full `lake build 2>&1 | tee /tmp/shake-post-build.log` — catches R1 (a downstream module that
      relied on the removed import transitively). *(3309/3309 jobs, no downstream break)*
- [x] Diff the warning sets: `grep -E '^(warning|.*: warning)' /tmp/shake-pre-build.log` vs the
      post log. The post set must be a subset of the pre set. Any genuinely new warning fails this
      phase — revert the offending import line and report rather than papering over it. *(sets are
      byte-identical: the same 5 pre-existing sorry warnings, zero new warnings)*
- [x] Re-run `lake shake --add-public --keep-implied --keep-prefix Cslib 2>&1 | tee /tmp/shake-post.log`.
      Expect exit code still 1 and **exactly 10** flagged files, being precisely the 10 marked
      IDENTICAL in the research report §1 table — neither of the two edited files may still appear,
      and no file may appear that was not in the original 12. *(deviation: altered -- live result is
      exactly 9 flagged files, not 10. Verified stable across two consecutive runs (byte-identical
      `lake shake` output both times). `Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/LcAt.lean`
      (report §1 row 11, IDENTICAL, needed to add `Mathlib.Data.Int.ConditionallyCompleteOrder`) no
      longer appears. Root cause: `LcAt.lean` imports `Untyped/Basic.lean`, which imports
      `HasFresh.lean`; with `--keep-implied`, one of the four Mathlib imports newly added to
      `HasFresh.lean` in this phase now transitively supplies the import `LcAt.lean` needed, so shake
      no longer flags it. `LcAt.lean` itself was not touched and remains byte-identical to upstream --
      this is a side effect of the sanctioned `HasFresh.lean` edit, not a new NON-GOALS violation. The
      live 9-file set is used as the Phase 2 baseline ground truth per the guard's own
      live-output-is-authoritative design (mirrors the lint-count-preflight philosophy elsewhere in
      this codebase.)*
- [x] Keep `/tmp/shake-post.log`; Phase 2 seeds the baseline from it.

**Timing**: 1.5 hours (dominated by two full Mathlib-backed builds)

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - add one `public import` line to the header
- `Cslib/Foundations/Data/HasFresh.lean` - remove one `public import`, add four

**Verification**:
- Both modules build clean individually and in a full `lake build`.
- Post-edit warning set is a subset of the pre-edit warning set (no new warnings).
- `lake shake --add-public --keep-implied --keep-prefix Cslib` flags exactly 10 files, and that set
  equals the research report's IDENTICAL rows verbatim.

---

### Phase 2: Add the local shake-residue guard [COMPLETED]

**Goal**: Add `scripts/check-shake-residue.sh` + `scripts/shake-residue-baseline.txt` so that any
*new* import debt this fork introduces still fails a check, even with the CI step disabled.

**Tasks**:
- [x] Inspect `/tmp/shake-post.log` (from Phase 1) to determine shake's exact stdout line format
      for a flagged file. Do not guess the format — derive the extractor from the live output, then
      normalize extracted paths to repo-root-relative form. *(confirmed: absolute path lines
      matching `^/.*\.lean:$`, distinct from the delta lines and from build-noise lines)*
- [x] Write `scripts/check-shake-residue.sh`, mirroring `scripts/check-lint-suppressions.sh`'s
      structure (header comment explaining the problem and the rule, `REPO_ROOT` resolution + `cd`,
      `set -uo pipefail` **without** `-e` per R4, a `case` on `${1:-}` for flags, then the
      comparison):
  - [x] No args: run `lake shake --add-public --keep-implied --keep-prefix Cslib`, capture stdout
        and the exit code explicitly.
  - [x] **Exit 2 on environment error** (R3): shake exit code outside `{0,1}`, or output that
        yields no parseable file lines while shake reported suggestions. A failed shake run must
        never be reported as a clean/empty flagged set.
  - [x] Exact-set comparison against the baseline, not a count ceiling:
    - File in live flagged set but NOT in baseline -> `FAIL`, exit 1. This is new import debt owned
      by this fork and is exactly what the disabled CI step used to catch.
    - File in baseline but NOT in live flagged set -> report as an improvement, exit 0, print
      "re-baseline with: bash scripts/check-shake-residue.sh --update". Ratchet-only-decreases,
      same philosophy as the lint-suppression baseline.
    - Sets equal -> `OK`, exit 0.
  - [x] `--update`: rewrite the baseline from the live flagged set, with a generated header
        matching `lint-suppression-baseline.txt`'s style (do-not-hand-edit note, the ratchet rule,
        the format line).
  - [x] `--list`: print the live flagged set, exit 0.
  - [x] Any other argument: usage message to stderr, exit 2.
  - [x] Header comment must state the alignment rationale in durable terms: the baseline entries
        are files byte-identical to upstream `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1` as of
        2026-07-28, so they are upstream's own import debt, not this fork's; no task numbers (R6).
- [x] Generate `scripts/shake-residue-baseline.txt` via `bash scripts/check-shake-residue.sh --update`
      and confirm by eye that it contains exactly the 10 paths from the research report §1
      IDENTICAL rows — no more, no fewer. *(deviation: altered -- contains exactly the 9 paths from
      the Phase 1 live-verified residue, not 10, per the documented LcAt.lean side effect. All 9 are
      confirmed IDENTICAL rows from the research report §1 table; none is one of the two
      locally-modified files.)*
- [x] `chmod +x scripts/check-shake-residue.sh`.
- [x] Verify the clean path: `bash scripts/check-shake-residue.sh` -> exit 0, "OK".
- [x] Verify the regression path without touching the Lean tree: `cp` the baseline to a `.bak`,
      delete one line from the baseline, re-run the guard (expect `FAIL` + exit 1), then restore
      with `mv` from the `.bak`. Use `cp`/`mv` — do **not** use `git checkout -- <path>` or
      `git restore <path>` to restore, both are forbidden on a dirty tree. *(proven: deleting
      TimeM.lean's baseline line produced FAIL + exit 1; restored via mv)*
- [x] Verify the improvement path the same way: append a fabricated extra path to a `.bak`-backed
      copy of the baseline, re-run (expect exit 0 plus the re-baseline note), then restore. *(proven:
      fabricated path produced IMPROVED + exit 0 + re-baseline note; restored via mv)*
- [x] Wire into `scripts/pre-pr-check.sh` as step 7, following the existing step-6
      `check-lint-suppressions.sh` block verbatim in shape (accumulate into `failed`, do not
      `set -e`). Note in a comment that this step requires a completed `lake build` (step 4/5
      already provide one in that script's ordering).
- [x] Add a row for `check-shake-residue.sh` and `shake-residue-baseline.txt` to
      `scripts/README.md`'s "Current scripts and their purpose" section.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `scripts/check-shake-residue.sh` - new; the guard
- `scripts/shake-residue-baseline.txt` - new; checked-in baseline, exactly the 10 residual paths
  (required by the task's own "checked-in baseline" instruction even though not in the declared
  FILE SCOPE list — the guard is inoperable without it)
- `scripts/pre-pr-check.sh` - add step 7 invoking the guard (local-only file; beyond the declared
  FILE SCOPE, included because the research report calls for the guard to be a documented manual
  pre-PR script)
- `scripts/README.md` - document the new script and baseline

**Verification**:
- `bash scripts/check-shake-residue.sh` exits 0 with an OK message on the current tree. **Proven.**
- Baseline contains exactly 9 paths (deviation from the plan's predicted 10, documented in Phase
  1), all matching research report IDENTICAL rows. **Proven.**
- Deleting a baseline line makes the guard exit 1 with a FAIL naming the unexpected file.
  **Proven.**
- Adding a phantom baseline line makes the guard exit 0 with an improvement/re-baseline note.
  **Proven.**
- `bash scripts/check-shake-residue.sh --list` and `--update` both behave as specified; an
  unrecognized flag exits 2. **Proven.**

---

### Phase 3: Disable the `lake shake` CI step with inline alignment rationale [COMPLETED]

**Goal**: Comment out the `lake shake` step in `.github/workflows/lean_action_ci.yml`, recording
the full audit trail inline so a future reader (or a future sync) can tell exactly why it is off
and what would re-enable it.

**Tasks**:
- [x] Read `.github/workflows/lean_action_ci.yml` around the `"lake shake"` step (currently near
      lines 29-32) and check how upstream comments the same block
      (`git show 74600063621f66f0dbfbac31963cd1219e0e05ed -- .github/workflows/lean_action_ci.yml`
      or `git show upstream/main:.github/workflows/lean_action_ci.yml`). Match upstream's commenting
      shape where practical — the closer this hunk is to upstream's, the smaller the future sync
      conflict. *(confirmed upstream/main resolves to f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1,
      matching plan expectation; upstream comments each line with a leading `#`)*
- [x] Comment out the step (the `- name: "lake shake"` line, its `run:` block, and the
      `lake shake --add-public --keep-implied --keep-prefix Cslib` invocation). Do not delete it —
      it must remain readable and trivially re-enableable.
- [x] Add an inline comment block immediately above the disabled step recording, at minimum:
  - [x] Audit date: `2026-07-28`.
  - [x] Upstream SHA compared against: `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`.
  - [x] The explicit statement that after fixing the two locally-modified files, every remaining
        flagged file is **byte-identical to upstream** — this is upstream's own unresolved import
        debt, not this fork's.
  - [x] Upstream's own disabling commit `74600063621f66f0dbfbac31963cd1219e0e05ed`
        ("ci: disable shake again (#397)"), i.e. upstream disabled this same check for this same
        reason; re-commenting here *reduces* this file's divergence from upstream rather than
        increasing it.
  - [x] Why selective exemption was rejected: shake's `-- shake: keep` / `keep-all` annotations
        exist but require editing the flagged (pristine) file, and `keep-all` suppresses only
        removal findings while most of the residual files need an *addition*; module-scoping via
        positional args cannot exclude them either, since several are import hubs.
  - [x] Pointer to `scripts/check-shake-residue.sh` + `scripts/shake-residue-baseline.txt` as the
        local guard that still catches this fork's own new import debt, and a one-line note that it
        is deliberately not a CI step (it needs built `.olean`s, so it cannot join the Lean-free
        `lint-hygiene.yml`, and a new step here would add a sync-conflict hunk).
  - [x] No task-number references (R6) — cite the date, SHAs, and sibling filenames only.
- [x] Confirm the file is still valid YAML: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/lean_action_ci.yml'))"`
      (or `yq . <file>` if available). *(confirmed VALID YAML)*
- [x] Confirm no other step was touched: `git diff .github/workflows/lean_action_ci.yml` must show
      changes confined to the shake step and its new comment block — `TEST_ARGS`, `lean-action`,
      `mk_all`, `checkInitImports`, and the `lint-style-action` pin must be byte-unchanged.
      *(confirmed: diff shows only the shake-step hunk)*

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `.github/workflows/lean_action_ci.yml` - comment out the `lake shake` step, add the rationale
  block above it

**Verification**:
- The file parses as YAML.
- `git diff` on the workflow shows only the shake step + comment block changed.
- The comment block contains the literal strings `2026-07-28`,
  `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`, `74600063621f66f0dbfbac31963cd1219e0e05ed`, and
  `scripts/check-shake-residue.sh`.

---

### Phase 4: Re-verify CI steps and upstream byte-identity [NOT STARTED]

**Goal**: Prove the definition of done: four non-build CI steps green, the 10 residual files still
byte-identical to upstream, and the guard passing.

**Tasks**:
- [ ] `git fetch upstream main` and assert `git rev-parse upstream/main` still resolves to
      `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1` (R7). If it has moved, record the new SHA in the
      summary and re-run the byte-identity check against the new ref before concluding anything.
- [ ] For each of the 10 residual files, run `git diff --quiet upstream/main -- <file>` and confirm
      exit 0 (still byte-identical). All 10 must pass; a single failure means a pristine file was
      touched, violating the NON-GOALS.
- [ ] Confirm the working-tree diff is confined to the intended set:
      `git status --short` should show only `Cslib/Logics/Modal/Basic.lean`,
      `Cslib/Foundations/Data/HasFresh.lean`, `.github/workflows/lean_action_ci.yml`,
      `scripts/check-shake-residue.sh`, `scripts/shake-residue-baseline.txt`,
      `scripts/pre-pr-check.sh`, `scripts/README.md`, and the task's own `specs/` artifacts.
- [ ] Run and record exit codes for the four non-build CI steps:
  - [ ] `lake test` -> exit 0 (pre-existing sorry warnings in
        `Modal/Tableau/FrameSoundness.lean`, `Propositional/Tableau/Intuitionistic/{Scheme,Completeness}.lean`,
        `Propositional/Tableau/Minimal/Completeness.lean`, and the `privateInPublic` warning in
        `CslibTests/FreeMonad.lean` are pre-existing and acceptable; anything new is not)
  - [ ] `lake exe mk_all --check` -> exit 0
  - [ ] `lake exe checkInitImports` -> exit 0
  - [ ] `lake exe lint-style` -> exit 0
- [ ] `bash scripts/check-shake-residue.sh` -> exit 0.
- [ ] `bash scripts/check-lint-suppressions.sh` -> exit 0 (unchanged; confirms no collateral).
- [ ] Explicitly confirm the out-of-scope item: `lake build --wfail --iofail` is **expected** to
      remain red (sorry gate). Do not attempt to fix it, and do not alter the build args.
- [ ] Write the implementation summary to
      `specs/580_shake_ci_gate_restore_green/summaries/01_restore-shake-ci-gate-summary.md`,
      recording: the four exit codes, the 10-file byte-identity result, the resolved upstream SHA,
      and the guard's clean/regression test results.

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3

**Files to modify**:
- (verification only; plus the summary artifact under `specs/`)

**Verification**:
- All four CI commands exit 0.
- All 10 residual files report `git diff --quiet upstream/main` exit 0.
- `check-shake-residue.sh` and `check-lint-suppressions.sh` both exit 0.
- No file outside the intended change set is modified.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Basic Cslib.Foundations.Data.HasFresh` succeeds.
- [ ] Full `lake build` succeeds with no warnings absent from the pre-edit snapshot.
- [ ] `lake shake --add-public --keep-implied --keep-prefix Cslib` flags exactly the 10
      upstream-identical files (exit 1 remains expected and is now unenforced in CI).
- [ ] `bash scripts/check-shake-residue.sh` exits 0 on the clean tree.
- [ ] `bash scripts/check-shake-residue.sh` exits 1 when the baseline is missing a currently-flagged
      file (regression path proven, not assumed).
- [ ] `bash scripts/check-shake-residue.sh` exits 0 with a re-baseline note when a baseline entry is
      no longer flagged (improvement path).
- [ ] `bash scripts/check-shake-residue.sh --list` / `--update` behave as specified; bad flag -> exit 2.
- [ ] `.github/workflows/lean_action_ci.yml` parses as YAML; diff confined to the shake step.
- [ ] `lake test`, `lake exe mk_all --check`, `lake exe checkInitImports`, `lake exe lint-style` all
      exit 0.
- [ ] All 10 upstream-identical files still `git diff --quiet upstream/main` clean.
- [ ] `bash scripts/check-lint-suppressions.sh` still exits 0.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Basic.lean` (modified: +1 import)
- `Cslib/Foundations/Data/HasFresh.lean` (modified: -1 import, +4 imports)
- `.github/workflows/lean_action_ci.yml` (modified: shake step commented out + rationale block)
- `scripts/check-shake-residue.sh` (new, executable)
- `scripts/shake-residue-baseline.txt` (new, 10 paths)
- `scripts/pre-pr-check.sh` (modified: step 7)
- `scripts/README.md` (modified: script documentation)
- `specs/580_shake_ci_gate_restore_green/plans/01_restore-shake-ci-gate.md` (this plan)
- `specs/580_shake_ci_gate_restore_green/summaries/01_restore-shake-ci-gate-summary.md`

## Rollback/Contingency

Every phase is independently revertible and the phases are committed separately, so rollback is
per-commit rather than all-or-nothing:

- **Phase 1 fails** (R1: a downstream module breaks on the `HasFresh.lean` import removal): restore
  only the removed `public import Mathlib.Analysis.Normed.Field.Lemmas` line, keep the four
  additions if they build clean, re-run shake, and record in the summary that `HasFresh.lean`
  remains partially flagged. Do not modify the broken downstream file — that would widen scope
  beyond the declared FILE SCOPE. If the additions also fail, revert `HasFresh.lean` entirely and
  proceed with `Modal/Basic.lean` alone, seeding the Phase 2 baseline with 11 files instead of 10
  and noting the deviation prominently.
- **Phase 2 fails** (guard cannot reliably parse shake output): delete
  `scripts/check-shake-residue.sh` and `scripts/shake-residue-baseline.txt`, revert the
  `pre-pr-check.sh` and `README.md` edits. Do NOT proceed to Phase 3 disabling the CI step without
  a working guard — disabling without the guard loses enforcement outright, which the definition of
  done forbids. Report as BLOCKED instead.
- **Phase 3 fails** (YAML invalid or diff creeps beyond the shake step): revert
  `.github/workflows/lean_action_ci.yml` to its committed state and redo the edit by hand from the
  upstream commenting shape.
- **Phase 4 finds a regression**: whichever of the four CI steps regressed identifies the culprit
  phase; revert that phase's commit and re-run. If one of the 10 residual files is no longer
  byte-identical, that is a NON-GOALS violation — revert that file to `upstream/main` content
  immediately (via a targeted `git show upstream/main:<path> > <path>` rewrite; do not use a
  forbidden destructive git command on the dirty tree) and re-verify.

All rollbacks are file-level restores from committed state or from `.bak` copies; no destructive
git operation (`git reset --hard`, `git checkout -- <path>`, `git restore <path>`, `git clean -fd`)
is used on the dirty tree. If one becomes genuinely necessary, run
`bash .claude/scripts/git-snapshot.sh 580` first.
