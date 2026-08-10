# Implementation Plan: Task #625

- **Task**: 625 - shake_residue_list_false_clean
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/625_shake_residue_list_false_clean/reports/01_shake-residue-false-clean.md`
- **Artifacts**: plans/01_shake-list-guard-hoist.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

`scripts/check-shake-residue.sh --list` can exit 0 with zero output when `lake shake` failed to
complete an analysis, because the `--list` branch implements only one of the two fatal conditions
its own EXIT-CODE CONTRACT declares. Research empirically confirmed that `lake shake` exits **1**
(not 0) on the out-of-date-target failure, so the fix is the narrow one: the existing
`shake_exit == 1 && empty parse -> exit 2` guard must also govern `--list`. Rather than adding a
third copy-pasted guard block — the very duplication that let `--list` drift out of sync — this
plan consolidates both fatal conditions into a single shared validator mirroring
`scripts/check-axiom-census.sh`'s `run_and_validate_census()`, rewires all three modes onto it,
adds a `--self-test` subcommand whose fixtures include the literal reproduced failure transcript,
and reconciles the header contract with the implementation.

### Research Integration

Key findings carried into this plan, treated as established and not re-litigated:

- `lake shake` exits **1** on a stale `Cslib` facade target (traced through Lake's `MainM.error`
  default `rc := 1`), producing zero `^/.*\.lean:$` lines. Reproduced end-to-end: the real
  `bash scripts/check-shake-residue.sh --list` exits 0 with zero output under that state.
- This is the **narrow-fix branch**. No baseline-corruption risk exists (`--update` already
  guards correctly), so the heavier positive-confirmation redesign is explicitly out of scope.
- `scripts/check-axiom-census.sh` lines 100-129 (`run_and_validate_census()`) is the in-tree
  template for the shared-helper shape, called identically from `--list` (132-138), `--update`
  (139-143), and the bare path (~180). Its header even names the function inside its own
  EXIT-CODE CONTRACT — the same reconciliation this plan applies to the shake script.
- The task description's suggested self-test precedent (`check-runtime-file-tracking.sh`) is
  **wrong** — that script does live git-ignore probes, not synthetic-fixture parsing. Use
  `check-boneyard-quarantine.sh`'s `--self-test` naming convention instead, with fixtures
  assigned directly to `$shake_raw`/`$shake_exit` so no `lake` invocation is needed.
- Reproduction via `touch` does **not** work (Lake trace checking is content-hash-based); a real
  content edit is required. Relevant only if an implementer tries to re-reproduce manually —
  they should not need to, the fixture encodes it.

**Correction to the research's proposed snippet**: the report's suggested `--list` body ends with
an unconditional `printf '%s\n' "$live"`, which emits a **spurious blank line** when `$live` is
empty (the genuine shake-exit-0 clean case), silently changing `--list`'s output contract from
"zero bytes" to "one newline". Phase 2 must guard that print with `[ -n "$live" ]`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Make `--list` fatal (exit 2) on `shake_exit == 1` with an empty parsed flagged set, closing the
  false-clean defect.
- Eliminate the three-way duplication of the guard conditions by consolidating them into one
  shared validator used identically by `--list`, `--update`, and the bare verify path.
- Preserve every existing exit-code behavior: 0 clean/improved, 1 regression, 2 usage/environment
  error; and preserve `--list`'s one-path-per-line stdout contract exactly (including emitting
  zero bytes on a genuinely clean run).
- Add a `--self-test` subcommand with deterministic fixtures — including the literal reproduced
  stale-target transcript — that asserts the guard in all three modes without invoking `lake`.
- Reconcile the EXIT-CODE CONTRACT header block so the documented rule, the named implementing
  function, and all three implemented paths agree.

**Non-Goals**:
- The positive-confirmation redesign contemplated as a contingency in the task description.
  Research established shake exits 1, so this is unnecessary.
- Changing `parse_flagged_set`'s regex or `run_shake`'s `SHAKE_ARGS`.
- Regenerating or otherwise touching `scripts/shake-residue-baseline.txt`.
- Introducing `set -e`. The header block explains why it is wrong here (shake's exit 1 is a
  normal outcome); the no-`set -e` design is deliberate and must survive this task intact.
- **Wiring `--self-test` into `scripts/pre-pr-check.sh`.** The research recommends this as a
  regression-durability mitigation (a step 11 alongside the existing Boneyard self-test at line
  119), but the declared file scope for this task is `scripts/check-shake-residue.sh` plus new
  fixtures. Recorded as a follow-up, not done here — see Rollback/Contingency.
- Auditing sibling ratchet scripts. Research already checked `check-lint-suppressions.sh` and
  `check-sorry-suppressions.sh`: both are pure local `grep`/`perl` scans with no external-tool
  exit-code ambiguity, so this defect class does not apply.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Consolidating three guard blocks into one changes stderr wording for `--update`/bare | L | H (certain) | Wording-only, exit codes unchanged. Mirror the census precedent: helper prints the generic diagnostic, `--update` appends its own "refusing to update baseline" line. Document in Phase 1. |
| Unconditional `printf` of `$live` adds a blank line on a clean `--list` | M | H if the research snippet is copied verbatim | Phase 2 guards the print with `[ -n "$live" ]`; Phase 5 asserts byte-empty stdout on the clean fixture. |
| `run_shake` called inside `$(...)` loses both globals to a subshell | H | L | Existing hazard documented at lines 72-74. Helper calls `run_shake` directly; `if ! run_and_validate_shake; then` is not a subshell. Same shape as the census script. |
| `--self-test` fixture injection becomes a backdoor in a production gate | M | L | Injection activates only when `SHAKE_SELF_TEST_FIXTURE` is non-empty; documented in the header; never consulted on any normal invocation path. |
| Refactor silently breaks the bare verify path (the one wired into pre-pr-check.sh step 7) | H | L | Phase 5 runs the bare path against the live built repo and asserts the baseline file is byte-unchanged via `git diff --exit-code`. |
| Re-reproducing the bug manually via `touch` appears to "disprove" the research | L | M | Explicitly flagged above: Lake trace checking is content-hash-based. Implementers must rely on the fixture, not a live re-reproduction. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is a strict chain: every phase
edits the same single file, so there is no parallelism to exploit and territory conflicts are
avoided by construction.

---

### Phase 1: Extract the shared shake validator [COMPLETED]

**Goal**: Introduce one shared validator holding both fatal conditions, and rewire the two
already-correct paths (`--update`, bare) onto it. Behavior-preserving except for stderr wording.

**Tasks**:
- [x] Add `validate_shake_result()` immediately after `parse_flagged_set` (around line 93). It
      reads the globals `$shake_exit` and a caller-supplied parsed set, prints a diagnostic to
      stderr and `return 2` on failure, `return 0` otherwise. It must NOT call `exit` itself —
      the census precedent explicitly keeps this returnable so `--update` can add its own line.
      *(completed)*
- [x] Implement both fatal conditions in it, preserving the current diagnostics' substance:
      (a) `shake_exit` outside `{0,1}` -> "lake shake exited N (expected 0 or 1). Environment
      likely broken (missing .olean files?) -- run a full 'lake build' first. This is NOT
      reported as a clean/empty flagged set."; (b) `shake_exit -eq 1` and the parsed set empty ->
      the "no flagged-file lines were parseable ... This is NOT reported as a clean/empty flagged
      set." diagnostic currently at lines 158-161. *(completed)*
- [x] Add `run_and_validate_shake()` = `run_shake` then compute `live="$(parse_flagged_set)"`
      then `validate_shake_result`. Keeping `run_shake` (impure) separate from
      `validate_shake_result` (pure, globals-only) is what makes Phase 3's fixtures possible
      without a `lake` invocation — do not collapse them into one function. *(completed)*
- [x] Decide and document how `$live` reaches the caller: assign it to a global (not `local`) so
      the bare path's downstream comparison logic at lines 164-198 keeps working unchanged.
      *(completed: `live=""` declared at global scope before the function, matching `shake_exit`/
      `shake_raw`'s existing pattern)*
- [x] Rewire `--update` (lines 105-115) to `if ! run_and_validate_shake; then echo "ERROR:
      refusing to update baseline from a failed/unparseable run." >&2; exit 2; fi`, matching
      `check-axiom-census.sh` lines 139-143 verbatim in shape. *(completed)*
- [x] Rewire the bare path (lines 147-162) to `if ! run_and_validate_shake; then exit 2; fi`,
      deleting the two now-redundant inline guard blocks. *(completed)*
- [x] Confirm no `set -e` was introduced and `set -uo pipefail` at line 64 is untouched.
      *(completed)*

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts it removes exactly **four** inline guard blocks
(`--update` lines 108-111 and 112-115; bare lines 150-155 and 157-162) and adds exactly **two**
new functions. Confirm at implementation time by re-reading the file after the edit and grepping
`grep -c 'expected 0 or 1' scripts/check-shake-residue.sh` — it must drop from 3 occurrences to
1. If the count differs, stop and reconcile rather than proceeding.

**Files to modify**:
- `scripts/check-shake-residue.sh` - add `validate_shake_result()` + `run_and_validate_shake()`;
  replace the `--update` and bare-path inline guards with calls to the helper.

**Verification**:
- `bash -n scripts/check-shake-residue.sh` parses clean.
- `shellcheck scripts/check-shake-residue.sh` reports no new findings (skip gracefully if
  shellcheck is unavailable; note it in the summary rather than pretending it ran).
- `grep -c 'expected 0 or 1' scripts/check-shake-residue.sh` returns 1.
- `grep -n 'set -e' scripts/check-shake-residue.sh` returns no bare `set -e` line.

---

### Phase 2: Route `--list` through the shared validator [COMPLETED]

**Goal**: Close the actual defect — `--list` must exit 2, not 0, when shake exits 1 with an
unparseable/empty flagged set.

**Tasks**:
- [x] Replace the `--list` branch body (lines 96-104) with:
      `if ! run_and_validate_shake; then exit 2; fi` followed by the guarded print and `exit 0`.
      *(completed)*
- [x] Print with `[ -n "$live" ] && printf '%s\n' "$live"` — **not** the research report's
      unconditional `printf`, which would emit a stray blank line on a genuinely clean run. Note
      that under `set -uo pipefail` without `set -e`, a false `[ -n ... ]` test is harmless as
      the branch's last-but-one statement because `exit 0` follows explicitly. *(completed)*
- [x] Confirm `parse_flagged_set` is no longer called bare-for-its-stdout in `--list` (that call
      shape is exactly what made the emptiness uninspectable); its output now flows through
      `$live` only. *(completed: verified via `grep -n 'parse_flagged_set'`, only two hits — the
      definition and the single call site inside `run_and_validate_shake`)*
- [x] Confirm all three modes now share one and only one implementation of both conditions.
      *(completed: `grep -c 'expected 0 or 1'` returns 1, confirmed after this phase per the
      Phase 1 deviation note)*

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `scripts/check-shake-residue.sh` - `--list` branch.

**Verification**:
- `bash -n scripts/check-shake-residue.sh` parses clean.
- Against the live, fully-built repo: `bash scripts/check-shake-residue.sh --list` still exits 0
  and prints the same path set as before the change (capture the pre-change output first, or
  compare against `scripts/shake-residue-baseline.txt`, which is the same set when clean).
- `bash scripts/check-shake-residue.sh --list | wc -c` is non-zero on the live repo, confirming
  the guarded print did not suppress real output.
- Deferred to Phase 3: the negative case (stale-target fixture -> exit 2). Do not attempt to
  re-reproduce it by editing a `Cslib/**` file; the fixture is the intended mechanism.

---

### Phase 3: Add the `--self-test` subcommand with fixtures [COMPLETED]

**Goal**: Encode the reproduced regression as a deterministic, `lake`-free fixture that asserts
the guard fires in all three modes, so this asymmetry cannot silently return.

**Tasks**:
- [x] Add a `--self-test` case to the `case "${1:-}"` statement (before the `""` and `*` arms),
      following `check-boneyard-quarantine.sh`'s self-test naming and its 0-pass/1-fail exit
      contract. *(completed)*
- [x] Define four fixtures as heredoc-assigned strings paired with an exit code:
      1. **flagged** — `shake_exit=1`, several `^/abs/path.lean:$` header lines plus
         `add #[...]` / `remove #[...]` delta lines and some `⚠ [n/m] Replayed X` noise.
      2. **stale-target** (the reproduced regression) — `shake_exit=1`, containing the literal
         `error: target is out-of-date and needs to be rebuilt` and ``error: there are out of
         date oleans; run `lake build` or fetch them from a cache first`` lines plus
         `Cslib/…/Driver.lean:893:100:`-style repo-relative warnings, with **zero**
         `^/.*\.lean:$` lines. Source the text from the research report's reproduction section.
      3. **clean** — `shake_exit=0`, only harmless replay/warning noise, no flagged lines.
      4. **bad-exit** — `shake_exit=2`, arbitrary output.
      *(completed: all four implemented in `load_self_test_fixture()`, called both by `run_shake`'s
      `SHAKE_SELF_TEST_FIXTURE` short-circuit and directly by the in-process assertions)*
- [x] Add in-process assertions calling `validate_shake_result` directly against each fixture
      (set `shake_raw`/`shake_exit`, compute `live`, call, compare the return code): fixture 1 ->
      0, fixture 2 -> 2, fixture 3 -> 0, fixture 4 -> 2. Also assert `parse_flagged_set` returns
      exactly the expected path set for fixture 1 and empty for fixtures 2 and 3. *(completed)*
- [x] Add end-to-end per-mode assertions by re-invoking the script as a subprocess with a fixture
      selector env var (`SHAKE_SELF_TEST_FIXTURE=<name> bash "$0" --list`, `… --update`, `… ""`).
      Make `run_shake` honor that variable at its top: when non-empty, populate
      `shake_raw`/`shake_exit` from the named fixture and return without invoking `lake`;
      otherwise behave exactly as today. Document the variable in the header (Phase 4).
      *(completed)*
- [x] **`--update` safety**: the `--update` end-to-end assertions must not clobber the real
      baseline. Point `BASELINE` at a temp file for fixture runs (e.g. honor a
      `SHAKE_SELF_TEST_BASELINE` override, or have the self-test run `--update` in a
      `mktemp -d` copy) and assert `scripts/shake-residue-baseline.txt` is byte-identical before
      and after the self-test. Treat this as a hard requirement, not a nicety. *(completed:
      `SHAKE_SELF_TEST_BASELINE` override + explicit before/after `assert_eq` on `$BASELINE`'s
      content; empirically confirmed via `git diff --exit-code scripts/shake-residue-baseline.txt`)*
- [x] Assert per mode: fixture 2 -> exit 2 in `--list`, `--update`, **and** bare (this triple is
      the regression this task exists to prevent); fixture 3 -> `--list` exits 0 with zero bytes
      of stdout; fixture 4 -> exit 2 in all three modes. *(completed)*
- [x] Print one line per assertion with a PASS/FAIL prefix and a final summary; `exit 0` if all
      pass, `exit 1` otherwise. *(completed: 18 assertions total, all PASS on the real fix; 17
      pass / 1 fail — the stale-target `--list` triple member — when deliberately run against a
      scratch copy with the Phase 2 fix reverted, proving the self-test has teeth)*

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts **four** fixtures and roughly **20** assertions (4
in-process validator returns + ~5 parser assertions + ~11 per-mode subprocess assertions). The
counts are a design target, not a fact — confirm at implementation time by running
`bash scripts/check-shake-residue.sh --self-test` and reading its printed summary line. If the
realized assertion set is materially smaller, verify the fixture-2-in-all-three-modes triple is
still present before closing the phase; that triple is non-negotiable regardless of total count.

**Files to modify**:
- `scripts/check-shake-residue.sh` - `--self-test` case, fixture definitions, fixture-injection
  branch in `run_shake`.

**Verification**:
- `bash scripts/check-shake-residue.sh --self-test` exits 0 and every assertion prints PASS.
- Deliberately revert the Phase 2 `--list` fix in a scratch copy (`cp` to a temp file, re-apply
  the old branch body there) and confirm the self-test **fails** on that copy — a self-test that
  passes against the buggy code proves nothing. Discard the scratch copy afterwards; do not use
  `git checkout --` on the working tree to clean up.
- `git diff --exit-code scripts/shake-residue-baseline.txt` is clean after running `--self-test`.
- Normal invocations are unaffected: `bash scripts/check-shake-residue.sh --list` (with
  `SHAKE_SELF_TEST_FIXTURE` unset) behaves exactly as in Phase 2.

---

### Phase 4: Reconcile the EXIT-CODE CONTRACT header and usage block [COMPLETED]

**Goal**: Make the documented rule, the named implementing function, and all three implemented
paths agree — the drift between header and implementation is what allowed this defect.

**Tasks**:
- [x] In the EXIT-CODE CONTRACT block (lines 46-55), state explicitly that all four bullet rules
      govern **all three usage modes** (`--list`, `--update`, and the bare verify gate)
      uniformly. The current text reads mode-agnostically while the implementation was not; make
      the universality explicit rather than implicit. *(completed)*
- [x] Name `validate_shake_result()` / `run_and_validate_shake()` as the single implementation of
      those rules, mirroring how `check-axiom-census.sh`'s header names `run_and_validate_census`
      inside its own contract block, and state that adding a fourth call site means calling the
      helper, never re-implementing the conditions inline. *(completed)*
- [x] Preserve the existing justification for the absence of `set -e` (lines 48-50) verbatim in
      substance — it explains why the naive fix is wrong and must not be lost. *(completed:
      original wording left byte-identical, only additions made after it)*
- [x] Extend the Usage block (lines 57-61) with the `--self-test` line, and the `Exit:` line
      (line 62) to note `--self-test` exits 0 on all-pass / 1 on any failed assertion.
      *(completed)*
- [x] Document `SHAKE_SELF_TEST_FIXTURE` (and any baseline-override variable added in Phase 3) in
      the header: what it does, that it is consulted only when non-empty, and that it exists
      solely for `--self-test`. *(completed: both `SHAKE_SELF_TEST_FIXTURE` and
      `SHAKE_SELF_TEST_BASELINE` documented in a new "SELF-TEST FIXTURE INJECTION" subsection)*
- [x] Add a short note recording that `--self-test` is **not** currently wired into
      `scripts/pre-pr-check.sh`, so a future maintainer knows it must be run deliberately. Do not
      cite a task number — use a durable anchor (the script name and the step-10 Boneyard
      self-test it would sit beside). *(completed: no task-number citation; anchored to
      `scripts/pre-pr-check.sh`'s existing Boneyard quarantine self-test step by name)*

**Timing**: 0.5 hours

**Depends on**: 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `scripts/check-shake-residue.sh` - header comment block only (lines ~46-62).

**Verification**:
- Diff read-through confirms every changed hunk lies inside the leading `#` comment block; zero
  executable lines touched (`git diff -U0` shows no change below line 64).
- `bash -n scripts/check-shake-residue.sh` still parses clean (guards against an edit that
  accidentally escapes the comment region — the named blind spot of the `prose` tier).
- Every function name cited in the header exists: `grep -n 'validate_shake_result\|run_and_validate_shake' scripts/check-shake-residue.sh` shows both the header mentions and the definitions.
- No task-number citations introduced (`.claude/rules/no-task-references-in-deliverables.md`).

---

### Phase 5: Full-gate verification against the live repo [NOT STARTED]

**Goal**: Confirm the three real modes still behave correctly against an actual built workspace,
and that nothing outside the intended file changed.

**Tasks**:
- [ ] Confirm the workspace is fully built (`lake build` completed) — the script requires built
      `.olean` files per the header at lines 37-44. If the build is stale, build first; do **not**
      interpret a stale-state failure as a defect in this change (it is now, correctly, exit 2).
- [ ] Run `bash scripts/check-shake-residue.sh --list`; assert exit 0 and output identical to the
      pre-change baseline set.
- [ ] Run `bash scripts/check-shake-residue.sh` (bare verify gate); assert the same exit code and
      summary line as before the change.
- [ ] Run `bash scripts/check-shake-residue.sh --self-test`; assert exit 0.
- [ ] Run `bash scripts/check-shake-residue.sh --bogus`; assert exit 2 and the usage message
      (confirms the new `--self-test` arm did not disturb the `*` fallthrough).
- [ ] Assert `git status --porcelain` shows only `scripts/check-shake-residue.sh` modified within
      the repo's source tree (plus `specs/**` task artifacts). In particular
      `scripts/shake-residue-baseline.txt` must be unmodified.
- [ ] Optionally run `bash scripts/pre-pr-check.sh` if a full build is already warm, to confirm
      step 7 (which invokes the bare path) still passes. Skip and say so if the build cost is
      prohibitive — do not report it as run if it was not.

**Timing**: 0.5 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None (verification only).

**Verification**:
- All four invocations above produce their asserted exit codes.
- `git diff --exit-code scripts/shake-residue-baseline.txt` is clean.
- `git diff --stat` outside `specs/**` lists exactly one file.

---

## Testing & Validation

- [ ] `bash -n scripts/check-shake-residue.sh` parses clean after every phase.
- [ ] `bash scripts/check-shake-residue.sh --self-test` exits 0 with all assertions PASS.
- [ ] The self-test demonstrably **fails** against a scratch copy with the Phase 2 fix reverted.
- [ ] `--list` exits 2 (not 0) on the stale-target fixture — the defect this task closes.
- [ ] `--list` prints zero bytes and exits 0 on the genuinely-clean fixture (no stray newline).
- [ ] `--update` and the bare path retain their pre-change exit codes on all four fixtures.
- [ ] `scripts/shake-residue-baseline.txt` is byte-unchanged throughout, including after running
      `--self-test`.
- [ ] The no-`set -e` design and the 0/1/2 exit-code contract are intact.
- [ ] EXIT-CODE CONTRACT header, the named helper, and all three implemented paths agree.

## Artifacts & Outputs

- `scripts/check-shake-residue.sh` — shared `validate_shake_result()` /
  `run_and_validate_shake()`, all three modes rewired onto it, `--list` defect fixed,
  `--self-test` subcommand with four fixtures, reconciled header contract.
- `specs/625_shake_residue_list_false_clean/summaries/01_*-summary.md` — implementation summary.
- No new standalone files: fixtures live inline in the script (the research-recommended shape),
  so no separate fixture files are created.

## Rollback/Contingency

- All changes are confined to one script. `git revert` of the phase commits, or discarding the
  working-tree change to `scripts/check-shake-residue.sh`, fully restores prior behavior. No
  baseline, build artifact, or generated file is touched, so there is nothing else to unwind.
  If the working tree is dirty and a discard is needed, snapshot first per
  `.claude/rules/git-workflow.md` (`bash .claude/scripts/git-snapshot.sh 625`).
- **If Phase 3's subprocess fixture-injection proves unworkable** (e.g. the env-var backdoor is
  judged unacceptable in a production gate script): fall back to in-process assertions against
  `validate_shake_result` only, and record in the summary that per-mode wiring is asserted by
  inspection rather than execution. This is a degradation, not a failure — the pure-function
  assertions still encode the reproduced regression. Do not silently drop the per-mode claim.
- **If a phase reveals shake exits 0 (not 1) in some other stale state** not covered by the
  research: stop, do not improvise the positive-confirmation redesign inside this task. Record
  the finding and let it drive a follow-up — the shared helper added here is the correct place
  for such a condition to land later, which is the point of the refactor.
- **Named follow-up (deliberately not done here)**: wire `--self-test` into
  `scripts/pre-pr-check.sh` as a step beside the existing Boneyard quarantine self-test, so the
  fixture assertions run on every local pre-PR check without needing a `lake build`. Out of this
  task's declared file scope.
