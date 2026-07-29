# Implementation Plan: Scope pre-pr-check step 1's sorry gate

- **Task**: 584 - scope_pre_pr_check_sorry_gate
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/584_scope_pre_pr_check_sorry_gate/reports/01_scope-pre-pr-check-sorry-gate.md
- **Artifacts**: plans/01_scope-sorry-gate-delegation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Step 1 of `scripts/pre-pr-check.sh` announces itself as a PR-scope check but is a tree-wide
"fail on ANY sorry" gate over four whole directory trees, making the completion bar
"pre-pr-check.sh passes end to end" unsatisfiable for any scoped task. The research report
establishes that step 1's detection logic is a verbatim duplicate of
`check-sorry-suppressions.sh`'s `count_sorries()`, and that step 8's baseline
(`scripts/sorry-suppression-baseline.txt`) already contains step 1's entire 24-hit/6-file
failure set per file, over a strict superset scan root. Therefore the fix is **delegation, not
a second baseline**: add a `--scope PATH...` filter (plus an opt-in `--changed` narrowing) to
`check-sorry-suppressions.sh`, make step 1 a scoped invocation of it, and fix the misleading
wording plus two stale companion comments. Done means: step 1 is green on the unmodified tree,
still red on genuinely new in-scope debt, step numbering is unchanged, and
`sorry-suppression-baseline.txt` is byte-identical.

### Research Integration

Findings carried forward from `reports/01_scope-pre-pr-check-sorry-gate.md`:

- **Reuse means delegation** (§1, §4). Step 8's baseline already holds step 1's exact failure
  set (7, 2, 12, 1, 1, 1 = 24 across 6 files) and its scan root `Cslib` is a strict superset of
  step 1's four trees. A second baseline inside step 1 would be a strict-subset duplicate that
  can never fail where step 8 passes.
- **Changed-files mode alone provably does not work** (§1 finding 4, §2.5). Against
  `git merge-base HEAD origin/main`, 114 in-scope `.lean` files are changed and 3 of the 6 debt
  files are among them. The predicate must become baseline-relative; `--changed` is an optional
  extra narrowing only, defaulting OFF.
- **Option 1 chosen; Option 2 (delete step 1 and renumber) rejected on cost** (§5). Seven
  external sites cite `pre-pr-check.sh` steps by number (§3.2); preserving numbering keeps that
  edit at zero.
- **Highest-risk trap** (§6 item 1): a scoped `--update` would rewrite the whole-tree baseline
  from a partial sweep, silently zeroing the out-of-scope `Propositional/Tableau` rows. It MUST
  `exit 2`.
- **Two zero-file conditions must not collapse** (§6 item 2): a mistyped `--scope` stays a
  fatal `exit 2`; an empty `--changed` set is `exit 0` with an explicit "nothing to check" line.
- **Baseline comparison stays whole-file-keyed** (§6 item 3): scoping filters which files are
  *swept*, never which baseline rows are *loaded*.
- **Blast radius is low** (§3.3): `pre-pr-check.sh` is fork-local, absent from `upstream/main`,
  and is not invoked by either CI workflow or the `/pr` pipeline. It is a local developer/agent
  pre-flight aggregator only.
- **No agent-system change is in scope** (§3.4): the "passes end to end" phrasing is per-task
  prose under `specs/`, with no template in `agent-system/extensions/cslib/`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap path was supplied in the delegation context; no ROADMAP.md was consulted or modified.

## Goals & Non-Goals

**Goals**:

- Make `pre-pr-check.sh` step 1 baseline-relative so it fails only on NEW sorry debt beyond
  `scripts/sorry-suppression-baseline.txt`, and is therefore satisfiable on a clean tree.
- Implement that by adding `--scope PATH...` to `check-sorry-suppressions.sh` and having step 1
  delegate to it — one baseline, one discrimination rule, no duplicated logic.
- Add `--changed [--base REF]` as an opt-in extra narrowing, defaulting OFF in
  `pre-pr-check.sh`.
- Replace step 1's misleading "Checking for sorry instances in PR scope..." wording with text
  naming the actual predicate and the actual trees.
- Fix the two stale companion comments: `check-sorry-suppressions.sh`'s "can run as step 1"
  claim, and `pre-pr-check.sh`'s steps 8/9 rationale block which asserts the very behaviour this
  task removes.
- Preserve step numbering so all seven external "step N of pre-pr-check.sh" citations stay
  correct.

**Non-Goals**:

- **Do NOT narrow step 5** (`lake build --wfail --iofail`). It deliberately mirrors CI and must
  keep failing on repo-wide sorry warnings. Steps 1 and 5 have different scopes and are not
  redundant.
- **Do NOT resolve any existing sorry.** This is gate-scoping work, not proof work.
- **Do NOT edit any file under `Cslib/`.**
- **Do NOT change `scripts/sorry-suppression-baseline.txt`.** It must remain byte-identical; the
  ratchet is currently exactly at baseline (18/18 markers, 28/28 sorries).
- Do NOT renumber any `pre-pr-check.sh` step.
- Do NOT touch `agent-system/extensions/**` or `.claude/**`; the authoritative `file_scope` is
  `scripts/pre-pr-check.sh`, `scripts/check-sorry-suppressions.sh`, `scripts/README.md`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A scoped `--update` rewrites the whole-tree baseline from a partial sweep, silently zeroing out-of-scope rows and breaking the ratchet | H | M | Phase 1 makes `--update` combined with `--scope` or `--changed` a hard `exit 2` usage error before any file is written; Phase 5 verifies the baseline's content and mtime are unchanged after attempting it |
| Refactoring the argument parser breaks the existing no-arg / `--list` / `--update` invocations used by CI and step 8 | H | M | The no-arg path is exercised in Phase 1 and again in Phase 5 item 1; the existing `markers: 18 ... sorries: 28 ... OK` output is the fixed expected string |
| Collapsing "scope matched nothing" with "changed set is empty" makes a mistyped path read as clean | H | M | Two distinct code paths and two distinct exit codes, specified in Phase 1 and Phase 2 and separately verified in Phase 5 item 6 |
| Scoped run's summary line compares a scoped current total against a whole-tree baseline ceiling and reads as a spurious improvement | M | H | Phase 1 restricts the *displayed* ceiling total to swept paths and labels the run as scoped; the per-file comparison arrays stay whole-tree-keyed and untouched |
| Improvement message tells the user to run a scoped `--update`, which is the exact forbidden operation | H | M | Phase 1 keeps the printed remediation command bare (`bash $0 --update`) and adds a scoped-run caveat line |
| `--changed` git mechanics silently yield an empty set on a detached HEAD or missing remote, reading as clean | M | M | Phase 2 makes unresolvable base ref / absent remote / detached HEAD an `exit 2` environment error, never a silent empty set |
| Editing `scripts/README.md` (the one file in scope that exists upstream) enlarges sync-conflict surface | L | M | Phase 4 keeps edits additive and localized to the existing "Sorry/suppression volume ratchet" section; no restructuring |
| `shellcheck` is unavailable locally, so a shell defect ships unlinted | L | H | Model all new code closely on the three existing passing ratchet scripts; the path-triggered `shellcheck.yml` workflow sweeps on push |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Add `--scope PATH...` to check-sorry-suppressions.sh [NOT STARTED]

**Goal**: Give the existing ratchet gate a scope filter that narrows which files are swept while
leaving the baseline, the comparison keying, and every existing invocation byte-for-byte
unchanged in behaviour.

**Tasks**:

- [ ] Replace the single-argument `case "${1:-}"` dispatch with a real argument loop that
      recognizes `--list`, `--update`, `--scope PATH...` (consuming paths until the next
      `--`-prefixed token or end of args), and reserves `--changed` / `--base REF` for Phase 2.
      An unrecognized token remains a usage error with `exit 2`.
- [ ] Introduce a `SCOPE_PATHS=()` array. When empty, the sweep root stays exactly `SCAN_ROOT`
      (`Cslib`) so the no-arg, `--list`, and `--update` paths are unchanged.
- [ ] Factor the file sweep into one helper (e.g. `sweep_files()`) that emits the sorted `.lean`
      file list, and route **all three** existing `find "$SCAN_ROOT" -name '*.lean'` call sites
      through it: `current_counts()`'s process substitution, the `--update` `nfiles` guard, and
      the verify path's `nfiles` guard.
- [ ] Implement the `--update` refusal: if `--update` is combined with `--scope` (or, once Phase
      2 lands, `--changed`), print a usage error naming the silent-ratchet-break hazard and
      `exit 2` **before** any write to `$BASELINE`.
- [ ] Preserve the zero-file fatal condition for the default and `--scope` sweeps: a sweep
      yielding zero files stays `exit 2` ("a scan root that resolves to nothing must never read
      as clean"), including a mistyped `--scope` path.
- [ ] Leave the baseline loader untouched: `base_markers` / `base_sorries` continue to be
      populated from every non-comment row of `$BASELINE`, never from a filtered subset.
- [ ] Adjust the summary line for scoped runs only: label the run as scoped (naming the scope
      paths) and compute the *displayed* ceiling totals by summing baseline rows restricted to
      the swept paths. This is display-only — do not let it touch `base_markers`/`base_sorries`
      or the per-file comparison.
- [ ] Keep the improvements "ACTION REQUIRED" remediation command bare
      (`bash $0 --update`, never with the scope args appended), and add a caveat line noting a
      scoped run sees only part of the tree so the re-baseline must be run unscoped.
- [ ] Exercise the unchanged paths: `bash scripts/check-sorry-suppressions.sh` still prints
      `markers: 18 (baseline ceiling 18); sorries: 28 (baseline ceiling 28)` and exits 0;
      `--list` still exits 0; `--update` on a clean invocation is NOT run (it would rewrite the
      baseline) — instead confirm by inspection that its code path is reached only when no scope
      is set.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that exactly three `find "$SCAN_ROOT" -name '*.lean'`
call sites exist in `check-sorry-suppressions.sh` (in `current_counts()`, the `--update` guard,
and the verify-path guard). Confirm at implementation time with
`grep -n 'find "\$SCAN_ROOT"' scripts/check-sorry-suppressions.sh` before refactoring; if the
count differs, route every occurrence found through the helper rather than the three assumed.

**Files to modify**:

- `scripts/check-sorry-suppressions.sh` - argument loop, `SCOPE_PATHS`, `sweep_files()` helper,
  `--update` refusal guard, scoped summary-line display, scoped improvement caveat

**Verification**:

- `bash scripts/check-sorry-suppressions.sh` (no args) exits 0 with the exact pre-change summary
  line.
- `bash scripts/check-sorry-suppressions.sh --scope Cslib/Logics/Modal` exits 0 and reports a
  scoped run.
- `bash scripts/check-sorry-suppressions.sh --scope Cslib/Does/Not/Exist` exits 2.
- `bash scripts/check-sorry-suppressions.sh --update --scope Cslib/Logics/Modal` exits 2 and
  `git diff --stat scripts/sorry-suppression-baseline.txt` is empty.

---

### Phase 2: Add opt-in `--changed [--base REF]` narrowing [NOT STARTED]

**Goal**: Add a git-aware extra narrowing that restricts the sweep to files this branch actually
touches, as an opt-in flag that is never the sole predicate and defaults OFF everywhere.

**Tasks**:

- [ ] Wire `--changed` and `--base REF` into the Phase 1 argument loop. Default base ref is
      `origin/main`. Do **not** default to `upstream/main` (626 changed `.lean` files; useless
      as a filter).
- [ ] Resolve the merge base with `git merge-base HEAD "$BASE_REF"`. An unresolvable base ref,
      an absent remote, or a detached HEAD is an environment error: `exit 2` with a clear
      message, never a silent empty/clean set.
- [ ] Build the changed set as the union of `git diff --name-only --diff-filter=d <mb> HEAD`,
      `git diff --name-only --diff-filter=d HEAD` (unstaged), and
      `git diff --name-only --diff-filter=d --cached`, plus
      `git ls-files --others --exclude-standard` for new untracked files. Use lowercase
      `--diff-filter=d` so deleted paths are never stat'd.
- [ ] Restrict the union to `*.lean` paths under the scan root, and intersect with `SCOPE_PATHS`
      when `--scope` is also given. Defensively drop any path that no longer exists on disk.
- [ ] Implement the distinct empty-set semantics: when `--changed` is active and the resulting
      set is empty, print an explicit "no changed .lean files in scope; nothing to check" line
      and `exit 0`. This must NOT reuse the `--scope`/default zero-file `exit 2` path — the two
      conditions stay separate branches.
- [ ] Confirm `--update` still refuses `--changed` (the Phase 1 guard must cover both flags).
- [ ] Leave `pre-pr-check.sh` untouched in this phase — `--changed` is not wired into any step.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Files to modify**:

- `scripts/check-sorry-suppressions.sh` - `--changed` / `--base` parsing, merge-base resolution,
  changed-set union, empty-changed-set exit-0 branch

**Verification**:

- `bash scripts/check-sorry-suppressions.sh --changed` exits 0 or 1 (never 2) on a working
  `origin/main`, and its sweep is a subset of the full tree.
- `bash scripts/check-sorry-suppressions.sh --changed --base HEAD` (empty diff) exits 0 and
  prints the "nothing to check" line.
- `bash scripts/check-sorry-suppressions.sh --changed --base no/such/ref` exits 2.
- `bash scripts/check-sorry-suppressions.sh --update --changed` exits 2 with the baseline
  unmodified.
- The no-arg path still exits 0 with the unchanged summary line (the shared parser must not have
  regressed).

---

### Phase 3: Rewire pre-pr-check.sh step 1 and fix its comments [NOT STARTED]

**Goal**: Replace step 1's inline tree-wide sorry sweep with a scoped delegation to
`check-sorry-suppressions.sh`, correct the misleading wording, and repair the two in-file
comments that the change falsifies.

**Tasks**:

- [ ] Delete step 1's inline detection block (the `perl -0777` / `sed` / `grep -n` /
      `grep -v 'warn\.sorry'` pipeline, the `sorry_hits` accumulator, and its `find ... -print0`
      loop over the four trees).
- [ ] Replace it with a delegated invocation, keeping the step number at 1 and using the same
      `"$(dirname "${BASH_SOURCE[0]}")/check-sorry-suppressions.sh"` form steps 6-9 already use,
      passing `--scope Cslib/Foundations/Logic Cslib/Logics/Modal Cslib/Logics/Temporal
      Cslib/Logics/Bimodal`. Do not pass `--changed`.
- [ ] Accumulate failure into `failed=1` on a nonzero exit, matching the surrounding steps'
      pattern.
- [ ] Rewrite the announcement line so it names the predicate rather than claiming "PR scope":
      state that it is a baseline-relative sorry ratchet over the four named trees that fails
      only on NEW debt.
- [ ] Add a comment recording that the four-tree list is a stale artifact of an earlier PR
      series (mirroring step 4's hand-picked module list) and is not a live definition of "PR
      scope", so the next reader does not treat it as authoritative.
- [ ] Add a comment stating the honest relationship: step 1 is early, scoped, same-baseline
      fast-fail; it contributes no unique failure coverage over step 8 and can never fail where
      step 8 passes. Its value is early scoped feedback.
- [ ] Update the steps 8/9 rationale comment block, which currently justifies the split by
      saying step 1 "fails on ANY sorry found there" — the exact sentence this task removes.
      Replace with the new relationship, and preserve the note that steps 1 and 5 have different
      scopes (the three `Propositional/Tableau/*` files trip step 5 but are invisible to step 1).
- [ ] Update the file-top comment, which says "steps 1-3 are advisory greps" — step 1 is no
      longer a grep. Adjust to describe the surviving advisory-grep steps accurately.
- [ ] Confirm no step was renumbered and step 5 was not touched.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that step numbering is unchanged and therefore that all
seven external "step N of `pre-pr-check.sh`" citations (`scripts/README.md` ×3,
`docs/lint-suppression-policy.md` ×1, and header comments in `check-sorry-suppressions.sh`,
`check-shake-residue.sh`, `check-axiom-census.sh`) need no edit. Confirm at implementation time
with `grep -rn 'step [0-9] of .*pre-pr-check' scripts/ docs/` and check each hit still names the
correct step; if the count differs from seven, reconcile against what the grep actually returns
rather than the asserted number.

**Files to modify**:

- `scripts/pre-pr-check.sh` - step 1 body and announcement, step 1 comments, steps 8/9 rationale
  comment, file-top comment

**Verification**:

- `bash scripts/pre-pr-check.sh` reaches and passes step 1 on the unmodified tree (later steps,
  including step 5, may still fail — that is the declared non-goal and is expected).
- `grep -n 'lake build --wfail --iofail' scripts/pre-pr-check.sh` shows step 5 unchanged.
- `grep -cE '^echo "[0-9]\.' scripts/pre-pr-check.sh` still yields 9 step announcements with the
  same numbering.

---

### Phase 4: Update the script header and scripts/README.md [NOT STARTED]

**Goal**: Bring the two documentation surfaces in scope into agreement with the new behaviour,
including the pre-existing stale cross-reference the research report flagged.

**Tasks**:

- [ ] Extend `check-sorry-suppressions.sh`'s Usage block to document `--scope PATH...`,
      `--changed`, and `--base REF`.
- [ ] Extend its EXIT-CODE CONTRACT block with the two new, deliberately distinct conditions: a
      `--scope` sweep matching zero files is `exit 2`; an empty `--changed` set is `exit 0` with
      an explicit "nothing to check" line.
- [ ] Add a short header subsection explaining why `--update` refuses `--scope`/`--changed`: a
      partial sweep would rewrite the whole-tree baseline and silently zero out-of-scope rows,
      lowering their ceiling to 0 — a silent ratchet break.
- [ ] Fix the stale line in the "WHAT THIS GATE DOES NOT NEED" section claiming the script "can
      run as step 1 of `scripts/pre-pr-check.sh`'s local checks" — it is wired as step 8, and
      after Phase 3 it is invoked at **both** step 1 (scoped) and step 8 (whole-tree). State
      that precisely rather than leaving it ambiguous.
- [ ] In `scripts/README.md`, extend the existing "Sorry/suppression volume ratchet" section's
      usage block with the new flags, and add a sentence recording the dual wiring (step 1
      scoped, step 8 whole-tree) and that step 1 contributes no unique coverage.
- [ ] Keep README edits additive and localized to that section; do not restructure the file, and
      do not touch the shake (step 7) or axiom-census (step 9) sections.
- [ ] Do not cite task numbers anywhere in these files (deliverables outside `specs/**`).

**Timing**: 0.75 hours

**Depends on**: 2, 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the README edit is confined to one existing section
("Sorry/suppression volume ratchet") and that the three README step citations (steps 7, 8, 9)
remain correct. Confirm with `grep -n 'step [0-9] of' scripts/README.md` before and after; the
set of cited step numbers must be identical.

**Files to modify**:

- `scripts/check-sorry-suppressions.sh` - header Usage block, EXIT-CODE CONTRACT, new
  `--update`-refusal rationale subsection, stale step-1 cross-reference fix
- `scripts/README.md` - "Sorry/suppression volume ratchet" section usage block and wiring note

**Verification**:

- Diff read-through confirming every changed hunk in `check-sorry-suppressions.sh` lies inside
  the leading `#` comment block (no executable line touched by this phase).
- `grep -n 'step [0-9] of' scripts/README.md` returns the same step numbers as before the phase.
- No occurrence of a task-number citation in either file.

---

### Phase 5: Full verification sweep and baseline invariance proof [NOT STARTED]

**Goal**: Demonstrate both the pass path and the fail path, prove the two zero-file conditions
stay distinct, prove the `--update` guard holds, and restore a bit-identical tree.

**Tasks**:

- [ ] **Baseline invariance**: `git diff --stat scripts/sorry-suppression-baseline.txt` is
      empty; `bash scripts/check-sorry-suppressions.sh` prints
      `markers: 18 (baseline ceiling 18); sorries: 28 (baseline ceiling 28)` and exits 0.
- [ ] **Step 1 passes**: `bash scripts/pre-pr-check.sh` — step 1 green on the unmodified tree.
      Step 5 is expected to still fail; record that explicitly as the declared non-goal, not as
      a defect.
- [ ] **Step 1 still catches regressions**: create a scratch `.lean` file under one of the four
      trees containing a bare code-position `sorry`; confirm step 1 exits nonzero naming that
      file; delete the scratch file and re-confirm green.
- [ ] **Scope asymmetry is demonstrated, not asserted**: place the same scratch probe under
      `Cslib/Logics/Propositional/`; confirm step 1 stays green while step 8 goes red; delete
      the probe and re-confirm.
- [ ] **`--update` guard**:
      `bash scripts/check-sorry-suppressions.sh --update --scope Cslib/Logics/Modal` exits 2 and
      leaves `sorry-suppression-baseline.txt` unchanged in both content and mtime; repeat with
      `--update --changed`.
- [ ] **Two zero-file conditions stay distinct**:
      `--scope Cslib/Does/Not/Exist` exits 2; `--changed --base HEAD` exits 0 with the
      "nothing to check" line.
- [ ] **Doc consistency**: `grep -rn 'step [0-9] of .*pre-pr-check' scripts/ docs/` — every
      surviving citation still names the correct step. Under the chosen design none should need
      editing, which is itself the check.
- [ ] **Tree restored**: `git status --porcelain` shows no scratch probe files and no changes
      under `Cslib/`; the only modified files are the three in `file_scope`.
- [ ] Note in the summary that `shellcheck` is unavailable in this environment (as recorded by
      prior tasks); the path-triggered `shellcheck.yml` workflow will sweep on push.

**Timing**: 1 hour

**Depends on**: 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the exact figures `markers: 18 (baseline ceiling 18);
sorries: 28 (baseline ceiling 28)` and step 1's historical 24-hit/6-file failure set. Confirm by
running `bash scripts/check-sorry-suppressions.sh` at the start of the phase and comparing
against these values; if they differ, the tree changed since the research measurement and the
discrepancy must be investigated and reported before proceeding — it is not to be silently
re-baselined.

**Files to modify**:

- None (verification only; scratch probe files are created and deleted within the phase and must
  not be committed)

**Verification**:

- All eight checklist items above pass.
- Final `git status --porcelain` limited to `scripts/pre-pr-check.sh`,
  `scripts/check-sorry-suppressions.sh`, `scripts/README.md`, and `specs/**` artifacts.

---

## Testing & Validation

- [ ] `bash scripts/check-sorry-suppressions.sh` (no args) — unchanged output, exit 0.
- [ ] `bash scripts/check-sorry-suppressions.sh --list` — exit 0.
- [ ] `bash scripts/check-sorry-suppressions.sh --scope <four trees>` — exit 0, scoped label.
- [ ] `bash scripts/check-sorry-suppressions.sh --scope Cslib/Does/Not/Exist` — exit 2.
- [ ] `bash scripts/check-sorry-suppressions.sh --changed --base HEAD` — exit 0, "nothing to
      check".
- [ ] `bash scripts/check-sorry-suppressions.sh --changed --base no/such/ref` — exit 2.
- [ ] `bash scripts/check-sorry-suppressions.sh --update --scope ...` — exit 2, baseline
      untouched.
- [ ] `bash scripts/check-sorry-suppressions.sh --update --changed` — exit 2, baseline untouched.
- [ ] `bash scripts/pre-pr-check.sh` — step 1 green; step 5 still red (expected, declared
      non-goal).
- [ ] Scratch-probe in-scope: step 1 red. Scratch-probe out-of-scope: step 1 green, step 8 red.
- [ ] `git diff --stat scripts/sorry-suppression-baseline.txt` empty at every phase boundary.
- [ ] `git status --porcelain` shows no changes under `Cslib/`.

## Artifacts & Outputs

- `scripts/check-sorry-suppressions.sh` — `--scope`, `--changed`, `--base` flags; `--update`
  refusal guard; corrected header documentation
- `scripts/pre-pr-check.sh` — step 1 delegating to the scoped ratchet; corrected wording and
  three comment blocks
- `scripts/README.md` — updated "Sorry/suppression volume ratchet" usage and wiring note
- `specs/584_scope_pre_pr_check_sorry_gate/summaries/01_scope-sorry-gate-delegation-summary.md`
- Unchanged (asserted invariants): `scripts/sorry-suppression-baseline.txt`, every file under
  `Cslib/`, step 5 of `pre-pr-check.sh`, step numbering across all nine steps

## Rollback/Contingency

All three modified files are fork-local or additively edited, and none is on a CI path
(`pre-pr-check.sh` is invoked by neither workflow nor the `/pr` pipeline), so reverting is
low-risk: `git revert` the phase commits, or `git checkout <pre-task-sha> -- scripts/pre-pr-check.sh
scripts/check-sorry-suppressions.sh scripts/README.md`. Because commits are per-green-substep,
partial rollback to any completed phase boundary is available. If Phase 1's parser refactor
proves to destabilize the existing no-arg path, fall back to a narrower variant that leaves the
existing `case` dispatch intact and adds scope handling as a separate pre-pass — the delegation
design in Phase 3 is unaffected by which parser shape is used. If the scratch-probe experiments
in Phase 5 leave stray files, remove them explicitly by path; do not run `git clean` or any
destructive git operation on a dirty tree.
