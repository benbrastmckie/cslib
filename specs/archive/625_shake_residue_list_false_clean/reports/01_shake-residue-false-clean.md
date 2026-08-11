# Research Report: Task #625

**Task**: 625 - shake_residue_list_false_clean
**Started**: 2026-08-10T16:00:00-07:00
**Completed**: 2026-08-10T16:20:00-07:00
**Effort**: Small (single-function fix + self-test addition)
**Dependencies**: None
**Sources/Inputs**:
- Codebase: `scripts/check-shake-residue.sh`, `scripts/check-axiom-census.sh`,
  `scripts/check-boneyard-quarantine.sh`, `scripts/pre-pr-check.sh`,
  `.claude/scripts/check-runtime-file-tracking.sh`
- Lake/Lean toolchain source: `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/lake/Lake/{Build/Common.lean,Build/Run.lean,CLI/Main.lean}`
- Live empirical reproduction against this repo's actual `Cslib` facade target
**Artifacts**:
- This report: `specs/625_shake_residue_list_false_clean/reports/01_shake-residue-false-clean.md`
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Empirically confirmed (not inferred)**: when the `Cslib` facade target is out-of-date, `lake
  shake` exits **1** — the same exit code as its normal "I have suggestions" outcome — and
  produces zero lines matching `parse_flagged_set`'s `^/.*\.lean:$` pattern. This is the
  **"if shake exits 1" branch** of the task's own decision table, so the fix is the narrow one:
  hoist the existing `shake_exit -eq 1 && live is empty -> exit 2` guard (already present on the
  bare and `--update` paths) into the `--list` branch. No baseline-corruption or `--update`
  danger exists — `--update` already has the correct guard.
- Root cause confirmed exactly as hypothesized: the `--list` branch (`scripts/check-shake-residue.sh`
  lines 96-104) implements only the "non-0/1 exit" guard (lines 99-102) and is missing the
  "exit 1 + empty parse" guard that both the bare path (lines 157-162) and `--update` (lines
  112-115) already have.
- Reproduced the exact live failure end-to-end through the real script: `bash
  scripts/check-shake-residue.sh --list` exits `0` with `0` lines of stdout when run against a
  genuinely stale `Cslib` facade target — indistinguishable from a real "nothing flagged" clean
  run, exactly as task 625 describes.
- Found a strong, already-in-tree precedent for the correct fix shape: `scripts/check-axiom-census.sh`
  (explicitly documented in its own header as "the direct analogue of check-shake-residue.sh")
  implements this exact validation as **one shared `run_and_validate_census()` helper** called
  identically by `--list`, `--update`, and the bare path — rather than three independently
  duplicated guards (which is the architecture that let `--list` fall out of sync in the first
  place). Recommend the shake script adopt the same shared-helper shape rather than a third
  copy-pasted guard block.
- The task's suggested self-test precedent (`check-runtime-file-tracking.sh`'s "fixture
  convention") does not actually exist as described — that script performs live git-ignore
  *probes* against real paths, not synthetic captured-output fixtures fed through a parser. The
  closer, real precedent for a synthetic-fixture self-test is `check-boneyard-quarantine.sh`'s
  self-test terminology plus `parse_flagged_set`/`parse_summary`'s own pure-function shape,
  which is directly testable by assigning literal heredoc text to `$shake_raw`/`$shake_exit` and
  calling the parser functions without invoking `lake` at all.

## Context & Scope

Task 625 asks to determine, empirically, what exit code `lake shake` returns when the `Cslib`
facade target is out-of-date, since the fix differs materially depending on the answer (a
5-line guard hoist for the "exits 1" case vs. a much larger three-mode positive-confirmation
redesign for the "exits 0" case). This research reproduces the failure directly against the
live repository, traces the exact mechanism through the Lake toolchain source, and confirms the
result via the actual `check-shake-residue.sh --list` invocation (not just the raw `lake shake`
command), then designs the corresponding fix.

## Findings

### The empirically determined answer: `lake shake` exits 1, not 0

**Reproduction procedure** (repo root, no state left behind — see "Reproduction is
non-destructive" below):

1. Baseline sanity check: `lake shake --add-public --keep-implied --keep-prefix Cslib` against
   the repo's normal, fully-built state exits `1` (its ordinary "has suggestions" outcome) with
   203 lines of output including many `^/.*\.lean:$` flagged-file header lines. This confirms the
   build was fully up to date before the experiment and that `parse_flagged_set` behaves
   normally on a healthy run.
2. **Touching a file's mtime is not sufficient to reproduce the bug.** Lake's default trace
   checking is content-hash-based, not mtime-based (`BuildConfig.oldMode` defaults to `false` —
   see `Lake/Build/Context.lean:19`, `"Use modification times for trace checking"`). `touch
   Cslib.lean` followed by `lake shake` triggered a normal rebuild-and-replay cycle and exited 1
   with the same 203-line healthy output — this does **not** reproduce the reported bug and is a
   trap for anyone trying to reproduce it via `touch`.
3. **Genuinely invalidating the build** requires a real content change. Appending one comment
   line to a small leaf file (`Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`)
   changes its content hash, which invalidates its own build trace and every trace that
   transitively depends on it (including the `Cslib` facade, since `Cslib.lean` imports it
   transitively). Running `lake shake --add-public --keep-implied --keep-prefix Cslib` directly
   afterward (no intervening `lake build`) reproduced the exact reported symptom in ~2.25s:
   ```
   ✖ [3228/3325] Building Cslib.Logics.Propositional.NaturalDeduction.Normalization
   error: target is out-of-date and needs to be rebuilt
   ...
   error: there are out of date oleans; run `lake build` or fetch them from a cache first
   ```
   **`echo $?` immediately after this run reported exit code `1`.**
4. The full 179-line combined stdout+stderr output contains **zero** lines matching
   `grep -E '^/.*\.lean:$'` (shake's own per-file header format) — every path-bearing warning
   line in this failure mode is a repo-relative path with an embedded `:LINE:COL:` suffix (e.g.
   `Cslib/Logics/Modal/Tableau/S4/Driver.lean:893:100:`), which does not match the absolute-path,
   trailing-colon-only header pattern shake normally emits for a flagged file. So
   `parse_flagged_set` correctly returns empty on this input — the bug is not in the parser, it
   is in what happens when the parser's emptiness is combined with `shake_exit == 1`.
5. **Ran the actual deployed script**, not just raw `lake shake`, against the same reproduced
   stale state: `bash scripts/check-shake-residue.sh --list` exited **`0`** and printed **zero**
   lines of stdout — the exact false-clean signature task 625 reports.
6. Reverted the one-line edit (`git checkout -- Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`)
   and confirmed `git status --porcelain` shows the file clean again. No repository state was
   left behind by this research.

**Mechanism, traced through Lake's own source** (`~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/lake/`):

- `lake shake`'s CLI handler (`Lake/CLI/Main.lean:1099-1118`, the `protected def shake`
  function) runs a **pre-flight staleness check** before doing anything else, unless `--force`
  is passed (the script's `SHAKE_ARGS` never passes `--force`):
  ```lean
  unless args.force do
    let specs ← parseTargetSpecs ws []
    let upToDate ← ws.checkNoBuild (buildSpecs specs)
    unless upToDate do
      error "there are out of date oleans; run `lake build` or fetch them from a cache first"
  ```
- `Workspace.checkNoBuild` (`Lake/Build/Run.lean:405-413`) is explicitly documented as
  "equivalent to checking whether `lake build --no-build` exits with code 0" — it runs the build
  graph with `noBuild := true` and reports whether any target needed rebuilding.
- Internally, `buildAction` (`Lake/Build/Common.lean:307-327`) is the function that, when
  `noBuild` is set and a target needs rebuilding, throws the literal error string **"target is
  out-of-date and needs to be rebuilt"** (line 318) — this is exactly the string quoted in the
  task description, and it is printed as part of the pre-flight check's own progress reporting
  (`BuildConfig.showProgress` is `true` by default even during a `noBuild` dry-run, per
  `Lake/Build/Context.lean:44-49`), interleaved with shake's normal per-module replay output
  before the pre-flight check concludes and the CLI-level `error` call fires.
- Lake's CLI-level `error` helper (`Lake/Util/MainM.lean:73`) defaults to **exit code 1**
  (`rc : ExitCode := 1`) — this is the exit code the shell process actually receives, confirmed
  empirically above.
- So the full sequence for a stale target is: shake's pre-flight `checkNoBuild` dry-run hits the
  stale target, `buildAction` throws "target is out-of-date and needs to be rebuilt" (printed to
  the combined output stream), `checkNoBuild` reports `upToDate = false`, and the CLI handler
  then calls `error "there are out of date oleans; ..."`, which prints that second message and
  terminates the process with **exit 1** — before shake ever reaches its own import-analysis
  logic, so no `^/.*\.lean:$` header lines are ever produced.

### Root cause: guard asymmetry confirmed exactly as hypothesized

Reading `scripts/check-shake-residue.sh` line-for-line confirms the task's own diagnosis with no
correction needed:

| Path | non-0/1 shake exit guard | shake exit 1 + empty parse guard |
|------|---------------------------|-----------------------------------|
| bare (verify gate) | lines 150-155 (`exit 2`) | lines 157-162 (`exit 2`) — **present** |
| `--update` | lines 108-111 (`exit 2`) | lines 112-115 (`exit 2`) — **present** |
| `--list` | lines 99-102 (`exit 2`) | **absent** — falls through to unconditional `exit 0` at line 103 |

The `--list` branch (lines 96-104) is:
```bash
--list)
    run_shake
    parse_flagged_set
    if [ "$shake_exit" -ne 0 ] && [ "$shake_exit" -ne 1 ]; then
      echo "ERROR: lake shake exited $shake_exit (expected 0 or 1)." >&2
      exit 2
    fi
    exit 0
    ;;
```
`parse_flagged_set` is called directly (printing its output as it runs, unlike `--update`/bare
which capture it into `$live` first) so its emptiness is never inspected. The only guard present
checks for a shake exit code outside `{0, 1}`; since the reproduced failure mode is exit `1`, it
sails through this guard and falls to the unconditional `exit 0`.

### Fix design

**Minimal fix** (closes the defect completely, per the task's own "if shake exits 1" branch):
hoist the exact guard already used at lines 112-115 (`--update`) / 157-162 (bare) into `--list`,
which requires capturing `parse_flagged_set`'s output into a variable first so it can be tested
for emptiness before being printed:

```bash
--list)
    run_shake
    live="$(parse_flagged_set)"
    if [ "$shake_exit" -ne 0 ] && [ "$shake_exit" -ne 1 ]; then
      echo "ERROR: lake shake exited $shake_exit (expected 0 or 1)." >&2
      exit 2
    fi
    if [ "$shake_exit" -eq 1 ] && [ -z "$live" ]; then
      echo "ERROR: lake shake exited 1 (suggestions expected) but no flagged-file lines were" >&2
      echo "parseable from its output. Either shake's output format changed (update the" >&2
      echo "extractor in this script) or the environment is broken (stale/unbuilt oleans --" >&2
      echo "run 'lake build' first). This is NOT reported as a clean/empty flagged set." >&2
      exit 2
    fi
    printf '%s\n' "$live"
    exit 0
    ;;
```
(`printf '%s\n' "$live"` at the end preserves the current one-path-per-line `--list` output
contract when `$live` is non-empty; when `$live` is empty and both guards pass — the genuine
"shake exit 0, nothing flagged" case — this correctly prints nothing and exits 0, matching
today's intended behavior for a real clean run.)

**Recommended stronger fix** (structural, not just line-patching): the three guard blocks
across `--list`/`--update`/bare are currently three independently maintained copies of the same
two conditions — this is exactly the shape that let `--list` drift out of sync with the other
two in the first place, and a fourth call site (or a future edit to one copy but not the others)
can reintroduce the same class of bug. `scripts/check-axiom-census.sh` — which its own header
comment explicitly calls "the direct analogue of check-shake-residue.sh" for this exact
guard — already solves the identical problem the correct way: a single
`run_and_validate_census()` function (lines 105-129) that runs the external tool once, validates
all fatal conditions, and returns 0/2, called identically from `--list` (132-138), `--update`
(139-143), and the bare path (180+). Recommend refactoring `check-shake-residue.sh` to the same
shape — a `run_and_validate_shake()` helper wrapping `run_shake` + both guard checks + returning
0 or 2 — called from all three branches, rather than leaving the fix as a third copy-pasted
guard block. This is a larger diff than the minimal fix but directly prevents recurrence, and
`check-axiom-census.sh` is a working, in-tree template to mirror almost verbatim.

### Self-test recommendation (correction to the task's suggested precedent)

The task's suggested approach names `check-runtime-file-tracking.sh` as the fixture-convention
precedent to follow. That script (`.claude/scripts/check-runtime-file-tracking.sh`) was read in
full: it performs three checks (A: ignore coverage, B: no tracked ephemeral files, C: provenance
not over-ignored), each via `git check-ignore -q` / `git ls-files` probes against literal
**example paths** (e.g. `specs/000_probe/.orchestrator-loop-guard`) run against the **real**
repository's actual `.gitignore` and index — there is no synthetic captured-command-output
fixture and no parser function under test. It is a live-repo self-test, not a synthetic-fixture
self-test, so it is not a literal template for testing `parse_flagged_set`/the guard logic
against captured `lake shake` output strings.

The actually-relevant precedent in this repo is `check-boneyard-quarantine.sh`, which uses the
term "self-test" for a `scripts/*.sh` gate script (its own header: "B0-style self-test") and
`pre-pr-check.sh`'s "Boneyard quarantine self-test" step name — establishing "self-test" as this
repo's convention for a script that asserts its own invariants. Combined with
`check-shake-residue.sh`'s existing pure-function design (`run_shake`/`parse_flagged_set` are
already cleanly separated, and `run_shake` populates two globals rather than being tangled into
the case-statement bodies), the natural self-test shape is a `--self-test` subcommand that:

1. Sets `shake_raw`/`shake_exit` directly to literal captured fixture strings (no `lake`
   invocation at all — instant, deterministic, no build dependency) for at least these cases:
   - **Normal flagged run**: `shake_exit=1`, `shake_raw` containing several `^/path.lean:$`
     header lines plus `add #[...]`/`remove #[...]` delta lines -> `parse_flagged_set` should
     return exactly those paths.
   - **The exact reproduced regression fixture**: `shake_exit=1`, `shake_raw` set to (or closely
     modeled on) the literal captured transcript from this report's reproduction — containing
     `error: target is out-of-date and needs to be rebuilt` and `error: there are out of date
     oleans; run \`lake build\` or fetch them from a cache first` with zero `^/.*\.lean:$` lines
     -> the guard (or `run_and_validate_shake`, if the structural fix is adopted) must reject
     this as an error, in all three modes (`--list`, `--update`, bare), never as an empty clean
     set.
   - **Genuinely clean run**: `shake_exit=0`, `shake_raw` with no flagged lines (e.g. just
     harmless warning/replay noise) -> all three modes must treat this as legitimately empty/clean.
   - **Unexpected exit code**: `shake_exit=2` (or any value outside `{0,1}`) -> exit 2 in all
     three modes, unchanged from current behavior.
2. Asserts on each mode's exit code and (where applicable) stdout content.
3. Exits 0 if every assertion passes, 1 otherwise — consistent with `check-boneyard-quarantine.sh`'s
   own exit contract.

This directly exercises the regression fixed by this task (case 2 above **is** the reproduced
bug, encoded as a fixture) without requiring a real Lean build in CI or locally, and would have
caught the original asymmetry mechanically.

### Header contract update

The EXIT-CODE CONTRACT block (`scripts/check-shake-residue.sh` lines 46-55) already states the
intended rule generally ("never silently treat an unparseable failed run as an empty clean set")
without restricting it to any one mode — the header text itself does not need substantive
rewording, only a note (or a worked example) added confirming all three usage modes are governed
by the same rule, since the current text's phrasing reads as mode-agnostic while the
implementation below it was not. If the structural `run_and_validate_shake()` refactor is
adopted, the header should name that function as the single implementation of the rule, mirroring
how `check-axiom-census.sh`'s header explicitly names `run_and_validate_census` in its own
EXIT-CODE CONTRACT section.

### Reproduction is non-destructive

All reproduction was done against real, uncommitted content edits reverted with `git checkout --
<file>` immediately after use; `git status --porcelain` was confirmed clean for both touched
files (`Cslib.lean`, `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`) before
concluding. No baseline files, build artifacts, or committed state were altered by this research.

## Decisions

- Confirmed the task's own hypothesis: shake exits **1**, not 0, on the out-of-date-target
  failure mode. The fix is the narrow "hoist the exit-1+empty guard into `--list`" path, not the
  larger three-mode positive-confirmation redesign the task flagged as the alternative
  (unnecessary — the existing guard shape is already correct in principle, just not applied
  uniformly).
- Recommend the structural `run_and_validate_shake()` refactor (mirroring
  `check-axiom-census.sh`) over a bare line-patch, specifically because the line-patch approach
  is what produced this exact defect once already (three independently maintained copies of the
  same two conditions, one of which silently fell behind).
- Recommend a `--self-test` subcommand using literal captured-fixture assignment to
  `$shake_raw`/`$shake_exit` (bypassing `lake` entirely) rather than attempting to follow
  `check-runtime-file-tracking.sh`'s live-git-probe pattern, which does not fit this script's
  external-tool-output-parsing shape.

## Recommendations

1. **Take the narrow fix branch.** Because `lake shake` exits 1 (empirically confirmed, not
   inferred) on the out-of-date-target failure mode, hoisting the existing
   `exit 1 + empty parse -> exit 2` guard into `--list` closes the defect completely. The
   three-mode positive-confirmation redesign the task held in reserve is not required, and the
   baseline ratchet in `scripts/shake-residue-baseline.txt` is not at risk.
2. **Implement it as a shared helper, not a third copy of the guard.** Extract
   `validate_shake_result()` / `run_and_validate_shake()` and route all three modes
   (`--list`, `--update`, bare) through it, mirroring `check-axiom-census.sh`'s
   `run_and_validate_census()`. Copy-paste divergence across the three modes is what produced
   this defect in the first place.
3. **Guard the `--list` print with `[ -n "$live" ]`.** An unconditional `printf` would emit a
   stray newline on a genuinely clean run, changing `--list`'s output contract from zero bytes
   to one — a second, quieter false signal in the same code path.
4. **Add a `--self-test` subcommand** with literal captured fixtures assigned directly to
   `$shake_raw`/`$shake_exit`, bypassing `lake` entirely. Follow
   `check-boneyard-quarantine.sh`'s self-test convention rather than
   `check-runtime-file-tracking.sh`, whose live-git-probe shape does not fit an
   external-tool-output-parsing script. Include the literal reproduced stale-target transcript,
   and confirm the self-test actually *fails* against a copy with the fix reverted.
5. **Keep the self-test away from the real baseline.** Redirect the baseline path to a temp
   file for the `--update` assertions and assert `scripts/shake-residue-baseline.txt` is
   byte-unchanged afterward.
6. **Reconcile the EXIT-CODE CONTRACT header block** so the documented rule and all three
   implemented paths agree, and preserve the script's deliberate absence of `set -e`.

## Risks & Mitigations

- **Risk**: A future edit to `parse_flagged_set`'s regex (e.g. if `lake shake`'s output format
  changes in a future toolchain) could reintroduce silent false-clean results if the
  fixture-based self-test is not kept in CI/pre-PR rotation. **Mitigation**: wire the
  `--self-test` subcommand into `scripts/pre-pr-check.sh` alongside the existing Boneyard
  self-test step (line 119), so it runs on every local pre-PR check without requiring a full
  `lake build`.
- **Risk**: `check-lint-suppressions.sh` and `check-sorry-suppressions.sh` were checked as
  possible siblings with the same class of bug; both operate purely on local `grep`/`perl`
  content scans with no external-tool exit-code ambiguity, so this specific defect class does not
  apply to them. No action needed there.
- **Risk**: The minimal line-patch fix alone (without the structural refactor) would leave the
  duplication-drift risk in place for any future guard-condition change. Flagged as a
  recommendation, not a blocker, since the task's own suggested approach explicitly permits the
  narrower fix when shake exits 1.

## Context Extension Recommendations

- **Topic**: Shared external-tool-invocation validation pattern for exact-set ratchet scripts.
- **Gap**: `scripts/check-axiom-census.sh`'s `run_and_validate_*()` pattern (single validation
  function shared across `--list`/`--update`/bare) is a proven, reusable shape for this repo's
  family of ratchet scripts (`check-shake-residue.sh`, `check-axiom-census.sh`, and any future
  sibling), but it is not documented anywhere as a named convention — it currently exists only
  as tribal knowledge encoded in one script's implementation.
- **Recommendation**: if a third ratchet script wrapping an external tool is ever added, consider
  documenting this pattern (e.g. in `scripts/README.md`) as "the `run_and_validate_*` shared-guard
  convention" so future authors reach for it directly rather than re-deriving (or re-forgetting)
  the three-mode symmetry requirement.

## Appendix

### Search queries / commands used

- `printf 'error: target is out-of-date and needs to be rebuilt\n' | grep -E '^/.*\.lean:$'`
  (from the task description, confirmed no match)
- `lake shake --add-public --keep-implied --keep-prefix Cslib` (baseline healthy run, and again
  after content-hash invalidation)
- `grep -rn "out-of-date and needs to be rebuilt" ~/.elan/toolchains/*/src/lean/lake/Lake/Build/Common.lean`
- Read `Lake/Build/Common.lean` (`buildAction`), `Lake/Build/Context.lean` (`BuildConfig`,
  `getNoBuild`, `showProgress`), `Lake/Build/Run.lean` (`Workspace.checkNoBuild`),
  `Lake/CLI/Main.lean` (`protected def shake`), `Lake/Util/MainM.lean` (`error` default exit code)
  — all from `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/lake/`
- `bash scripts/check-shake-residue.sh --list` run directly against the reproduced stale state
- Read `scripts/check-shake-residue.sh`, `scripts/check-axiom-census.sh`,
  `scripts/check-boneyard-quarantine.sh`, `scripts/pre-pr-check.sh`,
  `.claude/scripts/check-runtime-file-tracking.sh` in full

### Environment

- `Lake version 5.0.0-src+62eed1d (Lean version 4.33.0-rc1)`
- Reproduction performed against the actual `/home/benjamin/Projects/cslib` working tree, with a
  fully-built `.lake/build` prior to each experiment (confirmed via a healthy baseline `lake
  shake` run before invalidating any content).
