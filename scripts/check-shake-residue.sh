#!/usr/bin/env bash
# check-shake-residue.sh — ratchet gate on `lake shake` import-minimization debt.
#
# THE PROBLEM THIS EXISTS TO STOP
#
# `lake shake --add-public --keep-implied --keep-prefix Cslib` exits 1 whenever it has import
# suggestions (files with unused or missing imports). As of the 2026-07-28 audit against
# upstream SHA f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1, the CI step that ran this check was
# disabled (see the rationale block above the commented-out step in
# .github/workflows/lean_action_ci.yml) because the entire flagged residue at that time was
# byte-identical to upstream -- upstream's own unresolved import debt, not this fork's, and
# upstream's `lean_action_ci.yml` itself already has this same step commented out (upstream
# commit 74600063621f66f0dbfbac31963cd1219e0e05ed, "ci: disable shake again (#397)").
#
# Disabling the CI step, alone, would silently drop all enforcement -- this fork could introduce
# fresh import debt of its own and nothing would catch it. This script is the replacement local
# guard: it does NOT re-litigate the upstream residue (that's frozen in the baseline below), it
# only fails when the LIVE flagged set contains a file that is not already in the baseline --
# i.e. when this fork's own edits introduce new shake-flaggable import debt.
#
# WHY NOT THE PER-FILE `-- shake: keep` / `keep-all` ANNOTATION MECHANISM
#
# That mechanism exists and is used elsewhere in this repo, but is unusable for the frozen
# residue: applying it requires editing the flagged (pristine, upstream-identical) file, which
# is off-limits, and `keep-all` only suppresses removal findings -- most of the residue needs an
# addition, which `keep-all` cannot silence at all.
#
# THE RULE
#
# `shake-residue-baseline.txt` is an exact set of repo-relative paths, not a per-file ceiling
# (unlike scripts/check-lint-suppressions.sh's counts): a file is either flagged debt we already
# know about, or it isn't. The check fails when the live flagged set contains a path absent from
# the baseline. A path present in the baseline but no longer flagged live is reported as an
# improvement and does not fail -- re-baseline with --update to lock in the gain, mirroring
# check-lint-suppressions.sh's ratchet-only-decreases philosophy.
#
# THIS SCRIPT NEEDS BUILT .olean FILES
#
# `lake shake` inspects the build graph, so a completed `lake build` must precede this script.
# That is why this guard is NOT wired into the Lean-free lint-hygiene.yml CI workflow, and why
# scripts/pre-pr-check.sh runs this step after its own build steps. It is also deliberately not
# added as a fresh CI step in .github/workflows/lean_action_ci.yml: a new step in a shared,
# synced workflow file adds a conflict hunk to every future sync (see lint-hygiene.yml's own
# header for the same rule) -- wiring it into CI is a deferred option, not done this round.
#
# EXIT-CODE CONTRACT (READ BEFORE CHANGING)
#
# `lake shake` exits 1 by design whenever it has suggestions -- that is an expected, non-error
# outcome here, so this script does NOT use `set -e` (a naive `set -e` would abort on shake's
# normal "I have suggestions" exit before the comparison ever runs). Instead:
#   - shake exit 0, nothing flagged            -> live set is empty, proceed to comparison
#   - shake exit 1, suggestions flagged        -> parse flagged files, proceed to comparison
#   - any other shake exit code                -> environment error, exit 2 immediately
#   - shake exit 1 but zero flagged-file lines parseable from its output -> environment error,
#     exit 2 immediately (never silently treat an unparseable failed run as an empty clean set)
#
# Usage:
#   check-shake-residue.sh            verify against the baseline (exit 1 on regression)
#   check-shake-residue.sh --update   rewrite the baseline from the current live flagged set
#   check-shake-residue.sh --list     print the current live flagged set, one path per line
#
# Exit: 0 clean or improved, 1 regression (new import debt), 2 usage/environment error.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

# SHAKE_SELF_TEST_BASELINE, when non-empty, overrides BASELINE. Consulted only by --self-test's
# own subprocess re-invocations (see self_test_main below), so its fixture runs never write to
# the real scripts/shake-residue-baseline.txt ratchet file. Never set on any normal invocation.
BASELINE="${SHAKE_SELF_TEST_BASELINE:-scripts/shake-residue-baseline.txt}"
SHAKE_ARGS=(--add-public --keep-implied --keep-prefix Cslib)

# Runs `lake shake` exactly once, setting two globals: $shake_raw (its combined stdout+stderr)
# and $shake_exit (its exit code). Must be called directly (NOT inside a `$(...)` command
# substitution), or both assignments happen in a subshell and are lost to the caller.
#
# SHAKE_SELF_TEST_FIXTURE, when non-empty, short-circuits the real `lake shake` invocation and
# instead populates $shake_raw/$shake_exit from a literal captured fixture (see
# load_self_test_fixture below) -- consulted ONLY when non-empty, so this is never reachable on
# any normal invocation path. It exists solely so --self-test's per-mode subprocess assertions
# (self_test_main) can exercise --list/--update/bare end-to-end without a `lake` invocation or a
# built .olean tree.
shake_exit=0
shake_raw=""
run_shake() {
  if [ -n "${SHAKE_SELF_TEST_FIXTURE:-}" ]; then
    load_self_test_fixture "$SHAKE_SELF_TEST_FIXTURE"
    return
  fi
  shake_raw="$(lake shake "${SHAKE_ARGS[@]}" 2>&1)"
  shake_exit=$?
}

# Populates $shake_raw/$shake_exit from one of four literal fixtures, by name, with no `lake`
# invocation. Used both by run_shake's SHAKE_SELF_TEST_FIXTURE short-circuit above (subprocess
# end-to-end assertions) and directly by self_test_main's in-process assertions below.
load_self_test_fixture() {
  case "$1" in
    flagged)
      # A well-formed suggestions run: shake_exit=1, several genuine flagged-file header lines
      # plus their add/remove delta lines, interleaved with harmless replay/warning noise that
      # parse_flagged_set must NOT mistake for a flagged-file header.
      shake_exit=1
      shake_raw="$(cat <<EOF
⚠ [12/50] Replayed Cslib.Foo
⚠ [13/50] Replayed Cslib.Bar
${REPO_ROOT}/Cslib/Foo.lean:
  add #[Cslib.Bar]
${REPO_ROOT}/Cslib/Baz.lean:
  remove #[Cslib.Qux]
warning: ${REPO_ROOT}/Cslib/Foo.lean:10:2: declaration uses \`sorry\`
EOF
)"
      ;;
    stale-target)
      # The literal reproduced regression this task exists to fix: shake_exit=1 (Lake's
      # pre-flight `checkNoBuild` staleness check fails before shake's own import-analysis logic
      # ever runs), zero `^/.*\.lean:$` flagged-file header lines. Modeled directly on the
      # reproduction transcript in specs/625_shake_residue_list_false_clean/reports/
      # 01_shake-residue-false-clean.md (the literal "target is out-of-date" / "out of date
      # oleans" error text, plus a repo-relative `:LINE:COL:`-style warning line that must NOT be
      # mistaken for a flagged-file header by parse_flagged_set).
      shake_exit=1
      shake_raw="$(cat <<'EOF'
✖ [3228/3325] Building Cslib.Logics.Propositional.NaturalDeduction.Normalization
error: target is out-of-date and needs to be rebuilt
Cslib/Logics/Modal/Tableau/S4/Driver.lean:893:100: warning: unused variable `h`
error: there are out of date oleans; run `lake build` or fetch them from a cache first
EOF
)"
      ;;
    clean)
      # A genuinely clean run: shake_exit=0, only harmless replay noise, no flagged lines.
      shake_exit=0
      shake_raw="$(cat <<'EOF'
⚠ [1/50] Replayed Cslib.Foo
⚠ [2/50] Replayed Cslib.Bar
EOF
)"
      ;;
    bad-exit)
      # An unexpected shake exit code outside {0,1} -- environment/crash, never a clean/empty set.
      shake_exit=2
      shake_raw="$(cat <<'EOF'
fatal: unexpected internal error
stack trace omitted
EOF
)"
      ;;
    *)
      echo "ERROR: unknown --self-test fixture '$1'." >&2
      shake_exit=2
      shake_raw=""
      ;;
  esac
}

# Emits the flagged set from $shake_raw as repo-relative paths, one per line, sorted for a
# stable diff. Call run_shake first to populate $shake_raw.
parse_flagged_set() {
  # A flagged-file line is an absolute path (starts with '/') ending in ".lean:" -- shake's own
  # per-file header line, distinct from the "add #[...]" / "remove #[...]" delta lines that
  # follow it and from the unrelated "warning: ...: declaration uses `sorry`" / "⚠ [n/m] Replayed
  # X" build-noise lines that can also appear in the same stdout+stderr stream.
  printf '%s\n' "$shake_raw" \
    | grep -E '^/.*\.lean:$' \
    | sed -e 's/:$//' -e "s|^${REPO_ROOT}/||" \
    | sort -u
}

# Validates the two fatal conditions shared by all three usage modes, given the globals
# $shake_exit and $live already populated by the caller (run_and_validate_shake below, or a
# --self-test fixture assigning them directly with no `lake` invocation at all -- this is why
# this function is pure/globals-only and deliberately kept separate from the impure run_shake).
# Returns 0 if the run is trustworthy, 2 (with a stderr diagnostic) otherwise. Never calls `exit`
# itself so callers (e.g. --update) can append their own diagnostic line before exiting.
validate_shake_result() {
  if [ "$shake_exit" -ne 0 ] && [ "$shake_exit" -ne 1 ]; then
    echo "ERROR: lake shake exited $shake_exit (expected 0 or 1). Environment likely broken" >&2
    echo "(missing .olean files?) -- run a full 'lake build' first. This is NOT reported as a" >&2
    echo "clean/empty flagged set." >&2
    return 2
  fi
  if [ "$shake_exit" -eq 1 ] && [ -z "$live" ]; then
    echo "ERROR: lake shake exited 1 (has suggestions) but no flagged-file lines were parseable" >&2
    echo "from its output. Either shake's output format changed (update the extractor in this" >&2
    echo "script) or the environment is broken. This is NOT reported as a clean/empty flagged set." >&2
    return 2
  fi
  return 0
}

# Runs `lake shake` exactly once, computes the parsed flagged set, and validates both fatal
# conditions via validate_shake_result. On success, leaves $live populated (global, not local --
# callers such as the bare verify path's downstream comparison logic depend on reading it after
# this returns) and returns 0. On failure, returns 2 -- caller must `exit 2` itself (this
# function does not exit, so `--update` can append its own "refusing to update baseline" line
# first, matching check-axiom-census.sh's run_and_validate_census()).
live=""
run_and_validate_shake() {
  run_shake
  live="$(parse_flagged_set)"
  validate_shake_result
}

# --self-test: asserts the guard in all three modes against deterministic fixtures, with no
# `lake` invocation and no built .olean tree required. Encodes the reproduced regression (the
# "stale-target" fixture) as a permanent, mechanical check that this asymmetry cannot silently
# return -- see check-boneyard-quarantine.sh for this repo's "self-test" naming convention.
# Prints one PASS/FAIL line per assertion plus a final summary. Returns 0 iff every assertion
# passed, 1 otherwise; never calls `exit` itself so the caller controls the process exit code.
self_test_main() {
  local pass=0
  local fail=0
  local rc

  # assert_eq: compares two already-computed strings and records PASS/FAIL. Kept as a nested
  # function (not a subshell pipeline) so it can mutate the enclosing pass/fail counters.
  assert_eq() {
    local desc="$1" expected="$2" actual="$3"
    if [ "$expected" = "$actual" ]; then
      echo "PASS  $desc"
      pass=$((pass + 1))
    else
      echo "FAIL  $desc"
      echo "      expected: $(printf '%q' "$expected")"
      echo "      actual:   $(printf '%q' "$actual")"
      fail=$((fail + 1))
    fi
  }

  echo "== check-shake-residue.sh --self-test =="
  echo
  echo "-- in-process assertions (validate_shake_result / parse_flagged_set, no lake, no subprocess) --"

  # Fixture 1: flagged -- a well-formed suggestions run.
  load_self_test_fixture flagged
  live="$(parse_flagged_set)"
  validate_shake_result; rc=$?
  assert_eq "flagged: validate_shake_result returns 0" "0" "$rc"
  assert_eq "flagged: parse_flagged_set returns the expected path set" \
    "$(printf '%s\n' "Cslib/Baz.lean" "Cslib/Foo.lean")" "$live"

  # Fixture 2: stale-target -- the literal reproduced regression.
  load_self_test_fixture stale-target
  live="$(parse_flagged_set)"
  validate_shake_result; rc=$?
  assert_eq "stale-target: validate_shake_result returns 2 (the regression this task fixes)" "2" "$rc"
  assert_eq "stale-target: parse_flagged_set returns empty" "" "$live"

  # Fixture 3: clean -- a genuinely clean run.
  load_self_test_fixture clean
  live="$(parse_flagged_set)"
  validate_shake_result; rc=$?
  assert_eq "clean: validate_shake_result returns 0" "0" "$rc"
  assert_eq "clean: parse_flagged_set returns empty" "" "$live"

  # Fixture 4: bad-exit -- an unexpected shake exit code.
  load_self_test_fixture bad-exit
  live="$(parse_flagged_set)"
  validate_shake_result; rc=$?
  assert_eq "bad-exit: validate_shake_result returns 2" "2" "$rc"

  echo
  echo "-- end-to-end per-mode assertions (subprocess re-invocation via SHAKE_SELF_TEST_FIXTURE, no real lake call) --"

  # --update safety: point BASELINE at a scratch temp file for every subprocess fixture run below
  # so the real scripts/shake-residue-baseline.txt is never written by this self-test. Also seed
  # it with one entry so the bare mode's "baseline file missing" pre-check does not itself mask
  # the guard assertions under test.
  local tmp_baseline real_baseline_before real_baseline_after clean_out_file clean_bytes
  tmp_baseline="$(mktemp)"
  printf '%s\n' "Cslib/Placeholder.lean" > "$tmp_baseline"
  real_baseline_before="$(cat "$BASELINE" 2>/dev/null || true)"

  # fixture 2 (stale-target) must exit 2 in all three modes -- the non-negotiable triple this
  # self-test exists to lock in; this IS the reproduced bug, encoded as a fixture.
  SHAKE_SELF_TEST_FIXTURE=stale-target SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" --list >/dev/null 2>&1; rc=$?
  assert_eq "stale-target: --list exits 2" "2" "$rc"
  SHAKE_SELF_TEST_FIXTURE=stale-target SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" --update >/dev/null 2>&1; rc=$?
  assert_eq "stale-target: --update exits 2" "2" "$rc"
  SHAKE_SELF_TEST_FIXTURE=stale-target SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" >/dev/null 2>&1; rc=$?
  assert_eq "stale-target: bare verify exits 2" "2" "$rc"

  # fixture 4 (bad-exit) must exit 2 in all three modes.
  SHAKE_SELF_TEST_FIXTURE=bad-exit SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" --list >/dev/null 2>&1; rc=$?
  assert_eq "bad-exit: --list exits 2" "2" "$rc"
  SHAKE_SELF_TEST_FIXTURE=bad-exit SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" --update >/dev/null 2>&1; rc=$?
  assert_eq "bad-exit: --update exits 2" "2" "$rc"
  SHAKE_SELF_TEST_FIXTURE=bad-exit SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" >/dev/null 2>&1; rc=$?
  assert_eq "bad-exit: bare verify exits 2" "2" "$rc"

  # fixture 3 (clean) --list must exit 0 with ZERO bytes of stdout -- no stray blank line. Uses a
  # real file (not command substitution, which strips trailing newlines and would hide a stray
  # newline) so the byte count is trustworthy.
  clean_out_file="$(mktemp)"
  SHAKE_SELF_TEST_FIXTURE=clean SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" --list >"$clean_out_file" 2>/dev/null; rc=$?
  assert_eq "clean: --list exits 0" "0" "$rc"
  clean_bytes="$(wc -c < "$clean_out_file" | tr -d '[:space:]')"
  assert_eq "clean: --list emits zero bytes of stdout" "0" "$clean_bytes"
  rm -f "$clean_out_file"

  # fixture 1 (flagged) --list must exit 0 and print exactly the expected path set -- confirms
  # normal operation is unaffected by the self-test machinery.
  SHAKE_SELF_TEST_FIXTURE=flagged SHAKE_SELF_TEST_BASELINE="$tmp_baseline" \
    bash "$0" --list >"$tmp_baseline.flagged_out" 2>/dev/null; rc=$?
  assert_eq "flagged: --list exits 0" "0" "$rc"
  assert_eq "flagged: --list prints the expected path set" \
    "$(printf '%s\n' "Cslib/Baz.lean" "Cslib/Foo.lean")" "$(cat "$tmp_baseline.flagged_out")"
  rm -f "$tmp_baseline.flagged_out"

  rm -f "$tmp_baseline"

  echo
  echo "-- baseline safety check --"
  real_baseline_after="$(cat "$BASELINE" 2>/dev/null || true)"
  assert_eq "real baseline file ($BASELINE) is byte-unchanged by this self-test" \
    "$real_baseline_before" "$real_baseline_after"

  echo
  echo "== self-test summary: $pass passed, $fail failed =="
  if [ "$fail" -eq 0 ]; then
    return 0
  fi
  return 1
}

case "${1:-}" in
  --list)
    if ! run_and_validate_shake; then
      exit 2
    fi
    # Guarded print: an unconditional printf here would emit a spurious blank line when $live is
    # empty (the genuine shake-exit-0 clean case), silently changing the "zero bytes on clean"
    # contract to "one newline on clean". Under set -uo pipefail without set -e, a false
    # [ -n ... ] test here is harmless -- the explicit `exit 0` below always runs regardless.
    [ -n "$live" ] && printf '%s\n' "$live"
    exit 0
    ;;
  --update)
    if ! run_and_validate_shake; then
      echo "ERROR: refusing to update baseline from a failed/unparseable run." >&2
      exit 2
    fi
    {
      echo "# Exact set of files flagged by \`lake shake --add-public --keep-implied --keep-prefix"
      echo "# Cslib\`. Generated by scripts/check-shake-residue.sh --update -- do not hand-edit."
      echo "#"
      echo "# This is a frozen, exact-set baseline, not a per-file ceiling. As of the 2026-07-28"
      echo "# audit against upstream SHA f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1, every entry here"
      echo "# was byte-identical to upstream -- upstream's own unresolved import debt, not this"
      echo "# fork's. A live flagged file NOT in this list is new debt this fork introduced and"
      echo "# fails the check. A baseline entry no longer flagged live is an improvement; re-run"
      echo "# --update to ratchet the baseline down and commit the result."
      echo "#"
      echo "# Format: <repo-relative path>"
      printf '%s\n' "$live"
    } > "$BASELINE"
    n=$(printf '%s\n' "$live" | grep -c . || true)
    echo "Baseline updated: $n file(s)."
    exit 0
    ;;
  --self-test)
    self_test_main
    exit $?
    ;;
  "") : ;;
  *)
    echo "Usage: $0 [--update|--list|--self-test]" >&2
    exit 2
    ;;
esac

if [ ! -f "$BASELINE" ]; then
  echo "FAIL: baseline $BASELINE is missing. Generate it with:" >&2
  echo "  bash $0 --update" >&2
  exit 2
fi

if ! run_and_validate_shake; then
  exit 2
fi

# Load baseline into an associative set.
declare -A baseline
while read -r path; do
  case "$path" in ''|\#*) continue ;; esac
  baseline["$path"]=1
done < "$BASELINE"

# Load live set into an associative set for the reverse (improvement) comparison.
declare -A live_set
while read -r path; do
  [ -n "$path" ] && live_set["$path"]=1
done <<< "$live"

regressions=0
improvements=0

while read -r path; do
  [ -z "$path" ] && continue
  if [ -z "${baseline[$path]:-}" ]; then
    echo "FAIL  $path"
    echo "      flagged by lake shake but not in the baseline -- new import debt owned by this fork."
    regressions=$((regressions + 1))
  fi
done <<< "$live"

for path in "${!baseline[@]}"; do
  if [ -z "${live_set[$path]:-}" ]; then
    echo "IMPROVED  $path"
    improvements=$((improvements + 1))
  fi
done

live_count=$(printf '%s\n' "$live" | grep -c . || true)
base_count=$(grep -vcE '^[[:space:]]*(#|$)' "$BASELINE" || true)
echo "shake-flagged files: $live_count (baseline: $base_count)"

if [ "$improvements" -gt 0 ]; then
  echo "  $improvements file(s) no longer flagged -- re-baseline with: bash $0 --update"
fi

if [ "$regressions" -gt 0 ]; then
  cat >&2 <<EOF

FAILED: $regressions file(s) newly flagged by 'lake shake' that are not in the baseline.

This means this fork's own recent changes introduced import debt lake shake can detect (missing
or unused imports). Fix by applying shake's own suggestion to the file (re-run
'lake shake --add-public --keep-implied --keep-prefix Cslib' to see the exact delta), then re-run
this script to confirm it is clean.

If a new baseline entry is genuinely unavoidable and justified, add it deliberately via
'bash $0 --update' in the same commit and say why in the commit message -- never as a silent
side effect.
EOF
  exit 1
fi

if [ "$improvements" -gt 0 ]; then
  exit 0
fi

echo "OK: shake-flagged set matches the baseline exactly."
exit 0
