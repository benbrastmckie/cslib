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

BASELINE="scripts/shake-residue-baseline.txt"
SHAKE_ARGS=(--add-public --keep-implied --keep-prefix Cslib)

# Runs `lake shake` exactly once, setting two globals: $shake_raw (its combined stdout+stderr)
# and $shake_exit (its exit code). Must be called directly (NOT inside a `$(...)` command
# substitution), or both assignments happen in a subshell and are lost to the caller.
shake_exit=0
shake_raw=""
run_shake() {
  shake_raw="$(lake shake "${SHAKE_ARGS[@]}" 2>&1)"
  shake_exit=$?
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
  "") : ;;
  *)
    echo "Usage: $0 [--update|--list]" >&2
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
