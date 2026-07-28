#!/usr/bin/env bash
# check-axiom-census.sh — exact-set ratchet gate on silent `sorryAx` taint over the public
# `Cslib` API.
#
# THE PROBLEM THIS EXISTS TO STOP
#
# `lake build --wfail --iofail` only promotes a warning to a build failure when a declaration's
# OWN elaborated term directly contains a `sorry` token. It says nothing about a declaration
# that consumes an already-sorry'd lemma as an opaque dependency: such a declaration's kernel
# axiom set still contains `sorryAx` (visible via `#print axioms`), but Lean never emits a
# "declaration uses 'sorry'" warning for it directly, so `--wfail` never sees it. Two genuine,
# verified examples of this "silent taint" on this tree: `Cslib.Logic.PL.minimalTableau_decides`
# and `Cslib.Logic.PL.intuitionisticTableau_decides` — both contain zero `sorry` tokens in their
# own bodies, both build cleanly under `--wfail` with no warning attributed to them, and both
# still carry `sorryAx` in their axiom set because each calls its sorry'd `..._complete` lemma
# as a dependency. (The `..._complete` pair itself is NOT an example of this: those two DO
# contain direct `sorry` tokens and DO warn under `--wfail` — they are the ordinary, already-
# visible case. Do not cite them as silent-taint witnesses.)
#
# This script closes that gap: `scripts/AxiomCensus.lean` (invoked below) walks the public
# `Cslib` API once and reports every `sorryAx`-tainted declaration, direct or transitive. This
# script ratchets that set against a frozen baseline so a NEW silently-tainted declaration
# fails the check, while the pre-existing 43-declaration baseline (all attributable to the same
# 9 files' genuine sorries) does not.
#
# WHY THE BASELINE IS AN EXACT SET, NOT A COUNT
#
# A declaration either is or isn't `sorryAx`-tainted — there is no meaningful "how many times"
# the way `check-lint-suppressions.sh` counts blanket-suppression occurrences. This mirrors
# `check-shake-residue.sh`'s exact-set design (a file either is or isn't flagged), keyed here on
# fully-qualified declaration name instead of file path.
#
# THE `<file>` AND `<reason>` COLUMNS ARE LEDGER METADATA, NOT PART OF THE COMPARISON
#
# The baseline's second and third TSV columns (owning file, durable-anchor reason) are a debt
# ledger (D1: declaration name + owning file + in-source blocking reason, never a task number).
# The comparison below reads ONLY the first column (declaration name). A declaration whose
# `reason` column changes (e.g. because an intermediate dependency in its taint chain was
# refactored) while it remains tainted must NEVER fail this check — only a name entering or
# leaving the tainted set matters.
#
# THIS SCRIPT NEEDS BUILT .olean FILES
#
# `scripts/AxiomCensus.lean` does `import Cslib`, so a completed `lake build` must precede this
# script, exactly like `check-shake-residue.sh` needs `lake shake` to see a built dependency
# graph. See `.github/workflows/lean_action_ci.yml` and `scripts/pre-pr-check.sh` for how this
# ordering constraint is honoured at each call site.
#
# EXIT-CODE CONTRACT (READ BEFORE CHANGING)
#
#   0  clean or improved (ratchet-only-decreases: an improvement is reported, never failed)
#   1  regression: the live tainted set contains a name absent from the baseline
#   2  usage or environment error — MUST be used whenever the underlying census fails to
#      produce a trustworthy result, never silently reported as "0 tainted". Three such
#      conditions, all fatal (the direct analogue of check-shake-residue.sh's "shake exit 1 but
#      zero flagged-file lines parseable -> exit 2, never a clean empty set"):
#        - `lake env lean --run scripts/AxiomCensus.lean` exits nonzero;
#        - it exits 0 but no `# total=<N> tainted=<M>` summary line is parseable from its
#          output (the census script's own output format changed, or it crashed silently);
#        - the summary line parses but reports `total=0` (an empty/broken environment must
#          never read as "zero taint" — a real census of `Cslib` always has thousands of
#          public declarations).
#
# Usage:
#   check-axiom-census.sh            verify against the baseline (exit 1 on regression)
#   check-axiom-census.sh --update   rewrite the baseline from the current live tainted set
#   check-axiom-census.sh --list     print the current live tainted set (name, file, reason)

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

BASELINE="scripts/axiom-census-baseline.txt"
CENSUS_SCRIPT="scripts/AxiomCensus.lean"

# Runs the Lean census exactly once, setting two globals: $census_raw (its combined
# stdout+stderr) and $census_exit (its exit code). Must be called directly (NOT inside a
# `$(...)` command substitution), or both assignments happen in a subshell and are lost to the
# caller -- the documented trap from check-shake-residue.sh's own run_shake helper.
census_exit=0
census_raw=""
run_census() {
  census_raw="$(lake env lean --run "$CENSUS_SCRIPT" 2>&1)"
  census_exit=$?
}

# Parses the `# total=<N> tainted=<M>` summary line from $census_raw. Prints "<N> <M>" on
# success, prints nothing and returns 1 if no such line is present.
parse_summary() {
  printf '%s\n' "$census_raw" | grep -oE '^# total=[0-9]+ tainted=[0-9]+$' \
    | tail -1 | grep -oE '[0-9]+' | tr '\n' ' ' | sed -e 's/ $//'
}

# Emits the live tainted set as sorted TSV lines (name, file, reason), i.e. every non-comment,
# non-blank line of $census_raw.
parse_rows() {
  printf '%s\n' "$census_raw" | grep -vE '^[[:space:]]*(#|$)' | sort -u
}

# Runs the census and validates it against all three exit-2 conditions. On success, leaves
# $census_raw/$census_exit populated and returns 0. On any failure, prints a diagnostic to
# stderr and returns 2 (caller must `exit 2` immediately -- this function does not exit itself,
# so it can also be used by --update to decide whether to refuse writing).
run_and_validate_census() {
  run_census
  if [ "$census_exit" -ne 0 ]; then
    echo "ERROR: 'lake env lean --run $CENSUS_SCRIPT' exited $census_exit. Environment likely" >&2
    echo "broken (missing .olean files?) -- run 'lake build' first. This is NOT reported as a" >&2
    echo "clean/empty tainted set." >&2
    return 2
  fi
  local summary total tainted
  summary=$(parse_summary)
  if [ -z "$summary" ]; then
    echo "ERROR: no parseable '# total=<N> tainted=<M>' summary line in the census output." >&2
    echo "Either AxiomCensus.lean's output format changed (update parse_summary in this" >&2
    echo "script) or the run failed silently. This is NOT reported as a clean/empty tainted set." >&2
    return 2
  fi
  total=$(printf '%s' "$summary" | awk '{print $1}')
  tainted=$(printf '%s' "$summary" | awk '{print $2}')
  if [ "${total:-0}" -eq 0 ]; then
    echo "ERROR: census summary reports total=0 public declarations. A real census of Cslib" >&2
    echo "always has thousands -- this reads as a broken/empty environment, NOT as zero taint." >&2
    return 2
  fi
  return 0
}

case "${1:-}" in
  --list)
    if ! run_and_validate_census; then
      exit 2
    fi
    parse_rows
    exit 0
    ;;
  --update)
    if ! run_and_validate_census; then
      echo "ERROR: refusing to update baseline from a failed/unparseable run." >&2
      exit 2
    fi
    rows="$(parse_rows)"
    n=$(printf '%s\n' "$rows" | grep -c . || true)
    {
      echo "# Exact set of sorryAx-tainted public Cslib declarations. Generated by"
      echo "# scripts/check-axiom-census.sh --update -- do not hand-edit."
      echo "#"
      echo "# This is a frozen, exact-set baseline keyed on column 1 (declaration name) ONLY."
      echo "# Columns 2 (owning file) and 3 (reason) are D1 debt-ledger metadata -- a durable"
      echo "# anchor of declaration name + owning file + in-source blocking reason, deliberately"
      echo "# not a task number (see .claude/rules/no-task-references-in-deliverables.md). They"
      echo "# are NOT compared: a changed reason for an already-tainted declaration never fails"
      echo "# this check, only a name entering or leaving the tainted set does."
      echo "#"
      echo "# A live tainted name NOT in this list is new silent sorryAx taint this fork"
      echo "# introduced and fails the check. A baseline name no longer tainted live is an"
      echo "# improvement; re-run --update to ratchet the baseline down and commit the result."
      echo "#"
      echo "# Format: <declaration name>\\t<owning file>\\t<reason>"
      printf '%s\n' "$rows"
    } > "$BASELINE"
    echo "Baseline updated: $n tainted declaration(s)."
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

if ! run_and_validate_census; then
  exit 2
fi

live_rows="$(parse_rows)"

# Load baseline names into an associative set (column 1 only -- file/reason are ledger
# metadata and are never part of the comparison).
declare -A baseline_names
while IFS=$'\t' read -r name _file _reason; do
  case "$name" in ''|\#*) continue ;; esac
  baseline_names["$name"]=1
done < "$BASELINE"

# Load live names into an associative set for the reverse (improvement) comparison.
declare -A live_names
while IFS=$'\t' read -r name _file _reason; do
  [ -n "${name:-}" ] && live_names["$name"]=1
done <<< "$live_rows"

regressions=0
improvements=0

while IFS=$'\t' read -r name file reason; do
  [ -z "${name:-}" ] && continue
  if [ -z "${baseline_names[$name]:-}" ]; then
    echo "FAIL  $name"
    echo "      ($file) newly sorryAx-tainted (reason: $reason) -- not in the baseline."
    regressions=$((regressions + 1))
  fi
done <<< "$live_rows"

for name in "${!baseline_names[@]}"; do
  if [ -z "${live_names[$name]:-}" ]; then
    echo "IMPROVED  $name"
    improvements=$((improvements + 1))
  fi
done

live_count=$(printf '%s\n' "$live_rows" | grep -c . || true)
base_count=$(grep -vE '^[[:space:]]*#' "$BASELINE" | grep -c . || true)
echo "sorryAx-tainted declarations: $live_count (baseline: $base_count)"

if [ "$improvements" -gt 0 ]; then
  cat <<EOF

ACTION REQUIRED (not a failure -- this check still exits 0):
  $improvements declaration(s) are no longer sorryAx-tainted.
  Re-tighten the ratchet to lock in the gain:
    bash $0 --update
  Then commit the updated scripts/axiom-census-baseline.txt.
EOF
fi

if [ "$regressions" -gt 0 ]; then
  cat >&2 <<EOF

FAILED: $regressions declaration(s) newly sorryAx-tainted that are not in the baseline.

This means a declaration outside the existing debt baseline now transitively depends on a
sorry (directly or through another declaration's axiom set), and CI's own --wfail build cannot
see this because the declaration's own body has no literal sorry token (see this script's
header for why). Fix by discharging the underlying sorry, or by tracing the taint chain
('grep -rn <name> Cslib/' plus '#print axioms <name>' in the editor) to find and fix the real
sorry site.

If a new baseline entry is genuinely justified (a deliberate, tracked TODO), add it
deliberately via 'bash $0 --update' in the same commit and say why in the commit message --
never as a silent side effect.
EOF
  exit 1
fi

echo "OK: sorryAx-tainted set matches the baseline exactly."
exit 0
