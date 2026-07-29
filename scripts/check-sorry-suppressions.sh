#!/usr/bin/env bash
# check-sorry-suppressions.sh — ratchet gate on `sorry` debt: suppression markers and true
# code-position sorries.
#
# THE PROBLEM THIS EXISTS TO STOP
#
# A naive `grep -c sorry` over `Cslib/` massively overcounts (currently 180 on this tree):
# most hits are prose mentions in doc comments, and the option name
# `set_option warn.sorry false` itself matches `\bsorry\b` (`.` is a non-word character, so
# there is a word boundary right before "sorry" inside "warn.sorry"). Neither of those two
# effects has anything to do with actual proof debt, so a naive count is useless as a ratchet:
# it can't distinguish "someone added a real sorry" from "someone edited a docstring."
#
# This script counts two things that DO track real debt, per file:
#   - marker count: occurrences of the literal option `set_option warn.sorry false` (both the
#     file-scoped and the declaration-scoped `... false in` form — see "WHY BOTH FORMS COUNT"
#     below);
#   - sorry count: true code-position `sorry` occurrences, using the discrimination rule below.
# Both are ratchet ceilings: a file may not exceed its baseline in either count. A file that
# drops below its baseline in either count is reported as an improvement, never a failure.
#
# THE DISCRIMINATION RULE (tested against this tree; do not weaken)
#
# To count real code-position sorries, in this exact order:
#   1. strip block comments (`/- ... -/`, which also captures doc comments `/-- ... -/` since
#      they start with `/-`) non-greedily across the WHOLE file
#      (`perl -0777 -pe 's/\/-.*?-\///gs'`), so a multi-line doc comment mentioning the word
#      "sorry" in prose is removed in full;
#   2. strip line comments (`--` to end of line) on each surviving line;
#   3. drop any surviving line that still contains the substring `warn.sorry` — this step is
#      LOAD-BEARING, not decorative: `\bsorry\b` matches inside `warn.sorry` itself (word
#      boundary before "sorry" since `.` is non-word), so without this exclusion every
#      declaration-scoped suppression marker line would also count itself as a code-position
#      sorry;
#   4. count `\bsorry\b` word-boundary occurrences on what remains.
# `sorryAx` (the kernel axiom name) is excluded automatically by the `\b` boundary — there is
# no word boundary between "y" and "A" in "sorryAx" (both are word characters), so no special
# case is needed for it.
#
# Known, currently-vacuous edge case: a single line carrying BOTH a `warn.sorry` option and a
# separate code-position `sorry` would be undercounted by step 3 (the whole line is dropped).
# Verified: no line in this tree does this. Recorded here so a future reader knows the limit
# if it ever changes.
#
# WHY BOTH SUPPRESSION-MARKER FORMS COUNT (unlike check-lint-suppressions.sh)
#
# `check-lint-suppressions.sh` ratchets ONLY the blanket (file-scoped, no trailing `in`) form
# of `set_option linter.X false`, because declaration-scoped suppressions decay naturally there
# (they die with the declaration). Do NOT copy that script's `$`-anchored regex here: on this
# tree, all 18 `set_option warn.sorry false` markers are the declaration-scoped `... false in`
# form (verified: zero are the blanket form), so an anchored blanket-only regex would count 0
# markers here, silently disabling this half of the gate. This gate deliberately counts BOTH
# forms as a plain substring match, because its ratchet is on total suppression VOLUME (how
# much of this codebase's sorry debt is hidden from `--wfail`), not on suppression SCOPE
# discipline — scope discipline is a different, narrower question this script does not answer.
#
# WHAT THIS GATE DOES NOT NEED
#
# Unlike `scripts/check-axiom-census.sh`, this is a pure text sweep over `Cslib/*.lean` source
# files — it needs no built `.olean`s and no `lake build`. That is why it is placed before the
# build step in `.github/workflows/lean_action_ci.yml` (see the comment there). It is wired as
# step 8 of `scripts/pre-pr-check.sh` (whole-tree, unscoped), and separately, as of the
# `--scope` flag documented below, ALSO invoked at step 1 of that same script (scoped to four
# hand-picked trees, for early fast-fail feedback against the identical baseline). Step 1
# contributes no unique failure coverage over step 8 — see the rationale comment above step 8 in
# `pre-pr-check.sh`.
#
# EXIT-CODE CONTRACT (READ BEFORE CHANGING)
#
#   0  clean or improved (ratchet-only-decreases: an improvement is reported, never failed), OR
#      an empty --changed set ("nothing to check" -- see below; deliberately NOT exit 2, unlike
#      the --scope zero-file case)
#   1  regression: some file exceeds its baseline marker or sorry ceiling
#   2  usage or environment error — MUST be used whenever the underlying tooling fails to RUN,
#      never silently reported as "0 suppressions, clean". Conditions, all fatal:
#        - `perl` is not on `PATH` (needed for the block-comment strip);
#        - the default or `--scope`-restricted sweep yields zero files (a scan root, or a
#          mistyped `--scope` path, that resolves to nothing must never read as "clean" — it
#          reads as broken). This is DELIBERATELY DISTINCT from an empty `--changed` set (see
#          above): a mistyped path is a real usage error, while "this branch changed nothing in
#          scope" is a genuinely clean result. The two must never collapse into each other;
#        - the block-comment-stripping pass itself exits nonzero on any file;
#        - `--changed`'s merge-base resolution fails (unresolvable base ref, absent remote, or a
#          detached HEAD with no common ancestor) — an environment error, never a silent empty
#          changed-set;
#        - `--update` combined with `--scope` or `--changed` (see below).
#
# WHY --update REFUSES --scope AND --changed
#
# `--update` always rewrites the WHOLE-TREE baseline from a fresh whole-tree sweep, unscoped, by
# construction. If it instead accepted `--scope`/`--changed`, a partial sweep would overwrite
# the same whole-tree baseline file, silently lowering every out-of-scope file's ceiling to 0 —
# a silent ratchet break that reads as "clean" the next time those files are swept (0 exceeds
# nothing). So combining `--update` with either flag is refused outright with `exit 2`, before
# any write to `$BASELINE`. To re-baseline after a scoped/changed run confirms an improvement,
# always run the bare, unscoped `bash scripts/check-sorry-suppressions.sh --update`.
#
# Usage:
#   check-sorry-suppressions.sh                       verify against the baseline (exit 1 on regression)
#   check-sorry-suppressions.sh --update              rewrite the whole-tree baseline (refuses --scope/--changed)
#   check-sorry-suppressions.sh --list                print current per-file counts, highest sorry-count first
#   check-sorry-suppressions.sh --scope PATH...       verify, restricted to the given PATH(s) (fatal if none match)
#   check-sorry-suppressions.sh --changed [--base REF]  verify, restricted to changed .lean files
#                                                        (opt-in; default base ref origin/main; empty result is exit 0)

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

SCAN_ROOT="Cslib"
BASELINE="scripts/sorry-suppression-baseline.txt"
MARKER_STR="set_option warn.sorry false"

# Scope/changed-set state, populated by the argument loop below. When SCOPE_PATHS is empty and
# CHANGED=0, every sweep below is exactly the pre-existing whole-tree behaviour: SCAN_ROOT only,
# with no filtering. `--changed` is reserved for Phase 2 wiring; see the argument loop below.
MODE=""
SCOPE_PATHS=()
CHANGED=0
BASE_REF="origin/main"

if ! command -v perl >/dev/null 2>&1; then
  echo "ERROR: perl is not on PATH -- required for the block-comment-stripping pass. This is" >&2
  echo "an environment error, not a clean/empty result." >&2
  exit 2
fi

# Block-comment-stripped content of $1, or empty + nonzero return on a perl failure (caller
# must check the return code -- a perl failure must never be silently treated as "no content").
strip_block_comments() {
  perl -0777 -pe 's/\/-.*?-\///gs' "$1"
}

# Count of literal marker occurrences in $1. grep -c always prints a count (0 included) but
# exits 1 on zero matches; assign-then-default, never `|| echo 0` (which would print an extra
# stray "0" to the script's own stdout instead of just setting the variable).
count_markers() {
  local n
  n=$(grep -cF -- "$MARKER_STR" "$1" 2>/dev/null) || n=0
  printf '%s' "$n"
}

# True code-position sorry count in $1, per the discrimination rule above. Returns nonzero
# (via the caller checking $?) if the block-comment strip itself failed.
count_sorries() {
  local stripped rc
  stripped=$(strip_block_comments "$1")
  rc=$?
  if [ "$rc" -ne 0 ]; then
    return 2
  fi
  local n
  n=$(printf '%s\n' "$stripped" | sed -e 's/--.*//' | grep -v 'warn\.sorry' \
    | grep -oE '\bsorry\b' | wc -l) || n=0
  printf '%s' "$n"
  return 0
}

# True iff $1 lies inside one of SCOPE_PATHS (or SCOPE_PATHS is empty, in which case everything
# is in scope). Prefix-matches on a path-component boundary so "Cslib/Logics/Modal" does not
# spuriously match "Cslib/Logics/ModalX".
path_in_scope() {
  local p="$1" sp
  [ ${#SCOPE_PATHS[@]} -eq 0 ] && return 0
  for sp in "${SCOPE_PATHS[@]}"; do
    case "$p" in
      "$sp"|"$sp"/*) return 0 ;;
    esac
  done
  return 1
}

# Resolves the merge-base commit for --changed into the global $MERGE_BASE, or exits 2 on
# failure. MUST be called directly from the main script body, never from inside a pipe or
# command-substitution subshell -- bash forks a subshell for the non-last stage of a pipeline,
# and an `exit` there would only terminate that subshell, silently leaving the parent script
# running with an empty/bogus result instead of actually failing. This is why merge-base
# resolution is split out from the pipe-safe listing helpers below.
resolve_merge_base() {
  if ! MERGE_BASE=$(git merge-base HEAD "$BASE_REF" 2>/dev/null); then
    echo "ERROR: cannot resolve a merge-base between HEAD and '$BASE_REF' for --changed --" >&2
    echo "unresolvable base ref, absent remote, or a detached HEAD with no common ancestor." >&2
    echo "This is an environment error, never a silent empty/clean changed-file set." >&2
    exit 2
  fi
}

# Pipe-safe: raw union of changed paths (working tree + index + committed-since-merge-base),
# each category using --diff-filter=d (lowercase) so a deleted path is never emitted for
# downstream stat'ing. No filtering by extension, scan root, or scope yet -- see
# resolve_changed_files() below for that.
changed_files_raw() {
  {
    git diff --name-only --diff-filter=d "$MERGE_BASE" HEAD
    git diff --name-only --diff-filter=d HEAD
    git diff --name-only --diff-filter=d --cached
    git ls-files --others --exclude-standard
  } 2>/dev/null | sort -u
}

# Pipe-safe: the --changed sweep list, restricted to "*.lean" under $SCAN_ROOT, intersected with
# SCOPE_PATHS when --scope is also given, and defensively dropping any path that no longer
# exists on disk (e.g. renamed/removed since the diff was taken).
resolve_changed_files() {
  changed_files_raw | while IFS= read -r p; do
    case "$p" in
      "$SCAN_ROOT"/*.lean) : ;;
      *) continue ;;
    esac
    [ -f "$p" ] || continue
    path_in_scope "$p" || continue
    printf '%s\n' "$p"
  done | sort -u
}

# Emits the sorted list of `.lean` files to sweep.
#   - CHANGED=1: the --changed set (git-diff-derived, filtered/scoped -- see
#     resolve_changed_files above). Requires $MERGE_BASE already resolved via
#     resolve_merge_base(), called from the main script body before this is ever reached.
#   - CHANGED=0, SCOPE_PATHS empty: exactly the pre-existing whole-tree sweep
#     (find "$SCAN_ROOT" -name '*.lean' -type f | sort) -- unchanged behaviour for the no-arg,
#     --list, and --update paths.
#   - CHANGED=0, SCOPE_PATHS non-empty: restricted to those paths only; a path that does not
#     exist contributes no files (silently, from find's perspective) rather than erroring here --
#     the caller is responsible for treating a resulting empty sweep as fatal where that is the
#     desired semantics (see the zero-file checks below, which is exactly where a mistyped
#     --scope path is caught).
sweep_files() {
  if [ "$CHANGED" -eq 1 ]; then
    resolve_changed_files
  elif [ ${#SCOPE_PATHS[@]} -eq 0 ]; then
    find "$SCAN_ROOT" -name '*.lean' -type f | sort
  else
    find "${SCOPE_PATHS[@]}" -name '*.lean' -type f 2>/dev/null | sort -u
  fi
}

# Emits "<markers> <sorries> <path>" for every file with markers>0 or sorries>0, path-sorted.
# Sets $current_counts_failed=1 (global) if any file's block-comment strip failed.
current_counts_failed=0
current_counts() {
  local f markers sorries
  while IFS= read -r f; do
    markers=$(count_markers "$f")
    sorries=$(count_sorries "$f")
    if [ $? -ne 0 ]; then
      echo "ERROR: block-comment strip failed on $f" >&2
      current_counts_failed=1
      continue
    fi
    if [ "$markers" -gt 0 ] || [ "$sorries" -gt 0 ]; then
      printf '%s %s %s\n' "$markers" "$sorries" "$f"
    fi
  done < <(sweep_files)
}

# D1 ledger: for files with sorries, extract the distinct trailing blocker comment (`-- ...`)
# found on each genuine code-position-sorry line. Purely informational -- emitted as `#`
# comment lines under --update, never read back by the comparison logic. Uses a line-count-
# preserving block-comment strip (block comment content is replaced by an equal count of
# newlines) so extracted lines still correlate 1:1 with the source file's own line numbers.
ledger_for_file() {
  local f="$1"
  perl -0777 -pe 's/(\/-.*?-\/)/"\n" x (($1) =~ tr#\n##)/gse' "$f" 2>/dev/null | awk -v path="$f" '
    {
      line = $0
      cpos = index(line, "--")
      if (cpos > 0) { code = substr(line, 1, cpos - 1); comment = substr(line, cpos) }
      else { code = line; comment = "" }
      if (code ~ /warn\.sorry/) next
      if (code ~ /\<sorry\>/ && comment != "") {
        print path ": " comment
      }
    }
  ' | sort -u
}

# Argument loop. Recognizes --list, --update, --scope PATH... (consuming paths until the next
# --prefixed token or end of args), --changed, and --base REF. Any other token is a usage error.
USAGE="Usage: $0 [--update|--list] [--scope PATH...] [--changed] [--base REF]"
while [ $# -gt 0 ]; do
  case "$1" in
    --list)
      if [ -n "$MODE" ] && [ "$MODE" != "list" ]; then
        echo "$USAGE" >&2
        exit 2
      fi
      MODE="list"
      shift
      ;;
    --update)
      if [ -n "$MODE" ] && [ "$MODE" != "update" ]; then
        echo "$USAGE" >&2
        exit 2
      fi
      MODE="update"
      shift
      ;;
    --scope)
      shift
      if [ $# -eq 0 ] || [[ "$1" == --* ]]; then
        echo "Usage: --scope requires at least one PATH argument" >&2
        exit 2
      fi
      while [ $# -gt 0 ] && [[ "$1" != --* ]]; do
        SCOPE_PATHS+=("$1")
        shift
      done
      ;;
    --changed)
      CHANGED=1
      shift
      ;;
    --base)
      shift
      if [ $# -eq 0 ] || [[ "$1" == --* ]]; then
        echo "Usage: --base requires a REF argument" >&2
        exit 2
      fi
      BASE_REF="$1"
      shift
      ;;
    *)
      echo "$USAGE" >&2
      exit 2
      ;;
  esac
done

# --update refuses --scope and --changed: a partial sweep would rewrite the whole-tree baseline
# and silently zero out-of-scope rows -- a silent ratchet break. This runs BEFORE any write to
# $BASELINE.
if [ "$MODE" = "update" ] && { [ ${#SCOPE_PATHS[@]} -gt 0 ] || [ "$CHANGED" -eq 1 ]; }; then
  echo "ERROR: --update refuses --scope/--changed -- a partial sweep would rewrite the" >&2
  echo "whole-tree baseline and silently zero out-of-scope rows (a silent ratchet break)." >&2
  echo "Run 'bash $0 --update' unscoped instead." >&2
  exit 2
fi

# Resolve the --changed merge-base up front, from the main script body (not inside a pipe), so
# an unresolvable base ref/absent remote fails the whole script via exit 2 -- see
# resolve_merge_base()'s own comment for why this call site matters.
if [ "$CHANGED" -eq 1 ]; then
  resolve_merge_base
fi

case "$MODE" in
  list)
    current_counts | sort -k2,2rn
    if [ "$current_counts_failed" -ne 0 ]; then
      exit 2
    fi
    exit 0
    ;;
  update)
    live=$(current_counts)
    if [ "$current_counts_failed" -ne 0 ]; then
      echo "ERROR: refusing to update baseline -- one or more files failed the block-comment" >&2
      echo "strip pass (see errors above)." >&2
      exit 2
    fi
    nfiles=$(sweep_files | wc -l)
    if [ "$nfiles" -eq 0 ]; then
      echo "ERROR: '$SCAN_ROOT' contains no .lean files -- refusing to update baseline from an" >&2
      echo "empty sweep (this would silently record a clean/empty result for a broken scan root)." >&2
      exit 2
    fi
    {
      echo "# Per-file sorry debt ceiling: <marker count> <sorry count> <path>. Generated by"
      echo "# scripts/check-sorry-suppressions.sh --update -- do not hand-edit."
      echo "#"
      echo "# marker count  = occurrences of the literal option \"set_option warn.sorry false\""
      echo "#                 (both the file-scoped and declaration-scoped '... false in' form)."
      echo "# sorry count   = true code-position \\bsorry\\b occurrences after stripping block"
      echo "#                 comments, line comments, and warn.sorry lines -- see the"
      echo "#                 discrimination rule in this script's own header comment."
      echo "#"
      echo "# Both columns are CEILINGS and may only decrease. A file exceeding either column,"
      echo "# or introducing either where it previously had none, is a regression. Reduce by"
      echo "# discharging the sorry or removing the marker, then re-run --update and commit."
      echo "#"
      echo "# Format: <markers> <sorries> <path>"
      printf '%s\n' "$live"
      echo "#"
      echo "# Debt ledger (D1 durable anchor: declaration file + in-source blocking comment)."
      echo "# Informational only -- these lines are skipped by the comparison parser."
      echo "# Format: #   <path>: <blocker comment text>"
      while IFS= read -r f; do
        ledger_for_file "$f" | while IFS= read -r entry; do
          [ -n "$entry" ] && echo "#   $entry"
        done
      done < <(printf '%s\n' "$live" | awk '{print $3}')
    } > "$BASELINE"
    marker_total=$(printf '%s\n' "$live" | awk '{s+=$1} END {print s+0}')
    sorry_total=$(printf '%s\n' "$live" | awk '{s+=$2} END {print s+0}')
    file_count=$(printf '%s\n' "$live" | grep -c . || true)
    echo "Baseline updated: $marker_total marker(s), $sorry_total sorrie(s), across $file_count file(s)."
    exit 0
    ;;
esac
# MODE="" (verify) falls through past the case with neither branch matched.

if [ ! -f "$BASELINE" ]; then
  echo "FAIL: baseline $BASELINE is missing. Generate it with:" >&2
  echo "  bash $0 --update" >&2
  exit 2
fi

nfiles=$(sweep_files | wc -l)
if [ "$nfiles" -eq 0 ]; then
  if [ "$CHANGED" -eq 1 ]; then
    # Distinct from the --scope zero-file case below: an empty --changed set genuinely means
    # "this branch touches nothing in scope" and is a clean, expected outcome, not an error.
    # This must stay a separate branch -- collapsing it with the --scope case would make a
    # mistyped --scope path read as "nothing to check" instead of the fatal error it is.
    echo "OK: no changed .lean files in scope; nothing to check."
    exit 0
  fi
  echo "ERROR: the sweep (${SCOPE_PATHS[*]:-$SCAN_ROOT}) contains no .lean files. Environment" >&2
  echo "likely broken (wrong working directory, scan root renamed, or a mistyped --scope path)" >&2
  echo "-- this is NOT reported as a clean/empty result." >&2
  exit 2
fi

# Load baseline into associative arrays (marker ceiling, sorry ceiling), keyed by path.
declare -A base_markers
declare -A base_sorries
while read -r m s path; do
  case "$m" in ''|\#*) continue ;; esac
  base_markers["$path"]="$m"
  base_sorries["$path"]="$s"
done < "$BASELINE"

live=$(current_counts)
if [ "$current_counts_failed" -ne 0 ]; then
  echo "ERROR: block-comment strip failed on one or more files (see above). Environment likely" >&2
  echo "broken -- this is NOT reported as a clean/empty result." >&2
  exit 2
fi

regressions=0
improvements=0
cur_marker_total=0
cur_sorry_total=0

while read -r m s path; do
  [ -z "${path:-}" ] && continue
  cur_marker_total=$((cur_marker_total + m))
  cur_sorry_total=$((cur_sorry_total + s))
  bm="${base_markers[$path]:-0}"
  bs="${base_sorries[$path]:-0}"
  file_regressed=0
  if [ "$m" -gt "$bm" ]; then
    echo "FAIL  $path"
    echo "      $m marker(s), baseline allows $bm."
    file_regressed=1
  fi
  if [ "$s" -gt "$bs" ]; then
    echo "FAIL  $path"
    echo "      $s sorrie(s), baseline allows $bs."
    file_regressed=1
  fi
  if [ "$file_regressed" -eq 1 ]; then
    regressions=$((regressions + 1))
  elif [ "$m" -lt "$bm" ] || [ "$s" -lt "$bs" ]; then
    improvements=$((improvements + 1))
  fi
done <<< "$live"

base_marker_total=$(grep -vE '^[[:space:]]*#' "$BASELINE" | awk 'NF>=3 {s+=$1} END {print s+0}')
base_sorry_total=$(grep -vE '^[[:space:]]*#' "$BASELINE" | awk 'NF>=3 {s+=$2} END {print s+0}')

if [ ${#SCOPE_PATHS[@]} -gt 0 ]; then
  # Scoped run: restrict the *displayed* ceiling to the swept paths only, so e.g. a 24-vs-28
  # comparison never misreads as a spurious improvement when the real story is "the other 4
  # files simply weren't swept". Display-only: base_markers/base_sorries and the per-file
  # comparison loop above stay whole-baseline-keyed and untouched by this.
  scoped_marker_total=0
  scoped_sorry_total=0
  while IFS= read -r p; do
    [ -z "$p" ] && continue
    scoped_marker_total=$((scoped_marker_total + ${base_markers[$p]:-0}))
    scoped_sorry_total=$((scoped_sorry_total + ${base_sorries[$p]:-0}))
  done < <(sweep_files)
  echo "scoped run (paths: ${SCOPE_PATHS[*]})"
  echo "markers: $cur_marker_total (scoped baseline ceiling $scoped_marker_total; whole-tree ceiling $base_marker_total); sorries: $cur_sorry_total (scoped baseline ceiling $scoped_sorry_total; whole-tree ceiling $base_sorry_total)"
else
  echo "markers: $cur_marker_total (baseline ceiling $base_marker_total); sorries: $cur_sorry_total (baseline ceiling $base_sorry_total)"
fi

if [ "$improvements" -gt 0 ]; then
  cat <<EOF

ACTION REQUIRED (not a failure -- this check still exits 0):
  $improvements file(s) now have fewer markers and/or sorries than the baseline ceiling.
  Re-tighten the ratchet to lock in the gain:
    bash $0 --update
  Then commit the updated scripts/sorry-suppression-baseline.txt.
EOF
  if [ ${#SCOPE_PATHS[@]} -gt 0 ]; then
    cat <<EOF
  NOTE: this was a scoped run that only swept part of the tree. Do NOT try to re-baseline with
  a scoped --update -- --update always refuses --scope (a partial sweep would rewrite the
  whole-tree baseline and silently zero out-of-scope rows). Run the bare command above,
  unscoped, from the repo root.
EOF
  fi
fi

if [ "$regressions" -gt 0 ]; then
  cat >&2 <<EOF

FAILED: $regressions file(s) exceed their marker or sorry ceiling.

This means this fork's own recent changes introduced new sorry debt (a bare code-position
sorry, or a new set_option warn.sorry false suppression) beyond what the baseline already
tracks. Fix by discharging the sorry or removing the marker, then re-run this script to
confirm it is clean.

If a new entry is genuinely justified (a deliberate, tracked TODO with an in-source blocking
comment), add it deliberately via 'bash $0 --update' in the same commit and say why in the
commit message -- never as a silent side effect.
EOF
  exit 1
fi

echo "OK: sorry/suppression counts match the baseline (or improved)."
exit 0
