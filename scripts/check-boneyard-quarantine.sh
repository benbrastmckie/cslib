#!/usr/bin/env bash
# check-boneyard-quarantine.sh — B0-style self-test asserting Boneyard/ stays outside the build.
#
# THE PROBLEM THIS EXISTS TO STOP
#
# Boneyard/'s exclusion from `lake build`, `mk_all`, `lint-style`, `shake`, and every
# sorry/axiom census is entirely IMPLICIT: it works because every one of those mechanisms is
# scoped by Lake `lean_lib` declaration, by import reachability from `Cslib.lean`, or by a
# hardcoded `Cslib` scan root (see `Boneyard/README.md`'s "Why This Is Free" section), not
# because anything actively excludes it. Nothing in this repo's existing CI or lint pipeline
# would notice if that implicit exclusion silently broke -- a `lean_lib` glob added later, a
# stray `import Boneyard.*` from live code, a `lakefile.toml` reference, or a second Boneyard
# directory that escapes an ad hoc filter. Upstream's own README records having suffered exactly
# this failure mode ("Several past counts of this repository were wrong for exactly that
# reason") and ships a `B0` self-test to catch it mechanically. This script is this repo's
# analogue, scaled to its current single-Boneyard layout.
#
# THE FIVE CHECKS
#
#   (a) Boneyard/ exists at the repository root.
#   (b) No `Boneyard` reference appears in `Cslib.lean` (the aggregator) -- nothing under
#       Boneyard/ is reachable from it.
#   (c) No `Boneyard` path appears in `lakefile.toml`.
#   (d) No `.lean` file under Boneyard/ carries a live TODO:/FIXME:-family marker -- guards the
#       repo-wide, diff-driven `.github/workflows/todo-issue.yml` scanner (see
#       `Boneyard/README.md`'s "Two Repo-Wide Scanner Constraints" section) without editing that
#       synced workflow file.
#   (e) The `B0` mirror: the exclusion pattern matches the EXPECTED NUMBER of Boneyard
#       directories, hard-coded below rather than derived at runtime -- a self-test that computes
#       its own expectation asserts nothing. If a second Boneyard is ever added deliberately,
#       update EXPECTED_BONEYARD_COUNT in the same commit that adds it.
#
# WHY THIS IS NOT WIRED INTO CI
#
# Wired into `scripts/pre-pr-check.sh` (a local, non-synced file) rather than into
# `.github/workflows/lean_action_ci.yml`, matching the established divergence-cost convention
# this repo already follows for `check-lint-suppressions.sh` and `check-shake-residue.sh`: every
# file under `.github/workflows/` is shared with the upstream `leanprover/cslib` remote, and
# editing one adds a recurring sync-conflict hunk on every future sync.
#
# Usage:
#   check-boneyard-quarantine.sh   run all five checks (exit 1 on any failure)
#
# Exit: 0 all checks pass, 1 one or more checks failed.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 1

# (e) Hard-coded expected count -- see the header comment above for why this must not be derived.
EXPECTED_BONEYARD_COUNT=1

failed=0

echo "=== Boneyard Quarantine Self-Test ==="

echo "(a) Boneyard/ exists at the repository root..."
if [ -d "Boneyard" ]; then
  echo "  OK: Boneyard/ exists."
else
  echo "  FAIL: Boneyard/ does not exist at the repository root."
  failed=1
fi

echo "(b) No 'Boneyard' reference in Cslib.lean..."
cslib_lean_hits=$(grep -c 'Boneyard' Cslib.lean 2>/dev/null || true)
cslib_lean_hits=${cslib_lean_hits:-0}
if [ "$cslib_lean_hits" -eq 0 ]; then
  echo "  OK: Cslib.lean has zero Boneyard references."
else
  echo "  FAIL: Cslib.lean references 'Boneyard' ($cslib_lean_hits hit(s)) -- something under"
  echo "        Boneyard/ may be reachable from the aggregator."
  failed=1
fi

echo "(c) No 'Boneyard' path in lakefile.toml..."
lakefile_hits=$(grep -c 'Boneyard' lakefile.toml 2>/dev/null || true)
lakefile_hits=${lakefile_hits:-0}
if [ "$lakefile_hits" -eq 0 ]; then
  echo "  OK: lakefile.toml has zero Boneyard references."
else
  echo "  FAIL: lakefile.toml references 'Boneyard' ($lakefile_hits hit(s)) -- a lean_lib or"
  echo "        target may have pulled the quarantine into the build."
  failed=1
fi

echo "(d) No live TODO:/FIXME:-family marker under Boneyard/..."
if [ -d "Boneyard" ]; then
  todo_hits=$(grep -rlnE 'TODO:|FIXME:|BUG:|HACK:|NOTE:|QUESTION:' \
    --include='*.lean' Boneyard/ 2>/dev/null || true)
  if [ -z "$todo_hits" ]; then
    echo "  OK: no live TODO:/FIXME:-family markers found under Boneyard/."
  else
    echo "  FAIL: live TODO:/FIXME:-family marker(s) found under Boneyard/:"
    echo "$todo_hits" | sed 's/^/        /'
    echo "        Neutralize to ARCHIVED-TODO: (or equivalent) -- see Boneyard/README.md."
    failed=1
  fi
else
  echo "  SKIP: Boneyard/ does not exist (check (a) already failed)."
fi

echo "(e) B0 mirror: Boneyard directory count matches the hard-coded expectation..."
boneyard_count=$(find . -type d -name 'Boneyard' -not -path './.lake/*' -not -path './.git/*' | wc -l | tr -d ' ')
if [ "$boneyard_count" -eq "$EXPECTED_BONEYARD_COUNT" ]; then
  echo "  OK: found $boneyard_count Boneyard director(y/ies), matches expected $EXPECTED_BONEYARD_COUNT."
else
  echo "  FAIL: found $boneyard_count Boneyard director(y/ies), expected $EXPECTED_BONEYARD_COUNT."
  echo "        If a new Boneyard was added deliberately, update EXPECTED_BONEYARD_COUNT in this"
  echo "        script (scripts/check-boneyard-quarantine.sh) in the same commit."
  failed=1
fi

echo "=== Boneyard Quarantine Self-Test Complete ==="
if [ "$failed" -ne 0 ]; then
  echo "One or more checks FAILED."
  exit 1
fi
echo "OK: all Boneyard quarantine invariants hold."
exit 0
