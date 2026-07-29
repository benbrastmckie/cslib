#!/usr/bin/env bash
# Note: intentionally does NOT use `set -e` for the whole script -- steps 2-3 are advisory
# greps that legitimately return nonzero when they find nothing to report (step 1 is a scoped
# ratchet delegation, not a grep, but shares the same non-fatal-on-failure treatment), and all
# steps are expected to keep running past a "found something"/failed result so every check
# always executes. Failure is instead accumulated explicitly into `failed` and turned into a
# single `exit 1` at the end.
echo "=== Pre-PR Verification ==="

failed=0

echo "1. Sorry ratchet, scoped to four trees (baseline-relative; fails only on NEW debt)..."
# This is a scoped delegation to check-sorry-suppressions.sh's baseline-relative ratchet, not a
# second detection pipeline -- see that script for the discrimination rule (block-comment strip,
# line-comment strip, warn.sorry-line exclusion, then \bsorry\b word-boundary count) and for
# scripts/sorry-suppression-baseline.txt, the single ceiling both this step and step 8 compare
# against. This step fails only on NEW sorry/suppression debt introduced beyond the baseline in
# the four trees below; it does not fail on the tree's existing (pre-baselined) debt.
#
# The four-tree list below is a stale artifact of an earlier PR series and is NOT a live
# definition of "PR scope" -- it predates this step's rewrite and nothing keeps it in sync with
# whatever a future PR actually touches. Do not treat it as authoritative; treat it as a
# convenient, historically-motivated narrowing for fast local feedback, same spirit as step 4's
# hand-picked module list below.
#
# Honest relationship to step 8: this step is early, scoped, same-baseline fast-fail. It
# contributes no unique failure coverage over step 8 (step 8 sweeps a strict superset of these
# four trees against the identical baseline) and can never fail where step 8 passes. Its value
# is purely early, scoped feedback before the slower steps run.
if ! bash "$(dirname "${BASH_SOURCE[0]}")/check-sorry-suppressions.sh" \
    --scope Cslib/Foundations/Logic Cslib/Logics/Modal Cslib/Logics/Temporal Cslib/Logics/Bimodal; then
  echo "  FAIL: sorry/suppression counts in the four scoped trees exceeded the baseline ceiling"
  failed=1
fi

echo "2. Checking for debug artifacts..."
# Anchor to the start of a (whitespace-trimmed) line so prose mentions of these commands
# inside doc comments (e.g. "... where \`#eval\`/\`native_decide\` are blocked ...") are not
# flagged -- only lines where the command is actually invoked as code.
debug_hits=$(grep -rnE '^[[:space:]]*(#check|#eval|dbg_trace)\b' \
  Cslib/Foundations/Logic/ Cslib/Logics/Modal/ Cslib/Logics/Temporal/ Cslib/Logics/Bimodal/ \
  --include="*.lean" 2>/dev/null)
if [ -n "$debug_hits" ]; then
  echo "$debug_hits"
  echo "  FAIL: debug artifacts found"
  failed=1
else
  echo "  OK: No debug artifacts"
fi

echo "3. Checking for missing copyright headers..."
header_missing=0
while IFS= read -r -d '' f; do
  if ! head -1 "$f" | grep -q "^/-"; then
    echo "  FAIL: Missing header in $f"
    header_missing=1
  fi
done < <(find Cslib/Foundations/Logic/ Cslib/Logics/Modal/ Cslib/Logics/Temporal/ Cslib/Logics/Bimodal/ -name "*.lean" -print0)
if [ "$header_missing" -eq 0 ]; then
  echo "  OK: All files have headers"
else
  failed=1
fi

echo "4. Building PR-scope modules..."
if ! lake build Cslib.Foundations.Logic.Metalogic.Consistency \
    Cslib.Logics.Modal.Metalogic \
    Cslib.Logics.Temporal.Metalogic \
    Cslib.Logics.Bimodal.Metalogic.Core \
    Cslib.Logics.Bimodal.Metalogic.Completeness \
    Cslib.Logics.Bimodal.Metalogic.Decidability \
    Cslib.Logics.Bimodal.Metalogic.Separation; then
  echo "  FAIL: lake build failed"
  failed=1
fi

echo "5. Full-repo warning gate (matches CI's lake build --wfail --iofail)..."
if ! lake build --wfail --iofail; then
  echo "  FAIL: lake build --wfail --iofail reported warnings or errors"
  failed=1
fi

# Step 6 is deliberately independent of step 5. A blanket suppression makes step 5 pass by
# hiding the warning rather than fixing it, so a green --wfail build is not evidence that
# suppressions did not grow. This check is what distinguishes the two.
echo "6. Blanket linter-suppression ratchet..."
if ! bash "$(dirname "${BASH_SOURCE[0]}")/check-lint-suppressions.sh"; then
  echo "  FAIL: blanket linter suppressions increased"
  failed=1
fi

echo "7. Shake import-debt ratchet (needs the completed build from steps 4/5 above)..."
if ! bash "$(dirname "${BASH_SOURCE[0]}")/check-shake-residue.sh"; then
  echo "  FAIL: lake shake flagged new import debt not in the baseline"
  failed=1
fi

# Step 8 shares its baseline and discrimination rule with step 1 above: both delegate to
# check-sorry-suppressions.sh, step 1 scoped to four trees and step 8 unscoped (whole-tree,
# SCAN_ROOT=Cslib, a strict superset of step 1's four trees). Step 1 therefore contributes no
# unique failure coverage over step 8 and can never fail where step 8 passes -- its only value
# is early, scoped feedback before the slower steps run. Step 9's axiom-taint ratchet is a
# separate, independent check with its own baseline. Note step 1 and step 5 (`lake build
# --wfail --iofail`) have different scopes and are NOT redundant: the three
# `Propositional/Tableau/*` files trip step 5 (repo-wide) but are invisible to step 1 (its four
# named trees never include Propositional/Tableau).
echo "8. Sorry-suppression count ratchet..."
if ! bash "$(dirname "${BASH_SOURCE[0]}")/check-sorry-suppressions.sh"; then
  echo "  FAIL: sorry/suppression counts exceeded the baseline ceiling"
  failed=1
fi

echo "9. Axiom-census ratchet (needs the completed build from steps 4/5 above)..."
if ! bash "$(dirname "${BASH_SOURCE[0]}")/check-axiom-census.sh"; then
  echo "  FAIL: a declaration outside the axiom-census baseline became sorryAx-tainted"
  failed=1
fi

echo "=== Pre-PR Verification Complete ==="
if [ "$failed" -ne 0 ]; then
  echo "One or more checks FAILED."
  exit 1
fi
exit 0
