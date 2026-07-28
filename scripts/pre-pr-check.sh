#!/usr/bin/env bash
# Note: intentionally does NOT use `set -e` for the whole script -- steps 1-3 are advisory
# greps that legitimately return nonzero when they find nothing to report, and are expected
# to keep running past a "found something" result so all four checks always execute. Failure
# is instead accumulated explicitly into `failed` and turned into a single `exit 1` at the end.
echo "=== Pre-PR Verification ==="

failed=0

echo "1. Checking for sorry instances in PR scope..."
# Strip block (/- -/) and line (--) comments before scanning, and exclude lines mentioning
# `warn.sorry` (the option name contains "sorry" at a word boundary and is not a proof hole).
# A naive `\bsorry\b` scan without these two exclusions is what previously inflated this
# repo's own sorry counts -- see the plan's "Measurement notes" for the two documented causes.
sorry_hits=""
while IFS= read -r -d '' f; do
  hit=$(perl -0777 -pe 's/\/-.*?-\///gs' "$f" | sed -e 's/--.*//' \
    | grep -n '\bsorry\b' | grep -v 'warn\.sorry')
  if [ -n "$hit" ]; then
    sorry_hits="${sorry_hits}${f}:
${hit}
"
  fi
done < <(find Cslib/Foundations/Logic/ Cslib/Logics/Modal/ Cslib/Logics/Temporal/ Cslib/Logics/Bimodal/ -name "*.lean" -print0)
if [ -n "$sorry_hits" ]; then
  echo "$sorry_hits"
  echo "  FAIL: sorry instances found"
  failed=1
else
  echo "  OK: No sorry instances"
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

echo "=== Pre-PR Verification Complete ==="
if [ "$failed" -ne 0 ]; then
  echo "One or more checks FAILED."
  exit 1
fi
exit 0
