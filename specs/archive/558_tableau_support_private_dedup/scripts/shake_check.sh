#!/usr/bin/env bash
# Runs lake shake and filters to genuine shake FINDINGS (import add/remove blocks),
# stripping the build-replay warning noise (⚠ progress lines, `warning: ... sorry` lines)
# that would otherwise false-positive-match a naive `grep Modal/Tableau` on raw shake output.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
RAW=$(lake shake --add-public --keep-implied --keep-prefix 2>&1)
EXIT=$?
# Drop build-replay/warning noise lines; keep only shake's own output (file paths + add/remove lines)
FINDINGS=$(echo "$RAW" | grep -vE '^(⚠ |warning: )')
echo "$FINDINGS"
echo "---"
echo "raw_exit=$EXIT"
echo "modal_tableau_findings=$(echo "$FINDINGS" | grep -c 'Modal/Tableau')"
echo "total_finding_files=$(echo "$FINDINGS" | grep -c '^/home.*\.lean:$')"
