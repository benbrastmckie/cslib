#!/usr/bin/env bash
# prepare-foundation-branch.sh
#
# Task 399 — Refresh PR #648: IPL-base foundation
#
# PURPOSE: Create a LOCAL branch 'feat/propositional-foundation' off upstream/main
#          containing the propositional foundation cherry-pick. NO push, NO gh calls,
#          NO remote CI. Use this to stage the branch for manual review before running
#          '/pr 399' (user-only command).
#
# USAGE:
#   bash specs/399_refresh_pr648_ipl_base_foundation/prepare-foundation-branch.sh
#
#   Run from the repository root (~/Projects/cslib or wherever cslib is checked out).
#   Requires: git remote 'upstream' pointing to https://github.com/leanprover/cslib.git
#
# WHAT THIS SCRIPT DOES:
#   1. Fetches upstream/main
#   2. Creates branch 'feat/propositional-foundation' off upstream/main (fails if exists)
#   3. Copies Defs.lean from local main (minus Connectives import + typeclass instances)
#   4. Copies NaturalDeduction/Basic.lean from local main (as-is)
#   5. Deletes NaturalDeduction/Theory.lean
#   6. Removes Theory import from Cslib.lean barrel
#   7. Adds 7 missing references.bib entries from local main
#   8. Stages all changes (does NOT commit)
#
# WHAT THIS SCRIPT DOES NOT DO:
#   - Does NOT push to any remote
#   - Does NOT call gh or any GitHub API
#   - Does NOT run CI (run manually: lake build, lake exe checkInitImports, etc.)
#   - Does NOT modify the current branch (fork main is unaffected)
#
# IDEMPOTENCY: Re-running after the branch already exists will fail at step 2.
#   To re-run: git branch -D feat/propositional-foundation && re-run this script.
#
# SAFETY VERIFICATION (grep to confirm no remote operations):
#   grep -E "push|gh[[:space:]]|remote.*CI" prepare-foundation-branch.sh
#   # Should return no matches

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"
FORK_MAIN="main"
NEW_BRANCH="feat/propositional-foundation"

echo "=== prepare-foundation-branch.sh ==="
echo "Repository root: $REPO_ROOT"
echo "Branching from:  upstream/main"
echo "New branch name: $NEW_BRANCH"
echo ""

cd "$REPO_ROOT"

# --- Step 1: Fetch upstream ---
echo "[1/8] Fetching upstream..."
git fetch upstream
UPSTREAM_HEAD="$(git rev-parse upstream/main)"
echo "      upstream/main HEAD: $UPSTREAM_HEAD"

# --- Step 2: Create new branch off upstream/main ---
echo "[2/8] Creating branch '$NEW_BRANCH' off upstream/main..."
if git show-ref --verify --quiet "refs/heads/$NEW_BRANCH"; then
  echo "ERROR: Branch '$NEW_BRANCH' already exists."
  echo "       To re-run: git branch -D $NEW_BRANCH && re-run this script."
  exit 1
fi
git checkout -b "$NEW_BRANCH" upstream/main
echo "      Branch created."

# --- Step 3: Copy Defs.lean from fork main (minus Connectives import + typeclass instances) ---
echo "[3/8] Applying Defs.lean (fork main version, connectives excluded)..."

# Get Defs.lean content from fork main
git show "${FORK_MAIN}:Cslib/Logics/Propositional/Defs.lean" > /tmp/foundation_defs_raw.lean

# Remove the Connectives import line (exact match)
grep -v "^public import Cslib\.Foundations\.Logic\.Connectives$" \
  /tmp/foundation_defs_raw.lean > /tmp/foundation_defs_no_import.lean

# Remove the three typeclass instance blocks (lines starting the 3 instances through their bodies)
# We use Python for reliable multi-line block removal
python3 - <<'PYEOF' /tmp/foundation_defs_no_import.lean /tmp/foundation_defs_final.lean
import sys

src_path, dst_path = sys.argv[1], sys.argv[2]
with open(src_path) as f:
    content = f.read()

# Remove PropositionalConnectives instance block
PROP_CONN = """/-- Register `Proposition` as an instance of `PropositionalConnectives`. -/
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp

/-- Register `HasAnd` instance for `Proposition`. -/
instance : HasAnd (Proposition Atom) where
  and := .and

/-- Register `HasOr` instance for `Proposition`. -/
instance : HasOr (Proposition Atom) where
  or := .or

"""
content = content.replace(PROP_CONN, "")

# Also handle without trailing newline (idempotent)
PROP_CONN_NO_TRAIL = PROP_CONN.rstrip("\n")
content = content.replace(PROP_CONN_NO_TRAIL, "")

with open(dst_path, 'w') as f:
    f.write(content)

print("      Typeclass instances removed.")
PYEOF

cp /tmp/foundation_defs_final.lean Cslib/Logics/Propositional/Defs.lean
echo "      Defs.lean written."

# --- Step 4: Copy Basic.lean from fork main (as-is) ---
echo "[4/8] Applying NaturalDeduction/Basic.lean (fork main version, as-is)..."
git show "${FORK_MAIN}:Cslib/Logics/Propositional/NaturalDeduction/Basic.lean" \
  > Cslib/Logics/Propositional/NaturalDeduction/Basic.lean
echo "      Basic.lean written."

# --- Step 5: Delete Theory.lean ---
echo "[5/8] Deleting NaturalDeduction/Theory.lean (Option A: incompatible old API)..."
if [ -f "Cslib/Logics/Propositional/NaturalDeduction/Theory.lean" ]; then
  rm Cslib/Logics/Propositional/NaturalDeduction/Theory.lean
  echo "      Theory.lean deleted."
else
  echo "      Theory.lean not found (already absent — OK)."
fi

# --- Step 6: Remove Theory import from Cslib.lean barrel ---
echo "[6/8] Removing Theory import from Cslib.lean..."
THEORY_IMPORT="public import Cslib.Logics.Propositional.NaturalDeduction.Theory"
if grep -qF "$THEORY_IMPORT" Cslib.lean; then
  grep -vF "$THEORY_IMPORT" Cslib.lean > /tmp/foundation_cslib.lean
  cp /tmp/foundation_cslib.lean Cslib.lean
  echo "      Theory import removed from Cslib.lean."
else
  echo "      Theory import not found in Cslib.lean (already absent — OK)."
fi

# --- Step 7: Add 7 missing references.bib entries from fork main ---
echo "[7/8] Adding missing references.bib entries from fork main..."

# Extract the 7 entries from fork main's references.bib
BIB_KEYS=(
  "Church1956"
  "ChagrovZakharyaschev1997"
  "Johansson1937"
  "Gentzen1935"
  "Prawitz1965"
  "TroelstraVanDalen1988"
  "SorensenUrzyczyn2006"
)

python3 - <<PYEOF2
import re, sys

fork_main_bib = None

# Read fork main bib via git
import subprocess
result = subprocess.run(
    ['git', 'show', '${FORK_MAIN}:references.bib'],
    capture_output=True, text=True, check=True
)
fork_main_bib = result.stdout

keys_to_add = ${BIB_KEYS[@]@Q}
# Convert bash array to python list
import shlex
keys_list = shlex.split(keys_to_add)

# Parse bib entries from fork main
# A bib entry starts with @type{key, and ends with the matching }
def extract_entry(bib_text, key):
    # Find the entry starting with @...{key,
    pattern = rf'@\w+\{{{re.escape(key)},'
    match = re.search(pattern, bib_text)
    if not match:
        return None
    start = match.start()
    # Find matching closing brace
    depth = 0
    i = start
    while i < len(bib_text):
        if bib_text[i] == '{':
            depth += 1
        elif bib_text[i] == '}':
            depth -= 1
            if depth == 0:
                return bib_text[start:i+1]
        i += 1
    return None

# Read current references.bib
with open('references.bib') as f:
    current_bib = f.read()

entries_added = []
entries_skipped = []

additions = ""
for key in keys_list:
    if key in current_bib:
        entries_skipped.append(key)
        continue
    entry = extract_entry(fork_main_bib, key)
    if entry:
        additions += "\n" + entry + "\n"
        entries_added.append(key)
    else:
        print(f"  WARNING: Could not find {key} in fork main references.bib", file=sys.stderr)

if additions:
    with open('references.bib', 'a') as f:
        f.write(additions)

if entries_added:
    print(f"      Added entries: {', '.join(entries_added)}")
if entries_skipped:
    print(f"      Already present: {', '.join(entries_skipped)}")
PYEOF2

# --- Step 8: Stage all changes ---
echo "[8/8] Staging all changes..."
git add Cslib/Logics/Propositional/Defs.lean
git add Cslib/Logics/Propositional/NaturalDeduction/Basic.lean
git add Cslib.lean
git add references.bib
if [ -f "Cslib/Logics/Propositional/NaturalDeduction/Theory.lean" ]; then
  # Shouldn't exist at this point, but handle gracefully
  echo "  WARNING: Theory.lean still exists — was it not deleted?"
else
  git rm --cached Cslib/Logics/Propositional/NaturalDeduction/Theory.lean 2>/dev/null || \
    git add -u Cslib/Logics/Propositional/NaturalDeduction/Theory.lean 2>/dev/null || true
fi
echo "      Changes staged. Review with: git diff --staged"

echo ""
echo "=== BRANCH READY: $NEW_BRANCH ==="
echo ""
echo "Next steps:"
echo "  1. Verify the diff:   git diff --staged"
echo "  2. Build locally:     lake exe cache get && lake build"
echo "  3. Run CI checks:     lake exe checkInitImports && lake exe lint-style"
echo "  4. Review pr-description.md and zulip-response.md in specs/399_*/"
echo "  5. When ready:        commit and run /pr 399 (user-only command)"
echo ""
echo "IMPORTANT: Do NOT run 'git push' — the /pr command handles that."
echo ""

# Cleanup temp files
rm -f /tmp/foundation_defs_raw.lean /tmp/foundation_defs_no_import.lean \
       /tmp/foundation_defs_final.lean /tmp/foundation_cslib.lean

echo "Temp files cleaned up."
