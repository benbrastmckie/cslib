# Research Report: Task 438 — Upstream Comment/Docstring Cleanups (PR Prep)

**Task Type**: cslib (PR preparation)
**Session**: sess_1782912232_20267a_438
**Date**: 2026-07-01
**Status**: researched

## Executive Summary

Task 438 aims to upstream two comment-only cleanups from local commit `35436d7e` to
`leanprover/cslib`. Research reveals a **critical scope correction**:

- **Cleanup #1 (Basic.lean stub deletion)**: Valid and upstreamable. The
  `Term.subst_comm` commented-out TODO/sorry stub still exists in `upstream/main` and is
  cleanly removed by local HEAD. This is a genuine, isolated, comment-only diff (9 lines
  deleted, 0 build impact). **This is the entire actionable content of the PR.**

- **Cleanup #2 (GNBA.lean docstring reword)**: **MOOT — must NOT be in the PR.**
  `Cslib/Logics/LTL/Semantics/GNBA.lean` does **not exist in `upstream/main`** at all; it is
  part of a large body of unupstreamed local LTL-tableau work. Furthermore, the specific
  docstring that commit `35436d7e` reworded was **superseded** by task 321's barrel-split
  refactor (commit `2344a765`), which rewrote GNBA.lean into a 4-phase barrel module with no
  `sorry`-referencing text at all. There is nothing to upstream for GNBA.lean.

**Net recommendation**: The PR should contain a **single-file, 9-line deletion** in
`Basic.lean`. Title prefix `chore:` or `doc:` per CONTRIBUTING.md.

## 1. Verification of Committed Edits (Working Tree)

Commit `35436d7e` ("chore: remove stale sorry-referencing comments flagged by task 431
audit") is an ancestor of HEAD (`fa1552b1`). Both edits are present as committed; working
tree is clean for both files (no uncommitted modifications).

| Edit | Committed at 35436d7e | State at HEAD | Upstreamable? |
|------|----------------------|---------------|---------------|
| Delete `Term.subst_comm` stub (Basic.lean) | Yes | Present (stub gone) | **YES** |
| Reword GNBA.lean Phase-5 docstring to past tense | Yes | **Superseded** by 2344a765 | **NO (moot)** |

- `grep subst_comm Basic.lean` -> not found (stub confirmed removed at HEAD).
- `HEAD:GNBA.lean` -> no "discharged" / "removing the sorry" / "Phase 5" / "five phases" text;
  file is now a 37-line 4-phase barrel module (import re-exports of
  `GNBA.Closure/Atoms/Construction/Correctness`). The reworded sentence no longer exists.

## 2. PR Diff Scope vs upstream/main (leanprover/cslib)

Remotes: `origin` = `benbrastmckie/cslib` (fork), `upstream` = `leanprover/cslib`.
Local `upstream/main` ref tip: `2772f421` (2026-06-26; a few days stale — re-fetch before PR).
HEAD is **2459 commits ahead** of `upstream/main`.

`git diff upstream/main..HEAD` for the two files:

| File | vs upstream/main | Interpretation |
|------|------------------|----------------|
| `Basic.lean` | `0` insertions / `9` deletions | Only the stub removal; file otherwise identical to upstream. Clean isolated diff. |
| `GNBA.lean` | `37` insertions / `0` deletions | Entire file is new local work; **not present upstream**. Out of scope. |

Confirmed `upstream/main:Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean` still
contains the stub at lines 105-113 (`-- TODO` / `-- theorem Term.subst_comm ... sorry`).
Confirmed `upstream/main:.../GNBA.lean` does not exist (`git cat-file -e` fails).

### Implication for PR branch construction (IMPORTANT for /pr)

Because HEAD is 2459 commits ahead of upstream, the PR branch must **not** be HEAD. It must
be a fresh branch off an up-to-date `upstream/main` containing **only** the Basic.lean
deletion. Recommended approach for the `/pr` (user-only) step:

```
git fetch upstream
git switch -c chore/lambda-subst-comm-stub upstream/main
# apply only the Basic.lean deletion, e.g.:
git checkout 35436d7e -- Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean
git commit -m "chore(LambdaCalculus): remove stale Term.subst_comm sorry stub"
```

Do NOT cherry-pick `35436d7e` directly — that commit also touches GNBA.lean (in its
pre-barrel-split form), which does not exist upstream and would fail to apply / drag in scope.

## 3. Comment-Only / Zero Build Impact Confirmation

Verified every removed line in the Basic.lean diff is either a `--` comment line or blank:
the removed block is entirely `-- TODO`, a fully commented-out theorem body, and one trailing
blank line. No executable Lean was touched. **Zero build/proof impact confirmed** — the PR
does not require a Mathlib rebuild for correctness, though CI (`lake build`, `lake test`,
`lake exe checkInitImports`, `lake exe lint-style`) should still run per CONTRIBUTING.md.

## 4. Additional Doc-Hygiene To Bundle? (Optional)

- **Basic.lean (HEAD)**: Broad scan for `TODO|FIXME|XXX|HACK|NOTE|sorry|admit|WIP|commented
  decls|placeholder|revisit` -> **no markers found**. No further hygiene to bundle; file is
  otherwise identical to upstream. Nothing to add.
- **GNBA.lean + GNBA/ submodules**: No stale `sorry`-referencing comments, TODO, or WIP
  markers. Irrelevant to this PR anyway (not upstream).

**Recommendation**: Keep the PR minimal — the single Basic.lean stub deletion. No bundling
is warranted; there is no additional in-scope hygiene, and bundling anything from GNBA.lean
would violate scope (unupstreamed feature work).

## 5. PR Title / Prefix Recommendation (CONTRIBUTING.md)

CONTRIBUTING.md §"Pull Request Titles" (lines 102-106) requires a conventional-commit
category prefix + colon: `feat|fix|doc|style|refactor|test|chore|perf`, optionally followed
by a parenthetical area. The local commit used `chore:`; both `chore` and `doc` are
defensible for a commented-out-code removal. Since this removes dead commented code (not
prose documentation), `chore` is the better fit.

**Recommended title**:
`chore(LambdaCalculus): remove stale Term.subst_comm sorry stub`

Acceptable alternative: `doc(LambdaCalculus): remove commented-out Term.subst_comm TODO stub`.

**PR body should include** (per cslib.md rules): AI-disclosure note (Mathlib AI usage policy),
statement that the change is comment-only with no build/proof impact, and reference to the
task 431 audit as the source.

## 6. Zero-Debt / Standards Compliance

No `sorry`, no axioms, no vacuous definitions involved — this is a pure deletion of dead
commented code. No zero-debt concerns. No new declarations, so no docBlame/defLemma/naming
lint exposure.

## Recommended Next Actions

1. Plan phase can be lightweight: this is a documentation/PR-prep task with a single-file,
   9-line deletion and no proof work.
2. Correct the task's working assumption: **drop the GNBA.lean item entirely** (moot —
   superseded by task 321 and not present upstream).
3. For the `/pr` step (user-only): construct a fresh branch off re-fetched `upstream/main`
   with only the Basic.lean deletion (see §2). Title `chore(LambdaCalculus): remove stale
   Term.subst_comm sorry stub`.
4. Run CSLib CI pipeline (`lake build`, `lake exe checkInitImports`, `lake lint`,
   `lake exe lint-style`, `lake test`) on the PR branch before submission.

## Key File Paths

- `/home/benjamin/Projects/cslib/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean`
  (target of the sole in-scope change; stub was at upstream lines 105-113)
- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Semantics/GNBA.lean` (out of scope; not upstream)
- `/home/benjamin/Projects/cslib/CONTRIBUTING.md` (PR title rules, §102-106)
- Local commit: `35436d7e` (source of edits); superseding refactor: `2344a765` (task 321)
