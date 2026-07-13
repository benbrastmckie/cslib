# Task 489: Modal Proposition Base Reshape onto #607 — Patch Export

## Summary

Produced a clean, build-verified, standalone patch reshaping the modal `Proposition` type in
upstream PR #607 (`fmontesi/connectives`, HEAD `ddc2c9b8`) from the diamond-primitive
`{atom, not, and, diamond}` basis to the fully-primitive
`{atom, bot, imp, and, or, box, diamond}` basis, with `not` derived as `imp · .bot`. The patch
contains ONLY the base reshape — no cube-completion machinery (b/four/five/d validity,
Canonicity, Correspondence) was brought over from the #662 reference branch.

## 1. Branch and Worktree

- Branch: `modal-base-reshape-onto-607` (created from `upstream/fmontesi/connectives` @ `ddc2c9b8b0b7848948eefe00002323d02440c2e3`)
- Worktree: `/home/benjamin/Projects/cslib-modal-base-reshape`
- Single commit on top of upstream: `c2e37e20e9ab473c062e0f88272d1902bfb7cdf7`

## 2. Patch File

- `/home/benjamin/Projects/cslib/specs/489_propose_modal_base_reshape_to_607/artifacts/0001-feat-Logics-Modal-make-modal-Proposition-fully-primi.patch`
- Exactly one patch file produced by `git format-patch upstream/fmontesi/connectives`.

## 3. Diff Stat vs #607

```
 Cslib/Logics/Modal/Basic.lean              | 120 +++++++++++++++++------------
 Cslib/Logics/Modal/Denotation.lean         |   9 ++-
 Cslib/Logics/Modal/LogicalEquivalence.lean |  21 ++++-
 CslibTests/GrindLint.lean                  |   4 +
 4 files changed, 98 insertions(+), 56 deletions(-)
```

`Cslib/Logics/Modal/Cube.lean` diff vs upstream is empty (0 lines) — confirmed untouched.

## 4. Cube.lean Backward-Compatibility Confirmation

`Cslib/Logics/Modal/Cube.lean` was never modified. Its existing content (`K.k_valid`,
`T.t_valid`, and all logic/subset-ordering definitions for K, T, B, Four, Five, D, K45, D4, D5,
D45, DB, TB, KB5, S4, S5) builds **cleanly and unmodified** against the reshaped
`Proposition` type. Verified via:

```
lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Denotation \
  Cslib.Logics.Modal.LogicalEquivalence Cslib.Logics.Modal.Cube
```
→ `Build completed successfully (645 jobs).`

This is the key proof point demonstrating the reshape is backward compatible with #607's
existing minimal cube.

## 5. Sorry / Axiom / Vacuous-Definition Audit

- **Sorry count in the 3/4 changed files**: 0
- **Sorry count repo-wide**: 1, but it is a pre-existing commented-out line in
  `Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean:112` (`--   sorry`), unrelated to
  this patch and unchanged by it.
- **Vacuous-definition grep repo-wide**: 1 hit, but it is a pre-existing legitimate proof
  (`Cslib/Computability/URM/Basic.lean:92`, `theorem J_IsJump ... := trivial`), unrelated to
  this patch.
- **New axioms**: 0. Repo-wide axiom count is 0 both before (unmodified upstream) and after
  this patch — no axioms introduced.

## 6. CI Pipeline Results

All steps run in the dedicated worktree, in order:

0. `lake exe cache get` — cache hit, completed.
1. `lake build` (full) — 2759 jobs, `Build completed successfully`.
2. `lake exe checkInitImports` — passed silently (no output = no violations).
3. `lake lint` — `Linting passed for Cslib.` No hits for the 7 prevention categories
   (docBlame, defLemma, defsWithUnderscore, simpNF, unusedSectionVars, topNamespace,
   dupNamespace) in the modified files.
4. `lake exe lint-style` — passed (only a benign `nolints-style.txt` file-not-found warning,
   which is standard/expected across the repo).
5. `lake shake --add-public --keep-implied --keep-prefix` — reported the same baseline
   import-shuffle suggestions across many unrelated files (e.g. `Foundations/Relation/Defs`,
   `HasFresh`, `LambdaCalculus/...`) that are present identically on **unmodified upstream
   #607** (verified via `git stash` / re-run / `git stash pop` comparison). No new suggestions
   were introduced by this patch beyond the expected Set/Euclidean import reshuffling in
   `Basic.lean`/`Denotation.lean`/`Cube.lean`, which is advisory only (not gating).
6. `lake exe mk_all --module` — regenerated `CslibTests.lean` into `module`/`public import`
   syntax, but this same regeneration occurs identically on unmodified upstream #607
   (verified via the same stash comparison), so it is unrelated pre-existing drift. This file
   was reverted (`git checkout -- CslibTests.lean`) to keep the patch scoped to exactly the
   4 intended files.
7. `lake test` — `Built CslibTests (2.4s)`. All tests pass, including `CslibTests.GrindLint`
   after the one-line skip addition (see Deviations below).

## 7. Deviations from Plan

- **`CslibTests/GrindLint.lean` required a one-line `#grind_lint skip` addition.** After the
  reshape, `Cslib.Logic.Modal.not_denotation`'s proof (in `Denotation.lean`) routes through the
  derived-negation `grind =` lemma set (negation is now `imp · .bot` rather than a primitive
  constructor), which triggers 28 additional `grind` theorem instantiations and exceeds the
  `GrindLint` runaway-instantiation threshold (`min := 20`). Added:
  ```lean
  #grind_lint skip Cslib.Logic.Modal.not_denotation
  ```
  with an explanatory comment, immediately before the final `#guard_msgs in` block. This is
  the ONLY deviation from the base 3-file reshape; it was anticipated in the task description
  as an acceptable one-line addition if genuinely required by the build, which it was.
- **`CslibTests.lean` mk_all regeneration was reverted** (not committed) since it reproduces
  identically on unmodified upstream #607 and is unrelated pre-existing drift, not part of the
  reshape's scope.
- No changes to `references.bib` were needed.

## Files Changed (committed, in the patch)

- `Cslib/Logics/Modal/Basic.lean`
- `Cslib/Logics/Modal/Denotation.lean`
- `Cslib/Logics/Modal/LogicalEquivalence.lean`
- `CslibTests/GrindLint.lean` (one-line skip addition only)

## Files Explicitly NOT Touched

- `Cslib/Logics/Modal/Cube.lean` (verified empty diff vs upstream)
- `references.bib`
- Any file under FromPropositional, Metalogic, ProofSystem, Tableau, InterSystem, HML
- Task 486/487 branches or worktrees (read-only reference only, via `git checkout <branch> -- <path>`)

## Constraints Honored

- No push, no GitHub PR created (local patch-export only).
- No modification to `main` or any #662 branch/worktree.
- Exactly one new worktree/branch created, plus the one patch file.
