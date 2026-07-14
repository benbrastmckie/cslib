# Task 500 — PR #662 Reconstruction Summary

**Date**: 2026-07-13
**Outcome**: PR #662 rebuilt as a single squashed commit on `main`, force-pushed with user approval.

## Decisions (user-confirmed during orchestration)
- **Design**: 7-primitive native `Proposition {atom, bot, imp, and, or, box, diamond}` (neg/top/iff derived).
- **Base**: standalone on `main` (`e5ed905c`, includes #707/#708) — NOT stacked on the stale #607.
  Rationale: "based on 707 to facilitate review". Required reworking the foundational slice off
  #607's `Cslib.Foundations.Logic.Connectives` dependency (absent from main) into main's inline style.
- **Copyright**: deferred — "Benjamin Brast-McKie" NOT added to headers (separate maintainer gate).
- **Branch cleanup / preservation**: DEFERRED by user — not performed this run.

## What shipped
Single commit `24825833` on `main`, force-pushed `70b7ec4d → 24825833` to
`origin/feat/modal-formula-primitives` (the #662 head on the benbrastmckie fork; `fmontesi/connectives`
was never touched — comment-only discipline preserved).

PR #662 retargeted: base `fmontesi/connectives` → `main`; title → "feat(Logics/Modal): make
Proposition a native 7-primitive type"; body rewritten to reflect the main-based 7-primitive content.

### Files (5): +145 / −40 (local git diff)
- `Cslib/Logics/Modal/Basic.lean` — 7-primitive `Proposition`, native `Satisfies`, derived neg/top/iff,
  per-connective characterisation lemmas now `Iff.rfl`, `Satisfies.dual` as a semantic theorem (EM).
  ALL frame-correspondence theorems (T/B/4/5/D + converses) preserved.
- `Cslib/Logics/Modal/Denotation.lean` — 7-constructor denotation; `satisfies_mem_denotation`,
  `not_denotation`, `theoryEq_denotation_eq` preserved.
- `Cslib/Logics/Modal/Cube.lean` — +1 import; Modal Cube + validities intact.
- `Cslib/Logics/Modal/LogicalEquivalence.lean` — Context `not`→`neg` former; congruence preserved.
- `references.bib` — Simpson1994 added.

### Verification (independently re-run on worktree)
`lake build` (full, 2781 jobs) ✓ · Modal build ✓ · `checkInitImports` ✓ · `lake lint` ✓ ·
`lint-style` ✓ · `shake` (no Modal findings) ✓ · `lake test` (agent run, 8835 jobs) ✓.
Sorry-free; `Satisfies.dual`/`Satisfies.k` axioms = propext/Classical.choice/Quot.sound only.

## Build environment
Reconstruction done in worktree `/home/benjamin/Projects/cslib-662-rebuild`
(branch `rebuild/662-main-7prim`, Lean v4.32.0) — LEFT INTACT for possible review revisions.
Main working tree untouched (stayed on `task-441-native-refactor`).

## Deferred follow-ups (not done this run, per user)
1. **Branch preservation + cleanup** — "don't lose anything; merge useful branches into main if not
   already represented", then reduce to the three PR branches (648/649/662). Recommended approach:
   audit each local branch (already-represented vs unique unpushed work) before any merge/delete.
2. Remove worktree `cslib-662-rebuild` + branch `rebuild/662-main-7prim` once the PR is settled.
3. Copyright-holder line (add contributor) — awaits Fabrizio's confirmation.
