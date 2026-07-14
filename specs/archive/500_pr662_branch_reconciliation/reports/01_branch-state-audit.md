# PR #662 Branch-State Audit

**Task 500** — Reconcile the PR #662 branch: get it up to date with upstream, stacked on #607
correctly, carrying the intended primitive design and the task-499 compliance/citation work,
then (and only then) force-push.

Status: pre-seeded audit (findings gathered 2026-07-13 while investigating a force-push request).
No branches were pushed, rebased, or reset. All findings are read-only.

## PR #662 identity

- URL: https://github.com/leanprover/cslib/pull/662 (OPEN, cross-repository)
- Title: `feat(Logics/Modal): make box primitive alongside diamond (stacked on #607)`
- Head: `benbrastmckie:feat/modal-formula-primitives`
- Base: `fmontesi/connectives` (the #607 stack target)
- Current PR commit count: 1 (origin head `70b7ec4d`)

## The core problem: four competing primitive designs

`inductive Proposition` constructors differ across every candidate branch:

| Branch | Constructors | Count | Role |
|--------|--------------|-------|------|
| `origin/feat/modal-formula-primitives` (**live PR 662**) | `atom, not, and, diamond, box` | 5 | what reviewers currently see; "box alongside diamond" |
| local `feat/modal-formula-primitives` | `atom, bot, imp, box` | 4 | diverged from origin (24 behind / 5 ahead) |
| `feat/modal-formula-primitives-v2` | `atom, bot, imp, box` | 4 | stacked on `feat/propositional-v2` |
| `task-441-native-refactor` | `atom, bot, imp, and, or, box, diamond` | 7 | **task-499 work lives here**; = slice "version B" |
| base `fmontesi/connectives` / `pr607` | `atom, not, and, diamond` | 4 | the #607 base |

**Decision required (blocking): which design is canonical for PR #662?** The task-499 audit +
citation work assumed the **7-primitive** `{atom,bot,imp,and,or,box,diamond}` design (slice
"version B"), but the **live PR shows the 5-primitive** `{atom,not,and,diamond,box}` design.
These are not reconcilable by a mechanical rebase — they are different formalizations.

## Git-history hazards

1. **`task-441-native-refactor` has NO common ancestor** with `feat/modal-formula-primitives`
   (local or origin) or with `upstream/fmontesi/connectives` / `upstream/main`. `git merge-base`
   returns empty for all three. Its recent root commits reference a "task graph: reconcile
   #662/#648/#607 stacking to #607 direction" (`82184d93`) and batch-orchestration commits — it
   appears to be a disjoint/replanted history. **The task-499 changes therefore cannot be
   cherry-picked/rebased onto the PR branch without first resolving this disjointness.**

2. **Local vs origin `feat/modal-formula-primitives` have diverged**: 24 commits on origin not in
   local, 5 commits on local not in origin — AND they hold different designs (origin = 5-prim,
   local = 4-prim). A naive `git push --force` of the local branch would replace the PR's
   5-primitive content with the local 4-primitive content.

3. **Staleness**: both `origin/feat/modal-formula-primitives` and the base
   `upstream/fmontesi/connectives` are **8 commits behind `upstream/main`**.

## Where the task-499 work currently sits (uncommitted, on `task-441-native-refactor`)

- `Cslib/Logics/Modal/Basic.lean` — citation fix (Blackburn/C&Z → Simpson1994) + earlier
  task-number scrub; docstring reflowed; CI green (466/466, lint-style clean).
- `references.bib` — added `Simpson1994` (`@phdthesis`).
- `specs/498_.../artifacts/pr-662-slice/Basic.lean` — slice mirror of the same edits.
- `specs/literature-index.json` — sub-index pointers for the newly ingested sources.
- Copyright-holder line addition (Benjamin Brast-McKie) **deliberately deferred** pending
  Fabrizio Montesi's confirmation (task-499 Phase 5).

## Goal / acceptance criteria for task 500

1. **Decide the canonical primitive design** for PR #662 (5-prim vs 7-prim vs 4-prim) — needs
   user + likely maintainer (Fabrizio) input, since it changes the PR's substance.
2. Reconstruct/repair a single PR-head branch that:
   - is rebased onto the current `upstream/fmontesi/connectives` (#607),
   - is up to date w.r.t. `upstream/main` (resolve the 8-commit gap as appropriate for a stacked PR),
   - carries the chosen design,
   - incorporates the task-499 compliance + citation work,
   - resolves the disjoint-history problem on `task-441-native-refactor` (rebase/graft or
     re-derive the 7-primitive changes on top of the proper base).
3. Verify full CSLib CI on the reconstructed branch (lake build / checkInitImports / lint /
   lint-style / test / shake).
4. Only then force-push `feat/modal-formula-primitives` to origin and confirm the PR diff.

## Explicitly out of scope until decided

- Any `git push`, `push --force`, `rebase`, or `reset` — **await user confirmation of the
  target design and branch strategy first.**
- Changing the copyright-holder line (separate maintainer gate).

## Open questions for the user

1. Which primitive design is the intended PR #662 — the 5-primitive `{atom,not,and,diamond,box}`
   currently live, or the 7-primitive native layer (`task-441` / slice "version B"), or the
   minimal 4-primitive `{atom,bot,imp,box}` (local/v2)?
2. Is `feat/modal-formula-primitives` still the intended PR head branch, or should the PR be
   re-pointed at a rebuilt branch?
3. Should the base stay `fmontesi/connectives`, or has the #607 target moved?
