# Implementation Summary: Rebase PR #648 onto upstream/main and clear the stale blocking review

- **Task**: 620 - Rebase PR #648 onto current upstream and clear the stale blocking review
- **Status**: [COMPLETED]
- **Started**: 2026-08-11T21:10:00Z
- **Completed**: 2026-08-11T22:45:00Z
- **Effort**: ~2.5 hours (vs. 7.5 hour estimate — build/test infra was already warm from prior
  task work, and no unpredicted conflict shape emerged)
- **Dependencies**: None
- **Artifacts**: `plans/01_rebase-pr648-clear-review.md`, `pr-scaffolding.md`, this summary
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md,
  `.claude/rules/pr-prohibition.md`, `.claude/rules/git-workflow.md`

## Overview

Rebased the PR #648 branch (`origin/feat/propositional-v2`) onto current `upstream/main` in a
dedicated git worktree, resolved the two conflicted files, reconciled `Defs.lean` to the approved
scope (PR's five-primitive-`bot` semantics on upstream's `Operators.lean` typeclass mechanism),
and greened all five of upstream's PR CI gates locally. Work is confined to a local, unpushed
worktree branch; per `.claude/rules/pr-prohibition.md`, no push, `gh` write, or Zulip post was
performed.

## What Changed

- Created worktree `/home/benjamin/Projects/cslib-pr648` on branch `rebase/pr648-upstream`,
  rooted at `origin/feat/propositional-v2` (never at this fork's `main`, which carries a drifted,
  out-of-scope `[IsIntuitionistic T]`-gated design).
- Rebased all 6 PR commits onto `upstream/main` (`4bec19fc`), resolving conflicts in
  `references.bib` (mechanical — kept both upstream's and the PR's append blocks; caught and
  corrected one transient duplicate `Avigad2022` entry) and `Cslib/Logics/Propositional/Defs.lean`
  (first-pass, per plan — took the PR's side wholesale to complete the rebase).
- Installed toolchain `leanprover/lean4:v4.34.0-rc1` and warmed the Mathlib `de5ce8a9` cache
  (revised from the plan's `v4.33.0`/`db584cd6` — upstream advanced one toolchain-bump commit
  since research, which does not touch `Propositional/` or `Foundations/Logic/`).
- Fully reconciled `Defs.lean` to the target shape: added `Operators.lean` import, registered
  `HasAnd`/`HasOr`/`HasImp`/`HasIff`/`HasNot` instances, made `Bot`/`Top` instances named
  (`instBotProposition`/`instTopProposition`), deleted the five local `scoped` notation
  declarations, added the ungated `not_eq` `@[grind =]` bridge and the upstream chained example.
- Fixed one unpredicted grind-automation regression in `NaturalDeduction/Theory.lean:55`
  (`IsClassical.pierce`), caused by the switch from direct notation to typeclass-projection
  notation — `grind` no longer unfolds `HasNot.not` to match a raw-constructor Finset element.
- Verified all five of upstream's PR CI gates pass locally: `lake build --wfail --iofail` (2801
  jobs, zero warnings), `lake test --wfail --iofail` (8905 jobs), `lake exe mk_all --check`,
  `lake exe checkInitImports`, `lake exe lint-style Cslib`.
- Confirmed the final diff against the new merge base names exactly the four approved files.
- Wrote `pr-scaffolding.md`: verified factual dispositions for ctchou's four review bullets, the
  `IPL`-repurposing and five-API-removal itemization, the blast-radius safety argument, and the
  standing-approval record — explicitly marked as raw material, not text to paste.

## Decisions

- Followed the plan's "first-pass, full reconciliation later" strategy for `Defs.lean` conflict
  resolution during the rebase itself (Phase 2), deferring the actual §4.3 reconciliation to
  Phase 4 as designed.
- Kept the approved constructor order `atom, bot, imp, and, or` — did not reorder.
- Did not run `lake shake`, `lake lint`, or this fork's sorry-suppression/axiom-census ratchet
  steps as gates, per the plan's explicit scope: none of these are part of
  `upstream/main`'s actual PR CI (`.github/workflows/lean_action_ci.yml`), confirmed by re-reading
  that file on the rebased tree.
- Task terminates at `[COMPLETED]` rather than `[PR READY]`: `task_type` is `cslib`, whose
  standard terminus is `[IMPLEMENTING] -> [COMPLETED]`; `[PR READY]` is `type=pr` only.

## Plan Deviations

- **Toolchain/Mathlib target revised** (Phase 1): `upstream/main` had advanced past the
  plan-time `3951377e` to `4bec19fc` (a toolchain-bump-only commit) by the time implementation
  started. Target revised from `v4.33.0`/`db584cd6` to `v4.34.0-rc1`/`de5ce8a9`. Verified the new
  commit does not touch `Cslib/Logics/Propositional/` or `Cslib/Foundations/Logic/`, so no
  re-derivation of the research §4.3 reconciliation table was needed.
- **`references.bib` conflicted across three commits, not one** (Phase 2): research predicted a
  single conflict hunk; the actual rebase produced conflicts on 3 of the 6 PR commits, because
  upstream had independently converged on a near-identical bibliography-append pattern. Resolved
  mechanically at each point per the same "keep both blocks" rule; final state has no duplicate
  keys and matches the PR's own pre-rebase head exactly.
- **`NaturalDeduction/Theory.lean` fallout, not the predicted `Basic.lean` `Equiv` region**
  (Phase 5): the plan's known candidate for post-reconciliation fallout was the
  `Equiv := IPL.Equiv` region of `Basic.lean`, which in fact needed no change. Instead,
  `Theory.lean:55` (`IsClassical.pierce`) needed a one-line-to-three-line change (see What
  Changed). Documented in the plan's Phase 5 task notes with the diagnostic trail
  (`lean_multi_attempt` comparisons ruling out simpler fixes).

## Impacts

- `origin/feat/propositional-v2` (the live PR branch, head `4834be23`) and its standing approval
  from thomaskwaring are entirely untouched — all work is confined to the new local branch
  `rebase/pr648-upstream` in the dedicated worktree.
- Once pushed (a user action), this rebase directly discharges ctchou's coordination-with-#607
  request and clears the review-organizational grounds for the CHANGES_REQUESTED state; no new
  technical objection was introduced.
- This fork's `main` (116 files under `Cslib/Logics/Propositional/`) is unaffected — it was never
  a merge, cherry-pick, or conflict-resolution source, per the structural worktree isolation.

## Follow-ups

- **User**: push `rebase/pr648-upstream` to `origin/feat/propositional-v2` (or open a fresh
  branch), update the PR description using `pr-scaffolding.md` as raw material (human-authored
  prose only, including the mandatory CONTRIBUTING.md AI-tools disclosure), and re-request review
  from ctchou.
- **User decision needed**: exact wording of the re-review request (see `pr-scaffolding.md` §6).
- A separate, already-filed follow-up task (connective notation `infix` → `infixr`) is correctly
  sequenced to run *after* this rebase lands, so as not to pollute the approved diff.

## References

- `specs/620_rebase_pr648_clear_review/plans/01_rebase-pr648-clear-review.md`
- `specs/620_rebase_pr648_clear_review/reports/01_rebase-pr648-clear-review.md`
- `specs/620_rebase_pr648_clear_review/pr-scaffolding.md`
- Worktree: `/home/benjamin/Projects/cslib-pr648`, branch `rebase/pr648-upstream`
