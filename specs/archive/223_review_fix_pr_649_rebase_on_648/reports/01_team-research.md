# Research Report: Task #223

**Task**: Review and fix PR #649 (stacked on PR #648): resolve CI failure and rebase onto updated PR #648
**Date**: 2026-06-16
**Mode**: Team Research (4 teammates, standard mode)
**Completed**: 2026-06-16

## Executive Summary

- CI failure in PR #649 is caused by two theorems (`Proposition.instBot_eq`, `Proposition.instTop_eq`) in `Defs.lean` that auto-include the section variable `[DecidableEq Atom]` but don't use it; the `--wfail` flag (warnings-as-errors) in the Lean Action CI promotes these to hard build errors.
- The immediate minimal fix is 2 `omit [DecidableEq Atom] in` annotations or deletion of the two theorems; a full rebase onto updated PR #648 is the correct long-term approach but should be deferred until PR #648 is approved and PR #649's reviewer-requested code changes are complete.
- PR #649 has substantive open reviewer requests (remove `snce`, redesign `LTL.Satisfies` for LTS semantics, remove irrelevant typeclasses) that are independent of the CI fix and must be addressed before merge is possible.
- Rebasing now onto the unapproved PR #648 risks 5+ file merge conflicts, potential Lean elaboration errors (MPL/IPL/CPL API mismatch), and double-work if PR #648 changes again after ctchou's re-review.
- The recommended sequence is: fix CI now (minimal patch), address reviewer requests, then rebase cleanly once PR #648 is finalized.

## Key Findings

### CI Failure Root Cause

The failing target is `Cslib.Logics.Propositional.Defs` (job 81712989982). The build succeeds for 2733/2734 targets and fails on the last one. The exact cause: `Proposition.instBot_eq` and `Proposition.instTop_eq` (lines 106-111 of `Cslib/Logics/Propositional/Defs.lean` in PR #649's branch) are inside a `section` with `variable {Atom : Type u} [DecidableEq Atom]`. Lean auto-includes that section variable in the theorems because `Atom` appears in their types, but neither theorem's type actually uses `DecidableEq`. This triggers two warnings — `unusedSectionVars` and `unusedDecidableInType` — and the Lean Action CI's `--wfail` flag converts them to build failures.

The `--wfail` flag is added internally by `leanprover/lean-action@v1` (the workflow file only specifies `--iofail`). It was introduced into upstream/main with PR #536 on June 16. PR #649 was authored before that merge and its CI had passed at 05:28 that same day; after PR #536 merged at 08:40, the stricter warning policy caused PR #649's next CI run to fail.

PR #648's updated commit (`7cc09612`) does not contain `instBot_eq` or `instTop_eq` at all — they were removed. This is the root cause of the stacking divergence: PR #649 was not rebased to pick up PR #648's update.

### PR #648 Current State

- **Branch**: `feat/propositional-v2`
- **Head commit**: `7cc09612`
- **Review status**: `CHANGES_REQUESTED` from ctchou (submitted 2026-06-15) — PR #648 is NOT approved
- **What it does**: Adds `Cslib/Foundations/Logic/Connectives.lean` with propositional typeclass hierarchy (`HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`); refactors `Defs.lean` to use primitive `bot`, renames `impl`→`imp`, removes `[Bot Atom]` constraints, uses `Set.range`-based IPL/CPL definitions, adds `Avigad2022` as the sole reference
- **Key fact**: PR #648's `Defs.lean` does NOT contain `instBot_eq` or `instTop_eq`
- ctchou has not re-reviewed after the `7cc09612` update; PR #648 remains in `CHANGES_REQUESTED` state

### PR #649 Current State

- **Branch**: `feat/temporal-formula-propositional`
- **Head commit**: `5785ebbd` (3 commits total)
- **Review status**: `CHANGES_REQUESTED` from ctchou
- **What it does**: Extends `Connectives.lean` with temporal typeclasses; adds `Temporal.Formula` (5 primitives including `snce`), `LTL.Formula`, `LTL.Satisfies` over omega-words
- **Substantive reviewer requests (not addressed by CI fix or rebase)**:
  1. Remove past-time operators — `snce` (since) is still present in `Temporal.Formula`
  2. Redesign `LTL.Satisfies` to use LTS-based semantics, not omega-word `ℕ → (Atom → Prop)` sequences
  3. Remove irrelevant typeclasses: `Encodable`/`Countable`/`Infinite`/`Denumerable`

### Stacking Relationship

Both PRs diverge from the same upstream ancestor `70c5bf58` (the PR #536 merge commit). They are parallel branches, NOT a true stack (PR #649's base is NOT PR #648's head):

```
upstream/main (70c5bf58)
  ├── feat/propositional-v2:  70c5bf58 → 7cc09612  [PR #648]
  └── feat/temporal-...:      70c5bf58 → 5700fedb → 0afc9d6c → 5785ebbd  [PR #649]
```

After a correct rebase, PR #649 should be:
```
70c5bf58 → 7cc09612 → [temporal-only commits]
```

PR #649 contains a superset of PR #648's changes to shared files — it includes its own copies of `Defs.lean`, `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`, and `Connectives.lean`. This is why the rebase will produce conflicts in 5+ files.

## Synthesis

### Points of Agreement

All four teammates agree on the following:

1. **Root cause is unambiguous**: The two `instBot_eq`/`instTop_eq` theorems in `Defs.lean` trigger unused section variable warnings, which `--wfail` promotes to errors. Confidence: HIGH across all teammates.

2. **The minimal fix is safe**: Adding `omit [DecidableEq Atom] in` before each theorem, or deleting both theorems outright, immediately unblocks CI with minimal risk. The temporal files (`Temporal/Formula.lean`, `LTL/Formula.lean`, `LTL/Satisfies.lean`) use `.bot` constructor syntax directly and do not rely on `instBot_eq`/`instTop_eq` for proof goals.

3. **Rebase is ultimately necessary**: For clean git history and proper stacking, PR #649 must eventually be rebased onto PR #648's head so its temporal-unique commits sit on top cleanly.

4. **PR #648 is the correct long-term base**: PR #648's changes are foundational (Foundations/Logic/Connectives, primitive bot refactor) and PR #649 should layer on top.

5. **Force-push with lease is acceptable**: The repo's pattern (PR #648 was itself rebased with force-push) accepts this workflow.

### Conflicts Resolved

**Core Conflict: Rebase now vs. fix-first-then-rebase-later**

Teammates A and D recommend rebasing PR #649 onto updated PR #648 immediately as the primary fix. Teammate B recommends the same as the long-term approach but suggests the immediate minimal fix first. Teammate C (the Critic) explicitly recommends NOT rebasing now.

**Resolution: Teammate C's position is stronger. Defer full rebase; fix CI now with minimal patch.**

Reasoning:
1. **PR #648 is unapproved** (ctchou `CHANGES_REQUESTED` as of 2026-06-15, no re-review after `7cc09612`). Rebasing PR #649 onto an unapproved moving target risks double-work when PR #648 changes again.
2. **Conflict risk is high**: 5 files have overlapping edits (Defs.lean, Basic.lean, Theory.lean, Connectives.lean, references.bib). Teammate C identified specific Lean elaboration risks post-rebase: `(MPL Atom)` vs `MPL : Theory Atom` style mismatch, `instIsIntuitionisticIntuitionisticCompletion` silently dropped if conflict resolution picks PR #649's Theory.lean version.
3. **Reviewer requests are independent and substantial**: Removing `snce`, redesigning `LTL.Satisfies`, removing irrelevant typeclasses — these changes modify the exact files that will conflict during rebase. Doing them before rebasing reduces the conflict surface significantly.
4. **The minimal fix is trivial**: 2 `omit` annotations (or 2 theorem deletions) unblock CI immediately at near-zero risk.
5. **Rebase will be cleaner after reviewer requests are addressed**: Once `snce` is removed and `LTL.Satisfies` is redesigned, PR #649's commits will have smaller overlap with PR #648.

Teammate A's recommendation to rebase now is based on the assumption that the rebase cleanly removes the failing theorems and no other changes are needed. Teammate C's analysis shows this assumption is incomplete — the rebase would introduce new Lean elaboration errors requiring additional debugging.

**Secondary Conflict: Delete theorems vs. `omit` annotation**

Teammate A recommends `omit` annotation as Option B (workaround). Teammate B recommends either `omit` (Strategy B) or direct deletion (Strategy D), with deletion being cleaner since PR #648 doesn't have them. Teammate C endorses `omit` as low-risk.

**Resolution: Delete the theorems directly.** PR #648's updated `Defs.lean` does not have them; they serve no purpose in PR #649's codebase (temporal files use `.bot` directly). Deleting them aligns PR #649 with the direction PR #648 established and avoids adding `omit` scaffolding that will disappear after the eventual rebase anyway.

### Coverage Gaps

1. **ctchou's exact PR #648 review comments**: All teammates confirmed the `CHANGES_REQUESTED` status but did not retrieve the exact text of ctchou's PR #648 review. The precise changes ctchou requires in PR #648 affect how soon PR #648 can be used as a stable rebase target.

2. **PR #607 (fmontesi HasImpl/impl) overlap**: Teammate D identified this as a potential naming conflict with PR #648's `HasImp`/`imp`. None of the teammates investigated the exact overlap or whether it blocks PR #648 landing.

3. **PR #413 (mell-o-tron LTL) coordination**: Teammate D flagged this as a concern (overlapping LTL formalization). Not investigated further — this is a social/coordination issue that may require maintainer input.

4. **`instBot_eq`/`instTop_eq` full downstream grep**: Teammate A said removal is "likely safe" based on 3 new files. Teammate C flagged this should be verified against ALL downstream imports. A `grep -r "instBot_eq\|instTop_eq" Cslib/` should be run to confirm no other files rely on these lemmas.

### Recommended Approach

**Phase 1 — Immediate CI fix (do now, low risk):**

1. Verify no downstream usage of `instBot_eq`/`instTop_eq`:
   ```bash
   grep -r "instBot_eq\|instTop_eq" /home/benjamin/Projects/cslib/Cslib/
   ```
2. Delete both theorems from `Cslib/Logics/Propositional/Defs.lean` (lines ~106-111):
   ```lean
   -- DELETE these two theorems:
   @[simp, grind =]
   theorem Proposition.instBot_eq : (⊥ : Proposition Atom) = Proposition.bot := rfl

   @[simp, grind =]
   theorem Proposition.instTop_eq : (⊤ : Proposition Atom) = Proposition.top := rfl
   ```
3. Run `lake build` locally to verify the fix.
4. Push to `feat/temporal-formula-propositional` with `--force-with-lease` (since this modifies existing commits... or add a new commit on top — either is acceptable).

**Phase 2 — Address reviewer requests (before rebase):**

1. Remove `snce` (since) from `Temporal.Formula` — reviewer explicitly said "future-time operators only"
2. Redesign `LTL.Satisfies` to use LTS-based semantics (or remove it entirely and defer to a follow-up PR as the reviewer implied)
3. Remove `Encodable`/`Countable`/`Infinite`/`Denumerable` instances flagged as "completely irrelevant"
4. Push changes and request re-review from ctchou

**Phase 3 — Rebase (after PR #648 is approved and Phase 2 is done):**

1. Wait for ctchou to re-review and approve PR #648
2. Once PR #648 is in `APPROVED` or `MERGED` state:
   ```bash
   git checkout feat/temporal-formula-propositional
   git rebase feat/propositional-v2
   ```
3. Resolve conflicts per file (see conflict table below for guidance):
   - `Defs.lean`: Take PR #648's version as base; drop `instBot_eq`/`instTop_eq` (already done in Phase 1); optionally preserve Architecture docblock from PR #649
   - `Connectives.lean`: Take PR #648's 71-line version as base; add temporal typeclasses (`HasUntil`, `HasNext`, temporal bundles) from PR #649 on top
   - `NaturalDeduction/Theory.lean`: Keep PR #648's version (which has `instIsIntuitionisticIntuitionisticCompletion`); verify PR #649's changes don't drop it
   - `NaturalDeduction/Basic.lean`: Verify `(MPL Atom)` vs `MPL : Theory Atom` style is consistent with Defs.lean after rebase
   - `references.bib`: Include `Avigad2022` from PR #648 plus temporal refs from PR #649
4. Run `lake build` and CI pipeline locally before pushing
5. Force-push with `--force-with-lease`

**Key conflict resolution guidance for Phase 3:**

| File | Resolution Strategy |
|------|---------------------|
| `Defs.lean` | Use PR #648's version as truth; verify no PR #649-unique content is needed |
| `Connectives.lean` | PR #648 as base; add temporal classes from PR #649 (`HasUntil`, `HasSince`→dropped, `HasNext`, bundles) |
| `NaturalDeduction/Basic.lean` | Keep `instIsIntuitionisticIntuitionisticCompletion`; use `IPL (Atom := Atom)` style from PR #648 |
| `NaturalDeduction/Theory.lean` | Careful: PR #648 adds new instance that PR #649 lacks; do not drop it |
| `references.bib` | Include Avigad2022 (PR #648) + all temporal refs (PR #649) |
| `Cslib.lean` | PR #648's Connectives import position + PR #649's 3 temporal imports |

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary — PR details, CI failure analysis, recommended fix | completed | high |
| B | Alternatives — branch topology, CI pipeline, all 4 fix strategies | completed | high |
| C | Critic — risks, conflict analysis, reviewer status, recommendation divergence | completed | high |
| D | Horizons — strategic context, downstream dependencies, stacking patterns | completed | high (root cause), medium (reviewer timeline) |

## References

- CI run: https://github.com/leanprover/cslib/actions/runs/27633080931/job/81712989982?pr=649
- PR #648: `feat/propositional-v2`, head `7cc09612`
- PR #649: `feat/temporal-formula-propositional`, head `5785ebbd`
- Common base: `70c5bf58` (PR #536 merge into upstream/main)
- Related: PR #607 (fmontesi HasImpl), PR #413 (mell-o-tron LTL), PR #587 (thomaskwaring Models)
- CSLib ROADMAP.md — Temporal module dependency structure
- Tasks 39, 40 (discrete/continuous temporal completeness), 180, 181 (downstream of PR #649)
