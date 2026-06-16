# Teammate D Findings: Strategic Context for PRs 648 and 649

**Task**: 223 — Review and fix PR #649 (stacked on PR #648): resolve CI failure and rebase
**Role**: Horizons researcher — strategic context, long-term implications, PR stacking patterns
**Date**: 2026-06-16

---

## Key Findings

### CI Failure Root Cause

The CI failure for PR #649 (run 27633080931, job 81712989982) is **two warnings promoted to errors** by the `--wfail` build flag. The warnings appear in `Cslib/Logics/Propositional/Defs.lean` at lines 107 and 110:

```
warning: Defs.lean:107: automatically included section variable(s) unused in theorem `instBot_eq`
warning: Defs.lean:110: automatically included section variable(s) unused in theorem `instTop_eq`
```

The theorems `Proposition.instBot_eq` and `Proposition.instTop_eq` are inside a `section` with `variable {Atom : Type u} [DecidableEq Atom]`, but the theorem types are just `rfl` equalities on typeclass instances that don't use `[DecidableEq Atom]`. Lean 4 auto-includes section variables in theorems that mention affected types, but when the included variable is not needed in the theorem type, it generates this warning. With `--wfail`, this becomes a build failure.

**PR #648 does not have these theorems** — they were introduced by PR #649's version of `Defs.lean`. The fix is narrow: either move the theorems outside the section, or annotate them to explicitly exclude the unused variable.

### The Stacking Structure

PR #649 is stacked on PR #648 but **diverges from a shared ancestor** rather than being based on PR #648's head:

- **Common ancestor**: `70c5bf58` — commit for PR #536 (classical/intuitionistic inference systems)
- **PR #648 head**: `7cc09612` — single commit adding five-primitive Proposition with primitive bot
- **PR #649 head**: `5785ebbd` — three commits adding temporal formula types and LTL

PR #649 includes its **own copy** of `Connectives.lean` (116 lines, with temporal typeclasses) while PR #648 has a shorter version (71 lines, propositional only). When CI runs for PR #649, it tests the branch against upstream `main` — but upstream `main` currently ends at `70c5bf58` (PR #536). PR #649's branch does include `Connectives.lean` in its own commits so that dependency is satisfied; the issue is purely the warnings-as-errors in `Defs.lean`.

**Timeline**:
- June 15: PR #649 commits authored
- June 16 05:28: PR #649 CI passes (upstream main was at an earlier state)
- June 16 08:40: PR #536 merges into upstream main; `--wfail` flag activates (introduced with #536)
- June 16 12:53: PR #648 pushed (author adapts for #536)
- June 16 16:38: PR #649 CI fails — `--wfail` treats warnings as errors

---

## Strategic Context

### What These PRs Accomplish for the Project

The ROADMAP.md describes an ongoing effort to extract BimodalLogic repository content into four CSLib modules: Foundations/Logic, Modal, Temporal, and Bimodal. The dependency structure (from the mermaid diagram in ROADMAP.md) places Temporal and Modal as peers that both import from Propositional/Foundations:

```
Foundations/Logic (Connectives, ProofSystem)
         │
    Propositional (Defs, NaturalDeduction)
    ╱                 ╲
Modal                  Temporal
    ╲                  ╱
         Bimodal
```

**PR #648** establishes `Cslib.Foundations.Logic.Connectives` — a typeclass hierarchy (`HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`) that enables polymorphic axiom definitions. It also refactors `Proposition` to have primitive `bot`, eliminating `[Bot Atom]` constraints throughout the propositional API. This is foundational: every downstream module (Modal, Temporal, Bimodal) eventually imports from Foundations.

**PR #649** builds directly on #648's infrastructure:
- Extends `Connectives.lean` with temporal typeclasses (`HasUntil`, `HasSince`, `HasNext`, `FutureTemporalConnectives`, `LTLConnectives`, `TemporalConnectives`)
- Introduces `Temporal.Formula` (5 primitives: atom, bot, imp, untl, snce) with derived propositional and temporal operators
- Introduces `LTL.Formula` (5 primitives: atom, bot, imp, next, untl) with embedding into `Temporal.Formula`
- Provides `LTL.Satisfies` over omega-words

Together, these two PRs establish the syntax layer for both LTL and full tense logic — the prerequisite for semantics, proof systems, and metalogic in the Temporal module.

### The Broader Arc: From Syntax to Completeness

The ROADMAP.md shows that temporal completeness is the remaining major goal. Once PRs 648 and 649 land:
- Temporal semantics (deferred from 649 per reviewer request) needs a follow-up PR
- The existing Temporal metalogic (chronicle completeness pipeline) in `Logics/Temporal/Metalogic/` needs to be reconciled with the new formula types from 649
- Dense temporal completeness remains to be ported; discrete and continuous temporal completeness are still open

Tasks 39 and 40 in TODO.md target discrete and continuous temporal completeness respectively — both are currently blocked waiting on the upstream temporal module stabilization.

---

## Related Work and Dependencies

### Immediate Upstream Coordination

**PR #607** (fmontesi, OPEN): Adds `HasImpl`/`impl` typeclass in a different file hierarchy. PR #648 adds `HasImp`/`imp` in `Foundations/Logic/Connectives.lean`. These are different classes doing similar things. The research from task 222 identified this as a naming conflict that is currently unresolved — both PRs are open simultaneously. If #607 merges before #648/#649, there will be a naming tension in the codebase.

**PR #587** (thomaskwaring, DRAFT): Models typeclass framework. Thomaskwaring has requested that semantics be split to a separate PR, partly to coordinate with his framework. PR #649 defers `LTL.Satisfies` but includes the satisfaction relation — a reviewer may ask for this to be removed too.

**PR #413** (mell-o-tron, OPEN, CHANGES_REQUESTED): Separate LTL formalization. This PR introduces LTL independently and overlaps directly with PR #649's `LTL.Formula` and `LTL.Satisfies`. Ctchou has already requested changes. If PR #649 lands first with the stronger formalization, #413 may need to be closed or substantially revised.

**PR #536** (merged, June 16): Refactored `IsIntuitionistic`/`IsClassical` to use `InferenceSystem` parameters. PR #648 was adapted for this. PR #649 was NOT yet adapted when its CI failed — the divergence from `70c5bf58` means PR #649 predates the #536 integration.

### Downstream Dependencies

**Task 180**: Add `allFuture` (G) and `allPast` (H) as primitive constructors to `Temporal.Formula` — currently `[NOT STARTED]`, blocked until PR #649's formula type is stable.

**Task 181**: Propagate primitive diamond/allFuture/allPast to Bimodal layer — depends on task 180, which depends on PR #649.

**Task 219**: Address PR #648 review from ctchou about merging semantics files — `[PLANNED]`, downstream of PR #648 landing.

**Tasks 39, 40**: Discrete and continuous temporal completeness — blocked on temporal module stabilization.

---

## Long-term Implications

### For the Project

**Good**: The typeclass hierarchy (`PropositionalConnectives` → `FutureTemporalConnectives` → `LTLConnectives`/`TemporalConnectives`) is a well-designed polymorphism layer. It allows future code to be generic over formula types — LTL vs. full temporal vs. modal vs. bimodal. This investment pays off when writing axiom systems and proof systems that should work uniformly.

**Risk — Semantics deferral creates orphan risk**: The `LTL.Satisfies` module was included in PR #649 then may be asked out again (ctchou's review requests semantics over LTS transitions, not just omega-words). If semantics land in a separate PR but no one follows up, the syntax infrastructure exists without semantics for an extended time. A task should be created explicitly for "LTL semantics follow-up PR."

**Risk — PR #407 tension**: PR #413 (mell-o-tron's LTL) has been open since March 2026. If CSLib maintainers prefer that author's version or want to merge it alongside #649, there will be a design choice to make. #649's design is more architecturally sophisticated (typeclass hierarchy, embedding into Temporal.Formula) but #413 has seniority.

**Risk — instBot_eq/instTop_eq theorems**: These theorems were added in PR #649 without the equivalent in PR #648. When PR #649 is rebased onto PR #648, these theorems need to go somewhere. If they're kept in PR #649, the unused variable warning must be resolved. The simplest fix is to either use `@[simp] theorem Proposition.instBot_eq : (⊥ : Proposition Atom) = .bot := rfl` moved outside the section, or annotated with `{Atom : Type u}` without `[DecidableEq Atom]`.

### For PR Stacking Strategy

The current approach — where PR #649 contains a superset of PR #648's changes — has both advantages and problems:

**Advantage**: PR #649 is self-contained; reviewers can see the full picture without needing PR #648 to be merged.

**Problem**: When PR #648 evolves (as it did — the author adapted it significantly for reviewer feedback and PR #536), PR #649 must manually track those changes and sync. The divergence from a shared ancestor (`70c5bf58`) rather than being based on PR #648's head (`7cc09612`) means PR #649 did NOT automatically pick up PR #648's updates.

**The rebase task**: To fix this, PR #649's branch needs to be rebased so its temporal-only commits sit on top of PR #648's head. Currently:
- PR #648: `70c5bf58` → `7cc09612`
- PR #649: `70c5bf58` → `5700fedb` → `0afc9d6c` → `5785ebbd`

After rebase, PR #649 should be: `70c5bf58` → `7cc09612` → [temporal-only commits]

The key challenge is that PR #649's commits include changes to `Connectives.lean`, `Defs.lean`, `NaturalDeduction/Basic.lean`, and `NaturalDeduction/Theory.lean` — all of which PR #648 also modifies. These will conflict and need careful resolution.

**Precedent being set**: If this rebase goes well, it establishes a pattern for future stacked PRs in this codebase (temporal → bimodal, etc.). The recommended approach going forward:
1. Create the base PR with minimal scope
2. Keep the stacked PR's commits focused on *additions only* — do not duplicate base PR's changes
3. Use `git rebase --onto` when the base PR is updated, rather than manually syncing

---

## Recommendations for PR Stacking Strategy

1. **Immediate fix (task 223)**: Rebase `feat/temporal-formula-propositional` onto `feat/propositional-v2` head (`7cc09612`). The three temporal-only commits (`5700fedb`, `0afc9d6c`, `5785ebbd`) will need conflict resolution since they modify files PR #648 also modifies. After rebase, fix the `instBot_eq`/`instTop_eq` unused variable warning in `Defs.lean`.

2. **Drop or fix `LTL.Satisfies`**: Ctchou has requested semantics over LTS transitions, not just omega-words. The current `LTL.Satisfies` may need to be dropped from this PR or substantially revised. If dropped, create a follow-up task immediately.

3. **Update `Connectives.lean` to use #648's version as base**: After rebase, the merged `Connectives.lean` should be PR #648's 71-line version (propositional only) extended with PR #649's temporal additions (HasUntil, HasSince, HasNext, etc.). The docstring references in the file should use English-language references (not the German ones that PR #649's version still has from the original).

4. **Going forward — reduce overlap in stacked PRs**: Future stacked PRs should only include files that the parent PR does NOT touch. When a file is modified by both parent and child, the child's version must be kept in sync manually — this is the maintenance burden that caused the current CI failure.

5. **Consider the LTL overlap with PR #413**: Before PR #649 goes further in review, the maintainers should be asked whether PR #413 should be closed in favor of #649's more comprehensive approach. This is a social/coordination issue but has technical implications.

---

## Confidence Level

**High** on:
- Root cause of CI failure (warnings-as-errors in Defs.lean lines 107+110)
- Branch structure and rebase requirements
- Strategic importance of PRs 648+649 to the broader temporal logic roadmap
- Downstream dependency chain (180 → 181 → temporal metalogic)

**Medium** on:
- Whether reviewers (ctchou, thomaskwaring) will accept the current semantics scope in PR #649
- Whether PR #413 creates a coordination problem that will require deliberate resolution
- Whether the HasImp vs HasImpl naming conflict with PR #607 will become a blocker

**Low** on:
- Whether PR #536's `--wfail` flag was intentionally introduced to catch exactly this class of warning (the timing suggests it may have been inadvertent for PR #649)
- Exact timeline for when PR #648 will be reviewed/approved (ctchou's CHANGES_REQUESTED has not been resolved yet)
