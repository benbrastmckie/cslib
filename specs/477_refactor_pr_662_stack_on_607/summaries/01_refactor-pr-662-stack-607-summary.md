# Implementation Summary: Refactor PR #662 to Stack on PR #607 (box + diamond both primitive)

- **Task**: 477 - Refactor PR #662 (leanprover/cslib) to stack on PR #607 so both □ (box) and ◇
  (dia) are primitive modal connectives
- **Status**: [PARTIAL]
- **Started**: 2026-07-12T18:26:12Z
- **Completed**: 2026-07-12T20:10:00Z
- **Artifacts**: plans/01_refactor-pr-662-stack-607.md

## Overview

Reworked PR #662's modal-primitives contribution to stack on PR #607, making both `□` and `◇`
primitive `Proposition` constructors (`{atom, not, and, diamond, box}`) instead of deriving either.
Work was done on a new local branch `task-477-pr662-stack-607` (built from `pr607`) in a dedicated
git worktree, not on `main` — `main` has diverged far past both `pr607` and
`feat/modal-formula-primitives` with unrelated local-only Tableau/Metalogic/ProofSystem
development, so it was the wrong base and was left untouched. All 5 of the plan's box-primitive
Modal phases (1-4, plus the Modal-scoped parts of 5) are complete and verified green; Phase 5's
whole-library CI gate is blocked by a pre-existing, out-of-scope defect discovered in PR #607's
own `HML/LogicalEquivalence.lean` (unrelated to Modal/#662). Phase 6 (docs-only coordination note)
is complete.

## What Changed

Branch `task-477-pr662-stack-607` (based on `pr607`), worktree
`/home/benjamin/Projects/cslib-task-477-pr662-stack-607`:

- `Cslib/Logics/Modal/Basic.lean` (+63/-17, net +46): added `box` as a 5th primitive
  `Proposition` constructor; removed the old derived `Proposition.box := ¬◇¬φ` definition;
  `Satisfies` gained a primitive `.box φ => ∀ w', m.r w w' → Satisfies m w' φ` clause;
  `Satisfies.box_iff_forall` reduced from a `grind`-proved lemma to `Iff.rfl`; `Satisfies.dual`
  (`◇φ ↔ ¬□¬φ`) reworked into a genuine classical proof (`simp only [...]` unfolding + explicit
  `constructor`/`by_contra`/`push Not`), since it is no longer true by definition; added the
  optional companion `Satisfies.box_iff_not_diamond_not : □φ ↔ ¬◇¬φ`; added a short module-
  docstring paragraph motivating the both-primitive design, citing `[Blackburn2001]` and the new
  `[ChagrovZakharyaschev1997]`.
- `Cslib/Logics/Modal/Denotation.lean` (+1): added the `box` clause
  `{w | ∀ w', m.r w w' → w' ∈ φ.denotation m}` to `Proposition.denotation`; all existing
  characterisation proofs (`satisfies_mem_denotation`, `not_denotation`, `theoryEq_denotation_eq`)
  closed unchanged via their existing `induction ... <;> grind`.
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (+9): added a `box` `Proposition.Context`
  constructor, its `fill` clause, and a matching `Congruence` induction arm (mirroring `diamond`'s
  arm with `∀`/`intro` instead of `∃`/`rintro`). The `HasLogicalEquivalence` framework instance
  required **no migration** — it was already present on `pr607`.
- `references.bib` (+10): added `ChagrovZakharyaschev1997` (box-first presentation). Did not add
  `Avigad2022` (not needed; no Łukasiewicz-encoding note applies under the not/and propositional
  base kept from #607).
- `Cslib.lean`, `Cslib/Logics/Modal/Cube.lean`, `CslibTests/GrindLint.lean`,
  `Cslib/Foundations/Logic/Connectives.lean`: **no changes** — none were needed on the `pr607`
  base (see Decisions below).

**Net LOC**: +66/-17 = **+49 lines**, well under the 500-LOC target and the plan's own ~80-140
estimate.

## Decisions

- **Worked on a dedicated branch/worktree, not `main`**: `main`'s `Connectives.lean` is a 34-file,
  4-logic-module (Propositional/Modal/Temporal-LTL/Bimodal) shared foundation built by many later,
  unrelated local tasks — deleting it as Phase 1 literally instructs would have been a massive,
  out-of-scope blocker. The real upstream GitHub PR #662 (mirrored locally by branch
  `feat/modal-formula-primitives`) only ever touched `Connectives.lean` and `Modal/Basic.lean`, so
  `main`'s divergence is a local-development-only artifact, not part of the actual PR scope.
  Created `git branch task-477-pr662-stack-607 pr607` +
  `git worktree add /home/benjamin/Projects/cslib-task-477-pr662-stack-607 ...` instead.
- **Phase 1 required zero edits**: `pr607` never contained `Connectives.lean` in the first place
  (confirmed via `git show pr607:...` -> not found); it already uses the split
  `Operators/{And,Box,Diamond,Iff,Impl,Not,Or,Tensor}.lean` files described in the research report
  as a single `Operators.lean` (a minor report inaccuracy — the file is split, not monolithic).
- **Phase 4's `HasLogicalEquivalence` migration was already done upstream**: contrary to the
  research report §3 ("#607 does not touch `Modal/LogicalEquivalence.lean`"), the verified `pr607`
  tip already has `instance : HasLogicalEquivalence (Proposition Atom) (Judgement World Atom)`.
  Only the `box` `Context` case needed adding.
- **`Satisfies.dual`'s proof needed rework, not just a name change**: with both `□`/`◇` primitive,
  `constructor <;> grind` alone did not close the goal (quantifier duality over `∃`/`∀¬` needs
  explicit classical reasoning). Used `simp only [iff_iff_iff, diamond_iff_exists, not_iff_not,
  box_iff_forall]` to reduce to the meta-level statement, then an explicit `constructor` with
  `by_contra`/`push Not` (the codebase's preferred non-deprecated negation-pushing tactic, in
  place of the deprecated `push_neg`) for the classical backward direction.
- **Did not attempt to fix the pre-existing HML defect**: touching
  `Cslib/Logics/HML/LogicalEquivalence.lean` is explicitly out of the plan's declared Non-Goals
  ("Modifying downstream consumers beyond what the both-primitive [Modal] change requires") and
  is a different PR's (#607's) own unrelated bug, not something task 477 introduced or is
  chartered to fix.

## Impacts

- The Modal-logic box+diamond-both-primitive refactor is complete, builds green in isolation, has
  zero `sorry` and zero new axioms, and is ready to serve as the reference diff for `/pr`'s later
  stacking of `feat/modal-formula-primitives` (#662) onto `fmontesi/connectives` (#607).
- A previously-unknown, pre-existing defect in PR #607's own `HML/LogicalEquivalence.lean` was
  discovered: it still instantiates the old 3-arg `LogicalEquivalence` class against #607's own
  updated 4-arg signature, which fails to typecheck. This blocks `lake exe checkInitImports`,
  `lake shake`, and `lake test` for the **entire** library on the `pr607` tip, independent of
  anything in task 477. This should be raised with fmontesi as a blocker for #607 itself landing
  in a CI-green state — separate from, and prior to, any #662 stacking concern.
- No changes were made to `main`, `specs/`, or any other in-flight task's work.

## Follow-ups

- **Owner: fmontesi (or a dedicated follow-up task)** — fix
  `Cslib/Logics/HML/LogicalEquivalence.lean`'s instance to the new 4-arg
  `LogicalEquivalence`/`HasLogicalEquivalence` API (mirroring what #607 already did correctly for
  `Modal/LogicalEquivalence.lean` and CLL). Until this lands, whole-library `lake
  build`/`checkInitImports`/`shake`/`test` cannot succeed on `pr607`.
- **Owner: whoever resolves the above** — re-run `#grind_lint check` (via `lake test`'s
  `CslibTests.GrindLint`) once the HML blocker is fixed, to empirically confirm no
  `#grind_lint skip` entry is needed for the new `Proposition.box_def` lemma (reasoned by analogy
  to the unskipped `not_def`/`and_def`/`diamond_def` here, but not run to completion).
- **Owner: `/pr`** — when preparing the real submission, rebase `feat/modal-formula-primitives`
  (#662) onto `fmontesi/connectives` directly (not `main`), using this task's 3-file + bib diff as
  the reference patch for the Modal-specific portion.

## References

- specs/477_refactor_pr_662_stack_on_607/plans/01_refactor-pr-662-stack-607.md
- specs/477_refactor_pr_662_stack_on_607/reports/01_refactor-pr-662-stack-607.md
- specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md
- Local branch `task-477-pr662-stack-607` (based on `pr607`), worktree
  `/home/benjamin/Projects/cslib-task-477-pr662-stack-607`
