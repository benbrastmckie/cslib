<!--
  Task 407 – Q3 follow-on: InitialBot witness
  Session: sess_1782817543_eee5ae_407
-->

# Summary: HasInitialBot Initial-Object Witness

## What was implemented

Introduced `HasInitialBot` as an explicit, first-class named witness for the categorical
initial-object universal property of the bottom element in a poset-viewed-as-category.
The implementation consists of three focused additions layered across existing algebra files.

### Files modified

1. `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/BotProperties.lean`
   - Updated `## Property Hierarchy` docstring to add a level 3 `HasInitialBot` entry between
     `HasLeastBot` and canonical bottom.
   - Updated `## Main Definitions` docstring to list the four new items.
   - Added `class HasInitialBot` with field `initialArrow : ∀ a, b ≤ a` — the universal arrow.
   - Added `instHasInitialBotOfHasLeastBot` — `HasLeastBot b` implies `HasInitialBot b`.
   - Added `hasInitialBot_himp_eq_top` — explosion soundness via the initial-object witness.
   - Added `algEvaluate_imp_bot_eq_top_of_initialBot` — evaluator-level parallel lemma.

2. `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianBot.lean`
   - Added new `/-! ## HasInitialBot Bridge Lemmas -/` section.
   - Added `brouwerianBotEvaluate_efq_eq_top_of_initialBot` — EFQ via `HasInitialBot.initialArrow`
     for the free-bot Brouwerian evaluator.
   - Added `pointedBrouwerianEvaluate_efq_eq_top_of_initialBot` — EFQ for
     `PointedBrouwerianEvaluate` via the initial-object chain.

3. `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean`
   - Updated `## Proof Strategy` docstring to replace the bare `bot_le` mention with an
     explicit description of the `HasInitialBot` instance chain.
   - Updated the `efq` case in `conjImpBot_pointedBrouwerian_axiom_sound` docstring.
   - Updated the `efq` proof case: replaced `exact bot_le` with `exact HasInitialBot.initialArrow _`
     and added a comment explaining the categorical reading.

### Design rationale

`HasInitialBot b` and `HasLeastBot b` are logically equivalent (both assert `∀ a, b ≤ a`),
but differ in conceptual emphasis:
- `HasLeastBot`: order-theoretic view (b is the least element).
- `HasInitialBot`: categorical view (b is an initial object in the poset-as-category).

The instance chain `instHasLeastBotOrderBot → instHasInitialBotOfHasLeastBot` allows all
`OrderBot` algebras to automatically discharge `HasInitialBot` goals. No CategoryTheory
imports are needed — the statement is purely order-theoretic.

## Verification

- `lake build Cslib.Logics.Propositional.Semantics.Algebra.BotProperties` — green (504 jobs)
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianBot` — green (589 jobs)
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerianCompleteness` — green (672 jobs)
- Full `lake build` — green for all targets except the pre-existing
  `Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` failure (confirmed
  pre-existing on clean HEAD via `git stash`; caused by a sorry in `Scheme.lean`, unrelated
  to this task).
- `lake lint` — no warnings in touched files.
- `lake exe lint-style` — no warnings in touched files.
- `lake shake` — no redundant imports in touched modules.
- `lake exe mk_all --module` — no update necessary (no new files added).
- `lake test` — fails only on the pre-existing Tableau target (same as clean HEAD).
- Zero sorries in touched files.
- Zero new axioms in touched files.

## Plan deviations

None. All four phases were completed as specified:
- Phase 1: `HasInitialBot` added to `BotProperties.lean` — completed.
- Phase 2: Bridge lemmas added to `BrouwerianBot.lean` — completed.
- Phase 3: `efq` case updated in `PointedBrouwerianCompleteness.lean` — completed.
- Phase 4: CI verification — completed (pre-existing failure isolated).

## Orchestrator handoff

```json
{
  "status": "implemented",
  "phases_completed": 4,
  "phases_total": 4,
  "what_was_added": {
    "BotProperties.lean": [
      "class HasInitialBot",
      "instHasInitialBotOfHasLeastBot",
      "hasInitialBot_himp_eq_top",
      "algEvaluate_imp_bot_eq_top_of_initialBot"
    ],
    "BrouwerianBot.lean": [
      "brouwerianBotEvaluate_efq_eq_top_of_initialBot",
      "pointedBrouwerianEvaluate_efq_eq_top_of_initialBot"
    ],
    "PointedBrouwerianCompleteness.lean": [
      "efq case: exact bot_le -> exact HasInitialBot.initialArrow _",
      "updated docstrings throughout"
    ]
  },
  "sorry_inventory": [],
  "blocker": null,
  "verification": {
    "verification_passed": true,
    "sorry_count": 0,
    "vacuous_count": 0,
    "axiom_count": 0,
    "build_passed": true,
    "pre_existing_failure": "Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness (sorry in Scheme.lean, pre-existing on clean HEAD)"
  }
}
```
