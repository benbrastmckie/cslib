# Implementation Summary: Task #319 (Resume)

- **Task**: 319 - Minimal propositional tableau soundness and completeness
- **Status**: PARTIAL (sorry-dependent as planned)
- **Date**: 2026-06-24
- **Session**: sess_1782295917_5c49e6

## What Was Done (This Session)

### Phase 3: Fix Completeness.lean compile errors [COMPLETED]

The previous agent had created `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
(198 lines) with 5 compile errors in the `minOpen_no_contradiction` lemma. These were all
fixed:

1. **Lines 110, 112**: `of_decide_eq_true` used where BEq-to-Eq conversion was needed for
   `Proposition Atom`. Fixed by using `proposition_beq_eq` from Soundness.lean. This required
   making `proposition_beq_eq` non-private in Soundness.lean.

2. **Lines 137, 142**: `simp only [beq_iff_eq]` and `simp only [beq_iff_eq]` made no progress.
   Fixed with:
   - Sign case: `exact hneg_sign_b ▸ beq_self_eq_true _`
   - Formula case: `rw [hpos_form_eq]; exact hneg_form_b`
   - Label case: `simp only [decide_eq_true_eq]; exact hneg_label_b.trans hpos_label_b.symm`

3. **Line 129**: Removed unused `forall_const` from simp call.

4. **Additional**: Renamed `minBotForces` to `minBranchBotForces` in Completeness.lean to
   avoid name conflict with `MinStrongCompleteness.lean`'s `minBotForces` (which is for the
   canonical world, not branch-based).

5. **Style fixes**: Fixed two lines exceeding 100-char limit.

### Phase 4: Refactor DecisionProcedure.lean [COMPLETED]

Replaced the sorry-bearing stubs in `DecisionProcedure.lean` with a clean import-based
structure. The new file:
- Imports `Cslib.Logics.Propositional.Tableau.Minimal.Completeness` (transitively provides
  Soundness, Expansion, Kripke)
- Removes `minBranchSatisfied` def (now in Soundness.lean)
- Removes sorry'd `minimalTableau_sound` and `minimalTableau_complete` stubs (now proved
  in dedicated modules, available via import)
- Keeps `minimalTableau_decides`, `instDecidableMValid`, `instDecidableDerivableMinPropAxiom`
- Reduced from ~135 lines to ~80 lines

Also ran `lake exe mk_all --module` to update barrel imports.

## Sorry Inventory

| Location | Sorry | Source | Status |
|----------|-------|--------|--------|
| `Soundness.lean:minimalTableau_sound` | Inherits from `intExpandBranches_closed_unsat` | Task 316 | Inherited, expected |
| `Completeness.lean:minTruthLemma` | Full proof | Deep saturation/persistence reasoning | Planned sorry, separate task |
| `Completeness.lean:minOpenBranch_countermodel` | Depends on minTruthLemma | Truth lemma sorry | Planned sorry |
| `Completeness.lean:minimalTableau_complete` | Depends on above | Counter model | Planned sorry |

## Build Status

- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness`: SUCCESS
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness`: SUCCESS (with planned sorries)
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure`: SUCCESS

## Files Modified

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`
  - Made `proposition_beq_eq` non-private (accessible to Completeness.lean)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
  - Fixed 5 compile errors in `minOpen_no_contradiction` 
  - Renamed `minBotForces` to `minBranchBotForces` to avoid name conflict
  - Fixed 2 long-line style violations
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
  - Refactored to import Completeness module, removed sorry stubs
- `Cslib.lean` - updated via `lake exe mk_all --module`

## Plan Deviations

- **minBotForces renamed**: The plan used `minBotForces` but `MinStrongCompleteness.lean` already
  defines a `minBotForces` for the canonical world model. Renamed to `minBranchBotForces` to
  avoid the environment conflict that would prevent importing both modules.

- **proposition_beq_eq visibility**: Made non-private rather than copying it to Completeness.lean.
  The docstring was updated to reflect it's now a shared helper.

## Remaining Work (Future Tasks)

- Prove `minTruthLemma` (truth lemma for the minimal tableau by formula induction)
- Prove `minOpenBranch_countermodel` (follows from truth lemma)
- Prove `minimalTableau_complete` (follows from countermodel)
- Prove `intExpandBranches_closed_unsat` (blocked in Task 316)
