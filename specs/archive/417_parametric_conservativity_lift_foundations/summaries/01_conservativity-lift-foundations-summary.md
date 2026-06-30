# Implementation Summary: Task #417 — Parametric Conservativity Lift into Foundations

- **Task**: 417 - Parametric conservativity lift into Foundations
- **Status**: IMPLEMENTED
- **Date**: 2026-06-29
- **CI**: All green (build, checkInitImports, lint-style, lake shake, test)
- **Proof Debt**: 0 new sorry / 0 new axioms

## What Was Done

### Phase 1: Generic Foundations module (COMPLETED)

Created `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean`
with two generic declarations:

- `evaluate_iff_of_classicalBridge`: Abstract bridge lemma. Takes `emb : PL.Proposition Atom → Tgt`,
  `sat : Tgt → Prop`, `v : Atom → Prop`, and five per-connective compatibility `Iff`/`¬`
  hypotheses. Proves `∀ ψ, sat (emb ψ) ↔ PL.Evaluate v ψ` by structural induction.
  Proof bodies transcribed verbatim from the three existing copy-equal bridge lemmas.

- `conservative_over_cpl`: Parametric conservativity wrapper. Takes a valuation-parameterized
  bridge and a per-logic satisfaction callback from soundness. Derives `Derivable PropositionalAxiom φ`
  via `prop_completeness` in three lines.

Both declarations are in namespace `Cslib.Logic`, with snake_case names (correct for theorems).
Module includes docstring noting the deliberate Foundations → Logics layering exception with
DiegoEmbedding.lean:15-16 as precedent.

File added to `Cslib.lean` aggregator at line 86.

### Phase 2: Temporal instance (COMPLETED)

Re-expressed `Temporal/ConservativeExtension.lean`:
- `temporal_satisfies_toTemporal_iff_evaluate`: replaced inductive body with a single call to
  `evaluate_iff_of_classicalBridge` with all five `h_*` as `Iff.rfl` / `id`.
- `temporal_conservative_extension`: replaced body with `conservative_over_cpl` using
  `TemporalModel.constant v` and `soundness_thderivable` (per-logic content preserved).

### Phase 3: Bimodal instance (COMPLETED)

Re-expressed `Bimodal/.../PropositionalConservativity.lean`:
- `bimodal_truthAt_toBimodal_iff_evaluate`: replaced inductive body with call to
  `evaluate_iff_of_classicalBridge`. The one non-rfl hypothesis is `h_atom`, supplied as
  the existential-collapse term `⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩` (verbatim
  from the original proof at line 73).
- `bimodal_conservative_extension`: replaced body with `conservative_over_cpl` using the
  existing trivial-frame setup and `soundness` call (per-logic content preserved).

### Phase 4: Optional Modal re-home (SKIPPED)

The Modal `ConservativeExtension.lean` was not modified. `modal_conservative_extension_param`
remains as-is. Rationale: the 15 `Systems/*/ConservativeExtension.lean` callers are untouched;
the Modal re-home would add complexity without functional benefit at this stage. The task's
definition of done (Temporal + Bimodal re-expressed, CI green) is met without it.

### Phase 5: CI Verification (COMPLETED)

All CI steps passed:
- `lake build Cslib.Foundations.Logic.Metalogic.ConservativityLift` — green
- `lake build Cslib.Logics.Temporal.ConservativeExtension` — green
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.PropositionalConservativity` — green
- `lake exe checkInitImports` — green (no output = pass)
- `lake exe lint-style` — green (no output = pass)
- `lake lint` — no warnings on new/modified files
- `lake shake --add-public --keep-implied --keep-prefix` — no warnings on new/modified files
  (pre-existing shake warnings in Temporal/Tableau/Closure.lean etc. are unrelated)
- `lake test` — exit code 0; 4 sorry warnings all in pre-existing Tableau files
- 0 new sorry in new/modified files
- 0 new axioms in new/modified files

## Plan Deviations

| Phase | Deviation |
|-------|-----------|
| Phase 4 (Modal re-home) | Skipped — decision to leave Modal as-is, preserving 15 Systems callers |

## Files Modified

- **New**: `Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean`
- **Modified**: `Cslib/Logics/Temporal/ConservativeExtension.lean`
- **Modified**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`
- **Modified**: `Cslib.lean` (aggregator, line 86)

## Architectural Note

The Foundations → Logics.Propositional import direction is a deliberate layering exception.
`ConservativityLift.lean` needs `PL.Evaluate` and `prop_completeness`, which live in
`Cslib.Logics.Propositional`. No import cycle exists (verified by build success). The precedent
is `Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean`. This decision should be confirmed
in the PR review.
