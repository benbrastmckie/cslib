# Task 355 — Modal/Propositional Deduction Theorem Consolidation (Summary)

**Status:** Completed (orchestrated; agent return-meta was stale at phase 3, but on-disk
deliverables and targeted CI verification confirm completion).

## Delivered

- **Foundations**: `HasMinimalAxioms` generic class + `HilbertOf` predicate→type wrapper added to
  `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`, bridging the predicate-vs-type gap that
  blocked Modal/Propositional in task 350.
- **Modal**: `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` filled in (was doc-only);
  `Modal/Metalogic/DeductionTheorem.lean` rerouted through the bridge +
  `algebraic_has_deduction_theorem`, hand WF-recursion body removed.
- **Propositional**: new `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` (255 lines);
  `Propositional/Metalogic/DeductionTheorem.lean` rerouted, hand WF-recursion body removed.
- Barrel (`Cslib.lean`) updated with the new PL bridge import.

## Verification

- Targeted build of all touched modules + downstream consumers (Modal Completeness / MCS /
  ConservativeExtension, PL StrongCompleteness / IntStrongCompleteness / MinStrongCompleteness):
  **green, 0 errors / 0 warnings / 0 sorry** (745 + 762 jobs across two builds).
- Signatures preserved — the ~25 raw `DerivationTree` call sites compile unchanged.
- No new sorry, no new axioms (only `Classical.choice` inherent to the pre-existing
  `noncomputable` defs).

## Deviation / follow-up for task 366 (capstone audit)

- The `deductionWithMem` helper was **kept and rerouted** (now implemented on top of the generic
  `deductionTheorem` rather than via hand WF-recursion) instead of being deleted. Research noted it
  has zero external callers, so task 366's threading/documentation audit should decide whether to
  delete it outright and finalize the module docstrings.

## Note on full-library CI

A full `lake build` is currently **red due to pre-existing breakage unrelated to this task** —
`Cslib/Logics/Modal/Tableau/Soundness.lean` was left with errors by commit `396c9435`
("task 364: restore to best-known state (Phase 1 complete, 68 errors)"). That breakage is outside
task 355's scope; all task-355 modules and their deduction-theorem consumers build green in
isolation.
