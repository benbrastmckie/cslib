# Implementation Summary: Task #350

- **Task**: 350 - generic_deduction_theorem_lindenbaum_consolidation
- **Status**: [COMPLETED]
- **Completed**: 2026-06-25
- **Plan**: plans/01_deduction-theorem-consolidation.md

## What Was Done

### Phase 1: Temporal deduction theorem re-implementation
- Dropped non-load-bearing `import ...DeductionTheorem` from `GenericMCSBridge.lean` (line 9) to
  break the potential import cycle
- Re-implemented `deductionTheorem` in `DeductionTheorem.lean` via bridge round-trip:
  `⟨d⟩ → temporal_deriv_iff_algebraic → algebraic_has_deduction_theorem → mpr → .some`
- Deleted `deductionWithMem` (~72 lines) and the WF-recursion body
- Re-proved `temporal_has_deduction_theorem` through the bridge
- Downstream verified: `Chronicle/Frame.lean` (2 raw call sites) and `DenseMCS.lean`
  (`deductionTheoremFc` unchanged)

### Phase 2: Bimodal generic bridge
- Created new file `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
- Forward direction: `deriv_tree_to_list` structural induction, reconstructing `necessitation`,
  `temporal_necessitation`, `temporal_duality` at empty context via `InferenceSystem.derivable`
- Backward direction: `unfold_listImp_in_tree` + `list_deriv_to_tree` helpers
- Main lemma: `bimodal_deriv_iff_algebraic` pointwise equivalence at
  `HilbertTM`/`FrameClass.Base`
- Consistency/max-consistency equivalences mirroring temporal bridge

### Phase 3: Bimodal deduction theorem re-implementation
- Audited all raw consumers — all use `FrameClass.Base` (`fc = Base`)
- Re-implemented `deductionTheorem` in `Core/DeductionTheorem.lean` via
  `bimodal_deriv_iff_algebraic` round-trip
- Deleted `deductionWithMem` (~83 lines) and the WF-recursion body
- Re-proved `bimodalHasDeductionTheorem` through the bridge
- Downstream verified: `BXCanonical/TruthLemma`, `Completeness/Dense`,
  `Core/MaximalConsistent`, `Bundle/WitnessSeed`, `Metalogic/Completeness`,
  `BXCanonical/Frame`

### Phase 4: Modal doc correction and CI
- Corrected outdated gap-analysis comment in `Modal/Metalogic/GenericMCSBridge.lean`:
  added CORRECTION NOTICE noting that the temporal-style bridge IS buildable (same
  `InferenceSystem` pattern; barrier is the predicate-vs-type gap, not a semantic gap)
- Fixed pre-existing 113-char line in the Modal bridge file (line length enforcement)
- Fixed `Cslib.lean` via `lake exe mk_all --module`: removed stale `Scratch344` reference
  (introduced by concurrent task 352) and added missing `MplPointedConservative` entry
- Scoped CI builds passed: Temporal.Metalogic (939/939 jobs), Bimodal.Metalogic.Core
  (659/659 jobs), Bimodal.Metalogic.Completeness (660/660 jobs)
- Style linters (`lake exe lint-style`) passed cleanly
- Zero sorry in all modified files; zero new Lean `axiom` declarations introduced

## Plan Deviations

None. Implementation followed the plan exactly as written. The `Cslib.lean` correction
(removing the stale `Scratch344` reference) was not in the plan but was a mandatory fix
discovered during the `lake exe mk_all --module` CI step.

## What Was NOT Done (Deferred)

Modal and Propositional `deductionTheorem` consolidation is explicitly deferred to a follow-up
task. These require new `HilbertOf Axioms` wrapper infrastructure because their
`deductionTheorem` is polymorphic over an `Axioms : Proposition → Prop` predicate, whereas
`algebraicDerivationSystem` is keyed on a type with `[InferenceSystem S] [MinimalHilbert S]`.

## Follow-Up Task to Spawn

**Title**: Modal/Propositional deduction theorem consolidation via `HilbertOf` wrapper

**Description**: Build a `HilbertOf Axioms` wrapper type whose `derivation` is
`DerivationTree Axioms []`, with `MinimalHilbert` synthesised from the `implyK`/`implyS`
witnesses. Build per-predicate bridges `propDerivationSystem Axioms .Deriv ↔
algebraicDerivationSystem (S := HilbertOf Axioms) .Deriv` (and the modal analogue).
Re-implement both `deductionTheorem` defs (signatures preserved) and delete the two
`deductionWithMem`. ~25 raw call sites across Modal `Completeness`/`MCS`/`Systems/{K,D}`
and Propositional `StrongCompleteness`/`Min,IntLindenbaum`/`NaturalDeduction` must keep
compiling.

## Files Modified

1. `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — dropped non-load-bearing import
2. `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` — re-implemented,
   `deductionWithMem` removed
3. `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — NEW FILE (bridge)
4. `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` — re-implemented,
   `deductionWithMem` removed
5. `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — corrected gap-analysis comment,
   fixed 113-char line
6. `Cslib.lean` — removed stale Scratch344 reference; added missing MplPointedConservative

## CI Results

- **Scoped builds (task 350 modules)**: PASSED (Temporal.Metalogic 939 jobs,
  Bimodal.Metalogic.Core 659 jobs, Bimodal.Metalogic.Completeness 660 jobs)
- **Full `lake build`**: PARTIAL — pre-existing failures in unrelated modules
  (Bimodal.Theorems.Perpetuity.Principles, SequentCalculus, Modal.Tableau.Soundness, etc.);
  NONE in files modified by task 350
- **`lake exe checkInitImports`**: FAILED (cascades from pre-existing .olean build errors;
  not introduced by task 350)
- **`lake lint`**: FAILED (crashes due to missing .olean from pre-existing build errors;
  not introduced by task 350)
- **`lake exe lint-style`**: PASSED (no output = no issues)
- **`lake shake`**: PARTIAL — no shake issues in task 350 modified files; pre-existing
  "out-of-date" markers in unrelated failing modules
- **`lake exe mk_all --module`**: PASSED (fixed Cslib.lean)
- **`lake test`**: FAILED (cascades from build failure; CslibTests imports Cslib which
  cannot build due to pre-existing errors)
- **Sorry count (modified files)**: 0
- **New Lean `axiom` declarations**: 0
