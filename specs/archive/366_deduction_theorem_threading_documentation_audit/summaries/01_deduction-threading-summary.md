# Task 366: Deduction Theorem Threading & Documentation Audit — Summary

## Outcome: Option A (Full Consolidation)

The prior agent attempted Option A but left the working tree in a broken state with syntax
errors in `Bimodal/Metalogic/Core/GenericMCSBridge.lean` and
`Temporal/Metalogic/GenericMCSBridge.lean`. This agent repaired both files to a clean,
zero-sorry, zero-axiom, fully compiling state.

## What Was Repaired

### Temporal GenericMCSBridge.lean
- Fixed `HasAxiomImplyK` and `HasAxiomImplyS` instances: `fun φ ψ =>` wrapper was wrong
  because `implyK {φ ψ : F}` takes its formula args as implicit, not explicit.
  Changed to direct term form `implyK := ⟨.axiom [] _ (.imp_s _ _) ...⟩`.
- Fixed `temporal_deriv_iff_algebraic_fc` theorem: replaced forward reference
  `Temporal.DerivFc fc Γ φ` (defined later in `DenseMCS.lean`) with
  `Nonempty (DerivationTree fc Γ φ)`, which is its definitional expansion.

### Bimodal Core GenericMCSBridge.lean
- Fixed `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `MinimalHilbert` instances:
  the `(F := Bimodal.Formula Atom)` named argument syntax caused "unexpected ':='"
  parse errors when used with `instance (fc : FrameClass) :`. Replaced with `@`-syntax
  to supply `F` explicitly as the first positional argument (correct arg counts verified
  via `lean_hover_info`). Wrapped all four instances in a `section HilbertTMFcInstances`
  / `variable (fc : FrameClass)` block mirroring the Modal/PL pattern.

## Deliverables Completed

### D1 — Architecture docstring in GenericMCS.lean
Added comprehensive module-level docstring covering:
- The algebraic seam architecture (predicate → HilbertOf tag type → MinimalHilbert → seam)
- The `listImp → ListDeriv → algebraic_has_deduction_theorem` chain
- Frame-class parameterization: Task-366 extended both Bimodal and Temporal bridges
  to arbitrary `fc : FrameClass` via `HilbertTMFc` and `HilbertBXFc` tag types
- Bullet-list table of all six logic/bridge/deduction-theorem pairings (within 100-char limit)

### D2 — Module docstrings revised
- **Bimodal Core DeductionTheorem.lean**: Replaced stale hand-recursion narrative with
  accurate Option A description (seam routing via `bimodal_deriv_iff_algebraic_fc`).
  Added load-bearing note for `deductionWithMem`.
- **PL DeductionTheorem.lean**: Added 4-caller list for `deductionWithMem`
  (`IntLindenbaum:148`, `MinLindenbaum:131`, `StrongCompleteness:447`,
  `SemanticConsequence:159`); updated module `## Main Results` accordingly.
- **Modal DeductionTheorem.lean**: Added 1-caller note for `deductionWithMem`
  (`Completeness:542`).
- **Temporal DenseMCS.lean**: Added cross-ref to D1 and to parallel R1 file in References.

### D3 — References cross-refs
- Added D1 cross-ref to `## References` in: PL DeductionTheorem, Modal DeductionTheorem,
  PL GenericMCSBridge, Temporal DenseMCS.
- Bimodal Core DeductionTheorem references already updated as part of D2.

## Verification

All three scoped build batches pass:
- Batch 1 (deduction core + seam): 655 jobs, Build completed successfully
- Batch 2 (completeness consumers): 1003 jobs, Build completed successfully
- Batch 3 (equivalence/dense): 962 jobs, Build completed successfully

Zero sorries in touched files. Zero new axioms (15 baseline = 15 final).
`lake exe lint-style` reports no issues on touched files.

## Plan Deviations

- **Phase 1 [COMPLETED]**: Marked as already completed by prior agent (spike done).
- **Phase 2**: The prior agent attempted Option A but left broken files. This agent
  completed the repair using `@`-syntax for explicit typeclass argument supply in
  Bimodal, and direct-term form (no `fun` wrapper) + forward-reference elimination
  in Temporal. Deviation from plan: the repair strategy used `@` positional args
  rather than `(F := ...)` named args; functionally equivalent.
- **IntFMPSpike.lean** (task-370 orphan): not touched, as required.
- **task-364 Tableau subtree**: not touched, as required.
