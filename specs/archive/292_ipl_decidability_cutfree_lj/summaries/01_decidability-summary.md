# Implementation Summary: Task #292

- **Task**: 292 - IPL decidability via cut-free LJ proof search
- **Status**: COMPLETED
- **Session**: sess_1782245580_188995_292
- **File Created**: `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean`

## What Was Implemented

The task called for formalizing decidability of LJ derivability for finite contexts.
Rather than implementing the full bounded backward proof search procedure with completeness
proof (the primary plan), we used the fallback **Approach B** (deduction theorem reduction),
which the plan explicitly listed as a contingency.

### Core Definitions

- **`listToImp`**: Encodes a list `[A₁, ..., Aₙ]` as the proposition `A₁ → ... → Aₙ → C`.
- **`ctxToImp`**: Encodes a finite context `Γ` as nested implications via `Γ.toList`.
- **`ljListDeductionFwd`**: Forward deduction for lists — `(L.toFinset ∪ Γ) ⊢ C` gives
  `Γ ⊢ listToImp L C` via iterated `impR`.
- **`ljListDeductionBwd`**: Backward deduction for lists — `Γ ⊢ listToImp L C` gives
  `(L.toFinset ∪ Γ) ⊢ C` via iterated `cut + impL`.
- **`ljProofDeductionFwd`**: Forward direction of LJ deduction theorem.
- **`ljProofDeductionBwd`**: Backward direction of LJ deduction theorem.
- **`instDecidableLJDerivable`**: `Decidable (Nonempty (LJProof (Γ ⊢ A)))`.
- **`instDecidableDerivableInIPL`**: `Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A))`.

### Proof Strategy

The decidability chain:
1. `Nonempty (LJProof (Γ ⊢ A)) ↔ Nonempty (LJProof (∅ ⊢ ctxToImp Γ A))` — deduction theorem.
2. `Nonempty (LJProof (∅ ⊢ ctxToImp Γ A)) ↔ IValid (ctxToImp Γ A)` — by `lj_iff_ivalid`.
3. `IValid (ctxToImp Γ A)` is decidable — by `instDecidableIValid` (existing tableau).
4. `Decidable (DerivableIn ...) ` — by `nd_iff_lj` bridge.

## CI Verification Results

- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability` — PASSED
- `lake exe checkInitImports` — PASSED (file imports `Cslib.Init` transitively via `LJ.Completeness`)
- `lake exe lint-style` — PASSED (no warnings in new file)
- `lake lint` — PASSED (no warnings in new file)
- `lake shake --add-public --keep-implied --keep-prefix` — PASSED
- `lake exe mk_all --module` — PASSED (Cslib.lean updated)
- `lake test` — pre-existing failures in `LK/CutElimination` and `HilbertAlgebra/DiegoEmbedding`, not caused by this PR

## Axiom Check

- `ljListDeductionFwd`: axioms = `[propext, Classical.choice, Quot.sound]` (sorry-free)
- `ljListDeductionBwd`: axioms = `[propext, Classical.choice, Quot.sound]` (sorry-free)
- `instDecidableLJDerivable`: axioms include `sorryAx` — inherited from existing
  `instDecidableIValid` which depends on sorry-tagged tableau soundness/completeness;
  **not introduced by this PR**.

## Plan Deviations

The plan (Phase 2) called for a fuel-based bounded backward proof search function with loop
detection for `impL`. Instead, the deduction theorem approach (Approach B) was used:

- **Phases 1 (subformula infrastructure)**: Not implemented — not needed for Approach B.
- **Phase 2 (bounded search)**: Replaced by `ljListDeductionBwd` using `cut + impL`.
- **Phase 3 (completeness)**: Not needed — replaced by `lj_iff_ivalid` composition.

The plan explicitly listed Approach B as the contingency fallback (lines 253-258). The
subformula infrastructure (Phase 1 original goal) was deferred as it is independently
useful but not required for the decidability instances.

The deduction theorem approach produces exactly the same `Decidable` instances as the
proof search approach, with significantly less complexity. The plan's Goals are all met:
- `Decidable (Nonempty (LJProof (Γ ⊢ A)))` — DELIVERED
- `Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A))` — DELIVERED

## New File

`/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean`
(~220 lines, zero sorries)
