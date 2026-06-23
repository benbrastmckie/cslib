# Implementation Plan: Task #304

- **Task**: 304 - Define the HilbertAlgebra typeclass
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: None (BrouwerianSemilattice already exists)
- **Research Inputs**: specs/304_hilbert_algebra_typeclass/reports/01_hilbert-algebra-research.md
- **Artifacts**: plans/01_hilbert-algebra-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Define the `HilbertAlgebra` typeclass in the Foundations layer, derive a `PartialOrder` and
`OrderTop` instance from its axioms, provide a forgetful instance from `BrouwerianSemilattice`,
and define `HilbertEvaluate` in the Logics layer for the imp-top-only fragment. The typeclass
extends `HImp` and `Top` with four fields: `himp_K`, `himp_S`, `himp_antisymm`, and `himp_self`.
The fourth field (`himp_self`) avoids a circular bootstrap problem identified in research.

### Research Integration

Key findings from `01_hilbert-algebra-research.md`:

1. **Bootstrap circularity**: Deriving `a ⇨ a = ⊤` from K + S + antisymmetry alone requires
   algebraic modus ponens, which itself requires `a ⇨ ⊤ = ⊤`, creating genuine circularity.
   Resolution: include `himp_self` as a fourth field.
2. **GHA forgetful instance**: Not needed as a direct instance. The chain
   `GeneralizedHeytingAlgebra -> BrouwerianSemilattice -> HilbertAlgebra` already provides it
   transitively.
3. **Evaluator pattern**: Follow `BrouwerianEvaluate` exactly -- default non-fragment cases
   (`bot`, `and`, `or`) to `⊤`.
4. **BibKey**: Rasiowa1974 verified in `references.bib`. Diego1966 and Monteiro1955 not yet
   added (out of scope for this task).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Foundations/Order algebraic hierarchy and the Propositional/Semantics
evaluator family. It fills the gap between `BrouwerianSemilattice` (the `{⊓, ⇨, ⊤}` fragment)
and the purely implicational fragment `{⇨, ⊤}`.

## Goals & Non-Goals

**Goals**:
- Define `HilbertAlgebra` class extending `HImp` and `Top` with K, S, antisymmetry, and self fields
- Derive `PartialOrder` from the induced order `a ≤ b ↔ a ⇨ b = ⊤`
- Derive `OrderTop` instance
- Prove core algebraic lemmas: `himp_top`, `top_himp`, `himp_eq_top_iff`, algebraic modus ponens, transitivity
- Provide forgetful instance `BrouwerianSemilattice.toHilbertAlgebra` at priority 100
- Define `HilbertEvaluate` and `HilbertValid` in the Logics layer
- Prove simp lemmas for `HilbertEvaluate`
- Register both new files in `Cslib.Init` imports and pass CI

**Non-Goals**:
- Adding Diego1966 / Monteiro1955 to `references.bib` (separate task)
- Proving soundness of `ImpAxiom` w.r.t. `HilbertValid` (follow-up task)
- Proving agreement between `HilbertEvaluate` and `AlgEvaluate` for `IsImpTopOnly` formulas (task 308 scope)
- Prod/Pi instances for `HilbertAlgebra` (can be added later)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PartialOrder bootstrap proofs are harder than expected | H | M | `himp_self` as a field eliminates the main circularity; proofs of `himp_top` and `top_himp` follow standard patterns from `himp_self` + K + antisymmetry |
| Typeclass diamond with GHA | M | L | Only one forgetful instance (from BrouwerianSemilattice); GHA path goes through existing chain |
| S axiom proof for BrouwerianSemilattice forgetful instance is complex | M | M | Use adjunction `le_himp_iff` with currying and modus ponens lemmas already in BrouwerianSemilattice |
| Import cycle between Foundations and Logics | H | L | HilbertAlgebra in Foundations, HilbertEvaluate in Logics -- clean separation, no cycle |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

### Phase 1: HilbertAlgebra Typeclass and Algebraic Theory [COMPLETED]

**Goal**: Define the `HilbertAlgebra` class, derive `PartialOrder` and `OrderTop`, prove
core algebraic lemmas, and provide the forgetful instance from `BrouwerianSemilattice`.

**Tasks**:
- [ ] Create `Cslib/Foundations/Order/HilbertAlgebra.lean` with module header, copyright, and `import Cslib.Init` + `public import Cslib.Foundations.Order.BrouwerianSemilattice`
- [ ] Define `class HilbertAlgebra (H : Type*) extends HImp H, Top H` with four fields: `himp_K`, `himp_S`, `himp_antisymm`, `himp_self`
- [ ] Open `namespace HilbertAlgebra` and prove bootstrap lemmas:
  - `himp_mp`: algebraic modus ponens -- if `a ⇨ b = ⊤` and `a = ⊤` then `b = ⊤`
  - `himp_top`: `a ⇨ ⊤ = ⊤`
  - `top_himp`: `⊤ ⇨ a = a`
  - `himp_eq_top_iff`: `a ⇨ b = ⊤ ↔ a ≤ b` (where `≤` is the induced order)
  - `himp_trans`: if `a ⇨ b = ⊤` and `b ⇨ c = ⊤` then `a ⇨ c = ⊤`
- [ ] Define `instance instPartialOrder : PartialOrder H` using `le := fun a b => a ⇨ b = ⊤`
  - Reflexivity from `himp_self`
  - Transitivity from `himp_trans`
  - Antisymmetry from `himp_antisymm`
- [ ] Define `instance instOrderTop : OrderTop H` with `le_top` from `himp_top`
- [ ] Define forgetful instance `BrouwerianSemilattice.toHilbertAlgebra` at priority 100:
  - `himp_K`: from `BrouwerianSemilattice.himp_eq_top_iff.mpr (BrouwerianSemilattice.le_himp a b)`
  - `himp_S`: from adjunction + modus ponens in BrouwerianSemilattice
  - `himp_antisymm`: from `le_antisymm` + `himp_eq_top_iff.mp`
  - `himp_self`: from `BrouwerianSemilattice.himp_self`
- [ ] Verify with `lake build Cslib.Foundations.Order.HilbertAlgebra`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Order/HilbertAlgebra.lean` - NEW: typeclass, instances, lemmas (~150-200 lines)

**Verification**:
- `lake build Cslib.Foundations.Order.HilbertAlgebra` compiles without errors
- `lean_verify` on key definitions confirms no sorry or axiom leaks

---

### Phase 2: HilbertEvaluate and HilbertValid [COMPLETED]

**Goal**: Define the `HilbertEvaluate` evaluator for the imp-top-only fragment and
the `HilbertValid` validity predicate.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean` with module header and imports (`Cslib.Init`, `Cslib.Foundations.Order.HilbertAlgebra`, `Cslib.Logics.Propositional.Defs`)
- [ ] Define `HilbertEvaluate` following `BrouwerianEvaluate` pattern:
  - `.atom x => v x`
  - `.bot => ⊤`
  - `.imp a b => HilbertEvaluate v a ⇨ HilbertEvaluate v b`
  - `.and _ _ => ⊤`
  - `.or _ _ => ⊤`
- [ ] Define `HilbertValid` as validity in all Hilbert algebras
- [ ] Prove simp lemmas: `HilbertEvaluate_atom`, `_bot`, `_imp`, `_and`, `_or`
- [ ] Verify with `lake build Cslib.Logics.Propositional.Semantics.Algebra.Hilbert`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean` - NEW: evaluator and validity (~80-100 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Hilbert` compiles without errors
- `lean_verify` on `HilbertEvaluate` and `HilbertValid` confirms no sorry

---

### Phase 3: CI Verification and Init Imports [COMPLETED]

**Goal**: Register both new files in the barrel import, verify CI pipeline passes.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import with the two new modules
- [ ] Run `lake exe checkInitImports` to verify both files import `Cslib.Init`
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake build` (full project) to verify no import cycles or breakage
- [ ] Run `lake test` to verify test suite passes
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to verify import minimality

**Timing**: 1 hour

**Depends on**: 1, 2

**Files to modify**:
- `Cslib.lean` - update barrel import (via `mk_all`)
- Possibly `Cslib/Foundations/Order/HilbertAlgebra.lean` and `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean` for any lint/style fixes

**Verification**:
- All six CI commands pass without errors
- No new warnings introduced

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Order.HilbertAlgebra` compiles cleanly
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.Hilbert` compiles cleanly
- [ ] `lake build` (full project) succeeds
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `lean_verify` on `HilbertAlgebra`, `HilbertAlgebra.instPartialOrder`, `HilbertAlgebra.instOrderTop`, `BrouwerianSemilattice.toHilbertAlgebra`, `HilbertEvaluate`, `HilbertValid` -- all sorry-free and axiom-clean

## Artifacts & Outputs

- `Cslib/Foundations/Order/HilbertAlgebra.lean` -- new file: HilbertAlgebra typeclass, PartialOrder/OrderTop derivation, forgetful instance, algebraic lemmas (~150-200 lines)
- `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean` -- new file: HilbertEvaluate, HilbertValid, simp lemmas (~80-100 lines)
- `specs/304_hilbert_algebra_typeclass/plans/01_hilbert-algebra-plan.md` -- this plan

## Rollback/Contingency

Both new files are fully self-contained additions. If implementation fails:
1. Delete `Cslib/Foundations/Order/HilbertAlgebra.lean`
2. Delete `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean`
3. Re-run `lake exe mk_all --module` to remove from barrel import
4. `git restore` any other modified files

No existing files are modified (except the barrel import), so rollback is trivial.
