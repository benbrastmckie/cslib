# Implementation Plan: Brouwerian Semilattice Typeclass

- **Task**: 303 - Define the BrouwerianSemilattice typeclass
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/303_brouwerian_semilattice_typeclass/reports/01_brouwerian-semilattice-research.md
- **Artifacts**: plans/01_brouwerian-semilattice-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Define `BrouwerianSemilattice`, a new typeclass capturing `SemilatticeInf + OrderTop + HImp` with the adjunction `a <= b ==> c <-> a inf b <= c`. This fills the gap between `SemilatticeInf` and `GeneralizedHeytingAlgebra` in Mathlib's typeclass hierarchy, providing algebraic semantics for the conjunction-implication-verum fragment of intuitionistic logic. The implementation consists of the typeclass definition with ~20 algebraic lemmas in a pure order-theory file, a forgetful instance from `GeneralizedHeytingAlgebra`, `Prod`/`Pi` instances, and a `BrouwerianEvaluate` function in the propositional semantics module.

### Research Integration

Key findings from research report `01_brouwerian-semilattice-research.md`:
- Class definition verified to compile: `class BrouwerianSemilattice extends SemilatticeInf, OrderTop, HImp` with single axiom `le_himp_iff`
- Forgetful instance from `GeneralizedHeytingAlgebra` at priority 100 compiles with no diamond issues
- All ~20 algebraic lemmas verified to compile without sorry in test snippets
- `BrouwerianEvaluate` recommended on existing `PL.Proposition` with bot/or defaulting to top
- Evaluator placed in separate file `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean`
- No sorries expected; low-risk implementation

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly correspond to a specific ROADMAP.md item but strengthens the algebraic semantics infrastructure. It provides the typeclass foundation for downstream tasks 306 (Brouwerian soundness/completeness), 307 (free join completion), and 308 (IPL conservative over conjunction-implication).

## Goals & Non-Goals

**Goals**:
- Define `BrouwerianSemilattice` typeclass with the Galois adjunction axiom in `Cslib/Foundations/Order/BrouwerianSemilattice.lean`
- Provide the `ofHImp` convenience constructor
- Provide the forgetful instance `GeneralizedHeytingAlgebra.toBrouwerianSemilattice` at priority 100
- Prove ~20 algebraic identities (adjunction variants, basic identities, modus ponens, currying, monotonicity, distribution, Galois connection)
- Provide `Prod` and `Pi` instances
- Define `BrouwerianEvaluate` on `PL.Proposition` in `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean`
- Provide simp lemmas for `BrouwerianEvaluate` constructors
- Pass full CSLib CI pipeline

**Non-Goals**:
- Free join completion (`SemilatticeSup` from `BrouwerianSemilattice`) -- task 307
- Soundness/completeness theorems -- task 306
- `IsOrBotFree` predicate on `Proposition` -- task 302
- Bridge theorem between `BrouwerianEvaluate` and `AlgEvaluate` -- task 308
- Modifying existing Mathlib or CSLib files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Naming conflicts with GHA lemmas when both are in scope | L | M | Use `section BrouwerianSemilattice` with typeclass-based disambiguation; Lean resolves by instance |
| `@[simp]` lemmas conflict with existing GHA simp set | M | L | Run `simpNF` linter; adjust attributes if needed |
| Import of `Cslib.Logics.Propositional.Defs` in evaluator file creates unexpected dependency | L | L | Evaluator is in separate file from typeclass; follows existing `Algebra.lean` pattern |
| `noncomputable` propagation from `GaloisConnection` | L | M | Research verified `gc_inf_himp` compiles; mark noncomputable if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Typeclass definition, instances, and algebraic lemmas [NOT STARTED]

**Goal**: Create the `BrouwerianSemilattice` typeclass file with full algebraic theory and instances.

**Tasks**:
- [ ] Create directory `Cslib/Foundations/Order/`
- [ ] Create file `Cslib/Foundations/Order/BrouwerianSemilattice.lean` with CSLib copyright header
- [ ] Add imports: `import Cslib.Init` and `public import Mathlib.Order.Heyting.Basic`
- [ ] Add module docstring describing Brouwerian semilattices and the hierarchy gap they fill
- [ ] Define `class BrouwerianSemilattice` extending `SemilatticeInf`, `OrderTop`, `HImp` with `le_himp_iff` axiom
- [ ] Define `BrouwerianSemilattice.ofHImp` convenience constructor (analogous to `HeytingAlgebra.ofHImp`)
- [ ] Define forgetful instance `GeneralizedHeytingAlgebra.toBrouwerianSemilattice` at priority 100
- [ ] Open a `BrouwerianSemilattice` section with `variable [BrouwerianSemilattice alpha]`
- [ ] Prove core adjunction variants: `le_himp_iff'`, `le_himp_comm`
- [ ] Prove basic identities: `himp_self`, `top_himp`, `himp_top`, `himp_eq_top_iff`, `le_himp`, `le_himp_iff_left` with appropriate `@[simp]` attributes
- [ ] Prove modus ponens / interaction lemmas: `himp_inf_le`, `inf_himp_le`, `inf_himp`, `himp_inf_self`
- [ ] Prove currying and composition: `himp_himp`, `himp_left_comm`, `himp_idem`, `himp_triangle`, `le_himp_himp`
- [ ] Prove monotonicity: `himp_le_himp_left`, `himp_le_himp_right`, `himp_le_himp` with `@[gcongr]`
- [ ] Prove distribution: `himp_inf_distrib`
- [ ] Prove Galois connection: `gc_inf_himp`
- [ ] Define `Prod` and `Pi` instances for `BrouwerianSemilattice`
- [ ] Add docstrings to all declarations
- [ ] Run `lake build Cslib.Foundations.Order.BrouwerianSemilattice` to verify compilation
- [ ] Run `lake exe mk_all --module` to update barrel import

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Order/BrouwerianSemilattice.lean` - New file (typeclass, instances, lemmas)
- `Cslib.lean` - Updated by `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Foundations.Order.BrouwerianSemilattice` compiles without errors
- All lemmas compile without sorry
- `lean_verify` confirms no sorry or axiom use beyond standard foundations
- Docstrings present on all declarations

---

### Phase 2: BrouwerianEvaluate and CI verification [NOT STARTED]

**Goal**: Define the `BrouwerianEvaluate` function on `PL.Proposition`, provide simp lemmas, and pass full CI.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean` with CSLib copyright header
- [ ] Add imports: `import Cslib.Init`, `import Cslib.Foundations.Order.BrouwerianSemilattice`, `import Cslib.Logics.Propositional.Defs`
- [ ] Add module docstring describing Brouwerian evaluation and its role in the algebraic semantics hierarchy
- [ ] Define `BrouwerianEvaluate` recursive function mapping `PL.Proposition Atom` to `H` where `[BrouwerianSemilattice H]`: atom maps to `v x`, bot/or default to top, imp uses `himp`, and maps to `inf`
- [ ] Add `@[simp]` lemmas for each constructor: `BrouwerianEvaluate_atom`, `BrouwerianEvaluate_bot`, `BrouwerianEvaluate_imp`, `BrouwerianEvaluate_and`, `BrouwerianEvaluate_or`
- [ ] Add docstrings to all declarations
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian` to verify compilation
- [ ] Run `lake exe mk_all --module` to update barrel import
- [ ] Run full CI pipeline: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to verify import minimization

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean` - New file (evaluator, simp lemmas)
- `Cslib.lean` - Updated by `lake exe mk_all --module`

**Verification**:
- `lake build` succeeds with no errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- `lake shake` reports no unused imports
- All declarations have docstrings
- No sorry in any file

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Order.BrouwerianSemilattice` compiles without error
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian` compiles without error
- [ ] All ~20 algebraic lemmas compile without sorry
- [ ] `lean_verify` on key lemmas (e.g., `himp_self`, `gc_inf_himp`) confirms no sorry
- [ ] Forgetful instance diamond check: `SemilatticeInf` from forgetful instance equals that from `Lattice` (verified by `rfl` in research)
- [ ] Full CI pipeline passes: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes

## Artifacts & Outputs

- `Cslib/Foundations/Order/BrouwerianSemilattice.lean` - Typeclass, forgetful instance, Prod/Pi instances, ~20 algebraic lemmas
- `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean` - BrouwerianEvaluate function and simp lemmas
- `Cslib.lean` - Updated barrel import (via `lake exe mk_all --module`)
- `specs/303_brouwerian_semilattice_typeclass/plans/01_brouwerian-semilattice-plan.md` - This plan

## Rollback/Contingency

Both files are new additions with no modifications to existing files. Rollback is straightforward:
1. Delete `Cslib/Foundations/Order/BrouwerianSemilattice.lean`
2. Delete `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean`
3. Run `lake exe mk_all --module` to regenerate barrel imports
4. Verify `lake build` passes without the new files

If Phase 2 encounters issues with the evaluator (e.g., `PL.Proposition` structure changes), Phase 1 remains independently valuable -- the typeclass and algebraic theory are self-contained.
