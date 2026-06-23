# Implementation Plan: Task #284

- **Task**: 284 - Restate ipl_conservative_over_mpl and glivenko as Hilbert-primary
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: Task 283 (Hilbert algebraic completeness)
- **Research Inputs**: specs/284_hilbert_primary_conservative_glivenko/reports/01_conservative-glivenko.md
- **Artifacts**: plans/01_conservative-glivenko-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This task creates a new file `HilbertConservativeGlivenko.lean` containing Hilbert-primary
restatements of the conservative extension and Glivenko theorems, plus algebraic bridges
between the ND `DerivableIn` and Hilbert `Derivable` predicates. The Hilbert-primary
theorems compose existing algebraic infrastructure (completeness, `coe_AlgEvaluate`,
`glivenko_algebraic`) with the Hilbert completeness results from task 283. ND versions are
recovered as one-line corollaries via the algebraic bridges.

### Research Integration

Research report `01_conservative-glivenko.md` confirmed:
- The algebraic cores (`coe_AlgEvaluate`, `glivenko_algebraic`) are already proved
- No new definitions are needed; all new content composes existing infrastructure
- Universe alignment is expected to work (`{u, u}` throughout)
- The `AxiomTheory`/`MPL`/`IPL`/`CPL` gap means bridges must route through algebra, not through `hilbert_iff_nd_*`
- Estimated ~30-50 lines of new proof code with zero sorry risk

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the propositional logic algebraic semantics infrastructure. The ROADMAP.md
focuses on the BimodalLogic porting effort; this task is foundational work for the propositional
layer that supports those higher-level modules.

## Goals & Non-Goals

**Goals**:
- State and prove `hilbert_ipl_conservative_over_mpl` using `Derivable` + Hilbert completeness
- State and prove `hilbert_glivenko` using `Derivable` + Hilbert completeness
- Create algebraic bridges `derivableIn_*_iff_derivable_*` for MPL, IPL, and CPL
- Derive ND corollaries as one-liners via the bridges
- Register the new module in `Cslib.lean` barrel import
- Pass CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`

**Non-Goals**:
- Modifying existing `Conservative.lean` or `Glivenko.lean` files
- Creating direct ND-to-Hilbert bridges via `hilbert_iff_nd_*` (the `AxiomTheory` gap prevents this)
- Proving the `AxiomTheory Axioms = MPL/IPL/CPL` equivalence (that is a separate concern)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe mismatch between ND and Hilbert completeness | H | L | Both pin to atom universe `u`; research confirmed alignment |
| `alg_complete_classical` theory-validity discharge for CPL bridge | M | L | Same pattern as existing `glivenko` proof in Glivenko.lean |
| `DecidableEq Atom` constraint on ND completeness not present in Hilbert | M | L | Bridges may need `[DecidableEq Atom]`; Hilbert-primary theorems do not |
| `glivenko_algebraic` universe variable mismatch with `.{u,u}` | L | VL | Already quantifies over `Type u` matching Hilbert completeness |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Hilbert-Primary Conservative Extension and Glivenko [COMPLETED]

**Goal**: Create the new file with the two core Hilbert-primary theorems.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`
- [ ] Add module docstring explaining the Hilbert-primary approach
- [ ] Import `HilbertCompleteness`, `Conservative`, and `Glivenko`
- [ ] Prove `hilbert_ipl_conservative_over_mpl`:
  ```lean
  theorem hilbert_ipl_conservative_over_mpl {Atom : Type u} {φ : PL.Proposition Atom}
      (hBF : φ.IsBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
      Derivable (@MinPropAxiom Atom) φ
  ```
  Route: `IPL.hilbert_alg_complete.mp h` -> HAValid -> WithBot embedding via `coe_AlgEvaluate` -> GHAValid -> `MPL.hilbert_alg_complete.mpr`
- [ ] Prove `hilbert_glivenko`:
  ```lean
  theorem hilbert_glivenko {Atom : Type u} {φ : PL.Proposition Atom}
      (h : Derivable (@PropositionalAxiom Atom) φ) :
      Derivable (@IntPropAxiom Atom) (¬¬φ)
  ```
  Route: `CPL.hilbert_alg_complete.mp h` -> BAValid -> `glivenko_algebraic` -> HAValid of `¬¬φ` -> `IPL.hilbert_alg_complete.mpr`
- [ ] Verify with `lean_goal` at each proof step

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` - NEW file

**Verification**:
- `lean_verify` on both theorems (no sorry, no axiom beyond standard)
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko`

---

### Phase 2: Algebraic Bridges (DerivableIn ↔ Derivable) [COMPLETED]

**Goal**: Add three equivalence theorems bridging ND `DerivableIn` with Hilbert `Derivable` by routing through algebraic validity.

**Tasks**:
- [ ] Import `Completeness` (for ND-level `alg_complete` theorems)
- [ ] Prove `derivableIn_mpl_iff_derivable_min`:
  ```lean
  theorem derivableIn_mpl_iff_derivable_min {Atom : Type u} [DecidableEq Atom]
      {φ : PL.Proposition Atom} :
      DerivableIn (MPL (Atom := Atom)) φ ↔ Derivable (@MinPropAxiom Atom) φ
  ```
  Forward: `MPL.alg_complete.mp` -> GHAValid -> `MPL.hilbert_alg_complete.mpr`
  Backward: `MPL.hilbert_alg_complete.mp` -> GHAValid -> `MPL.alg_complete.mpr`
- [ ] Prove `derivableIn_ipl_iff_derivable_int`:
  ```lean
  theorem derivableIn_ipl_iff_derivable_int {Atom : Type u} [DecidableEq Atom]
      {φ : PL.Proposition Atom} :
      DerivableIn (IPL (Atom := Atom)) φ ↔ Derivable (@IntPropAxiom Atom) φ
  ```
  Same pattern using HAValid and `IPL.alg_complete` / `IPL.hilbert_alg_complete`
- [ ] Prove `derivableIn_cpl_iff_derivable_prop`:
  ```lean
  theorem derivableIn_cpl_iff_derivable_prop {Atom : Type u} [DecidableEq Atom]
      {φ : PL.Proposition Atom} :
      DerivableIn ((IPL ∪ CPL : Theory Atom)) φ ↔ Derivable (@PropositionalAxiom Atom) φ
  ```
  Forward: `alg_complete_classical.mp` (discharging theory-validity) -> BAValid -> `CPL.hilbert_alg_complete.mpr`
  Backward: `CPL.hilbert_alg_complete.mp` -> BAValid -> `alg_complete_classical.mpr` (discharging theory-validity)
- [ ] Handle `DecidableEq Atom` constraint (required by ND completeness, not by Hilbert)

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` - add bridges

**Verification**:
- `lean_verify` on all three bridge theorems
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko`

---

### Phase 3: ND Corollaries via Bridges [COMPLETED]

**Goal**: Derive ND versions of conservative extension and Glivenko as one-line corollaries of the Hilbert-primary versions, using the bridges from Phase 2.

**Tasks**:
- [ ] Prove `ipl_conservative_over_mpl'` (ND corollary of Hilbert conservative extension):
  ```lean
  theorem ipl_conservative_over_mpl' {Atom : Type u} [DecidableEq Atom]
      {A : PL.Proposition Atom}
      (hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
      DerivableIn (MPL (Atom := Atom)) A :=
    derivableIn_mpl_iff_derivable_min.mpr
      (hilbert_ipl_conservative_over_mpl hBF (derivableIn_ipl_iff_derivable_int.mp h))
  ```
- [ ] Prove `glivenko'` (ND corollary of Hilbert Glivenko):
  ```lean
  theorem glivenko' {Atom : Type u} [DecidableEq Atom]
      {A : PL.Proposition Atom}
      (h : DerivableIn ((IPL ∪ CPL : Theory Atom)) A) :
      DerivableIn (IPL : Theory Atom) (¬¬A) :=
    derivableIn_ipl_iff_derivable_int.mpr
      (hilbert_glivenko (derivableIn_cpl_iff_derivable_prop.mp h))
  ```
- [ ] Add docstrings noting these are corollaries of the Hilbert-primary versions

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` - add corollaries

**Verification**:
- `lean_verify` on both corollary theorems
- Corollaries should be term-mode one-liners

---

### Phase 4: CI Verification and Registration [COMPLETED]

**Goal**: Register the new module in the barrel import and pass all CI checks.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` with the new module
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports` (verify `Cslib.Init` import chain)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake test` (test suite)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (dependency analysis)
- [ ] Fix any lint or style issues

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib.lean` - add barrel import for `HilbertConservativeGlivenko`
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` - fix any lint issues

**Verification**:
- All CI commands pass with zero errors
- `lean_verify` final check on key theorems

## Testing & Validation

- [ ] `hilbert_ipl_conservative_over_mpl` type-checks with no sorry
- [ ] `hilbert_glivenko` type-checks with no sorry
- [ ] All three algebraic bridges type-check with no sorry
- [ ] Both ND corollaries type-check as term-mode one-liners
- [ ] `lake build` succeeds (full project)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] No axioms beyond standard Lean axioms (`lean_verify` clean)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` - new module
- `Cslib.lean` - updated barrel import
- `specs/284_hilbert_primary_conservative_glivenko/plans/01_conservative-glivenko-plan.md` - this plan

## Rollback/Contingency

If the implementation fails:
1. Delete `HilbertConservativeGlivenko.lean`
2. Revert `Cslib.lean` barrel import change
3. No existing files are modified, so no rollback needed for those

If universe issues arise in the bridges (Phase 2), the Hilbert-primary theorems (Phase 1)
can still stand alone without the bridges. The ND corollaries (Phase 3) can be deferred to
a follow-up task if the bridges prove more complex than expected.
