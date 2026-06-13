# Execution Summary: Propositional Metalogic Full Connectives (Prime Theories)

- **Task**: 174 - Extend propositional metalogic to full five-primitive connectives
- **Status**: Implemented
- **Date**: 2026-06-12
- **Plan**: specs/174_propositional_metalogic_full_connectives/plans/01_implementation-plan.md

## What Was Done

Eliminated 2 `sorry`s in the or-backward direction of completeness truth lemmas by
introducing prime theories (DCCSs satisfying the disjunction property) as canonical worlds.

### Phase 1: Prime Theory Definitions and Chain Union Lemmas

Added to `MinLindenbaum.lean`:
- `MinPrimeTheory`: A MinTheory with the disjunction property (if `φ ∨ ψ ∈ S` then `φ ∈ S` or `ψ ∈ S`)
- `MinPrimeExcludingSupersets S phi`: The Zorn domain -- MinTheory supersets of S that exclude phi
- `min_excluding_base_mem`: S is in its own phi-excluding supersets
- `min_excluding_chain_union`: Chain unions of phi-excluding supersets preserve MinTheory and phi-exclusion

Added same structure to `IntLindenbaum.lean`:
- `IntPrimeDCCS`: An IntDCCS with the disjunction property
- `IntPrimeExcludingSupersets S phi`: The Zorn domain for intuitionistic
- `int_excluding_base_mem`, `int_excluding_chain_union`: Parallel lemmas

### Phase 2: Prime Exclusion via Zorn's Lemma

Added to `MinLindenbaum.lean`:
- `min_maximal_is_prime`: If T is maximal in `MinPrimeExcludingSupersets S phi`, then T is prime. Proof: if `A ∨ B ∈ T` but `A ∉ T` and `B ∉ T`, then by maximality both `minDeductiveClosure(T ∪ {A})` and `minDeductiveClosure(T ∪ {B})` contain phi. By `min_deriv_imp_of_union`, `T ⊢ A → phi` and `T ⊢ B → phi`. By orE and deductive closure, `phi ∈ T`. Contradiction.
- `min_prime_exclusion`: Zorn application to MinPrimeExcludingSupersets

Added to `IntLindenbaum.lean`:
- `int_maximal_is_prime`: Same argument with a case split on consistency of `T ∪ {A}`. If `T ∪ {A}` is inconsistent, phi is derivable by EFQ; otherwise maximality applies.
- `int_prime_exclusion`: Zorn application to IntPrimeExcludingSupersets

### Phase 3: Updated Canonical Models and Eliminated Sorries

`MinCompleteness.lean`:
- Redefined `MinCanonicalWorld` to use `MinPrimeTheory` instead of `MinTheory`
- Updated all `S.property` → `S.property.1` (MinTheory part) and `T.property` → `T.property.1`
- Filled or-backward sorry: `rcases S.property.2 φ ψ h_mem with h | h`
- Updated imp-forward to use `min_prime_exclusion` to get prime canonical world T
- Updated `min_completeness` to use `min_prime_exclusion` on `min_theorems_theory`

`IntCompleteness.lean`:
- Redefined `IntCanonicalWorld` to use `IntPrimeDCCS` instead of `IntDCCS`
- Updated all `S.property.2` (deductive closure) → `S.property.1.2`, bot check → `S.property.1`
- Filled or-backward sorry: `rcases S.property.2 φ ψ h_mem with h | h`
- Updated imp-forward to use `int_prime_exclusion` to get prime canonical world T
- Updated `int_completeness` to use `int_prime_exclusion` on `int_theorems_dccs`

### Phase 4: CI Verification

- All 4 modified files build without errors
- Zero sorries in modified files
- Zero vacuous definitions
- Zero new axioms (axiom count: 18, unchanged)
- Style linting passed (no long lines after fixes)
- `Cslib.Logics.Propositional.Metalogic.Completeness` (classical) unchanged and still builds

Note: `lake build` (full project) has pre-existing failures in Modal/Temporal modules
(tasks 175/176 in progress). The Propositional Metalogic module is fully clean.

## Key Decisions and Deviations

### Deviation: IntMaximalIsPrime uses case split on consistency

The plan described a straightforward maximality argument for `int_maximal_is_prime`. In
implementation, we discovered that `intDeductiveClosure(T ∪ {A})` requires consistency of
`T ∪ {A}` to be an IntDCCS. The proof splits into two cases: if consistent, use maximality;
if inconsistent, EFQ gives phi directly. This is mathematically sound but differs from the
plan's single-path description.

### Deviation: No separate min_imp_witness_prime theorem

The plan described a separate `min_imp_witness_prime` helper. Instead, we inline the
prime extension directly in the imp-forward case of `min_truth_lemma`: use `min_imp_witness`
to get an ordinary theory, then apply `min_prime_exclusion` to get the prime extension.
This is equivalent but more direct.

## Artifacts

- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` (modified: +~150 lines)
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (modified: +~181 lines)
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` (modified: sorry eliminated)
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` (modified: sorry eliminated)
