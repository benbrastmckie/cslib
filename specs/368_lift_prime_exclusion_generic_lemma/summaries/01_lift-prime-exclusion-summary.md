# Task 368 Implementation Summary: Lift Prime Exclusion Generic Lemma

## What Was Done

Completed the lift of the prime-exclusion / maximal-is-prime argument into a generic
`Cslib.Logic.Metalogic.PrimeExclusion` module (done by a prior agent), then refactored
the two concrete instantiations as thin wrappers.

### Phase 4 (prior agent): PrimeExclusion.lean

`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (254 lines) provides the generic
framework parameterized by:
- `Cons : Set F → Prop` — consistency predicate (use `fun _ => True` for Min)
- `cl : Set F → Set F` — deductive closure operator
- `phi_mem_cl_of_not_cons` — EFQ bridge (vacuous for Min, uses `.efq` for Int)
- `hCut` — cut/deduction-theorem witness
- `hConsChain` — preservation of `Cons` under chain unions

Key lemmas: `prime_maximal_is_prime`, `prime_exclusion`.

### Phase 5 (this agent): MinLindenbaum and IntLindenbaum refactors

**MinLindenbaum.lean** (`Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`):
- Added import `Cslib.Foundations.Logic.Metalogic.PrimeExclusion`
- Deleted `MinPrimeExcludingSupersets`, `min_excluding_base_mem`,
  `min_excluding_chain_union`, `min_maximal_is_prime` (not used externally)
- Replaced `min_prime_exclusion` body with a call to `Metalogic.prime_exclusion`
  using `Cons := fun _ => True`, `cl := minDeductiveClosure`, and
  `hCut := min_deriv_imp_of_union`

**IntLindenbaum.lean** (`Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`):
- Added import `Cslib.Foundations.Logic.Metalogic.PrimeExclusion`
- Deleted `IntPrimeExcludingSupersets`, `int_excluding_base_mem`,
  `int_excluding_chain_union`, `int_maximal_is_prime` (not used externally)
- Replaced `int_prime_exclusion` body with a call to `Metalogic.prime_exclusion`
  using `Cons := PropSetConsistent IntPropAxiom`, `cl := intDeductiveClosure`,
  and the EFQ bridge from the inconsistency witness

## Public Names Preserved

All downstream-used names are preserved:
- `MinTheory`, `MinPrimeTheory`, `min_prime_exclusion`
- `IntDCCS`, `IntPrimeDCCS`, `int_prime_exclusion`

`MinStrongCompleteness` and `IntStrongCompleteness` both build successfully.

## Verification

- `lake build MinLindenbaum IntLindenbaum PrimeExclusion`: all green
- `lake build MinStrongCompleteness IntStrongCompleteness`: both green
- `lake lint` (scoped to modified files): no warnings
- `lake exe lint-style`: no warnings
- `lake shake`: no minimization issues
- Sorry count: 0
- New axioms: 0

## Plan Deviations

- The helpers `MinPrimeExcludingSupersets` / `IntPrimeExcludingSupersets` and their
  supporting lemmas were deleted entirely (not rewritten as thin wrappers) because they
  are not referenced outside their respective files. This is cleaner than keeping them
  as stubs.
- `lake test` has pre-existing failures in task-364 Tableau/Bimodal modules (unrelated
  to this task); scoped build of relevant modules passes.
