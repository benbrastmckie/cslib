# Implementation Plan: Propositional Metalogic Full Connectives (Prime Theories)

- **Task**: 174 - Extend propositional metalogic to full five-primitive connectives (and/or cases for completeness)
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Task 173 (completed)
- **Research Inputs**: specs/174_propositional_metalogic_full_connectives/reports/01_metalogic-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Task 173 completed almost all and/or extension work across the propositional metalogic. The only remaining work is eliminating two `sorry`s in the or-backward direction of `min_truth_lemma` (MinCompleteness.lean:164) and `int_truth_lemma` (IntCompleteness.lean:151). Both require the **disjunction property**: if `(phi or psi) in S` then `phi in S or psi in S`. This does not hold for arbitrary deductively closed sets; canonical worlds must be **prime theories** (theories satisfying the disjunction property). The implementation uses prime extension via Zorn's lemma on the set of phi-excluding supersets, proving that maximal elements are prime via the orE axiom argument.

### Research Integration

Key findings from the research report:

1. **Scope**: Only 2 sorries remain. All and/or infrastructure (semantics, soundness, axioms, ND bridges, derived rules) is already complete from task 173.
2. **Mathematical approach**: Prime Extension via Zorn's Lemma (Approach A from research). Define `MinPrimeTheory` and `IntPrimeDCCS` with the disjunction property, prove prime exclusion lemma using Zorn on phi-excluding supersets, update canonical worlds and completeness proofs.
3. **Key insight**: Use prime exclusion (extending to a prime theory that excludes a specific formula) rather than requiring the disjunction property of the logic itself, avoiding circularity with the completeness theorem.
4. **Available infrastructure**: `zorn_subset_nonempty` (Mathlib), `finite_list_in_chain_member` (Consistency.lean), `min_deriv_imp_of_union`/`int_deriv_imp_of_union` (cut lemmas), `deductionTheorem`, all orE axioms.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the propositional metalogic completeness proofs. While not directly listed as a remaining item on ROADMAP.md, it completes foundational infrastructure (prime theories for intuitionistic/minimal completeness) that supports the broader goal of a fully proved Kripke completeness pipeline used by downstream modal, temporal, and bimodal metalogic.

## Goals & Non-Goals

**Goals**:
- Eliminate both `sorry`s in MinCompleteness.lean and IntCompleteness.lean
- Define `MinPrimeTheory` and `IntPrimeDCCS` with the disjunction property
- Prove prime exclusion lemmas via Zorn's lemma for both minimal and intuitionistic logic
- Update `min_imp_witness` and `int_imp_witness` to produce prime extensions
- Redefine `MinCanonicalWorld` and `IntCanonicalWorld` to use prime theory types
- Update completeness proofs to use prime exclusion for the initial world W0
- Retain botForces parameterization of IForces (do NOT hard-code bot to False)
- Pass full CI pipeline (lake build, lake test, checkInitImports, lint-style)

**Non-Goals**:
- Modifying classical completeness (Completeness.lean) -- already handles or-backward via negation_complete
- Proving the standalone disjunction property of minimal/intuitionistic logic (avoided by prime exclusion approach)
- Changing any soundness proofs or axiom definitions
- Modifying any files listed as "DONE" in the research report

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Zorn's lemma chain argument for phi-excluding sets is more complex than standard Lindenbaum | M | M | Reuse `finite_list_in_chain_member` and `consistent_chain_union` patterns from Consistency.lean |
| MinTheory prime extension (no consistency requirement) needs different maximality argument than IntDCCS | M | M | Thread the excluded formula through the Zorn construction; maximality argument uses orE + deductive closure |
| Updating imp_witness to produce prime results requires composing prime exclusion with deductive closure | M | L | Prime exclusion lemma applies directly to deductive closure output; same pattern as existing imp_witness |
| Redefining canonical world types may break downstream imports or proofs | H | L | Only MinCompleteness.lean and IntCompleteness.lean define/use these types; no downstream consumers |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Define Prime Theory Types and Prove Prime Chain Union [COMPLETED]

**Goal**: Define `MinPrimeTheory` and `IntPrimeDCCS` and prove that chain unions of phi-excluding sets preserve the relevant properties (input to Zorn's lemma).

**Tasks**:
- [ ] In MinLindenbaum.lean: Define `MinPrimeTheory S` as `MinTheory S` plus the disjunction property `forall phi psi, (phi.or psi) in S -> phi in S or psi in S`
- [ ] In MinLindenbaum.lean: Define `MinPrimeExcludingSupersets S phi` as the set `{T | S subset T and MinTheory T and phi not-in T}`
- [ ] In MinLindenbaum.lean: Prove `min_excluding_chain_union` -- the union of a nonempty chain of MinTheory phi-excluding supersets of S is itself a MinTheory phi-excluding superset
- [ ] In IntLindenbaum.lean: Define `IntPrimeDCCS S` as `IntDCCS S` plus the disjunction property
- [ ] In IntLindenbaum.lean: Define `IntPrimeExcludingSupersets S phi` as the set `{T | S subset T and IntDCCS T and phi not-in T}`
- [ ] In IntLindenbaum.lean: Prove `int_excluding_chain_union` -- chain union preserves IntDCCS and phi-exclusion
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.MinLindenbaum` and `lake build Cslib.Logics.Propositional.Metalogic.IntLindenbaum` to verify

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - Add prime theory definition, chain union lemma
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - Add prime DCCS definition, chain union lemma

**Verification**:
- Both files compile without errors via scoped `lake build`
- Definitions use correct types and match the mathematical intent
- Chain union proofs follow the pattern from `Consistency.lean:consistent_chain_union`

---

### Phase 2: Prove Prime Exclusion Lemma (Zorn + Maximal-is-Prime) [COMPLETED]

**Goal**: Prove the prime exclusion lemma for both MinTheory and IntDCCS: given a phi-excluding theory, extend to a prime phi-excluding theory via Zorn's lemma and the maximal-is-prime argument.

**Tasks**:
- [ ] In MinLindenbaum.lean: Prove `min_maximal_is_prime` -- if T is maximal in MinPrimeExcludingSupersets, then T is prime. Proof: assume `A or B in T`, `A not-in T`, `B not-in T`; show `minDeductiveClosure(T union {A})` and `minDeductiveClosure(T union {B})` are both MinTheory supersets of T; if both contain phi, then by `min_deriv_imp_of_union`, `T |- A -> phi` and `T |- B -> phi`, hence by orE + deductive closure, `phi in T`, contradiction. So at least one does not contain phi, contradicting maximality.
- [ ] In MinLindenbaum.lean: Prove `min_prime_exclusion` -- if `MinTheory S` and `phi not-in S`, then exists `T` with `S subset T`, `MinPrimeTheory T`, and `phi not-in T`. Uses `zorn_subset_nonempty` on `MinPrimeExcludingSupersets` with `min_excluding_chain_union` for chain condition and `min_maximal_is_prime` for primality.
- [ ] In IntLindenbaum.lean: Prove `int_maximal_is_prime` -- same argument for IntDCCS, additionally threading consistency through the deductive closure construction using `intDeductiveClosure_is_dccs`
- [ ] In IntLindenbaum.lean: Prove `int_prime_exclusion` -- Zorn's lemma version for IntDCCS
- [ ] Run scoped builds to verify

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - Add maximal-is-prime and prime exclusion lemmas
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - Add maximal-is-prime and prime exclusion lemmas

**Verification**:
- Both prime exclusion lemmas compile and are sorry-free
- The Zorn application follows the same pattern as `set_lindenbaum` in Consistency.lean
- The orE-based argument for maximal-is-prime uses existing `min_deriv_imp_of_union`/`int_deriv_imp_of_union`

---

### Phase 3: Update Canonical Models, Truth Lemmas, and Imp Witnesses [COMPLETED]

**Goal**: Redefine canonical worlds to use prime theory types, update imp_witness to produce prime extensions, and eliminate both sorries in the truth lemma or-backward cases.

**Tasks**:
- [ ] In MinCompleteness.lean: Redefine `MinCanonicalWorld` to `{ S : Set (PL.Proposition Atom) // MinPrimeTheory S }`
- [ ] In MinCompleteness.lean: Add `min_imp_witness_prime` -- if S is MinPrimeTheory and `phi -> psi not-in S`, produce a MinPrimeTheory T with `S subset T`, `phi in T`, `psi not-in T`. Implementation: compute `minDeductiveClosure(S.val union {phi})` (a MinTheory containing phi), then apply `min_prime_exclusion` excluding psi to get a prime extension T.
- [ ] In MinCompleteness.lean: Update `min_truth_lemma` imp-forward case to use `min_imp_witness_prime` instead of `min_imp_witness`
- [ ] In MinCompleteness.lean: Fill in the or-backward sorry: from `MinPrimeTheory S` and `(phi.or psi) in S.val`, extract the disjunction property to get `phi in S.val or psi in S.val`, then apply recursive truth lemma
- [ ] In MinCompleteness.lean: Update `min_completeness` to use `min_prime_exclusion` for the initial world W0 instead of directly using `min_theorems_theory`
- [ ] In IntCompleteness.lean: Redefine `IntCanonicalWorld` to `{ S : Set (PL.Proposition Atom) // IntPrimeDCCS S }`
- [ ] In IntCompleteness.lean: Add `int_imp_witness_prime` -- same pattern for IntDCCS
- [ ] In IntCompleteness.lean: Update `int_truth_lemma` imp-forward case to use `int_imp_witness_prime`
- [ ] In IntCompleteness.lean: Fill in the or-backward sorry using the primality condition of IntPrimeDCCS
- [ ] In IntCompleteness.lean: Update `int_completeness` to use `int_prime_exclusion` for W0
- [ ] Run scoped builds for both modules

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` - Redefine canonical world, add prime imp_witness, eliminate sorry, update completeness
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` - Same changes for intuitionistic version

**Verification**:
- Both sorry statements are eliminated
- `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness` passes
- `lake build Cslib.Logics.Propositional.Metalogic.IntCompleteness` passes
- The `min_truth_lemma` and `int_truth_lemma` theorems are sorry-free
- The `min_completeness` and `int_completeness` theorems are sorry-free
- botForces parameterization is preserved (minBotForces unchanged)

---

### Phase 4: CI Verification and Cleanup [IN PROGRESS]

**Goal**: Run the full CI verification pipeline and clean up any style or import issues.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports` (verify Cslib.Init imports)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Fix any lint or style issues found
- [ ] Verify no `sorry` remains in any modified file using `lean_verify` or grep
- [ ] Verify the docstrings and comments are updated to reflect the prime theory approach

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- Any files that fail lint or style checks (minor fixes only)

**Verification**:
- All CI commands pass with exit code 0
- `grep -rn "sorry" Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` returns no results
- `grep -rn "sorry" Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` returns no results

## Testing & Validation

- [ ] `lake build` passes (no compilation errors)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No `sorry` in MinCompleteness.lean or IntCompleteness.lean
- [ ] `min_completeness` and `int_completeness` are sorry-free theorems
- [ ] `min_soundness_completeness` and `int_soundness_completeness` are sorry-free biconditionals
- [ ] Classical Completeness.lean is unchanged and still compiles
- [ ] botForces parameterization of IForces is preserved (minBotForces uses bot membership, not False)

## Artifacts & Outputs

- `specs/174_propositional_metalogic_full_connectives/plans/01_implementation-plan.md` (this file)
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` (modified: prime theory defs, chain union, prime exclusion)
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (modified: prime DCCS defs, chain union, prime exclusion)
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` (modified: prime canonical worlds, sorry elimination)
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` (modified: prime canonical worlds, sorry elimination)

## Rollback/Contingency

All changes are confined to 4 files in `Cslib/Logics/Propositional/Metalogic/`. If the prime extension approach encounters unexpected difficulties:

1. Revert all changes with `git checkout -- Cslib/Logics/Propositional/Metalogic/{MinLindenbaum,IntLindenbaum,MinCompleteness,IntCompleteness}.lean`
2. The sorries are non-blocking for the rest of the codebase (no downstream dependencies on the or-backward case)
3. Alternative approach: Countable enumeration (Approach C from research) could be attempted, but requires adding a `Countable` hypothesis on `Atom`
