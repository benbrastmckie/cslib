# Task 174 Research Report: Propositional Metalogic Full Connectives

Session: sess_1781317385_e83d59_174

## Executive Summary

The task extends the propositional metalogic from the `{imp, bot}` fragment to the full
five-primitive language `{atom, bot, imp, and, or}`. After comprehensive codebase analysis,
the key finding is that **most of the extension work is already done** by task 173. The
semantics (Basic.lean, Kripke.lean), soundness (all three variants), axiom definitions,
ND-Hilbert bridges, derived rules, and instance registrations all already handle `and`
and `or`. The classical completeness truth lemma already handles `and` and `or` cases.

The **only remaining work** is eliminating exactly **two `sorry`s** -- both in the backward
direction of the `or` case of the truth lemma for intuitionistic and minimal completeness.
These require **prime theories** (theories satisfying the disjunction property).

## Current State Analysis

### Files Already Complete (no changes needed)

| File | Status | Notes |
|------|--------|-------|
| `Defs.lean` | DONE | 5 constructors: atom, bot, imp, and, or |
| `Semantics/Basic.lean` | DONE | Evaluate has and/or cases |
| `Semantics/Kripke.lean` | DONE | IForces has and/or cases, persistence proved |
| `ProofSystem/Axioms.lean` | DONE | All 3 axiom sets have andI/E1/E2, orI1/I2/E |
| `ProofSystem/Derivation.lean` | DONE | Parameterized, connective-agnostic |
| `ProofSystem/Instances.lean` | DONE | ClassicalHilbert with all axiom instances |
| `ProofSystem/IntMinInstances.lean` | DONE | IntuitionisticHilbert and MinimalHilbert |
| `Metalogic/Soundness.lean` | DONE | and/or cases proved |
| `Metalogic/MinSoundness.lean` | DONE | and/or cases proved |
| `Metalogic/IntSoundness.lean` | DONE | and/or cases proved |
| `Metalogic/DeductionTheorem.lean` | DONE | Parameterized, connective-agnostic |
| `Metalogic/MCS.lean` | DONE | Parameterized, connective-agnostic |
| `Metalogic/Completeness.lean` | DONE | Classical truth lemma has and/or cases |
| `Metalogic/MinLindenbaum.lean` | DONE | MinTheory, imp witness, deductive closure |
| `Metalogic/IntLindenbaum.lean` | DONE | IntDCCS, imp witness, deductive closure |
| `NaturalDeduction/Basic.lean` | DONE | ND has and/or constructors |
| `NaturalDeduction/Equivalence.lean` | DONE | ndToHilbert handles and/or cases |
| `NaturalDeduction/HilbertDerivedRules.lean` | DONE | All derived rules for and/or |
| `NaturalDeduction/FromHilbert.lean` | DONE | Bridge helpers |
| `NaturalDeduction/DerivedRules.lean` | DONE | ND derived rules |

### Files with Sorry (the actual scope of task 174)

| File | Sorry Location | Goal |
|------|---------------|------|
| `Metalogic/MinCompleteness.lean:164` | `min_truth_lemma`, `.or` backward | `(phi or psi) in S.val -> IForces S (phi or psi)` |
| `Metalogic/IntCompleteness.lean:151` | `int_truth_lemma`, `.or` backward | `(phi or psi) in S.val -> IForces S (phi or psi)` |

## The Prime Theory Problem

### Why the Sorry Exists

The backward direction of the truth lemma for disjunction requires:
```
If (phi or psi) in S then phi in S or psi in S
```

This is the **disjunction property** (also called **primality**). For arbitrary deductively
closed sets (`MinTheory` or `IntDCCS`), this does NOT hold. A deductively closed set can
contain `phi or psi` without containing either disjunct.

For **classical MCS** (Completeness.lean), the or-backward case works because MCS has
`negation_complete`: either `phi in S` or `neg phi in S`. If `neg phi in S` and
`phi or psi in S`, then by the `orE` axiom + modus ponens, `psi in S`. This is already
proved (lines 166-196 of Completeness.lean).

For **intuitionistic/minimal** completeness, we cannot use `negation_complete` (it requires
classical logic). Instead, canonical worlds must be **prime theories** -- deductively
closed sets where the disjunction property holds.

### Standard Solution: Prime Extension (Lindenbaum for Prime Theories)

The standard approach from Troelstra & van Dalen (1988, vol 1 ch 2) and Chagrov &
Zakharyaschev (1997, ch 5):

**Definition**: A deductively closed set S is **prime** if:
  `(phi or psi) in S  implies  phi in S  or  psi in S`

**Prime Extension Lemma**: If S is consistent and deductively closed (IntDCCS/MinTheory),
and `phi or psi in S` but `phi not-in S`, then there exists a prime extension T of S
with `psi in T`.

More precisely, the Lindenbaum construction must be modified so that the resulting maximal
set is not just deductively closed, but also prime.

### Approach A: Direct Prime Construction (Recommended)

For each sorry, add the disjunction property as a requirement on canonical worlds:

1. **Define `IntPrimeDCCS`** (or equivalently, add primality to `IntDCCS`):
   ```lean
   def IntPrimeDCCS (S : Set (PL.Proposition Atom)) : Prop :=
     IntDCCS S ∧
     ∀ (φ ψ : PL.Proposition Atom), (φ.or ψ) ∈ S → φ ∈ S ∨ ψ ∈ S
   ```

2. **Prove the Prime Extension Lemma** (a strengthened Lindenbaum):
   Given a consistent set S, produce a prime deductively closed consistent superset.

   The standard proof uses a well-ordering of formulas and builds the prime extension by
   transfinite induction. For each disjunction `phi or psi` encountered during construction:
   - If `phi or psi` is in the current set, add `phi` if consistent, otherwise add `psi`

   Alternatively, use Zorn's lemma on the set of consistent deductively closed sets that
   are "prime below" a given enumeration point.

3. **Redefine canonical worlds** to use `IntPrimeDCCS` instead of `IntDCCS`.

4. **The truth lemma or-backward case** becomes immediate from the primality condition.

5. **The imp witness lemma** must be re-proved for prime theories (the extension `T` in
   `int_imp_witness` must itself be a prime DCCS).

### Approach B: Enumerate-and-Extend (Alternative)

Instead of modifying the DCCS definition, use a two-phase construction:

1. Start with a consistent set S
2. Phase 1: Apply standard Lindenbaum to get a DCCS
3. Phase 2: For each disjunction `phi or psi` in the DCCS, if neither disjunct is present,
   extend with one (maintaining consistency + deductive closure)

This is equivalent to Approach A but may be harder to formalize due to the need for
iteration over all formulas.

### Approach C: Countable Enumeration (Simplest Lean Formalization)

Since `PL.Proposition Atom` is countable when `Atom` is countable (it's a free algebra
on a countable type), we can use an enumeration:

1. Fix an enumeration `e : Nat -> PL.Proposition Atom`
2. Build a chain of sets `S_0 subset S_1 subset ...` where at step n:
   - If `e(n) = phi or psi` and `phi or psi` is in the current set:
     - Add `phi` if adding `phi` preserves consistency
     - Otherwise add `psi`
   - Otherwise do nothing (or extend for deductive closure)
3. Take the union

**Challenge**: This requires `Atom` to be `Countable` or `Encodable`. The current codebase
works with arbitrary `Atom : Type u`, so this approach would require either:
- Adding a `Countable` or `Encodable` hypothesis to the completeness theorems
- Or using a more abstract construction

### Recommended Approach

**Approach A** (Direct Prime Construction) is recommended because:
- It does not require countability
- It matches the literature (Troelstra & van Dalen, Chagrov & Zakharyaschev)
- It integrates cleanly with the existing IntDCCS/MinTheory infrastructure
- The same pattern can be reused for modal logics later

## Detailed Implementation Plan

### Phase 1: Define Prime Theory Types

**Files**: `MinLindenbaum.lean`, `IntLindenbaum.lean`

For minimal logic:
```lean
def MinPrimeTheory (S : Set (PL.Proposition Atom)) : Prop :=
  MinTheory S ∧
  ∀ (φ ψ : PL.Proposition Atom), (φ.or ψ) ∈ S → φ ∈ S ∨ ψ ∈ S
```

For intuitionistic logic:
```lean
def IntPrimeDCCS (S : Set (PL.Proposition Atom)) : Prop :=
  IntDCCS S ∧
  ∀ (φ ψ : PL.Proposition Atom), (φ.or ψ) ∈ S → φ ∈ S ∨ ψ ∈ S
```

### Phase 2: Prove Prime Extension Lemma

**Key Lemma**: For each disjunction `phi or psi`, if `S` is consistent and deductively
closed, and `phi or psi in S`, then `S union {phi}` is consistent OR `S union {psi}` is
consistent (at least one preserves consistency).

**Proof sketch**:
- Assume for contradiction that both `S union {phi}` and `S union {psi}` are inconsistent
- Then by the deduction theorem: `S |- phi -> bot` and `S |- psi -> bot`
- By orE: `S |- (phi or psi) -> bot`
- Since `phi or psi in S`: `S |- bot`
- Contradiction with consistency of S

This is a standard result and the proof components (deduction theorem, orE derivation)
are all already available in the codebase.

**For MinTheory** (no consistency requirement): The argument is slightly different since
MinTheory doesn't require consistency. Instead, we need to show that if the deductive
closure of `S union {phi}` contains `psi`, then `S` already derives `phi -> psi`, so
`psi in S` (since `phi -> psi in S` and `phi or psi in S` gives `psi` via orE + the
derivation from `S union {phi}`).

Actually, for MinTheory the approach needs more care. Let me reconsider.

**MinTheory Prime Extension**: Since MinTheory has no consistency requirement, the
standard "inconsistency implies the other disjunct" argument doesn't directly apply.
Instead:

Given `MinTheory S` and `(phi or psi) in S` with `phi not-in S`:
- The deductive closure of `S union {phi}` is a MinTheory containing both S and phi
- But we need psi to be in the result, not phi
- If phi not-in S, we need to show that psi in S (which is what we're trying to prove!)

Wait -- this is circular. For MinTheory (without consistency), we can't guarantee the
disjunction property at all without explicitly constructing prime extensions.

**Key insight**: The standard Lindenbaum for prime theories uses a different strategy.
Instead of extending an arbitrary MinTheory to a prime one, we modify the canonical
model construction:

For **minimal completeness**, canonical worlds should be **prime MinTheories** from the
start. The set of theorems `{psi | Derivable MinPropAxiom psi}` is a MinTheory, and we
need it to also be prime. But this is the **disjunction property of minimal logic** --
which does NOT hold in general for MinPropAxiom (e.g., `p or not-p` is not provable in
minimal logic, but neither is `p` nor `not-p`).

However, we don't need the theorem set to be prime. We need: for any MinTheory S, if
`phi or psi in S`, then we can extend S to a prime MinTheory where the disjunction is
resolved. This requires a **prime extension lemma using Zorn's lemma** with a refined
notion of prime supersets.

**Standard Construction (Troelstra & van Dalen style)**:

The prime extension is built by well-ordering all formulas and processing each disjunction.
Given a deductively closed set S (consistent or not), define the prime extension as follows:

1. Well-order the formulas: `phi_0, phi_1, phi_2, ...`
2. Set `S_0 = S`
3. At step `n+1`:
   - If `phi_n = A or B` and `phi_n in S_n` and `A not-in S_n` and `B not-in S_n`:
     - Let `S_{n+1} = deductive_closure(S_n union {A})` if this preserves consistency
       (for IntDCCS) or is chosen by some criterion (for MinTheory)
     - Otherwise `S_{n+1} = deductive_closure(S_n union {B})`
   - Otherwise `S_{n+1} = S_n`
4. Take `S_omega = union of S_n`

For **MinTheory** (no consistency), we need a different criterion at step 3. The standard
approach for minimal logic is:

- For MinTheory, the disjunction property is obtained by choosing the disjunct whose
  deductive closure does NOT derive ψ (for the imp witness) or by using the fact that
  if `S union {A}` derives ψ and `S union {B}` derives ψ, then by orE, `S` derives ψ
  (since `A or B in S`).

This means: if `A or B in S` and neither `A in S` nor `B in S`, then at least one of
`deductive_closure(S union {A})` or `deductive_closure(S union {B})` does not contain ψ
(for the specific ψ we're trying to exclude in the imp witness). This requires threading
the "excluded formula" through the construction.

### Revised Strategy for MinTheory

For the minimal completeness truth lemma, the or-backward sorry requires:
```
MinTheory S and (phi or psi) in S.val ==> phi in S.val or psi in S.val
```

This is only true if S is a **prime** MinTheory. So we need to:

1. Define `MinPrimeTheory` = MinTheory + disjunction property
2. Change `MinCanonicalWorld` to use `MinPrimeTheory` instead of `MinTheory`
3. Prove that the min_imp_witness produces a `MinPrimeTheory` (not just a MinTheory)
4. Prove that `min_theorems_theory` is a `MinPrimeTheory`
   - Wait: is the set of theorems prime? Only if minimal logic has the disjunction property
   - **YES**: Minimal logic HAS the disjunction property (provable by cut elimination or
     model-theoretic argument). If `|- A or B` in minimal logic, then `|- A` or `|- B`.
   - This is a significant auxiliary result that must be proved.

Actually, let me reconsider. The disjunction property of minimal logic (and intuitionistic
logic) is: if `|- A or B` then `|- A` or `|- B`. But this is a META-property of the logic,
not a property of arbitrary theories. The canonical world `W_0` is the set of theorems,
and we need `W_0` to be prime. The disjunction property of the logic ensures this.

**BUT**: the other canonical worlds (created by imp_witness) are NOT necessarily the
theorem set. They are arbitrary deductively closed (and possibly consistent) extensions.
The imp_witness creates worlds that exclude specific formulas. These worlds need to be
prime too.

The standard solution is indeed to use a **prime extension lemma**: any deductively closed
consistent set can be extended to a prime deductively closed consistent set. This uses
Zorn's lemma (or transfinite construction).

### Phase 2 Detailed: Prime Extension via Zorn's Lemma

The key insight: We can use Zorn's lemma on the partially ordered set of
`{T : Set F | S subset T and T is consistent-DC and phi not-in T}`
to find a maximal element. A maximal element of this set is prime.

**Proof that a maximal element is prime**:
- Let T be maximal in the set of consistent deductively closed supersets of S with `phi not-in T`
- Suppose `A or B in T` but `A not-in T` and `B not-in T`
- Then `deductive_closure(T union {A})` is a consistent DC superset of S
- If `phi in deductive_closure(T union {A})`: then by cut, `T |- A -> phi`
- Similarly if `phi in deductive_closure(T union {B})`: then `T |- B -> phi`
- Then by orE: `T |- (A or B) -> phi`, and since `A or B in T`, `T |- phi`, so `phi in T`.
  Contradiction.
- So at least one of `deductive_closure(T union {A})` or `deductive_closure(T union {B})`
  does not contain `phi`. This is a consistent DC superset of T not containing phi,
  contradicting maximality.

This approach works for **IntDCCS** (where consistency is required). For **MinTheory**
(no consistency), the argument is similar but we need to track the excluded formula.

Actually, for MinTheory, the argument is simpler. A MinTheory T is prime iff for all
`A or B in T`, `A in T` or `B in T`. We can prove:

**Claim**: If T is a maximal MinTheory in the set
`{T' | S subset T' and T' is a MinTheory and psi not-in T'}`,
then T is prime.

**Proof**: Suppose `A or B in T` but `A not-in T` and `B not-in T`.
- Let `T_A = minDeductiveClosure(T union {A})`. This is a MinTheory containing T.
- If `psi in T_A`: then by cut, there exists `L subset T` with `L |- A -> psi`
- Similarly `T_B = minDeductiveClosure(T union {B})`. If `psi in T_B`: exists `L' subset T`
  with `L' |- B -> psi`
- If both `psi in T_A` and `psi in T_B`: then by orE + deductive closure,
  `psi in T` (since `A or B in T`). Contradiction.
- So at least one of T_A, T_B does not contain psi. This contradicts maximality of T.

This proof uses exactly the same orE-based argument. The key auxiliary is the
**disjunction cut lemma**:
```
If L₁ ⊢ A → ψ and L₂ ⊢ B → ψ and A ∨ B ∈ S and L₁ ⊆ S and L₂ ⊆ S,
then ψ ∈ S (via orE + deductive closure)
```

### Phase 3: Update Canonical Models and Truth Lemma

Replace `MinCanonicalWorld` and `IntCanonicalWorld` with prime versions:

```lean
def MinCanonicalWorld (Atom : Type*) :=
  { S : Set (PL.Proposition Atom) // MinPrimeTheory S }

def IntCanonicalWorld (Atom : Type*) :=
  { S : Set (PL.Proposition Atom) // IntPrimeDCCS S }
```

The truth lemma or-backward case then follows immediately from the primality condition.

### Phase 4: Update imp_witness for Prime Extensions

The `min_imp_witness` and `int_imp_witness` must produce prime canonical worlds.
This requires showing that the deductive closure of `S union {phi}`, when extended to
a maximal element (not containing psi), is prime.

This is the prime extension lemma from Phase 2.

### Phase 5: Update Theorem Sets

Show that `min_theorems_theory` and `int_theorems_dccs` are prime:
- The set of theorems `{psi | Derivable Axioms psi}` is prime iff the logic has the
  disjunction property.
- For minimal logic: if `|- A or B` then `|- A` or `|- B` (standard result).
- For intuitionistic logic: same (the disjunction property is a fundamental property of
  IPC).

**Proof strategy**: Use the completeness theorem itself (circular?) No -- we need an
independent proof. The standard approach is:

The disjunction property follows from the existence of ANY prime model. Since we're
building the completeness proof, we can't use completeness to prove the disjunction
property.

**Alternative**: We don't need the theorem set to be prime per se. We need only that
any consistent DC set can be extended to a prime DC set. The canonical model construction
starts from the theorem set, and the imp_witness extends it. As long as imp_witness
produces prime extensions, the truth lemma works. The initial world `W_0` is the theorem
set, and we need it to be prime.

**Key observation**: We CAN avoid requiring the theorem set to be prime by using a
different construction. Instead of using the theorem set as `W_0`, we use the prime
extension of the theorem set. The truth lemma at `W_0` then gives:
- `phi not in W_0` implies `phi not forced at W_0`
- But `W_0` is a prime extension of the theorems, so it might contain extra formulas
  beyond what's provable.

Actually this doesn't work. The completeness proof assumes `phi` is not derivable, then
shows `phi not in W_0` where `W_0` is the theorem set. If `W_0` is the theorem set itself,
`phi not in W_0` is exactly `phi not derivable`. If `W_0` is a prime extension, it might
contain more formulas.

**Resolution**: The correct approach is:

For `min_completeness`:
- Start with `W_0 = {psi | Derivable MinPropAxiom psi}` (theorem set)
- We need `W_0` to be a prime MinTheory
- The disjunction property of minimal logic: if `|- A or B` then `|- A` or `|- B`
- This must be proved independently

For `int_completeness`:
- Start with `W_0 = {psi | Derivable IntPropAxiom psi}` (theorem set)
- We need `W_0` to be a prime IntDCCS
- The disjunction property of IPC: if `|- A or B` then `|- A` or `|- B`
- This must be proved independently

**Proof of disjunction property (model-theoretic)**:
- Assume `|- A or B` (derivable in minimal/intuitionistic logic)
- Assume `not |- A` and `not |- B`
- Build a model where A is not forced and B is not forced
- By soundness, `A or B` should be forced (since it's derivable)
- But `A or B` forced means `A` forced or `B` forced. Contradiction.

Wait -- this IS circular with the completeness we're proving! The model where A is not
forced requires the completeness construction (which requires prime theories).

**Resolution**: We avoid the disjunction property entirely by using a different
construction for `W_0`.

**Alternative approach**: Instead of requiring `W_0` to be the exact theorem set, define
`W_0` as the **prime extension** of the theorem set. This ensures primality. The
completeness proof becomes:

1. Assume `phi` is not derivable
2. Let `W_0 = prime_extension({psi | Derivable Axioms psi})`
3. `W_0` is a prime MinTheory/IntPrimeDCCS
4. `W_0` extends the theorem set, so every theorem is in `W_0`
5. We need `phi not in W_0`
6. Since the theorem set is consistent and doesn't contain `phi`...
   - Actually, the prime extension MIGHT contain `phi` (it extends the theorem set)

This doesn't work directly. The issue is that the prime extension might add `phi`.

**Correct resolution**: Use a **prime extension that excludes phi**. Specifically:

For `min_completeness`:
1. Assume `phi` is not derivable
2. The set `{psi | Derivable MinPropAxiom psi}` is a MinTheory not containing `phi`
3. Apply the prime extension lemma (from Phase 2) to get a prime MinTheory `W_0` that
   extends the theorems and does NOT contain `phi`
4. Use `W_0` as the initial canonical world

This is the approach used in Chagrov & Zakharyaschev. The prime extension lemma needs
to produce a prime extension that **excludes a specific formula**.

**Prime Exclusion Lemma**:
```
If S is a MinTheory (or IntDCCS) and phi not-in S,
then there exists a prime MinTheory (or IntPrimeDCCS) T with S subset T and phi not-in T.
```

This is proved by Zorn's lemma on the set
`{T | S subset T and T is MinTheory/IntDCCS and phi not-in T}`.
The maximal element is prime (proved above).

### Revised Phase Structure

**Phase 1**: Define prime theory types and basic properties
- `MinPrimeTheory`, `IntPrimeDCCS` definitions
- Basic accessors (a prime theory is a theory, etc.)

**Phase 2**: Prove the prime exclusion lemma (both min and int versions)
- Chain union preserves MinTheory/IntDCCS and phi-exclusion
- Zorn's lemma gives maximal element
- Maximal element is prime (via orE argument)
- For MinTheory: `min_prime_exclusion`
- For IntDCCS: `int_prime_exclusion`

**Phase 3**: Update imp_witness to produce prime results
- `min_imp_witness_prime`: produces `MinPrimeTheory` extensions
- `int_imp_witness_prime`: produces `IntPrimeDCCS` extensions
- Uses prime exclusion lemma internally

**Phase 4**: Update canonical models and truth lemma
- Redefine `MinCanonicalWorld` to use `MinPrimeTheory`
- Redefine `IntCanonicalWorld` to use `IntPrimeDCCS`
- The or-backward case of truth lemma follows from primality
- Update `min_completeness` to use prime exclusion for W_0
- Update `int_completeness` to use prime exclusion for W_0

**Phase 5**: CI verification

## Proof Component Inventory

### Available in Codebase (can be reused)

| Component | Location | Reuse |
|-----------|----------|-------|
| `MinTheory` definition | MinLindenbaum.lean:64 | Extended with primality |
| `IntDCCS` definition | IntLindenbaum.lean:47 | Extended with primality |
| `minDeductiveClosure` | MinLindenbaum.lean:185 | Used in prime extension |
| `intDeductiveClosure` | IntLindenbaum.lean:203 | Used in prime extension |
| `min_deriv_imp_of_union` | MinLindenbaum.lean:127 | Cut lemma for union |
| `int_deriv_imp_of_union` | IntLindenbaum.lean:144 | Cut lemma for union |
| `finite_list_in_chain_member` | Consistency.lean:105 | Chain argument |
| `zorn_subset_nonempty` | Mathlib | Core Zorn's lemma |
| `deductionTheorem` | DeductionTheorem.lean:128 | For orE-based arguments |
| `orE` axiom | Axioms.lean | For prime proof |
| `prop_has_deduction_theorem` | DeductionTheorem.lean:196 | DT instance |

### Must Be Built

| Component | Estimated Size | Difficulty |
|-----------|---------------|------------|
| `MinPrimeTheory` definition | ~5 lines | Low |
| `IntPrimeDCCS` definition | ~5 lines | Low |
| `min_prime_chain_union` | ~30 lines | Medium |
| `int_prime_chain_union` | ~30 lines | Medium |
| `min_prime_maximal_is_prime` | ~40 lines | Medium-High |
| `int_prime_maximal_is_prime` | ~40 lines | Medium-High |
| `min_prime_exclusion` | ~40 lines | Medium |
| `int_prime_exclusion` | ~40 lines | Medium |
| `min_imp_witness_prime` | ~30 lines | Medium |
| `int_imp_witness_prime` | ~30 lines | Medium |
| `min_theorems_prime` | ~30 lines | Medium |
| `int_theorems_prime` | ~30 lines | Medium |
| Updated `min_truth_lemma` | ~5 lines (or case) | Low |
| Updated `int_truth_lemma` | ~5 lines (or case) | Low |
| Updated `min_completeness` | ~15 lines | Low |
| Updated `int_completeness` | ~15 lines | Low |

**Total estimated new code**: ~400 lines

## Critical Design Decisions

### 1. Where to place prime theory definitions

**Option A**: In MinLindenbaum.lean/IntLindenbaum.lean alongside existing definitions.
**Option B**: In new files MinPrimeLindenbaum.lean/IntPrimeLindenbaum.lean.

**Recommendation**: Option A. The prime theory definitions are extensions of the existing
MinTheory/IntDCCS and belong in the same files. The Lindenbaum files are the natural home
for the prime extension lemma.

### 2. Whether to modify existing definitions or add new ones

**Option A**: Replace `MinTheory` with `MinPrimeTheory` everywhere.
**Option B**: Keep `MinTheory` and add `MinPrimeTheory` as a strengthening.

**Recommendation**: Option B. The existing `MinTheory` is used in `min_imp_witness` and
`min_theorems_theory`. We add `MinPrimeTheory` and prove that the canonical construction
produces prime theories. The `MinCanonicalWorld` definition changes from `MinTheory` to
`MinPrimeTheory`, but the underlying MinTheory results are still used.

### 3. botForces parameterization preservation

The task description emphasizes: "RETAIN botForces parameterization of IForces - do NOT
hard-code bot to False."

**Status**: This is already preserved. The `IForces` definition in Kripke.lean uses
`bot_forces : World -> Prop` as a parameter. The `MValid` definition quantifies over
all upward-closed `bot_forces`. The `IValid` specializes to `fun _ => False`. No changes
needed.

### 4. The disjunction property question

For the theorem set `W_0`, we need to show it's prime. We have two options:

**Option A**: Prove the disjunction property independently (if `|- A or B` then
`|- A` or `|- B`), making `min_theorems_theory` / `int_theorems_dccs` prime.

**Option B**: Use the prime exclusion lemma to produce a prime extension of the theorem
set that excludes `phi`, avoiding the need for the disjunction property.

**Recommendation**: Option B. This avoids the need for an independent proof of the
disjunction property (which itself requires a completeness-like argument or proof-theoretic
methods like cut elimination). The completeness proof then says:

```
Assume phi is not derivable.
Let S = {psi | Derivable Axioms psi}.
S is a consistent DCCS/MinTheory.
phi not-in S.
By prime_exclusion, there exists prime T with S subset T and phi not-in T.
Use T (not S) as W_0 in the canonical model.
Truth lemma at W_0: phi not-in T implies phi not forced at W_0.
Soundness gives phi forced at W_0. Contradiction.
```

Wait -- for the validity side, we need `phi` to be forced at EVERY world of EVERY model.
The canonical model is constructed, and we just need `phi` forced at `W_0`. Soundness
says: if `|- phi` then `phi` forced everywhere. But we're proving the converse (completeness):
if `phi` valid then `|- phi`. The proof by contrapositive: if `not |- phi`, build a model
where `phi` is not forced.

The canonical model has worlds = all prime MinTheories (or IntPrimeDCCS). The validity
says phi is forced at every world. So if phi is not forced at W_0, phi is not valid.

**Revised proof sketch for min_completeness**:
1. Assume `MValid phi` (phi forced at every world of every model)
2. Assume `not Derivable MinPropAxiom phi` for contradiction
3. `S = {psi | Derivable MinPropAxiom psi}` is a MinTheory
4. `phi not-in S`
5. By prime exclusion: exists `W_0 : MinPrimeTheory` with `S subset W_0` and `phi not-in W_0`
6. Canonical model: worlds = `MinPrimeTheory`, valuation = atom membership, botForces = bot membership
7. Truth lemma: forcing iff membership (uses primality for or-backward)
8. `phi not forced at W_0` (by truth lemma + phi not-in W_0)
9. But `MValid phi` gives `phi forced at W_0`. Contradiction.

This works. The imp_witness also needs to produce prime MinTheories. The imp_witness says:
if `phi -> psi not-in S` (where S is a prime MinTheory), then there exists a prime MinTheory
T with S subset T, phi in T, psi not-in T. This is the prime exclusion applied to
`deductive_closure(S union {phi})` excluding `psi`.

## Blockers

None identified. All proof components have known constructions using available tools
(Zorn's lemma, deduction theorem, orE axiom).

## Key References

- **Troelstra & van Dalen (1988)**: *Constructivism in Mathematics*, vol 1, ch 2 --
  prime extension lemma for intuitionistic logic
- **Chagrov & Zakharyaschev (1997)**: *Modal Logic*, ch 5 -- canonical model construction
  with prime theories
- **van Dalen (2004)**: *Logic and Structure*, Section 5.3 -- Kripke completeness for IPC
