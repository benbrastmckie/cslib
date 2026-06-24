# Task 339 Research: Unify swapTemporal

## Key Findings

### 1. Distinct Inductive Types Prevent Structural Subtyping

- `Temporal.Formula Atom`: 5 constructors (`atom`, `bot`, `imp`, `untl`, `snce`)
- `Bimodal.Formula Atom`: 6 constructors (`atom`, `bot`, `imp`, `box`, `untl`, `snce`)

Lean 4 cannot extend inductives, so `Bimodal.Formula` is not a subtype of `Temporal.Formula`. A one-way embedding `Temporal.Formula.toBimodal` exists in `TemporalEmbedding.lean` but has no inverse.

### 2. Typeclass-Based Approach Not Recommended

`swapTemporal` pattern-matches on inductive constructors directly (`.untl`/`.snce` swap). A typeclass would need to abstract over recursive inductive structure, which doesn't fit Lean's typeclass pattern. No existing `HasSwapTemporal` in Foundations.

### 3. Actual Duplication is Narrower Than Estimated

| Theorem | Temporal Lines | Bimodal Lines | Identical? |
|---------|---------------|---------------|------------|
| `swapTemporal` (def) | 337-342 (5) | 128-134 (6) | Near-identical, Bimodal adds `.box` case |
| `swapTemporal_involution` | 344-352 (8) | 136-145 (9) | Near-identical, Bimodal adds `box` case |
| `swapTemporal_neg` | 354-357 (3) | 147-150 (3) | Identical proof structure |
| `swapTemporal_someFuture` | 360-363 (3) | 158-161 (3) | Identical |
| `swapTemporal_somePast` | 366-369 (3) | 163-167 (3) | Identical |
| `swapTemporal_allFuture` | 372-375 (3) | 169-173 (3) | Identical |
| `swapTemporal_allPast` | 378-381 (3) | 175-179 (3) | Identical |
| `atoms` (def) | 437-442 (5) | 188-194 (6) | Near-identical, Bimodal adds `box` case |
| `atoms_swapTemporal` | 445-452 (7) | 196-205 (9) | Near-identical, Bimodal adds `box` case |

- Bimodal-only: `swapTemporal_diamond` (3 lines)
- Temporal-only: `swapTemporal_next`, `swapTemporal_prev`, `swapTemporal_strongRelease`, `swapTemporal_strongTrigger` (~20 lines)

**Truly duplicated code: ~38 lines** (the 5 derived-operator exchange theorems with identical proofs). The definition, involution, atoms, and atoms_swapTemporal all differ by the `box` case.

### 4. Embedding-Based Approach Has Significant Problems

Proving `toBimodal_swapTemporal` and deriving Bimodal theorems from Temporal versions would:
1. Break downstream `simp only [Formula.swapTemporal, truthAt]` chains
2. Lose `@[simp]` attribute behavior on Bimodal's theorems
3. Couple Bimodal proofs to the Temporal embedding unnecessarily

### 5. Downstream Consumer Analysis

**Bimodal consumers** (all use `Bimodal.Formula.swapTemporal` directly):
- `Soundness/Core.lean` — `truth_at_swap_swap`
- `Soundness/DenseValidity.lean` — 15+ uses, heavy simp chains
- `Core/MCSProperties.lean` — `swapTemporal_involution`
- `Separation/TemporalClosure.lean` — `swap_no_U_nested_gives_no_S_nested`
- `ConservativeExtension/ExtFormula.lean` — `embedFormula_swapTemporal`

**Temporal consumers** (all use `Temporal.Formula.swapTemporal`):
- `Soundness.lean`, `DenseSoundness.lean` — temporal duality
- `DenseCompleteness.lean` — swap-involution chains
- `CompletenessHelpers.lean`, `TemporalContent.lean` — swap-involution rewrites
- `ProofSystem/Derivation.lean` — `temporal_duality` rule
- `GeneralizedNecessitation.lean` — swap in derivation chains

## Recommendation

**Mark task as low-priority or abandon.** The duplication is structural (inherent to distinct inductive types) rather than abstraction-level. The 38 lines of truly identical proof code are trivial 1-2 line `simp` proofs. Unification risks breaking downstream `simp` chains that depend on concrete `Formula.swapTemporal` unfolding.

If the task must proceed, the safest minimal approach: factor only the 5 derived-operator exchange theorems via a new `HasSwapTemporal` typeclass, but this saves ~15 lines in Bimodal at the cost of introducing a new typeclass with careful `@[simp]` preservation.
