# Teammate A — Primary Approach Findings
## Task 252: Acceptance Conditions Zoo (Rabin + Parity)

---

## Key Findings

### 1. Existing Infrastructure (What We Have)

**`DA.Buchi` structure** (`Cslib/Computability/Automata/DA/Basic.lean`):
```lean
structure Buchi (State Symbol : Type*) extends DA State Symbol where
  accept : Set State
-- Acceptance: ∃ᶠ k in atTop, a.run xs k ∈ a.accept
```

**`DA.Muller` structure** (same file):
```lean
structure Muller (State Symbol : Type*) extends DA State Symbol where
  accept : Set (Set State)
-- Acceptance: (a.run xs).infOcc ∈ a.accept
```

**`infOcc` predicate** (`Cslib/Foundations/Data/OmegaSequence/InfOcc.lean`):
```lean
def infOcc (xs : ωSequence α) : Set α :=
  { x | ∃ᶠ k in atTop, xs k = x }
```
- `mem_infOcc`: `x ∈ xs.infOcc ↔ ∃ᶠ k in atTop, xs k = x`
- `infOcc_finite [Finite α]`: infOcc is always finite for finite-state automata
- `infOcc_nonempty [Finite α]`: infOcc is always nonempty (pigeonhole)
- `frequently_in_finite_type`: key bridge lemma connecting `∃ᶠ k, xs k ∈ s` to `∃ x ∈ s, ∃ᶠ k, xs k = x`

**`DA.IsLoop`** (`BuchiChar.lean`):
```lean
def IsLoop (da : DA State Symbol) (S : Set State) : Prop :=
  S.Nonempty ∧ ∀ s ∈ S, ∀ s' ∈ S, ∃ w : List Symbol, w ≠ [] ∧ da.mtr s w = s'
```
Already scoped for reuse in Rabin characterizations (noted in the docstring of that file).

**`ωAcceptor` typeclass** (`Cslib/Computability/Automata/Acceptors/OmegaAcceptor.lean`):
```lean
class ωAcceptor (A : Type u) (Symbol : outParam (Type v)) where
  Accepts (a : A) (xs : ωSequence Symbol) : Prop
```
Every new acceptance condition structure must implement this typeclass.

### 2. No Existing Rabin or Parity Definitions

Local search for `Rabin` and `Parity` returned empty. Mathlib also has no Rabin/parity omega-automata definitions. These are entirely new to CSLib.

### 3. Module System Pattern

Files use Lean 4's `module` keyword + `public import` pattern (not `import`). Every file in `DA/` opens with:
```lean
module
public import Cslib.Computability.Automata.DA.Basic  -- or other deps
```
New files `Rabin.lean`, `Parity.lean`, `Conversions.lean` must follow this exact pattern.

### 4. Rabin Acceptance Formalization

**Mathematical definition**: A run ρ is Rabin-accepting for pairs `(E₁,F₁),...,(Eₖ,Fₖ)` if there exists `i` such that:
- `Inf(ρ) ∩ Eᵢ = ∅` (Eᵢ is eventually avoided)
- `Inf(ρ) ∩ Fᵢ ≠ ∅` (Fᵢ is visited infinitely often)

**Recommended Lean 4 formalization** — two equivalent approaches:

**Approach A (using `infOcc` directly — aligns with Muller style):**
```lean
structure Rabin (State Symbol : Type*) extends DA State Symbol where
  pairs : List (Set State × Set State)  -- List of (E_i, F_i) pairs

instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (a : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ (EF : Set State × Set State), EF ∈ a.pairs ∧
      (a.run xs).infOcc ∩ EF.1 = ∅ ∧
      ((a.run xs).infOcc ∩ EF.2).Nonempty
```

**Approach B (using `∃ᶠ` — aligns with Büchi style):**
```lean
instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (a : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ (EF : Set State × Set State), EF ∈ a.pairs ∧
      (¬ ∃ᶠ k in atTop, a.run xs k ∈ EF.1) ∧
      (∃ᶠ k in atTop, a.run xs k ∈ EF.2)
```

**Recommendation: Approach A** using `infOcc` for consistency with the Muller acceptance style and to make the Muller↔Rabin conversions clean. The equivalence between the two is:
- `Inf(ρ) ∩ E = ∅` ↔ `¬ ∃ᶠ k in atTop, run xs k ∈ E` (by `mem_infOcc`)
- These are equivalent by `not_frequently` + `mem_infOcc`

**Pairs container type choice**: Use `List` rather than `Finset` because:
1. Pairs are ordered in practice (same approach as `NA.Buchi.complementNA` which uses `Finset.univ.filter`)
2. `Set State × Set State` has no `DecidableEq`, making `Finset` difficult
3. The `∃ p ∈ a.pairs` existential quantifier works cleanly with `List.Mem`

Alternative: use `ι → (Set State × Set State)` for an indexed family (more general). This matches the `Muller.accept : Set (Set State)` style of parameterizing on an abstract family. See Approach C below.

**Approach C (indexed family — most general):**
```lean
structure Rabin (State Symbol : Type*) extends DA State Symbol where
  pairs : Set (Set State × Set State)

instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (a : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ (EF : Set State × Set State), EF ∈ a.pairs ∧
      (a.run xs).infOcc ∩ EF.1 = ∅ ∧
      ((a.run xs).infOcc ∩ EF.2).Nonempty
```

**Recommendation: Approach A with `Set (Set State × Set State)`** (analogous to `Muller.accept : Set (Set State)`) for maximum generality and structural parallelism with Muller.

### 5. Parity Acceptance Formalization

**Mathematical definition**: A coloring `c : State → ℕ` assigns priorities. Run ρ is parity-accepting iff:
- **Min-even**: `∃ k : ℕ, Even k ∧ k ∈ (run xs).infOcc.image c ∧ ∀ j < k, j ∉ (run xs).infOcc.image c`
  (minimum priority in infOcc is even)
- Equivalently: the minimum element of `c '' infOcc(run xs)` is even

**Recommended Lean 4 formalization:**
```lean
structure Parity (State Symbol : Type*) extends DA State Symbol where
  /-- Priority coloring function: assigns a natural number priority to each state. -/
  color : State → ℕ

namespace Parity

instance : ωAcceptor (Parity State Symbol) Symbol where
  Accepts (a : Parity State Symbol) (xs : ωSequence Symbol) :=
    Even (((a.run xs).infOcc.image a.color).toFinset.min' (by
      apply Set.Finite.toFinset_nonempty.mpr
      exact Set.Nonempty.image _ (infOcc_nonempty xs)))
```

**Key challenge**: `infOcc` returns a `Set`, not a `Finset`. The minimum over a `Set ℕ` requires:
1. Using `Nat.sInf` (infimum of set of naturals) which works for any nonempty set:
   ```lean
   Accepts (a : Parity State Symbol) (xs : ωSequence Symbol) :=
     Even (Nat.sInf (a.color '' (a.run xs).infOcc))
   ```
2. `Nat.sInf_mem`: for nonempty sets of naturals, `sInf S ∈ S` — this is provable
3. Nonemptiness of `a.color '' infOcc(run xs)` follows from `infOcc_nonempty` (for `[Finite State]`)

**Simpler recommended formulation using `Nat.sInf`:**
```lean
instance : ωAcceptor (Parity State Symbol) Symbol where
  Accepts (a : Parity State Symbol) (xs : ωSequence Symbol) :=
    Even (Nat.sInf (a.color '' (a.run xs).infOcc))
```

This requires `[Finite State]` in the acceptance theorem (not in the definition) since we need `infOcc_nonempty` to show the set is nonempty. The definition itself is well-formed: `Nat.sInf ∅ = 0` which is even, so without `[Finite State]` the acceptor degenerates gracefully.

**Parity acceptance is decidable** when `State` is finite and `color` is computable — useful for model checking. Include `[Fintype State]` variants for decidability instances.

### 6. Conversion Theorems

#### Büchi → Rabin (trivial, 1 pair)

```lean
def Buchi.toRabin (a : Buchi State Symbol) : Rabin State Symbol where
  toDA := a.toDA
  pairs := {(∅, a.accept)}
-- Theorem: language a.toRabin = language a
```
Proof: `infOcc ∩ ∅ = ∅` is trivially true, and `infOcc ∩ accept ≠ ∅ ↔ ∃ᶠ k, run xs k ∈ accept` via `frequently_in_finite_type`.

#### Parity → Rabin (k/2 pairs, trivial)

For coloring `c : State → ℕ`, if max priority is `2k+1`:
- Rabin pair `i`: `Eᵢ = c⁻¹({2i+1})`, `Fᵢ = c⁻¹({2i})`
  (avoid odd priority 2i+1, visit even priority 2i)

Actually the standard construction is: for each even priority `2i`:
- `Fᵢ = c⁻¹({j | j ≤ 2i ∧ Even j})` — states with priority ≤ 2i that is even
- `Eᵢ = c⁻¹({j | j < 2i ∧ Odd j})` — states with odd priority strictly less than 2i

This can be implemented with a finite collection indexed by `Fin (k/2 + 1)`.

#### Muller → Rabin (polynomial, standard)

For Muller acceptance `F ∈ accept`, define Rabin pairs: for each `F ∈ accept`:
- `EF = ∅, F` — but this only works if all F cover the infOcc
- The correct construction: for each `F ∈ accept` (as a finite subset of states),
  create pairs that enforce `infOcc = F`:
  - `F_i = F` (the accepting set)
  - `E_i = State \ F` (states NOT in F must be eventually avoided)

Standard construction: exponentially many pairs in general but polynomial in the size of the acceptance table. Using `Set (Set State × Set State)` as `pairs` type handles this cleanly.

#### Rabin → Muller (straightforward)

```lean
def Rabin.toMuller (a : Rabin State Symbol) : Muller State Symbol where
  toDA := a.toDA
  accept := { S | ∃ EF ∈ a.pairs, S ∩ EF.1 = ∅ ∧ (S ∩ EF.2).Nonempty }
-- Theorem: language a.toMuller = language a
```
(Immediate from definitions.)

#### Rabin → Parity (Piterman 2007)

This is the non-trivial conversion. Produces a DPA with `O(n · k!)` states.

The Piterman construction:
1. Augments state space with a permutation of Rabin pairs encoding current priority ordering.
2. Assigns priority `2i` when pair `i` is "satisfied" (F_i-condition holds), `2i+1` otherwise.
3. Priority function depends on the current permutation of pairs.

**Implementation considerations for Lean 4:**
- State type: `State × (Fin k → Fin k)` (state × permutation of k Rabin pairs)
- `Fintype.card (Equiv.Perm (Fin k))` = `k!` — this is the source of `O(n · k!)` blowup
- Priority: `ℕ` coloring, values in `{0, 1, ..., 2k+1}`
- The permutation tracks the "latest satisfied" pair ordering

**Piterman 2007 construction outline (5 steps):**
1. Given DRA with `n` states, `k` pairs `(E_i, F_i)`.
2. New state: `(q, π)` where `q ∈ State`, `π : Fin k → Fin k` is a permutation.
3. Transition: `(q, π) -σ→ (q', π')` where `q' = tr q σ` and `π'` is obtained by:
   - If some `π(i)`-pair has `q' ∈ F_{π(i)}`, move `π(i)` to front.
   - Otherwise increment cyclically.
4. Color of `(q, π)`: `2 · π⁻¹(i) + ε` where `i` is the "current" pair index.
5. Accept by min-even parity.

**This is the most complex conversion and should likely be a `proof_wanted` initially.**

### 7. File Structure Recommendation

```
Cslib/Computability/Automata/DA/
├── Basic.lean       -- (existing) DA, DFA, DBA, DMA definitions
├── Buchi.lean       -- (existing) DBA eq finAcc_omegaLim
├── BuchiChar.lean   -- (existing) Landweber + DBA→DMA conversion + IsLoop
├── BuchiClosure.lean -- (existing) DBA closure properties
├── Rabin.lean       -- NEW: DA.Rabin definition + ωAcceptor instance
│                    --      + Buchi.toRabin + toRabin_language_eq
│                    --      + Rabin.toMuller + toMuller_language_eq
│                    --      + Muller.toRabin + toRabin_language_eq
├── Parity.lean      -- NEW: DA.Parity definition + ωAcceptor instance
│                    --      + Parity.toRabin + toRabin_language_eq
├── Conversions.lean -- NEW: Rabin.toParity (Piterman 2007, proof_wanted initially)
```

`Rabin.lean` imports `DA.Basic`, `BuchiChar.lean`.
`Parity.lean` imports `DA.Rabin`.
`Conversions.lean` imports `DA.Parity`.

### 8. `module` file vs. standalone file

`DA/Basic.lean` uses the `module` keyword and `public import` for Alloy-style modules. The new files should follow the same pattern as `BuchiChar.lean` (they import from `DA.Basic` and use `public import` if they re-export definitions).

Actually checking more carefully: `BuchiChar.lean` does NOT use the `module` keyword — it uses `@[expose] public section`. Let me clarify:

- Files that define their own namespace and expose definitions use `@[expose] public section`
- The `module` keyword is only in `Basic.lean` (the aggregator)

Looking at the pattern again: `Basic.lean` has `module` at the top, while `Buchi.lean`, `BuchiChar.lean`, `BuchiClosure.lean` use `public section` without `module`. New files should follow the same pattern as `BuchiChar.lean`:

```lean
module  -- OR: @[expose] public section

public import Cslib.Computability.Automata.DA.Basic
-- ... additional imports

@[expose] public section  -- if using @[expose]
namespace Cslib.Automata.DA
-- definitions here
end Cslib.Automata.DA
```

Wait — re-reading: `Buchi.lean` uses `public section` (no `@[expose]`), while `BuchiChar.lean` uses `@[expose] public section`. The `@[expose]` attribute controls whether definitions are re-exported when this module is transitively imported. New files should use `@[expose] public section` to match the pattern of the `BuchiChar.lean` file which is the most relevant precedent.

---

## Recommended Approach

### Phase 1: `Rabin.lean` — Core Rabin Structure

```lean
module  -- no, use @[expose] public section

public import Cslib.Computability.Automata.DA.Basic

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor
open scoped Cslib.FLTS

variable {State Symbol : Type*}

/-- Deterministic Rabin automaton. -/
structure Rabin (State Symbol : Type*) extends DA State Symbol where
  /-- The Rabin acceptance pairs: a set of (E, F) where a run is accepting iff
  for some pair, the run's infOcc avoids E and intersects F. -/
  pairs : Set (Set State × Set State)

namespace Rabin

/-- A run is Rabin-accepting iff there exists a pair (E, F) in `pairs` such that
states from E occur only finitely often and states from F occur infinitely often. -/
instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (a : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ EF ∈ a.pairs,
      (a.run xs).infOcc ∩ EF.1 = ∅ ∧
      ((a.run xs).infOcc ∩ EF.2).Nonempty

end Rabin

namespace Buchi

/-- Every DBA can be viewed as a DRA with a single Rabin pair (∅, accept). -/
def toRabin (a : Buchi State Symbol) : Rabin State Symbol where
  toDA := a.toDA
  pairs := {(∅, a.accept)}

/-- DBA-to-DRA conversion preserves the language. -/
theorem toRabin_language_eq [Finite State] (a : Buchi State Symbol) :
    language a.toRabin = language a := ...

end Buchi
```

### Phase 2: `Parity.lean` — Parity Structure

```lean
structure Parity (State Symbol : Type*) extends DA State Symbol where
  color : State → ℕ  -- priority coloring

instance : ωAcceptor (Parity State Symbol) Symbol where
  Accepts (a : Parity State Symbol) (xs : ωSequence Symbol) :=
    Even (Nat.sInf (a.color '' (a.run xs).infOcc))
```

### Phase 3: Basic Conversions

- `Rabin.toMuller` (immediate from definitions)
- `Muller.toRabin` (standard construction, finitely many pairs for finite acceptance tables)
- `Parity.toRabin` (k/2 pairs, direct construction)

### Phase 4: Piterman Conversion (`proof_wanted`)

The full Rabin→Parity (Piterman 2007) as a `proof_wanted` declaration with:
- State type: `State × Equiv.Perm (Fin k)` (requires `Fin k` for the pair count)
- Complete construction definition
- Language equivalence theorem as `proof_wanted`

---

## Evidence and Examples

### Pattern consistency with existing code

The Muller acceptance:
```lean
instance : ωAcceptor (Muller State Symbol) Symbol where
  Accepts (a : Muller State Symbol) (xs : ωSequence Symbol) :=
    (a.run xs).infOcc ∈ a.accept
```

The Rabin acceptance follows naturally:
```lean
instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (a : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ EF ∈ a.pairs,
      (a.run xs).infOcc ∩ EF.1 = ∅ ∧
      ((a.run xs).infOcc ∩ EF.2).Nonempty
```

### Key lemmas already available

1. **`mem_infOcc`**: Links `x ∈ infOcc xs` to `∃ᶠ k in atTop, xs k = x` — needed for all conversions
2. **`frequently_in_finite_type`**: Converts set-membership form to per-element form — needed for Büchi↔Rabin
3. **`infOcc_nonempty [Finite α]`**: Ensures non-degenerate parity acceptance
4. **`infOcc_finite [Finite α]`**: Makes `infOcc` a finite set — critical for `Nat.sInf` nonemptiness
5. **`DA.IsLoop`**: Already defined for use in Rabin characterizations (noted in `BuchiChar.lean`)

### Büchi↔Rabin proof sketch

Forward (`toRabin` accepts → original accepts):
- `infOcc ∩ ∅ = ∅` trivially
- `(infOcc ∩ accept).Nonempty` ↔ `∃ x ∈ infOcc, x ∈ accept` ↔ `∃ᶠ k, run xs k ∈ accept` via `frequently_in_finite_type`

Backward: same chain of equivalences in reverse.

### Parity acceptance well-definedness

When `[Finite State]`:
- `infOcc_nonempty xs` gives `infOcc (run xs) ≠ ∅`
- Therefore `color '' infOcc (run xs) ≠ ∅`
- Therefore `Nat.sInf (color '' infOcc (run xs))` is the actual minimum priority

When `State` is not finite: `Nat.sInf ∅ = 0` (by Lean's `sInf` for `ℕ`) which is Even, so all words are "accepted" — a degenerate case that won't occur in practice but requires the `[Finite State]` hypothesis in correctness theorems.

---

## Confidence Level

**High confidence** for:
- `DA.Rabin` structure definition using `Set (Set State × Set State)` for pairs
- `DA.Parity` structure with `Nat.sInf`-based acceptance
- `Buchi.toRabin` and `Rabin.toMuller` conversions (direct, immediate from definitions)
- `Parity.toRabin` conversion (direct, k/2 pairs)
- File structure (three new files: `Rabin.lean`, `Parity.lean`, `Conversions.lean`)

**Medium confidence** for:
- Whether `pairs : Set (Set State × Set State)` or `pairs : List (Set State × Set State)` is better
  (The `Set` form mirrors Muller; the `List` form is closer to the standard textbook presentation)
- Whether `Muller.toRabin` should live in `Rabin.lean` or `Conversions.lean`

**Low confidence / `proof_wanted`** for:
- The full Piterman 2007 Rabin→Parity construction (complex state-machine construction involving permutations)
- Whether the Piterman permutation state should use `Equiv.Perm (Fin k)` or a vector representation

---

## CSLib Reuse Check

- `DA.Buchi`, `DA.Muller`, `DA.IsLoop`: All exist, will be imported and reused
- `ωSequence.infOcc`, `infOcc_nonempty`, `infOcc_finite`: Exist, will be the main tools
- `frequently_in_finite_type`: Exists, needed for Büchi↔Rabin conversion
- `ωAcceptor` typeclass: Exists, new structures implement it
- No existing Rabin/Parity definitions to reuse in CSLib or Mathlib

## Lint Prevention Notes

- All new definitions need docstrings (docBlame)
- Acceptance instances use `@[simp, scoped grind =]` (following DBA/DMA pattern)
- Conversion functions use `def ... where` pattern (no `sorry`)
- `noncomputable` needed for `Muller.toRabin` if acceptance table involves `Classical.choice`
- Section variables should be minimal; `[Finite State]` goes on specific theorems not at section level unless most lemmas need it
