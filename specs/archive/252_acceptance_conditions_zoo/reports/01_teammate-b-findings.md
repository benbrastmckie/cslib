# Teammate B Findings: Prior Art, Alternatives, and Infrastructure for Acceptance Conditions

## Key Findings

### 1. Mathlib Has No Omega-Automata Acceptance Conditions

Mathlib's `Computability` directory contains only finite-word automata: `DFA`, `NFA`, `EpsilonNFA`
(all in `Mathlib.Computability.{DFA,NFA,EpsilonNFA}`). There are no Büchi, Rabin, Muller, or
parity automata in Mathlib. The `cofinite = atTop` connection (`Nat.cofinite_eq_atTop` in
`Mathlib.Order.Filter.Cofinite`) and the `∃ᶠ` machinery are mature, but no omega-automata
formalization exists in Mathlib to reuse or port.

**Consequence**: CSLib's existing approach—`structure DA.Rabin extends DA ... where accept : List (Set State × Set State)`—has no Mathlib precedent to standardize against. The field is open.

### 2. Existing CSLib Infrastructure Is Exactly Right for Rabin and Parity

The `infOcc` predicate in `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` maps directly
to both acceptance conditions:

- **Rabin**: `∃ᶠ k in atTop, ...` and `¬ ∃ᶠ k in atTop, ...` are the natural primitive.
  But using `infOcc` is better: `(da.run xs).infOcc ∩ Ei = ∅` (using `infOcc.disjoint`)
  and `(da.run xs).infOcc ∩ Fi ≠ ∅` (using `infOcc.nonempty_inter`).
- **Parity**: `(Finset.image coloring (da.run xs).infOcc.toFinset).min' h` where `coloring : State → ℕ`.

The key lemmas already present:
- `infOcc_finite [Finite α]` — priorities image over infOcc is finite
- `infOcc_nonempty [Finite α]` — infOcc is nonempty (pigeonhole), so `Finset.min'` is well-defined
- `frequently_in_finite_type` — connects `∃ᶠ` with `infOcc`

### 3. Two Alternative Representation Styles for Rabin

**Style A (List-of-pairs, `Set`-based)**:
```lean
structure DA.Rabin (State Symbol : Type*) extends DA State Symbol where
  accept : List (Set State × Set State)
```
- Acceptance: `∃ (EF : Set State × Set State) ∈ a.accept, (a.run xs).infOcc ∩ EF.1 = ∅ ∧ (a.run xs).infOcc ∩ EF.2 ≠ ∅`
- Pros: exactly mirrors the seed report's mathematical definition; no `Fintype` assumption needed
- Cons: `List` not `Finset` (ordering matters for Rabin→Parity construction where pair index is used)

**Style B (Finset-of-pairs, `Finset`-based)**:
```lean
structure DA.Rabin (State Symbol : Type*) extends DA State Symbol where
  accept : Finset (Set State × Set State)
```
- Pros: `DecidableEq` for intersection emptiness checks; can use `Finset.exists_mem` directly
- Cons: requires `DecidableEq (Set State × Set State)` which is non-trivial without Decidability

**Recommendation**: Use `List (Set State × Set State)` (Style A). It matches the existing
`DA.Muller` which uses `Set (Set State)`. There is no ordering on the pairs in the acceptance
semantics, and `List.Any` neatly expresses the existential. The Rabin→Parity conversion can
index pairs via `List.indexOf` when needed.

**Alternative style C (explicit indexing)**:
```lean
structure DA.Rabin (State Symbol : Type*) extends DA State Symbol where
  numPairs : ℕ
  E : Fin numPairs → Set State
  F : Fin numPairs → Set State
```
- This matches the mathematical phrasing "k pairs (E₁,F₁),...,(Eₖ,Fₖ)" most closely
- Pros: explicit pair index available directly; clean for the Piterman construction
- Cons: structurally more complex; adds the `numPairs` field rather than deriving length

### 4. Two Representation Styles for Parity Acceptance

**Style A (function on states, `Set`-based infOcc)**:
```lean
structure DA.Parity (State Symbol : Type*) extends DA State Symbol where
  coloring : State → ℕ
```
Acceptance: `Even ((Finset.image a.coloring (a.run xs).infOcc.toFinset).min' h)` where `h` is
proven using `infOcc_nonempty` (requires `[Finite State]`).

- Pros: exactly the parity-game definition; uses existing `Nat.even_or_odd` from `Mathlib.Algebra.Ring.Parity`
- Cons: `infOcc.toFinset` requires `[Finite State]` and `[DecidableEq State]` for decidability

**Style B (function on states, min over `∃ᶠ`)**:
```lean
-- Acceptance expressed without toFinset:
∃ p : ℕ, Even p ∧ (∃ᶠ k in atTop, a.coloring (a.run xs k) = p) ∧
         ∀ q < p, Odd q → ∀ᶠ k in atTop, a.coloring (a.run xs k) ≠ q
```
- Pros: avoids `toFinset` and finiteness assumptions; more directly expressible as filters
- Cons: unwieldy; the `∀ᶠ` condition is hard to work with; not as clean as `Finset.min'`

**Recommendation**: Style A with `Finset.min'` on `infOcc.toFinset`. The `[Finite State]`
assumption is already required for the existing `buchi_toMuller_language_eq` (see `BuchiChar.lean`
line 88: `[Finite State]`), so this is consistent with the library's existing conventions.

### 5. Muller → Rabin Conversion: Three Approaches

**Approach A (standard, via subset enumeration)**:
The standard conversion (Thomas 2003, Chapter 3): For a DMA with acceptance family `F ⊆ 2^Q`,
define k = |F| Rabin pairs: for each `Fi ∈ F`, pair `(Q \ Fi, Fi)`. This gives exactly
k = |F| pairs.
- Works directly with CSLib's `Set (Set State)` Muller representation
- Requires iterating over the acceptance family; in Lean 4 needs `Fintype` assumption on State

**Approach B (via infOcc)**:
```lean
-- Acceptance of DMA: infOcc ∈ F.accept
-- Acceptance of DRA constructed: ∃ (E, F_pair) in pairs, infOcc ∩ E = ∅ ∧ infOcc ∩ F_pair ≠ ∅
-- Conversion: E = Qᶜ \ Fi = ∅ (empty!) when Fi = infOcc; this simplifies to ∃ Fi ∈ F, infOcc = Fi
```
This shows the conversion reduces to the same thing, but using `Set.compl` cleanly.

**Approach C (generalized Büchi intermediate)**:
An alternative proof strategy routes Muller → GenBüchi → Rabin:
- Muller → Generalized Büchi (GNBA): trivially, since GNBA uses multiple accept sets
- GenBüchi → Büchi: the cycling counter construction (already implemented in `GNBA.lean`)
- Büchi → Rabin: trivially (1 pair with E = ∅)
- This route composes 3 existing/near-existing constructions but adds complexity

**Recommendation**: Approach A (direct Muller→Rabin) is simplest for correctness proofs.
The key lemma needed: `Finset.image` on the acceptance family with `Finite State` assumption.

### 6. Rabin → Parity: The Piterman Construction is Non-Trivial

The Piterman 2007 construction transforms a DRA with n states and k pairs into a DPA with
O(n · k!) states. The state space is:

```
State' = State × { ranked permutations of Fin k }
```

This requires:
- `Finset.permutations` or `Equiv.Perm (Fin k)` — Mathlib has `Equiv.Perm` and `Fintype (Equiv.Perm (Fin k))`
- `List.Perm`, `Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial` (Mathlib: `Fintype.card_perm`)
- Permutation update operations on `Equiv.Perm`

**Key Mathlib infrastructure for Piterman**:
- `Fintype.card_perm` (in `Mathlib.GroupTheory.Perm.Card`) — `Fintype.card (Equiv.Perm α) = (Fintype.card α)!`
- `Equiv.Perm.swap` — transposition
- `Finset.insertNth` — ordered insertion

**Alternative (Parity → Rabin, the easier direction)**:
For a DPA with priority `c : State → Fin (2n)`:
```lean
-- k = n Rabin pairs
-- Pair i (0 ≤ i < n): E_i = { q | c(q) = 2i+1 }, F_i = { q | c(q) = 2i }
-- i.e., "even priority 2i occurs infinitely often and odd 2i+1 does not"
```
This direction is trivial given `Finset.filter` and `infOcc`.

**Recommendation**: For an initial implementation, provide:
1. Parity→Rabin conversion (trivial, achievable immediately)
2. Stub Rabin→Parity with `proof_wanted` (matching the existing style in `BuchiChar.lean`)

### 7. Streett as Complement of Rabin: Worth Including

Streett acceptance (`∀ i, infOcc ∩ Fi ≠ ∅ → infOcc ∩ Ei ≠ ∅`) is the exact dual of Rabin.
Since CSLib already provides `DA.Buchi.not_closed_complement` (showing DBA is not closed under
complement), a natural pairing would be `DA.Rabin` and `DA.Streett` with a duality theorem:

```lean
theorem rabin_compl_eq_streett (a : DA.Rabin State Symbol) :
    (language a.toStreett)ᶜ = language a -- or equivalent
```

This adds minimal complexity but completes the "zoo" conceptually.

### 8. Generalized Büchi as an Intermediate Acceptance Condition

GNBA is already formalized in `Cslib/Logics/LTL/Semantics/GNBA.lean` (for the LTL tableau).
The acceptance condition there uses `Set (Set (GNBAState φ))` (a family of acceptance sets
where all must be visited infinitely often). A standalone `DA.GenBuchi` could be:

```lean
structure DA.GenBuchi (State Symbol : Type*) extends DA State Symbol where
  acceptSets : List (Set State)  -- run must visit each accept set infinitely often
```

This would provide:
- DBA → DGenBüchi (trivially, 1-element list)  
- DMA → DGenBüchi (straightforwardly)
- DGenBüchi → DRA (constructively)

However, the LTL GNBA code already has the cycling counter construction for GNBA→NBA. The
extra `DA.GenBuchi` type adds value only if conversion theorems are proved; otherwise it's
dead abstraction.

**Recommendation**: Skip standalone `DA.GenBuchi` for task 252 unless it simplifies the
Muller→Rabin proof path significantly.

### 9. Filter Infrastructure Available in Mathlib

Key Mathlib lemmas usable for parity and Rabin proofs:
- `Nat.frequently_atTop_iff_infinite` — `∃ᶠ n in atTop, p n ↔ {n | p n}.Infinite`
- `Nat.cofinite_eq_atTop` — connects cofinite and atTop filters
- `Finset.min'` with `Finset.min'_mem`, `Finset.min'_le` — minimum element API
- `Finset.exists_min_image` — `s.Nonempty → ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x'`
- `Set.exists_min_image` — same for sets
- `Nat.even_or_odd` — dichotomy needed for parity acceptance proofs
- `Filter.cofinite.limsup_set_eq` — set-valued limsup equals elements appearing infinitely often

The connection `Filter.limsup (fun k => {a.run xs k}) atTop = (a.run xs).infOcc` follows from
`Filter.mem_limsup_iff_frequently_mem` and `Nat.cofinite_eq_atTop`. This gives an alternative
characterization of `infOcc` via Mathlib's `limsup` machinery, useful for proofs.

### 10. No External Lean 4 Library for Omega-Automata Acceptance

The `ctchou/AutomataTheory` project referenced in Task 241 (McNaughton) is the closest Lean 4
external project. It is not a dependency of CSLib (not in `.lake/packages/`) and no Rabin/parity
formalization was found in the packages. The field is original work for CSLib.

---

## Recommended Approach

Based on the above analysis, the recommended formalization strategy is:

### Phase 1: `DA.Rabin` and `NA.Rabin` (using `List`-of-pairs, `infOcc`-based)

```lean
-- In DA/Basic.lean (or new Rabin.lean)
structure DA.Rabin (State Symbol : Type*) extends DA State Symbol where
  accept : List (Set State × Set State)

instance : ωAcceptor (DA.Rabin State Symbol) Symbol where
  Accepts (a : DA.Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ EF ∈ a.accept, (a.run xs).infOcc ∩ EF.1 = ∅ ∧ ((a.run xs).infOcc ∩ EF.2).Nonempty
```

This mirrors exactly how `DA.Muller` is defined with `Set (Set State)`. The `∩ = ∅` for E
and `∩ ≠ ∅` for F are both expressible via `Set.eq_empty_iff_forall_not_mem` and
`Set.Nonempty`.

### Phase 2: `DA.Parity` (using `coloring : State → ℕ`, `Finset.min'`-based)

```lean
structure DA.Parity (State Symbol : Type*) extends DA State Symbol where
  coloring : State → ℕ

instance [Finite State] : ωAcceptor (DA.Parity State Symbol) Symbol where
  Accepts (a : DA.Parity State Symbol) (xs : ωSequence Symbol) :=
    Even ((a.run xs).infOcc.toFinset.image a.coloring).min' (by
      apply Finset.Nonempty.image
      exact Set.Finite.toFinset_nonempty _ (infOcc_nonempty _))
```

**Note**: The `[Finite State]` assumption is already used by `Buchi.toMuller_language_eq`.
For `Set.infOcc.toFinset` to typecheck, we additionally need `[DecidableEq State]`.

### Phase 3: `DA.Streett` (dual of Rabin, complementary acceptance)

```lean
instance : ωAcceptor (DA.Streett State Symbol) Symbol where
  Accepts (a : DA.Streett State Symbol) (xs : ωSequence Symbol) :=
    ∀ EF ∈ a.accept, ((a.run xs).infOcc ∩ EF.2).Nonempty → ((a.run xs).infOcc ∩ EF.1).Nonempty
```

### Phase 4: Conversion theorems

**Priority order (from easiest to hardest)**:
1. `DA.Buchi.toRabin` — trivial (1 pair, E = ∅, F = accept)
2. `DA.Parity.toRabin` — trivial (k/2 pairs from priority coloring)
3. `DA.Rabin.toStreett` — trivial (flip E↔F in each pair, negate acceptance)
4. `DA.Muller.toRabin` — requires `Fintype State`, iterating the acceptance family
5. `DA.Rabin.toMuller` — direct (union of Fi sets forms Muller acceptance)
6. `DA.Rabin.toParity` — `proof_wanted` (Piterman 2007 construction)

---

## Evidence and Examples

### infOcc API available for Rabin

The `infOcc` predicate (`def infOcc (xs : ωSequence α) : Set α := { x | ∃ᶠ k in atTop, xs k = x }`)
in `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` provides:
- `mem_infOcc`: `x ∈ xs.infOcc ↔ ∃ᶠ k in atTop, xs k = x`
- `infOcc_finite [Finite α]`: the infOcc set is finite
- `infOcc_nonempty [Finite α]`: the infOcc set is nonempty

For the Rabin Eᵢ condition ("visit Eᵢ only finitely often"), the precise formulation is:
`(a.run xs).infOcc ∩ EF.1 = ∅`, which unfolds to `∀ q ∈ EF.1, q ∉ (a.run xs).infOcc`,
which is `∀ q ∈ EF.1, ∀ᶠ k in atTop, a.run xs k ≠ q` — this is exactly the "finitely often"
condition. The `Set.eq_empty_iff_forall_not_mem` and `Set.mem_empty_iff_false` simplification
lemmas make proofs of `∩ = ∅` tractable.

### Parity: min' nonemptiness from infOcc_nonempty

```lean
-- In a Parity acceptance proof, we need nonemptiness for min':
have h_ne : ((a.run xs).infOcc.toFinset.image a.coloring).Nonempty := by
  apply Finset.Nonempty.image
  rw [Set.Finite.toFinset_nonempty (infOcc_finite _)]
  exact infOcc_nonempty _
-- Then: Even ((…).min' h_ne) is the acceptance condition
```

### Existing parallel in BuchiChar.lean (typed variables)

`DA.BuchiChar.lean` uses `[Finite State]` and `[Fintype State]` and `[DecidableEq State]`
for the Landweber construction. The Rabin→Parity construction will follow the same pattern.

---

## Confidence Level

- **Rabin/Streett definitions**: High. The infOcc-based approach is direct and consistent with Muller.
- **Parity definition**: High. `Finset.min'` on `infOcc.toFinset` image is well-supported.
- **Simple conversions (Büchi→Rabin, Parity→Rabin, Muller→Rabin)**: High. Direct construction.
- **Rabin→Parity (Piterman)**: Medium (definition only). The Piterman construction requires
  `Equiv.Perm (Fin k)` state space; `Mathlib.GroupTheory.Perm.Card` provides needed infrastructure
  (`Fintype.card_perm`). A `proof_wanted` stub matching `BuchiChar.lean` style is recommended.
- **No Mathlib omega-automata prior art**: High. Exhaustive search confirms none exists.
- **`[Finite State]` assumption consistency**: High. Already used in `BuchiChar.lean`.
