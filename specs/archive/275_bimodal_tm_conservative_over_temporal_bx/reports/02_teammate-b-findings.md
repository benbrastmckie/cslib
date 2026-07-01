# Teammate B Research Findings: Alternative Strategies for Task 275

## Scope

Alternative approaches to bridge the domain mismatch in `temporal_valid_of_bimodal_derivable`,
specifically: model transfer via order isomorphism, syntactic derivation translation, and
restricting the completeness domain. Strategy 3 (satisfaction preservation via order isomorphism)
is the primary finding; Strategy 2 (syntactic approach) is also analyzed.

## Key Findings

### Finding 1: Order Isomorphism Preservation is Provable and the Core Mechanism

The `Temporal.Satisfies` relation is defined purely in terms of the strict linear order `<` on
the domain `D`. It does NOT use any additive group structure. The definition is:

```lean
def Satisfies (M : TemporalModel D Atom) (t : D) : Formula Atom → Prop
  | .atom p => M.valuation t p
  | .bot => False
  | .imp φ ψ => Satisfies M t φ → Satisfies M t ψ
  | .untl ψ φ => ∃ s, t < s ∧ Satisfies M s φ ∧ ∀ r, t < r → r < s → Satisfies M r ψ
  | .snce ψ φ => ∃ s, s < t ∧ Satisfies M s φ ∧ ∀ r, s < r → r < t → Satisfies M r ψ
```

This means: given an order isomorphism `e : D ≃o D'`, we can transfer any temporal model
`M : TemporalModel D Atom` to `M' : TemporalModel D' Atom` by setting `M'.valuation t' p :=
M.valuation (e.symm t') p`, and the following will hold by structural induction:

```lean
Satisfies M t φ ↔ Satisfies M' (e t) φ
```

This is a purely structural proof. The `untl` case uses that `e` is strictly monotone and
surjective (hence bijective) to match witnesses: `s > t` in `D` corresponds to `e s > e t` in `D'`,
and since `e` is surjective, every `s' > e t` in `D'` has the form `e s` for some `s > t` in `D`.

**This lemma does not yet exist in CSLib** (no `satisfies_orderIso` or similar was found via
local search). It needs to be proved, but it is a straightforward structural induction.

### Finding 2: The Temporal ChronicleSubtype is Already the Needed Target

The temporal completeness proof builds `ChronicleSubtype A h_mcs` which is:
- A subtype `{x : Rat // x ∈ limitDom A h_mcs}`
- Has `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`
- Lives in the rationals (already has `Countable` via `Subtype.countable` from Mathlib)

The key question is whether `ChronicleSubtype A h_mcs` has `DenselyOrdered`. Looking at the
temporal `DenseCompleteness.lean`, the Dense completeness proof uses `chronicleDenselyOrderedDense`
which establishes `DenselyOrdered (ChronicleSubtype A h_base_mcs)` conditional on starting from
a Dense-MCS. For Base completeness (which is what we need), the chronicle model is NOT
guaranteed to be dense.

However, this does not matter for Strategy 3. The approach is:

1. We need validity of `φ` on ALL serial linear orders (for temporal Base completeness).
2. Assume for contradiction that `φ` fails in some temporal model `M` on domain `D` (serial
   linear order, no AddCommGroup needed).
3. The temporal completeness proof (which already works and has no sorry) produces a
   ChronicleSubtype countermodel for `φ`. That ChronicleSubtype is a subtype of Rat, hence
   has all the structure we need (including being embeddable into Rat with AddCommGroup).

**The approach for fixing the sorry does NOT need to go through DenselyOrdered at all.**

### Finding 3: The Canonical Strategy is Two-Step Transfer

The cleanest approach to remove the sorry is:

**Step A**: Prove `satisfies_orderIso`: for any order isomorphism `e : D ≃o D'`,
`Satisfies M t φ ↔ Satisfies (M.transport e) (e t) φ` where
`(M.transport e).valuation t' p := M.valuation (e.symm t') p`.

**Step B**: Use `temporal_valid_on_addcommgroup` (already proven) applied to the
`ChronicleSubtype A h_mcs` (as a subtype of Rat, hence embeds into Rat, which has
AddCommGroup) OR, more precisely:

Actually, the cleanest path is: the ChronicleSubtype is a subtype of `Rat`. The rationals
have `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`, and `Nontrivial`. So
`ChronicleSubtype A h_mcs` embeds into `Rat` via the inclusion. However, what we need is an
*order isomorphism*, not just an embedding, to transfer satisfaction.

**The `cantorIsoDense` pattern from bimodal** (in
`ChronicleToCountermodelBasic.lean`) applies the Cantor isomorphism to bimodalChronicleSubtype
when it is dense. For temporal Base completeness, the ChronicleSubtype might NOT be dense.

### Finding 4: The Simplest Fix for the Sorry

The simplest approach that avoids all the DenselyOrdered complication:

For any temporal model `M` on domain `D` (with `[LinearOrder D] [Nontrivial D] [NoMaxOrder D]
[NoMinOrder D]`), construct a model `M'` on `Rat` as follows:

1. Since `D` is a serial linear order, use `Order.embedding_from_countable_to_dense`:
   this gives an order embedding `D ↪o Rat` (Mathlib's `Nonempty (D ↪o β)` for countable D and
   dense β with `Nontrivial β`). But this requires D to be countable, which is not given.

2. **Better approach**: Do NOT transfer the countermodel from `D` to `Rat`. Instead, establish
   the result directly by noting that the temporal `completeness` theorem uses a ChronicleSubtype
   (a subtype of Rat), and we can prove the result for ChronicleSubtype directly, then conclude
   for arbitrary D via the contrapositive.

### Finding 5: The Actual Gap and Its Direct Fix

The actual proof structure needed is:

```
temporal_valid_of_bimodal_derivable:
  h : Bimodal.ThDerivable φ.toBimodal
  D : Type, [LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
  M : TemporalModel D Atom, t : D
  ⊢ Satisfies M t φ
```

We have `temporal_valid_on_addcommgroup` which handles `D` with AddCommGroup. For general `D`,
the key insight from the bimodal completeness proof is:

**If `φ` is not temporally derivable, then `¬φ` is consistent, extends to MCS `A`, and
the ChronicleSubtype gives a countermodel where `¬φ` is satisfied.** But the ChronicleSubtype
IS a subtype of `Rat`, which has AddCommGroup. So the ChronicleSubtype model is ALREADY one of
the AddCommGroup models covered by `temporal_valid_on_addcommgroup`.

This gives the cleanest proof:

```lean
theorem temporal_valid_of_bimodal_derivable ... :
    Satisfies M t φ := by
  -- By the temporal completeness theorem (contrapositive):
  -- It suffices to show φ is BX-derivable.
  -- But we don't know that yet; we need to show validity on serial linear orders
  -- WITHOUT going through completeness first.
  -- Alternative: show temporal BX completeness uses AddCommGroup domains (ChronicleSubtype < Rat)
  sorry
```

Wait — let me reconsider. The issue is:

- `temporal_valid_on_addcommgroup` proves: if `φ.toBimodal` is bimodal-derivable, then `φ` is
  satisfied in every AddCommGroup domain.
- `temporal completeness` needs: `φ` is satisfied in every serial linear order.

These serial linear orders include domains with NO AddCommGroup structure. So the sorry gap is
genuine — we need to show that if something fails in ANY serial linear order, it also fails in
an AddCommGroup serial linear order.

**The ChronicleSubtype IS a subtype of `Rat`.** And `Rat` has `AddCommGroup`. The inclusion
`ChronicleSubtype → Rat` is an `OrderEmbedding`. We need it to be an `OrderIso` or at least
that satisfaction is reflected through the inclusion.

### Finding 6: The Order Embedding Obstacle and How to Avoid It

A plain order embedding `f : D ↪o D'` does NOT transfer temporal satisfaction because the
`untl` case requires: if `Satisfies M t (ψ U φ)` then ∃ `s > t, φ(s) ∧ guard(ψ, t, s)`.
After embedding, the witness `f s > f t` exists in `D'`, but there might be points `r'` in
`D'` between `f t` and `f s` that are NOT in the image of `f` — so the guard condition for
`D'` might fail.

**However, an order isomorphism `e : D ≃o D'` DOES transfer satisfaction.** In the untl case:
- If `∃ s, t < s ∧ Satisfies M s φ ∧ ∀ r, t < r < s → Satisfies M r ψ`
- Then `∃ s', e t < s' ∧ Satisfies M' s' φ' ∧ ∀ r', e t < r' < s' → Satisfies M' r' ψ'`
  where `s' = e s` and the guard uses: `r'` in `(e t, e s)` iff `e.symm r'` in `(t, s)`.

This works because `e` is a bijection that preserves strict order.

**The verification that `Satisfies` is transferred by order isomorphism is a clean proof**
that should be relatively easy to formalize — it is structural induction on `φ` with 5 cases,
all straightforward.

### Finding 7: Two Concrete Implementation Paths

**Path A (Recommended): Prove `satisfies_orderIso` + Use existing countermodel**

The temporal Base completeness proof (`Completeness.lean`) proceeds by contrapositive: if `φ`
is not derivable, construct a ChronicleSubtype countermodel. The ChronicleSubtype is a subtype
of `Rat`. We cannot directly use `temporal_valid_on_addcommgroup` on the ChronicleSubtype model
because that theorem requires AddCommGroup on the model domain. However:

- The inclusion `incl : ChronicleSubtype A h_mcs → Rat` is an order embedding (NOT iso).
- We cannot pull the `temporal_valid_on_addcommgroup` conclusion back through an embedding.

So the path is:

1. Prove `satisfies_orderIso` lemma.
2. For any temporal model `M` on domain `D` (serial linear order), note that:
   - Either `D` already has AddCommGroup: use `temporal_valid_on_addcommgroup` directly.
   - Or `D` does not: use the contrapositive. If `φ` fails in `M` at `t`, then `¬φ` is
     satisfiable. Since `¬φ` is satisfiable (in ANY serial linear order), it satisfies the
     antecedent of temporal incompleteness — but wait, this is circular.

**The actual cleanest path:**

Actually, the most direct approach is to show that temporal Base validity is equivalent to
validity on `ℤ`-models (or `ℚ`-models). This is essentially what the standard model property
says: BX is complete with respect to the rationals alone. But proving this requires work.

**Path B (Recommended for implementation): Work backward from the ChronicleSubtype**

The proof of `temporal_valid_of_bimodal_derivable` should work as follows:

```lean
theorem temporal_valid_of_bimodal_derivable ... :
    Satisfies M t φ := by
  -- Contrapositive: assume ¬(Satisfies M t φ)
  -- Then ¬φ is satisfiable in M at t
  -- By temporal completeness (contrapositive): ¬φ is not derivable, which means
  --   {¬¬φ, φ} is... wait this is circular.
```

The correct approach is NOT contrapositive on the goal but rather:

1. Use `temporal_valid_on_addcommgroup` to show φ is BX-valid on AddCommGroup domains.
2. Use the fact that BX-validity on AddCommGroup domains coincides with full BX-validity.
   This is the "standard completeness" direction: BX is complete with respect to `ℤ` alone.
   But this requires a proof.

**The path that works:** Transfer the problem to the ChronicleSubtype model using
`satisfies_orderIso`.

The ChronicleSubtype model for the BX completeness proof lives on `{x : Rat // x ∈ limitDom A h_mcs}`.
This is a subtype of Rat. To apply `temporal_valid_on_addcommgroup`, we need the domain to have
`AddCommGroup`. The domain is a subtype of Rat, so it inherits `LinearOrder` but NOT `AddCommGroup`
(subtypes of Rat don't automatically form a group under addition).

The ONLY approach that works cleanly is: transfer satisfaction through an order isomorphism to
`Rat` itself, then apply `temporal_valid_on_addcommgroup` to the Rat model.

This requires:
1. `satisfies_orderIso`: transfer of satisfaction through an order isomorphism.
2. An order isomorphism from `ChronicleSubtype A h_mcs` to `Rat`.
   This requires `DenselyOrdered (ChronicleSubtype A h_mcs)`.
3. But Base completeness does NOT guarantee `DenselyOrdered`.

**Conclusion**: The isomorphism approach only works for the Dense frame class. For Base, we
need a different argument.

### Finding 8: The Correct Approach — BX is Complete for Rat

The key theoretical insight is: **Burgess BX is complete with respect to `(ℚ, <)`** (the
rationals with the standard order). This is a classical result (also true for `ℝ` and `ℤ`).

In terms of the Lean formalization, what this means is: if `φ` is valid in every Rat model,
it is BX-derivable. The existing `completeness` theorem proves this for all serial linear orders.
But we need the CONVERSE for the sorry: valid in all AddCommGroup serial linear orders implies
valid in all serial linear orders.

This is NOT automatic. The key missing ingredient is that the ChronicleSubtype countermodel
(built from any MCS for `¬φ`) can be isomorphically embedded into Rat when it is dense.
For the non-dense case, the ChronicleSubtype might be discrete, and then we need an embedding
into `ℤ`, which also has AddCommGroup.

**This is the key insight from the bimodal `ChronicleToCountermodelBasic.lean`**: the bimodal
version does a case split on dense vs. discrete, uses `cantorIsoDense` for the dense case, and
`orderIsoIntOfLinearSuccPredArch` for the discrete case. The temporal version can follow the same
pattern.

### Finding 9: Syntactic Approach Analysis (Strategy 2)

The syntactic approach would translate a bimodal `DerivationTree FrameClass.Base [] φ.toBimodal`
into a temporal `DerivationTree FrameClass.Base [] φ`.

Comparing the derivation tree constructors:
- Bimodal has: `axiom`, `assumption`, `modus_ponens`, `necessitation`, `temporal_necessitation`,
  `temporal_duality`, `weakening`
- Temporal has: `axiom`, `assumption`, `modus_ponens`, `temporal_necessitation`,
  `temporal_duality`, `weakening`

The key difference is the `necessitation` rule (for modal `box`). For a temporal formula `φ`
(which has no `box` constructor), any bimodal derivation of `φ.toBimodal` might use
`necessitation` as an intermediate step. Specifically, `necessitation` can appear when deriving
bimodal theorems that are needed as lemmas in the proof of `φ.toBimodal`.

For example, the `modal_future` axiom (`box φ → box(G φ)`) uses `necessitation` to derive
`box(box φ → box(G φ))`. Even if the final conclusion `φ` has no `box`, intermediate steps
might use `box`.

This means the syntactic approach requires proving: "any bimodal derivation of a temporal
formula can be transformed to avoid the `necessitation` rule." This is a non-trivial
proof-theoretic result (cut-elimination or admissibility of necessitation in the temporal
fragment). **The syntactic approach is significantly harder than the semantic approach.**

### Finding 10: Recommended Strategy — Dense/Discrete Case Split on ChronicleSubtype

Based on the bimodal precedent, the recommended approach for removing the sorry is:

1. **Add `satisfies_orderIso`** to `Temporal/Semantics/Satisfies.lean`:
   ```lean
   theorem satisfies_orderIso {D D' : Type*} [LinearOrder D] [LinearOrder D']
       (e : D ≃o D') (M : TemporalModel D Atom) (t : D) (φ : Formula Atom) :
       Satisfies M t φ ↔ Satisfies (M.transport e) (e t) φ
   ```
   This is proved by structural induction on `φ`, 5 cases, all clean.
   Define `TemporalModel.transport`:
   ```lean
   def TemporalModel.transport (M : TemporalModel D Atom) (e : D ≃o D') :
       TemporalModel D' Atom where
     valuation t' p := M.valuation (e.symm t') p
   ```

2. **Prove temporal validity on dense AddCommGroup domains**: The ChronicleSubtype for Base
   completeness might be dense or discrete. We need a case split.
   - If the ChronicleSubtype is dense: apply `cantorIsoDense` analog (order isomorphism to Rat)
     then transfer satisfaction via `satisfies_orderIso`.
   - If it is discrete: apply the Z-isomorphism then transfer satisfaction.

3. **The alternative (simpler) approach**: Observe that the temporal `completeness` theorem
   quantifies over ALL serial linear orders. The ChronicleSubtype model is a serial linear order.
   So `temporal_valid_of_bimodal_derivable` can be proved as follows:

   ```
   h : BimodalThDerivable φ.toBimodal
   D : serial linear order, M : TemporalModel D Atom, t : D
   Goal: Satisfies M t φ
   ```

   Proof by contradiction:
   - Assume `¬Satisfies M t φ`.
   - Then `φ` is not valid (there is a countermodel).
   - By contrapositive of temporal completeness: `φ` is not BX-derivable.
   - Therefore `¬φ` is BX-consistent.
   - By Lindenbaum: extend to MCS `A` with `¬φ ∈ A`.
   - Build ChronicleSubtype model on `{q : Rat // q ∈ limitDom A h_mcs}`.
   - This model has `¬φ` satisfied at `chronicleZero`.
   - But this ChronicleSubtype is a SUBTYPE OF RAT.
   - We can apply `satisfies_orderIso` to get a `Rat`-model where `¬φ` is satisfied.
   - This Rat model contradicts `temporal_valid_on_addcommgroup` (since Rat has AddCommGroup).

   The inclusion `ChronicleSubtype → Rat` is an order embedding, NOT an isomorphism. So we
   cannot directly apply `satisfies_orderIso` to the inclusion. BUT we can use:
   - The ChronicleSubtype is countable (subtype of Rat).
   - Case split: is ChronicleSubtype dense? If yes, use Cantor iso to Rat.
   - If no (discrete): use the Z-iso.

   In either case, the target domain (Rat or Int) has AddCommGroup.

## Recommended Approach

**Strategy 3 via Cantor/Z Isomorphism + `satisfies_orderIso`** is the recommended approach.

The proof of `temporal_valid_of_bimodal_derivable` proceeds as follows:

1. Prove `TemporalModel.transport` and `satisfies_orderIso` (structural induction on `φ`).

2. For the sorry proof, work by contrapositive inside:
   - Assume `¬(Satisfies M t φ)` (i.e., `φ` fails somewhere).
   - The temporal completeness proof already constructs a ChronicleSubtype countermodel
     from ANY non-derivable formula. But we need to feed it `φ` being non-BX-derivable.

3. The DIRECT path (not contrapositive): use the fact that the chronicle construction
   produces a model on a subtype of Rat. Then:
   - The ChronicleSubtype is either dense or discrete.
   - If dense: `cantorIsoDense` gives `ChronicleSubtype ≃o Rat`.
   - Transfer the contradiction via `satisfies_orderIso` to a Rat-model.
   - `temporal_valid_on_addcommgroup` on Rat gives `Satisfies M_rat t_rat φ`.
   - The iso transfers this back: `Satisfies chronicleModel t₀ φ`.
   - Chronicle truth lemma: `φ ∈ limitF(0) = A`. But `¬φ ∈ A` (A was built from `¬φ`), contradiction.

4. The discrete case requires `ChronicleSubtype ≃o Int` (needs `IsSuccArchimedean`).

**The critical observation**: the current file's `bimodal_conservative_over_temporal` theorem
proceeds in the FORWARD direction (bimodal derivable → temporal derivable), and the sorry is
inside the FORWARD direction of the semantic argument. The approach of "build a contradiction
via a ChronicleSubtype isomorphism" is logically valid and matches the bimodal precedent exactly.

## Evidence and Code Sketches

**`satisfies_orderIso` (to be proved by structural induction):**

```lean
/-- Temporal satisfaction is preserved under order isomorphism. -/
theorem satisfies_orderIso
    {D D' : Type} [LinearOrder D] [LinearOrder D']
    (e : D ≃o D') (M : TemporalModel D Atom) (t : D) (φ : Formula Atom) :
    Satisfies M t φ ↔ Satisfies { valuation := fun t' p => M.valuation (e.symm t') p } (e t) φ := by
  induction φ generalizing t with
  | atom p => simp [Satisfies, OrderIso.symm_apply_apply]
  | bot => simp [Satisfies]
  | imp φ ψ ih_φ ih_ψ =>
    simp only [Satisfies]
    exact ⟨fun h h' => (ih_ψ t).mp (h ((ih_φ t).mpr h')),
           fun h h' => (ih_ψ t).mpr (h ((ih_φ t).mp h'))⟩
  | untl ψ φ ih_ψ ih_φ =>
    simp only [Satisfies]
    constructor
    · rintro ⟨s, hts, h_φ, h_ψ⟩
      refine ⟨e s, e.strictMono hts, (ih_φ s).mp h_φ, ?_⟩
      intro r' h1 h2
      -- r' in (e t, e s) means e.symm r' in (t, s)
      have hr' : e.symm r' ∈ Set.Ioo t s := by
        constructor
        · exact e.symm.strictMono (by rwa [e.apply_symm_apply])
        · exact e.symm.strictMono (by rwa [e.apply_symm_apply])
      exact (ih_ψ (e.symm r')).mp (h_ψ (e.symm r') hr'.1 hr'.2)
    · -- symmetric
      ...
  | snce => -- symmetric to untl
    ...
```

**Cantor isomorphism application (to be used in the main proof):**

The temporal ChronicleSubtype has:
- `Countable (ChronicleSubtype A h_mcs)` (from `Subtype.countable`, since Rat is countable)
- `NoMaxOrder`, `NoMinOrder`, `Nontrivial` (proved in `ChronicleToCountermodel.lean`)
- `DenselyOrdered` (needed only for the Dense case; requires `dense_indicator_in_all_limit_points`
  or equivalent for the temporal Base case — this is the harder part)

For Base completeness, the ChronicleSubtype is NOT guaranteed to be DenselyOrdered.
This means the Cantor-iso path requires establishing density for the Base case separately,
OR taking a different path for the non-dense case.

## Confidence Assessment

| Strategy | Confidence | Effort |
|----------|-----------|--------|
| Strategy 3 (`satisfies_orderIso`) | HIGH — provable by structural induction | Low (5-10 lemmas) |
| Cantor iso for Dense ChronicleSubtype | HIGH — follows bimodal pattern | Medium |
| Cantor iso for Base ChronicleSubtype | LOW — not guaranteed DenselyOrdered | High |
| Z-iso for discrete ChronicleSubtype | MEDIUM — needs `IsSuccArchimedean` | High |
| Strategy 2 (syntactic) | LOW — needs cut-elimination result | Very High |

## Recommended Implementation Plan

**Phase 1**: Add to `Temporal/Semantics/Satisfies.lean`:
- `TemporalModel.transport : TemporalModel D Atom → (D ≃o D') → TemporalModel D' Atom`
- `satisfies_orderIso`: satisfaction preserved by order isomorphism (structural induction)

**Phase 2**: Prove `temporal_valid_of_bimodal_derivable` via the following sub-lemma:

```lean
-- Sub-lemma: validity on Rat implies validity on all serial linear orders
-- (via the contrapositive/ChronicleSubtype argument)
lemma temporal_valid_rat_implies_all_serial
    {φ : Formula Atom} [Denumerable (Formula Atom)]
    (h_rat : ∀ (M : TemporalModel Rat Atom) (t : Rat), Satisfies M t φ)
    (D : Type) [LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ
```

This lemma follows from the temporal completeness proof (if valid on Rat then derivable, if
derivable then valid everywhere) but needs `[Denumerable (Formula Atom)]` on the hypothesis side.

**Alternatively for Phase 2**: The sorry can be removed by the following route:

Note that `temporal_valid_on_addcommgroup` proves validity for AddCommGroup domains. The
temporal Base completeness proof uses ChronicleSubtype (subtype of Rat, hence Countable).
We need: ChronicleSubtype is either dense or discrete.

**Pragmatic Option**: The temporal Base completeness proof does NOT split into dense/discrete.
It just uses the chronicle construction directly. The ChronicleSubtype is countable and either
dense or discrete. If we can show that in EITHER case the ChronicleSubtype embeds into an
AddCommGroup domain via an ORDER ISOMORPHISM, we can apply `satisfies_orderIso`.

- Dense case: Cantor iso to Rat (AddCommGroup).
- Discrete case: Z-iso to Int (AddCommGroup).

This requires the temporal `chronicle_satisfies_c4` to establish density, OR a separate
analysis of the discrete structure. The bimodal `ChronicleToCountermodelBasic.lean` does
exactly this and is the template to follow.

## Summary

The sorry in `temporal_valid_of_bimodal_derivable` can be removed by:

1. Proving `satisfies_orderIso` (straightforward structural induction, ~20 lines).
2. Showing the temporal ChronicleSubtype (from the completeness proof) is either dense or
   discrete, and in either case order-isomorphic to Rat or Int (both having AddCommGroup).
3. Applying `satisfies_orderIso` to transfer between the ChronicleSubtype model and the
   AddCommGroup model, enabling `temporal_valid_on_addcommgroup` to close the goal.

The bimodal `ChronicleToCountermodelBasic.lean` is the primary implementation template. The
temporal version requires a dense/discrete case split on the Base ChronicleSubtype, analogous
to what bimodal already does for the bimodal Base completeness proof.
