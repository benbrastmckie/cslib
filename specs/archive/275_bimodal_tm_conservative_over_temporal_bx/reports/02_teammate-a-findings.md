# Task 275 Research: Contrapositive Approach via Completeness Internals

## Summary

The `sorry` in `temporal_valid_of_bimodal_derivable` arises from a domain mismatch:
bimodal soundness requires `[AddCommGroup D]`, while temporal BX completeness quantifies
over ALL `D` with `[LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]`.

This report examines whether the **contrapositive approach** can close this gap by
using the structure of the completeness countermodel.

---

## Key Findings

### 1. The Chronicle Countermodel Domain

The temporal BX completeness proof (`Cslib/Logics/Temporal/Metalogic/Completeness.lean`)
uses the **contrapositive**:

1. Assume `phi` is not BX-derivable.
2. Extend `{neg phi}` to an MCS `A` via Lindenbaum (`temporal_lindenbaum`).
3. Build `ChronicleSubtype A h_mcs` as the countermodel domain.

```lean
-- In Completeness.lean lines 116-127:
let D := Metalogic.Chronicle.ChronicleSubtype M hM_mcs
let model := Metalogic.Chronicle.chronicleModel M hM_mcs
let t₀ : D := Metalogic.Chronicle.chronicleZero M hM_mcs
have h_sat := h_valid D model t₀
```

`ChronicleSubtype A h_mcs` is defined as:
```lean
abbrev ChronicleSubtype (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :=
  {x : Rat // x ∈ limitDom A h_mcs}
```

It is a **subtype of `ℚ`** — specifically, the union of all domains across the omega-chain.

### 2. Order Instances on ChronicleSubtype

`ChronicleSubtype A h_mcs` has these proven instances
(from `ChronicleToCountermodel.lean`):
- `LinearOrder` (inherited from `ℚ`)
- `Nontrivial`
- `NoMaxOrder`
- `NoMinOrder`
- `Countable` (subtype of `ℚ`, which is `Countable`)

**Critical gap**: `ChronicleSubtype` does **NOT** have `DenselyOrdered` for base BX.
The Dense BX variant (`chronicleDenselyOrderedDense` in `DenseCompleteness.lean`)
requires starting from a Dense-MCS. Base BX provides no density.

### 3. Why Order.iso_of_countable_dense Does NOT Apply

`Order.iso_of_countable_dense` (Mathlib, `CountableDenseLinearOrder`) has signature:
```lean
theorem Order.iso_of_countable_dense (α β : Type) 
    [LinearOrder α] [LinearOrder β] 
    [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] 
    [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β)
```

This requires `DenselyOrdered` on BOTH sides. Since base `ChronicleSubtype` lacks
`DenselyOrdered`, we cannot use this theorem to map it to `ℚ`.

### 4. Why Order Embedding Does NOT Suffice

`Order.embedding_from_countable_to_dense` gives a `↪o` (strict order embedding, not iso):
```lean
theorem Order.embedding_from_countable_to_dense (α β : Type)
    [LinearOrder α] [LinearOrder β] [Countable α] [DenselyOrdered β] [Nontrivial β] :
    Nonempty (α ↪o β)
```

An order **embedding** (not isomorphism) cannot transfer temporal satisfaction. The
`Satisfies` relation for `untl` and `snce` quantifies over the target domain:
```lean
| .untl ψ φ =>
    ∃ s, t < s ∧ Satisfies M s φ ∧
      ∀ r, t < r → r < s → Satisfies M r ψ
```
Embedding `ChronicleSubtype` into `ℚ` would ADD intermediate witnesses in `ℚ`
that do not exist in `ChronicleSubtype`, breaking the correspondence. A pullback
model (restricting the `ℚ` model to the subtype image) would only give an embedding,
not a surjection, and the intermediate-point quantifiers see the full `ℚ`.

An order **isomorphism** WOULD preserve satisfaction (the quantifiers range exactly
over the image). But `Order.iso_of_countable_dense` requires density.

### 5. The Rat Domain: All Required Instances Exist

`ℚ` has ALL the required instances:
- `LinearOrder ℚ` (`Rat.linearOrder`)
- `Nontrivial ℚ` (trivially: `0 ≠ 1`)
- `NoMaxOrder ℚ`, `NoMinOrder ℚ` (standard)
- `DenselyOrdered ℚ` (standard Archimedean field property)
- `AddCommGroup ℚ` (`Rat.addCommGroup`)
- `IsOrderedAddMonoid ℚ` (`Rat.instIsOrderedAddMonoid`)

So **`ℚ` has every instance required by both bimodal soundness AND temporal completeness**.

### 6. The Core Structural Insight

The existing `bimodal_conservative_over_temporal` proof applies:
```lean
apply Cslib.Logic.Temporal.completeness
intro D _lo _nt _nm _nm2 M t
exact temporal_valid_of_bimodal_derivable h D M t
```

The completeness theorem accepts **any** `D` with `[LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]`. The sorry is in providing this universally.

**But**: we ONLY need to disprove `phi ∉ A` for the specific `D = ChronicleSubtype M h_mcs`
constructed by the completeness proof. The completeness proof passes this specific `D`
by calling `h_valid D model t₀` (line 120 of `Completeness.lean`).

This means `temporal_valid_of_bimodal_derivable` only needs to work when `D = ChronicleSubtype`.

---

## Recommended Approach

### Primary Approach: Reformulate to Use ℚ Directly

**Strategy**: The contrapositive proof in `bimodal_conservative_over_temporal` can be
rewritten to bypass `temporal_valid_of_bimodal_derivable` entirely by using `ℚ` instead
of an arbitrary `D`.

Instead of calling `Temporal.completeness` (which quantifies over all domains), we
re-inline the contrapositive: if `phi` is not BX-derivable, build the MCS `A`, take
`D = ℚ` (or another AddCommGroup), and construct a temporal model on `ℚ` that
countermodels `phi`.

**Concrete plan**: The issue is that `chronicleModel` lives on `ChronicleSubtype` (a subtype
of `ℚ`), not on `ℚ` itself. However, `Satisfies` on `ChronicleSubtype` can be transferred
to a model on all of `ℚ` via **extension** of the valuation.

Define `extendedModel : TemporalModel ℚ Atom` with:
- `valuation t p := if h : t ∈ limitDom A h_mcs then Formula.atom p ∈ limitF A h_mcs t else False`

Then prove: for `t ∈ limitDom A h_mcs`, `Satisfies extendedModel t phi ↔ Satisfies chronicleModel ⟨t, ht⟩ phi`.

This is the model-transfer result. But it requires showing that the `until`/`since`
witnesses at rational points in `limitDom` agree. This is **exactly** the same difficulty
as the original problem, since the `extendedModel` quantifies over all of `ℚ`, not just
`limitDom`.

**Assessment**: This approach does not work cleanly because of the same witness quantifier issue.

### Secondary Approach: Inline Contrapositive with AddCommGroup Domain

**Strategy**: Do NOT call `Temporal.completeness`. Instead, inline the completeness proof.

The existing completeness proof calls `h_valid D model t₀` where `D = ChronicleSubtype`.
The goal is to apply `temporal_valid_on_addcommgroup` (which is sorry-free) to get
`Satisfies chronicleModel t₀ phi`. But this requires `[AddCommGroup (ChronicleSubtype A h_mcs)]`.

**Key question**: Does `ChronicleSubtype` (a subtype of `ℚ`) have `AddCommGroup`?

A subtype does NOT automatically inherit `AddCommGroup`. It would need to be a subgroup of `(ℚ, +)`, i.e., closed under addition and negation. The limit domain `limitDom A h_mcs` is a
countable subset of `ℚ` constructed by iteratively inserting midpoints and new witnesses.
There is **no reason** it is closed under addition.

**Assessment**: Subtype AddCommGroup is not available. This approach fails.

### Tertiary Approach: Satisfaction Invariance under Order Isomorphism (BEST APPROACH)

**Strategy**: Prove a lemma:
```lean
lemma Satisfies.orderIso_transfer {D₁ D₂ : Type} [LinearOrder D₁] [LinearOrder D₂]
    (f : D₁ ≃o D₂) (M : TemporalModel D₁ Atom) (t : D₁) (phi : Temporal.Formula Atom) :
    let M₂ : TemporalModel D₂ Atom := ⟨fun t p => M.valuation (f.symm t) p⟩
    Satisfies M t phi ↔ Satisfies M₂ (f t) phi
```

This is true: order isomorphisms preserve the quantifier structure of `until` and `since`
because `f` is a bijection preserving `<`. The proof is by induction on `phi`.

Then: to prove `Satisfies M t phi` for `D` arbitrary serial linear order, we need to know
that `phi` is valid on SOME AddCommGroup domain, and apply the isomorphism.

But what is the isomorphism? We cannot get an iso FROM arbitrary `D` TO `ℚ` without density.

**However**, there is a **different decomposition**: we can directly reformulate the
conservativity theorem to bypass universally quantified completeness and instead use an
_explicit_ countermodel construction.

### BEST APPROACH: Refactor Proof via ℚ-Model Directly

Here is the cleanest approach that avoids all these obstacles:

**Observation**: The completeness theorem has signature:
```lean
theorem completeness [Denumerable (Formula Atom)] {φ : Formula Atom}
    (h_valid : ∀ (D : Type) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ) :
    Temporal.ThDerivable φ
```

The key: the countermodel used internally is `D = ChronicleSubtype`. We need to show that IF `phi.toBimodal` is TM-derivable, THEN `Satisfies (ChronicleSubtype M h_mcs) t phi` — i.e., phi is satisfied at the chronicle model specifically.

And `temporal_valid_on_addcommgroup` gives us `Satisfies` for AddCommGroup domains.

**The core lemma needed**:
```lean
-- For ANY temporal model M_temp on ANY serial linear order D,
-- there exists an AddCommGroup serial linear order D' and a model M_temp' on D'
-- such that Satisfies M_temp t phi iff Satisfies M_temp' t' phi' for related t, t'.
```

This is equivalent to saying: every serial linear order embeds order-isomorphically into
an AddCommGroup serial linear order. That is FALSE in general (e.g., ωm* + 1 has no such embedding).

**BUT**: the only domain we actually need to handle is `ChronicleSubtype` (a subtype of `ℚ`).
And `ChronicleSubtype` DOES admit an order embedding into `ℚ` via the inclusion:
```lean
ChronicleSubtype A h_mcs ↪o ℚ  (by Subtype.val)
```

The inclusion is an order embedding (injective and order-preserving). But it is NOT surjective
(not an isomorphism), so `Order.iso_of_countable_dense` cannot directly be applied unless
`ChronicleSubtype` is also dense.

### The Density Gap and How to Close It

**For the base BX case**: `ChronicleSubtype` is NOT dense in general. The omega-chain
construction starts from a singleton `{0 -> A}` and inserts new points only for Until/Since
witnesses and C4 obligations. The resulting domain may have countable gaps.

**However**: there is an alternative that DOES work for our specific use case.

#### The Key Insight: ℚ as Canonical Domain

Since `Temporal.Satisfies` only uses `LinearOrder`, the completeness theorem works equally
well if we strengthen the hypothesis to:

```lean
-- Alternative completeness usage:
-- If phi is valid on ℚ (with standard order), then phi is BX-derivable.
```

Is this true? **Yes** — because if phi has a countermodel on some serial linear order `D`,
the chronicle construction from the completeness proof builds a countermodel on
`ChronicleSubtype ⊆ ℚ`. And any model on `ChronicleSubtype` can be "extended" to a model on
`ℚ` that still countermodels `phi`, AS LONG AS the extension is done carefully.

The correct extension: Given `M_chron : TemporalModel (ChronicleSubtype A h_mcs) Atom`,
define `M_rat : TemporalModel ℚ Atom`:
```lean
M_rat.valuation t p := if h : t ∈ limitDom A h_mcs
                       then M_chron.valuation ⟨t, h⟩ p
                       else False
```

**The transfer lemma**: For `t ∈ limitDom A h_mcs`, does
`Satisfies M_rat t phi ↔ Satisfies M_chron ⟨t, h⟩ phi`?

For `atom` and `bot`: trivially yes.
For `imp`: yes, by IH.
For `untl phi psi`: In `M_chron`, the witness `s > t` ranges over `limitDom`. In `M_rat`,
the witness `s > t` ranges over ALL of `ℚ`. This is DIFFERENT — `M_rat` has more potential
witnesses, which could make `phi` TRUE in `M_rat` even when it is FALSE in `M_chron`.

Wait — the direction we need for the conservativity proof is:
- `phi ∉ A` (phi is NOT in the starting MCS)
- The truth lemma gives `NOT (Satisfies M_chron t₀ phi)`.
- We need `NOT (Satisfies M_rat t₀ phi)`.

The issue: `M_rat` has MORE witnesses (all rationals), which could make phi TRUE in `M_rat`
even if it is FALSE in `M_chron`. So this extension does NOT give us what we need.

Conversely, if we restrict `M_rat` to only use witnesses in `limitDom`, then it is just
`M_chron` reindexed — not a full `ℚ` model.

#### Dead End Confirmed: No Simple Model Transfer

The document section in `TemporalConservativity.lean` (lines 218-240) correctly identifies
this as the fundamental obstacle. Adding new witnesses via extension introduces false
positives. Order embeddings do not preserve satisfaction.

---

## Revised Recommended Approach: Rewrite Conservativity Proof

The cleanest solution that avoids the sorry is to **completely rewrite
`bimodal_conservative_over_temporal`** to not call `Temporal.completeness` at all,
but instead INLINE the contrapositive.

**Inline Contrapositive Strategy**:

```lean
theorem bimodal_conservative_over_temporal
    [Infinite Atom] [DecidableEq Atom] [Denumerable (Temporal.Formula Atom)]
    {φ : Temporal.Formula Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal) :
    Cslib.Logic.Temporal.Temporal.ThDerivable φ := by
  -- Contrapositive: assume phi not BX-derivable.
  by_contra h_not_deriv
  -- Build MCS from the consistent set {neg phi}.
  have h_cons := neg_consistent_of_not_derivable h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum h_cons
  have h_neg_in_M : (¬φ) ∈ M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg hM_mcs h_neg_in_M
  -- The chronicle domain.
  let D := Metalogic.Chronicle.ChronicleSubtype M hM_mcs
  let model := Metalogic.Chronicle.chronicleModel M hM_mcs
  let t₀ : D := Metalogic.Chronicle.chronicleZero M hM_mcs
  -- NOW: apply temporal_valid_on_addcommgroup — but D must have AddCommGroup!
  -- This is the SAME WALL.
  sorry
```

We hit the same wall: `D = ChronicleSubtype` lacks `AddCommGroup`.

---

## The ONLY Viable Path: Prove Satisfies is Invariant Under OrderIso Then Use ℚ

Let us reconsider. The key question: **can we get an order isomorphism from
`ChronicleSubtype` to some AddCommGroup domain?**

`ChronicleSubtype` is:
- `Countable` (subtype of `ℚ`)
- `LinearOrder`
- `NoMaxOrder`
- `NoMinOrder`
- NOT necessarily `DenselyOrdered` (for base BX)

`ℚ` is:
- `Countable`
- `LinearOrder`
- `NoMaxOrder`
- `NoMinOrder`
- `DenselyOrdered`
- `AddCommGroup`

So we cannot use `Order.iso_of_countable_dense` directly without density.

**BUT**: `Order.embedding_from_countable_to_dense` gives an ORDER EMBEDDING (not iso) from
any countable linear order to `ℚ`. And if we can prove `Satisfies` is invariant under
order EMBEDDINGS (not just isomorphisms), we are done.

**Claim**: For temporal formulas WITHOUT `G/H` universal quantifiers, satisfaction is
NOT preserved by order embeddings. The `until` formula `∃ s > t, phi(s) ∧ ∀ r ∈ (t,s), psi(r)`
involves an intermediate universal quantifier — new points in the target domain between
`t` and `s` could falsify `psi`.

Therefore: order embedding invariance does NOT hold in general for Until/Since formulas.

---

## Final Assessment: The Difficulty is Real

The domain mismatch is a **genuine mathematical obstacle**, not a Lean formalization issue.
The problem is that:
1. Bimodal soundness gives validity only on AddCommGroup domains.
2. Temporal completeness needs a countermodel on some specific domain.
3. The chronicle countermodel lives on a subtype of `ℚ` that is not an AddCommGroup.
4. Model transfer from `ChronicleSubtype` to `ℚ` breaks for Until/Since quantifiers.
5. The `Order.iso_of_countable_dense` approach requires density, which base BX does not provide.

The most promising resolution — not yet explored in the codebase — is:

**APPROACH: Use a Different Completeness Proof Structure**

Instead of proving `∀ D ... Satisfies M t phi` and then applying `completeness`, directly
prove the completeness theorem with the restricted hypothesis:

```lean
-- A strengthened temporal completeness theorem:
theorem completeness_acg [Denumerable (Formula Atom)] {φ : Formula Atom}
    (h_valid : ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
      [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ) :
    Temporal.ThDerivable φ
```

If this is provable — i.e., if validity on AddCommGroup serial linear orders suffices for
BX-derivability — then the conservativity theorem follows immediately from
`temporal_valid_on_addcommgroup`.

**Is this provable?** We need to show: if `phi` is not BX-derivable, there is a
countermodel on an AddCommGroup serial linear order. The chronicle model lives on
`ChronicleSubtype ⊆ ℚ`. If the limit domain `limitDom` is in fact dense (which we can
prove it is for base BX — the C4 condition guarantees density between any two points
once the relevant Until formulas are handled), then we CAN use `Order.iso_of_countable_dense`
to get an iso `ChronicleSubtype ≃o ℚ`, and then transfer the countermodel to `ℚ` via the iso.

**The density question is critical**: Does the limit domain from the base BX completeness
proof end up dense? The dense completeness file proves density for Dense-BX. The base BX
omega-chain does NOT guarantee density — it only adds C4 witnesses (between existing domain
points) and C5 witnesses. The domain remains a well-ordered subtype without density.

**Conclusion**: The density approach does not work for base BX.

---

## Evidence: What the Codebase Contains vs. What is Needed

### What Exists (Sorry-Free)

1. `temporal_valid_on_addcommgroup` — validity on AddCommGroup domains (proven).
2. `bimodal_truthAt_toBimodal_iff_temporal_satisfies` — semantic bridge (proven).
3. `chronicle_truth_lemma` — satisfaction iff MCS membership (proven).
4. `ChronicleSubtype` properties: `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`.
5. `Temporal.completeness` — BX completeness over ALL serial linear orders (proven).

### What is Missing

1. An order isomorphism `ChronicleSubtype A h_mcs ≃o ℚ` — requires density.
2. Density of `ChronicleSubtype` for base BX — NOT proven (requires showing the limit domain is dense, which would require the Dense axiom or a separate argument).
3. `AddCommGroup (ChronicleSubtype A h_mcs)` — not available (subtype, not subgroup).
4. A `completeness_acg` variant with AddCommGroup hypothesis — not in codebase.

---

## Confidence Level

**HIGH confidence** on the analysis: the sorry gap is real and the standard approaches
(order embedding, subtype AddCommGroup) do not work.

**MEDIUM confidence** on resolution path: the most promising approach is to prove that the
limit domain is **dense** for base BX (which would follow from the C4 property applied to
the dense indicator formula), enabling `Order.iso_of_countable_dense`.

**Key to check**: Does `limit_satisfies_c4` imply density of `limitDom A h_mcs`?
Looking at the base BX chronicle: for any `x < y` in `limitDom`, if there exists `z` with
`x < z < y` in `limitDom`, then the domain is dense. The C4 condition guarantees intermediate
witnesses for specific Until/Since formulas, but NOT for arbitrary pairs.

Actually: `chronicleDenselyOrderedDense` in `DenseCompleteness.lean` uses the formula
`neg U(bot, top)` (the "dense indicator") to find a witness between any two points. For
BASE BX, this formula is NOT guaranteed to be in the starting MCS. So density fails for base BX.

**REVISED CONCLUSION**: The sorry cannot be eliminated with the current chronicle construction.
The only valid fix is a **structural refactoring** of one of:
(a) The bimodal soundness theorem to not require `AddCommGroup`, or
(b) An alternative completeness proof using an `AddCommGroup` domain from the start, or
(c) A domain-independence theorem for temporal satisfaction.

Option (a) would require fundamental changes to the bimodal semantic framework.
Option (b) requires a new completeness proof using `ℚ` directly as the time domain.
Option (c) is the domain-transfer approach which fails due to quantifier issues.

**Option (b) is the most feasible**: prove `completeness` using the existing chronicle but
verify that the chronicle model on `ChronicleSubtype ⊆ ℚ` can be transferred to `ℚ` by
showing the truth lemma still holds when evaluating on `ℚ` with valuation extended by
`False` outside `limitDom`. The key: although `ℚ` has more points, the truth lemma would
need to show that the extended model agrees with the chronicle model on `limitDom` points,
AND that this agreement suffices for the final contradiction.

**Whether option (b) is true**: The truth lemma (`chronicle_truth_lemma`) would need to hold
for `ℚ` with the extended valuation. For `until` formulas, the ℚ-extended model adds
potential witnesses outside `limitDom` that could make formulas TRUE that are FALSE in
`ChronicleSubtype`. So the extended model is NOT a valid countermodel in the sense needed.

**FINAL CONCLUSION**: The sorry gap documents a GENUINE mathematical difficulty. The task
should be marked `[PARTIAL]` with the current state (6 of 7 results proven) unless a
new approach is discovered. The most promising unexplored direction is option (b) with a
careful analysis of whether "validity on ℚ implies BX-derivability" is provable without
using the dense axiom.
