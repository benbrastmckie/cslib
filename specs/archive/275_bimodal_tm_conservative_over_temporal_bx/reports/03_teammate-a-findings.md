# Teammate A Findings: Primary Approach for Temporal Conservativity

**Task 275**: Prove Bimodal TM is conservative over Temporal BX for temporal formulas.
**Focus**: Direct proof strategy for the sorry in `temporal_valid_of_bimodal_derivable`.

---

## Key Findings

### 1. What the sorry covers

The sorry lives in `temporal_valid_of_bimodal_derivable` at
`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` lines 255-263.

Exact type signature:
```lean
theorem temporal_valid_of_bimodal_derivable
    [Infinite Atom] [DecidableEq Atom]
    {φ : Temporal.Formula Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal)
    (D : Type) [LinearOrder D] [Nontrivial D]
    [NoMaxOrder D] [NoMinOrder D]
    (M : Temporal.TemporalModel D Atom) (t : D) :
    Temporal.Satisfies M t φ
```

The goal is: given that `φ.toBimodal` is TM-derivable, show `φ` is satisfied in ANY
temporal model on ANY serial linear order (not just AddCommGroup ones).

The already-proven infrastructure above it:
- `temporal_valid_on_addcommgroup` (lines 196-206): proves the same conclusion but only when `D`
  additionally satisfies `[AddCommGroup D] [IsOrderedAddMonoid D] [Nontrivial D]`. This is
  fully proven using TM soundness + the semantic bridge.
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies` (lines 149-183): proven by structural
  induction. Translates bimodal `truthAt` in the `temporalTaskModel` to temporal `Satisfies`.

### 2. The exact domain mismatch

`temporal_valid_on_addcommgroup` requires `AddCommGroup D` because `temporalTaskFrame D`
uses addition for its task relation (`taskRel w d u := u = w + d`), and bimodal soundness
requires the domain `D` to be an `AddCommGroup` (or similar) to instantiate `TaskFrame D`.

But the temporal completeness theorem (`Temporal.completeness`, lines 101-127 of
`Completeness.lean`) quantifies over ALL `D : Type` with `[LinearOrder D] [Nontrivial D]
[NoMaxOrder D] [NoMinOrder D]` — no algebraic structure required.

So the gap is: given validity on all AddCommGroup serial linear orders, extend to all serial
linear orders. This requires a model-transfer result.

### 3. The chronicle countermodel's domain type

The completeness proof builds its countermodel on `ChronicleSubtype A h_mcs`, which is:
```lean
abbrev ChronicleSubtype (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :=
  {x : Rat // x ∈ limitDom A h_mcs}
```
This is a **subtype of `ℚ`** (rationals). Key instances:
- `ℚ` has `AddCommGroup ℚ` (Mathlib: `Rat.addCommGroup`)
- `ℚ` has `IsOrderedAddMonoid ℚ` (Mathlib: `Rat.instIsOrderedAddMonoid`)
- `ℚ` has `LinearOrder ℚ` (Mathlib: `Rat.linearOrder`)
- `ℚ` has `Nontrivial ℚ` (Mathlib: `Rat.nontrivial`)
- `ℚ` has `NoMaxOrder ℚ` and `NoMinOrder ℚ` (from `IsOrderedRing + Nontrivial`)
- `ℚ` has `DenselyOrdered ℚ` (from `LinearOrderedSemiField.toDenselyOrdered`)

The `ChronicleSubtype A h_mcs` inherits `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`
from `ℚ` (proven in `ChronicleToCountermodel.lean`). It also inherits `AddCommGroup` and
`IsOrderedAddMonoid` as a subtype of `ℚ`, since subtypes of ordered groups with the subtype
order are themselves ordered groups (provided the subtype is closed under the group operations
— but this is where care is needed; see obstacle below).

### 4. The recommended approach: semantic transfer via order isomorphism (Cantor's theorem)

The cleanest approach that avoids proving ChronicleSubtype is an ordered group is:

**Step A: Prove satisfaction is preserved by order isomorphism.**

Prove a lemma:
```lean
theorem satisfies_orderIso
    {D₁ D₂ : Type*} [LinearOrder D₁] [LinearOrder D₂]
    (e : D₁ ≃o D₂)
    {Atom : Type*} (M₁ : TemporalModel D₁ Atom) (t : D₁) (φ : Formula Atom) :
    Satisfies M₁ t φ ↔ Satisfies (M₁.pullback e) (e t) φ
```
where `M₁.pullback e` is the model on `D₂` with `valuation t₂ p := M₁.valuation (e.symm t₂) p`.

This is provable by structural induction on `φ`. The key is that `e` preserves strict order:
- For `untl`: `t < s ↔ e t < e s` (by `OrderIso.lt_iff_lt`), and the quantifiers
  `∀ r, t < r → r < s` become `∀ r', e t < r' → r' < e s` (via substitution `r' = e r`
  since `e` is surjective). This induction terminates because the formula is finite.
- The `snce` case is symmetric.
- `atom`, `bot`, `imp` are immediate.

**Step B: For any serial linear order `D`, pull the model back through an embedding into `ℚ`.**

Mathlib provides (Mathlib.Order.CountableDenseLinearOrder):
```
Order.embedding_from_countable_to_dense :
  ∀ (α β) [LinearOrder α] [LinearOrder β] [Countable α] [DenselyOrdered β] [Nontrivial β],
    Nonempty (α ↪o β)
```

However, this gives only an **embedding** (order-preserving injection), not an isomorphism.
Satisfaction is NOT preserved by mere order embeddings because the quantifiers `∃ s > t`
(in Until) range over the TARGET domain. Pulling back along an embedding `D ↪o ℚ` introduces
new witnesses in `ℚ` not in the image of `D`, which can break satisfaction.

**Step C: Use order isomorphism, not just embedding.**

For a full isomorphism, Mathlib provides:
```
Order.iso_of_countable_dense :
  ∀ (α β) [LinearOrder α] [LinearOrder β] [Countable α] [DenselyOrdered α]
    [NoMinOrder α] [NoMaxOrder α] [Nonempty α]
    [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β],
    Nonempty (α ≃o β)
```

This requires BOTH domains to be countable, densely ordered, without endpoints.

The arbitrary domain `D` appearing in `temporal_valid_of_bimodal_derivable` need not be
countable or densely ordered. So `Order.iso_of_countable_dense` does NOT directly apply.

### 5. The actual obstacle: no model-transfer for base BX

The module's comment (lines 220-239) accurately diagnoses the issue:

> "pushing a temporal model through an order-embedding does NOT in general preserve temporal
> satisfaction, because the quantifiers in `untl`/`snce` range over the target domain,
> introducing new potential witnesses."

And:

> "(a) An order-isomorphism ... requires ChronicleSubtype to be countable, dense, and without
> endpoints (by Cantor's theorem `Order.iso_of_countable_dense`). The density property holds
> only for the Dense BX completeness proof, not for base BX."

This is the key difficulty. Base BX completeness uses the chronicle countermodel, which lives
on `ChronicleSubtype` (a subtype of `ℚ`). But `ChronicleSubtype` is NOT necessarily densely
ordered — the chronicle construction is designed for base BX, which does not include the
density axiom. The density axiom is an extra axiom for the Dense BX frame class
(`FrameClass.Dense`), not for the base class (`FrameClass.Base`).

### 6. Alternative approach: directly prove AddCommGroup instances for ChronicleSubtype

If `ChronicleSubtype A h_mcs` had `AddCommGroup` and `IsOrderedAddMonoid` instances, then
`temporal_valid_on_addcommgroup` could be applied directly to it, bypassing the transfer
problem entirely.

`ChronicleSubtype A h_mcs = {x : ℚ // x ∈ limitDom A h_mcs}`.

The subtype of `ℚ` with a predicate `P` is an `AddCommGroup` only if it is closed under
addition and negation (the induced operations). The set `limitDom A h_mcs` is a subset of
`ℚ` defined by the chronicle construction — it is not a subgroup in general. Indeed,
`limitDom` is built as the union of finite rational domains of increasingly fine chronicles;
there is no reason to expect it is closed under addition.

So directly equipping `ChronicleSubtype` with `AddCommGroup` is likely FALSE without
additional structure.

### 7. Alternative approach: change the sorry strategy — use completeness directly on ℚ

A different approach: instead of going through an arbitrary `D`, prove the result via the
following route:

1. Given `h : Bimodal.ThDerivable φ.toBimodal`, apply `temporal_valid_on_addcommgroup`
   instantiated at `D = ℚ`: this gives `∀ (M : TemporalModel ℚ Atom) (t : ℚ), Satisfies M t φ`.
2. Now prove: if `φ` is valid on all ℚ-models, then `φ` is valid on all serial linear orders.

Step 2 is essentially "validity on `ℚ` models implies validity on all serial linear orders."
This is true only if `ℚ` is sufficiently rich (embeds all serial linear orders in a way that
preserves satisfaction). But again, embedding is insufficient — we need isomorphism.

For DENSE linear orders without endpoints, the situation is better: any countable dense
linear order without endpoints is isomorphic to `ℚ` by Cantor's theorem. The chronicle
countermodel for Dense BX is built on `ChronicleSubtype` which is proven densely ordered
(in `DenseCompleteness.lean`, `chronicleDenselyOrderedDense`). So:

- For Dense BX: the domain is `ChronicleSubtype` which is densely ordered and (as a subtype
  of the countable set `ℚ`) countable. By `Order.iso_of_countable_dense`, it is isomorphic to
  `ℚ` if `ℚ` is also countable + densely ordered. `ℚ` has both. So a ℚ-to-ChronicleSubtype
  isomorphism exists, and satisfaction transfers. This route works for Dense BX.

- For BASE BX: the domain `ChronicleSubtype` is NOT necessarily densely ordered. So Cantor's
  theorem does not apply.

### 8. What IS doable: a "sorry-free except for base BX" approach

The following is the current state of the proof:
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies`: fully proven (no sorry).
- `temporal_valid_on_addcommgroup`: fully proven (no sorry).
- `bimodal_conservative_over_temporal`: proven modulo the sorry in `temporal_valid_of_bimodal_derivable`.

The sorry gap is specifically about proving that temporal BX validity on `AddCommGroup` serial
linear orders implies validity on ALL serial linear orders. This is a genuine mathematical
gap, not a proof engineering issue.

### 9. The most promising direction: syntactic proof via liftDerivationQfree

There is an alternative to the semantic approach: prove conservativity syntactically.

The `liftDerivationQfree` infrastructure in `Lifting.lean` (line 691) already gives:
```lean
theorem liftDerivationQfree [Infinite Atom] [DecidableEq Atom]
    {fc : FrameClass} (L : List (Formula Atom)) (phi : Formula Atom)
    (d : ExtDerivationTree fc (L.map embedFormula) (embedFormula phi)) :
    Nonempty (DerivationTree fc L phi)
```

This lifts derivations in the EXTENDED system (with box) back to the BASE system, PROVIDED
the formula `phi` is in the IMAGE of `embedFormula`. The key question is: can we show that
if `φ.toBimodal` is TM-derivable, then there is a BX-derivation of `φ`?

The approach would be:
1. Show that the TM axioms include all BX temporal axioms (and the box axioms are additional).
2. Show that if a temporal formula (one using only untl/snce, no box) is derivable in TM,
   then any box introduction in the derivation can be eliminated when the conclusion has no box.

This would be a **cut-elimination / box-elimination** argument, analogous to how the existing
`liftDerivationQfree` eliminates the fresh atom. The core insight is: if the CONCLUSION is a
temporal formula (no box), then box-introduction steps in the derivation can be replaced by
purely temporal steps (or eliminated).

However, there is no existing `box_elimination` lemma or similar in the CSLib codebase, so
this would require new infrastructure.

---

## Recommended Approach

**Recommended**: The semantic bridge approach through `ℚ` is the correct mathematical route,
but requires one additional lemma as the critical bridge:

### Primary Recommendation: Prove `satisfies_orderIso` and use ℚ as pivot

The proof plan:

**Phase 1** (Straightforward): Prove satisfaction is preserved by order isomorphism:
```lean
theorem satisfies_orderIso {D₁ D₂ : Type*} [LinearOrder D₁] [LinearOrder D₂]
    (e : D₁ ≃o D₂) {Atom : Type*}
    (M : TemporalModel D₁ Atom) (t : D₁) (φ : Formula Atom) :
    Satisfies M t φ ↔ Satisfies (M.reindex e) (e t) φ
```
This is a structural induction on `φ`. Every constructor is easy; Until/Since use
`OrderIso.lt_iff_lt` and bijectivity of `e`.

**Phase 2** (Harder; requires new insight): For an arbitrary serial linear order `D`,
construct an order-isomorphism from `D` to some domain with `AddCommGroup`.

The obstacle: a serial linear order need not be isomorphic to `ℚ` (it need not be countable
or dense). So there is no universal isomorphism to `ℚ`.

**What does work**: If the proof uses `completeness` as a black box, the only domain that
actually needs to satisfy AddCommGroup is the `ChronicleSubtype`. And that DOES sit inside
`ℚ`. The question is whether restricting validity to `ℚ`-models is enough to conclude
validity on all models.

The correct strategy is:
1. Prove `φ` is valid in all `ℚ`-models (from `temporal_valid_on_addcommgroup` at `D = ℚ`).
2. Prove: temporal BX validity on ℚ-models implies BX-derivability (a restricted completeness).
3. Apply BX soundness to conclude validity on all serial linear orders.

Step 2 requires showing that if `φ` fails in some serial linear order, it fails in a ℚ-model.
This is the model-transfer step. The chronicle construction for base BX produces a subtype-of-ℚ
countermodel — so countermodels already live on subtypes of ℚ. But subtype-of-ℚ ≠ ℚ itself.

**The real gap**: Even though `ChronicleSubtype ⊆ ℚ` and `ℚ` has AddCommGroup, the quantifiers
in Until/Since range over the FULL domain `ChronicleSubtype`, not all of `ℚ`. Pulling the
countermodel into `ℚ` via inclusion introduces new witnesses (rationals not in the chronicle)
that might falsify a formula that was true in the chronicle.

### Alternative Recommendation: Mark as [BLOCKED] pending base BX model-transfer

Given the genuine mathematical difficulty — base BX models do not have enough structure for
Cantor's theorem, and subtypes of `ℚ` do not inherit `AddCommGroup` without closure
conditions — the most honest course is to:

1. Accept `temporal_valid_on_addcommgroup` as the achieved result (TM soundness transferred
   to AddCommGroup domains).
2. Declare `temporal_valid_of_bimodal_derivable` as blocked on the model-transfer lemma.
3. Document that the full proof requires one of:
   - A completeness theorem for temporal BX restricted to `AddCommGroup` serial linear orders
     (i.e., showing that `AddCommGroup` serial linear orders are sufficient for BX completeness).
   - A proof that every BX-consistent formula has an `AddCommGroup` countermodel.

The second option is essentially asking: "Is there a variant of the chronicle construction
that produces a countermodel on an additive group?" Since the chronicles live on subtypes of
ℚ, this reduces to: "Can the chronicle domain always be extended to a subgroup of ℚ while
preserving the satisfaction of the formula?"

This is non-trivial but potentially true: the chronicle domain is a countable subset of ℚ,
and one could try to close it under addition. But doing so might not preserve the MCS-labelling
or the chronicle conditions C0-C5.

---

## Evidence and Examples

### Why embedding alone fails (concrete example)

Consider `φ = someFuture (atom p)` (i.e., `F(p)`). Suppose `D = {0, 1}` (two-point serial
linear order, but actually that has no `NoMaxOrder`; take `D = ℤ` for clarity). Suppose in
the `D`-model, `p` holds only at time `1` and we evaluate at `0`. Then `F(p)` holds since
`1 > 0` and `p` holds at `1`. Now embed `D = ℤ` into `ℚ` via `n ↦ n`. The `ℚ`-model must
be defined on all of `ℚ` — so `p` at all the new rational points (not in the image of `ℤ`)
must be specified. If we define `p` false at all non-integer rationals, `F(p)` still holds
in the `ℚ`-model. So IMAGES of models are fine; the issue is PREIMAGES.

Conversely: can `F(p)` be true in a `ℚ`-model but false in the corresponding `D`-model? Yes:
if the embedding is `D = {0, 2}` and `p` is true only at `1 ∈ ℚ \ D`, then `F(p)` is true
in ℚ at 0 (witness 1) but there is no witness in `D` for `F(p)` at 0. So validity on ℚ
models does NOT imply validity on all models. (This shows ℚ-validity is weaker than
all-domain validity, not stronger — but the direction we need is the other way.)

The direction we need: all-`AddCommGroup`-domain validity implies all-domain validity.
This requires showing any countermodel can be simulated by an `AddCommGroup` countermodel.

### The Dense BX case (which DOES work) as a reference

In `DenseCompleteness.lean`, the chronicle countermodel for Dense BX is proven to be
`DenselyOrdered` (via `chronicleDenselyOrderedDense`). Combined with `Countable`
(as a subtype of the countable set `ℚ`, which is countable as `Rat.instDenumerable`
gives `Denumerable ℚ`) and `NoMinOrder`/`NoMaxOrder`, the conditions for
`Order.iso_of_countable_dense` are satisfied. This gives `ChronicleSubtype ≃o ℚ` for
Dense BX countermodels.

Since `ℚ` has `AddCommGroup`, after the isomorphism, the countermodel lives on `ℚ`, and
`temporal_valid_on_addcommgroup` at `D = ℚ` would give the contradiction. This route closes
the sorry FOR DENSE BX.

For BASE BX, `ChronicleSubtype` is not densely ordered, so this avenue is closed.

### The completeness theorem's exact signature (relevant)

```lean
theorem completeness [Denumerable (Formula Atom)] {φ : Formula Atom}
    (h_valid : ∀ (D : Type) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ) :
    Temporal.ThDerivable φ
```

The critical point: `completeness` requires validity on ALL types with serial linear order,
not just `ℚ`. To use it, we must establish `Satisfies M t φ` for ARBITRARY `D`.

---

## Confidence Level

**High confidence** on the following findings:
1. The sorry is precisely at `temporal_valid_of_bimodal_derivable`, lines 255-263.
2. The gap is the domain mismatch: `temporal_valid_on_addcommgroup` gives validity on
   `AddCommGroup` domains; `completeness` needs validity on all serial linear orders.
3. The semantic bridge and `temporal_valid_on_addcommgroup` are fully proven.
4. The Dense BX case CAN be closed using `Order.iso_of_countable_dense` on ChronicleSubtype.
5. The Base BX case cannot be closed the same way because ChronicleSubtype for base BX
   is not densely ordered.
6. Pushing along order-embeddings (not isomorphisms) does not preserve temporal satisfaction.
7. Pulling temporal-satisfaction along an order-isomorphism IS possible and provable by
   structural induction (`satisfies_orderIso`).

**Medium confidence** on:
- Whether a variant chronicle construction exists that yields densely ordered countermodels
  for base BX (possible by using density as a meta-theorem about BX, but not obvious).
- Whether the closure of `limitDom` under addition gives a valid countermodel.

**Low confidence** on:
- Whether a syntactic box-elimination approach (via `liftDerivationQfree`-style argument)
  can work without significant new infrastructure.
- Whether restricting BX completeness to `AddCommGroup` domains (i.e., proving a stronger
  form of BX completeness) is easier than the full proof.

---

## Summary for Implementer

The sorry in `temporal_valid_of_bimodal_derivable` blocks `bimodal_conservative_over_temporal`.
The mathematical gap is real: the bimodal TM soundness requires `AddCommGroup D`, but BX
completeness quantifies over all serial linear orders. The gap cannot be bridged by:
- Order embeddings (insufficient for satisfaction preservation)
- ChronicleSubtype inheriting AddCommGroup (false in general)

The gap CAN be bridged for the Dense BX case using `Order.iso_of_countable_dense` because
the Dense chronicle is densely ordered. For base BX, the most viable directions are:

1. **Prove `satisfies_orderIso`** (easy, ~30 lines) then separately prove
   **base BX completeness restricted to ℚ-models** (hard, requires new completeness argument).
2. **Replace base BX completeness** with an `AddCommGroup`-restricted version and show
   `Countable` + `Dense` subtypes of ℚ suffice (medium difficulty).
3. **Accept the sorry** with full documentation and mark `temporal_valid_of_bimodal_derivable`
   as [BLOCKED] pending a model-transfer lemma.

Option 3 is the current state of the code (with `set_option warn.sorry false`). The sorry
is localized and well-documented. The semantic bridge (Phase 1) and AddCommGroup validity
(Phase 2 partial) are complete.
