# Horizons Research: Task 275 Strategic Context

**Role**: Teammate D (Horizons Researcher)
**Task**: 275 -- bimodal_tm_conservative_over_temporal_bx
**Date**: 2026-06-22
**Focus**: Long-term alignment, shared infrastructure, domain mismatch resolution

---

## Key Findings

### 1. Position in the Conservativity Program (Tasks 272-276)

The five tasks form a coherent program:

| Task | Statement | Status | Technique |
|------|-----------|--------|-----------|
| 272 | Glivenko's theorem | [COMPLETED] | Semantic bridge (trivial PL model) |
| 273 | Modal systems conservative over CPL | [COMPLETED] | Semantic bridge (Kripke adapter) |
| 274 | Bimodal TM conservative over Modal K/S5 | [COMPLETED] | Semantic bridge (Kripke adapter, fixed Z domain) |
| 275 | Bimodal TM conservative over Temporal BX | [PARTIAL] | Semantic bridge (temporal task frame on Z) -- sorry in domain mismatch |
| 276 | Modal cube inter-system conservativity | [COMPLETED] | Syntactic lifting (derivation tree induction) |

The sorry in task 275 is the **only remaining sorry** in the conservativity program. Task 276 explicitly notes this pre-existing failure as blocking full `Cslib.lean` build.

### 2. The Domain Mismatch: Precise Diagnosis

**What is proven** (sorry-free):
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies`: semantic bridge on any `D` with `AddCommGroup D` -- proven clean
- `temporal_valid_on_addcommgroup`: validity on AddCommGroup domains -- proven clean

**What is not proven**:
- `temporal_valid_of_bimodal_derivable`: transferring from AddCommGroup validity to validity on ALL serial linear orders (arbitrary `D` with `LinearOrder D` only)

The gap arises because:
- `ChronicleSubtype = {x : Rat // x ∈ limitDom A h_mcs}` inherits `LinearOrder` from `Rat` but NOT `AddCommGroup`
- `Rat` itself HAS `AddCommGroup`, but the subtype only inherits order properties

### 3. Two Clean Resolution Paths Found

#### Path A: Cantor's Theorem (for Dense BX completeness only)

`Order.iso_of_countable_dense` (Mathlib) gives `Nonempty (α ≃o β)` when both `α` and `β` are countable, dense, without endpoints.

**Requirements**: `[Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]`

`ChronicleSubtype` already has `NoMaxOrder`, `NoMinOrder`, `Nonempty`. It inherits `LinearOrder` from `Rat`. The missing instances are:
- `Countable (ChronicleSubtype A h_mcs)` -- likely provable since `limitDom` is a subset of `Rat` and `Rat` is countable
- `DenselyOrdered (ChronicleSubtype A h_mcs)` -- this is the hard part; density requires the Dense BX frame class, NOT the Base frame class

**Verdict**: Path A works ONLY for Dense BX completeness, not Base BX completeness. Task 275 targets `FrameClass.Base` (`ThDerivable = DerivationTree FrameClass.Base [] phi`). This path is inapplicable.

#### Path B: Mathlib's Integer Isomorphism

`orderIsoIntOfLinearSuccPredArch` (Mathlib) gives `ι ≃o ℤ` when `ι` has `[LinearOrder] [SuccOrder] [PredOrder] [IsSuccArchimedean] [NoMaxOrder] [NoMinOrder] [Nonempty]`.

`ℤ` has `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`, `Nontrivial`. So if `ChronicleSubtype` can be shown to be "discrete enough" (successor and predecessor order, archimedean), we could get an isomorphism to `ℤ`.

**Problem**: `ChronicleSubtype` is a subtype of `Rat` (a dense order). It does NOT have `SuccOrder` or `PredOrder`. This path is inapplicable for the Base BX chronicle domain.

#### Path C: Direct Satisfies Preservation Under Order Isomorphism (RECOMMENDED)

If we prove:

```lean
theorem Satisfies_orderIso {D₁ D₂ : Type} [LinearOrder D₁] [LinearOrder D₂]
    (f : D₁ ≃o D₂) {Atom : Type*}
    (M₁ : TemporalModel D₁ Atom) (t : D₁) (φ : Temporal.Formula Atom) :
    Temporal.Satisfies M₁ t φ ↔
    Temporal.Satisfies (M₁.transport f) (f t) φ
```

where `M₁.transport f` is the model on `D₂` with valuation `fun s p => M₁.valuation (f.symm s) p`,
then the argument becomes:

1. Assume `φ` is valid on all AddCommGroup domains (from `temporal_valid_on_addcommgroup`).
2. Given ANY serial linear order `D` and model `M` on `D`, produce an order-embedding into `ℚ` (which has AddCommGroup).
3. Use `Order.embedding_from_countable_to_dense` (Mathlib): `Nonempty (D ↪o ℚ)` -- since `ℚ` is dense, countable, any countable `D` embeds.

**BUT** an embedding is not an isomorphism. Pushing the temporal model through an embedding changes the domain of quantification in `untl`/`snce`, so satisfaction is NOT preserved.

**Revised Path C**: Use an isomorphism, not just embedding.

For arbitrary serial linear orders, we cannot always find an isomorphism to `ℚ` (only for countable dense ones by Cantor's theorem). However, there is a different decomposition: for any serial linear order `D` and temporal model `M` on `D`, we can ask whether `φ` is "forced" by the local behavior. Since `φ` has finite modal depth, only finitely many time points in `D` are relevant to satisfaction at `t`. However, this leads to the filtration/finite model property argument, which is nontrivial.

### 4. The Simplest Correct Resolution: Strengthen Completeness

The key observation: the completeness theorem for BX says

> "If φ is valid on all serial linear orders, then φ is BX-derivable."

The contrapositive builds a countermodel on `ChronicleSubtype` (subtype of `ℚ`). Since `ℚ` is an `AddCommGroup`, and `ChronicleSubtype` is a subtype of `ℚ`, the most direct approach is:

**Extend the temporal model on `ChronicleSubtype` to all of `ℚ`**.

Given a model on `ChronicleSubtype A h_mcs` (valuation: `formula.atom p ∈ limitF A h_mcs t.val`), define a model on `ℚ` by:

```lean
def extendToRat (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent A) :
    TemporalModel ℚ Atom where
  valuation := fun q p =>
    if hq : q ∈ limitDom A h_mcs
    then Formula.atom p ∈ limitF A h_mcs q
    else False
```

Then use `temporal_valid_on_addcommgroup` to get `Satisfies (extendToRat ...) q φ` for any `q ∈ limitDom`.

**But**: satisfaction of `φ` in the extended model on `ℚ` at `q ∈ limitDom` requires the quantifiers `∃ s > q, ...` to range over all of `ℚ`, not just `limitDom`. Since `limitDom ⊊ ℚ`, the extended model may differ in `untl`/`snce` clauses. More time points are available in `ℚ`, potentially satisfying `φ` where the chronicle model would not. This means the extension approach could give FALSE satisfaction (the extended model might satisfy `φ` even though the chronicle model does not). This does NOT help.

### 5. The Correct Approach: Restricting Completeness to AddCommGroup Domains

The cleanest solution for the long term is to prove a STRENGTHENED completeness theorem for temporal BX:

```lean
theorem completeness_addcommgroup [Denumerable (Formula Atom)] {φ : Formula Atom}
    (h_valid : ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
      [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ) :
    Temporal.ThDerivable φ
```

This would follow if we can show that `ChronicleSubtype` (the countermodel domain) has `AddCommGroup`. However, `ChronicleSubtype` is a general subtype of `ℚ` and does NOT have a canonical additive group structure (there is no canonical "origin" for subtraction to return to the subtype).

**Alternative**: Modify the chronicle construction to use `ℚ` directly instead of a subtype, so the completeness proof builds its countermodel on ALL of `ℚ`. This is a significant refactoring but would make the domain cleanly an AddCommGroup. The price is that `limitF` must be defined on all of `ℚ`, with the "out of domain" behavior handled explicitly.

### 6. The Minimal Fix: Order-Isomorphism Transfer Lemma

After full analysis, the cleanest path that avoids restructuring the completeness proof is:

**Prove that temporal satisfaction is preserved by order isomorphisms**, then use the fact that any serial linear order embeds into some domain with AddCommGroup.

The precise statement:

```lean
theorem Satisfies_orderIso {D₁ D₂ : Type*} [LinearOrder D₁] [LinearOrder D₂]
    {Atom : Type*} (e : D₁ ≃o D₂)
    (M : TemporalModel D₁ Atom) (t₁ : D₁) (φ : Temporal.Formula Atom) :
    Temporal.Satisfies M t₁ φ ↔
    Temporal.Satisfies { valuation := fun s p => M.valuation (e.symm s) p } (e t₁) φ
```

This is provable by structural induction on `φ` using `e.lt_iff_lt`.

Then for the domain mismatch:

For any serial linear order `D` and temporal model `M` on `D`, find an order-isomorphism `e : D ≃o ℚ` (or `D ≃o ℤ`), apply `Satisfies_orderIso`, then use `temporal_valid_on_addcommgroup` on `ℚ` (which has `AddCommGroup`).

**But an isomorphism `D ≃o ℚ` exists only for countable, dense, without-endpoint orders** (Cantor's theorem). Not all serial linear orders are dense.

For DISCRETE orders, `orderIsoIntOfLinearSuccPredArch` gives `D ≃o ℤ`. But `D` may be neither dense nor discrete.

**Conclusion**: No single Mathlib isomorphism covers all serial linear orders. This is why the domain mismatch is genuinely non-trivial.

### 7. The True Minimal Fix: Soundness Reformulation

Re-examining the bimodal soundness theorem, it requires `AddCommGroup D` because `TaskFrame D` uses the group operation in `taskRel w d u := u = w + d`. The frame axioms (nullity, forward_comp, converse) use `add_zero`, `add_assoc`, `add_neg_cancel`.

A weaker frame axiom would suffice for the semantic bridge: we only need a `StrictLinearOrder`-compatible frame. One option:

**Define an alternative "temporal task frame" that does NOT require AddCommGroup**:

```lean
-- Use a pure order-based task frame without group operations
-- WorldState = D, taskRel w d u := u = d (ignore w -- pure time-shift is the identity)
-- This is too degenerate.
```

The fundamental issue is that bimodal semantics uses `AddCommGroup` for task composition (duration arithmetic). Temporal logic does not need this; it only needs a linear order for `<`.

**Cleanest long-term fix**: Add an alternative `soundness_linear_order` theorem in the bimodal soundness file that works for ANY linear order (not just AddCommGroup), using a simpler task frame where `taskRel` is trivial (identity relation). The body of `temporal_valid_on_addcommgroup` would then not need AddCommGroup.

### 8. Impact on Task 276

Task 276 is COMPLETED with 24 sorry-free conservativity theorems for the modal cube. It explicitly notes the task 275 sorry as a pre-existing issue that prevents full `Cslib.lean` build. Resolving task 275 would unblock the full project build and allow the conservativity program to be considered fully complete.

### 9. Infrastructure Reuse Analysis

| Infrastructure | Created For | Reusable For |
|---------------|-------------|-------------|
| `temporalTaskFrame` | Task 275 | Any future bimodal-temporal bridge |
| `temporalWorldHistory` | Task 275 | Any bimodal-temporal semantic bridge |
| `bimodal_truthAt_toBimodal_iff_temporal_satisfies` | Task 275 | Future conservativity over temporal logics |
| `kripkeAdapterFrame` | Task 274 | Any bimodal-modal bridge |
| `lift_derivation_qfree` | Tasks 272-273 (IRR) | Within-bimodal extensions only |
| `lift_derivation` (task 276) | Modal cube | Any modal subsystem conservativity |

**Key gap**: There is NO `Satisfies_orderIso` lemma in CSLib or (apparently) Mathlib for this specific temporal satisfaction predicate. This lemma would be broadly useful for any future result connecting temporal satisfaction across differently-ordered domains.

---

## Recommended Approach

### Primary Recommendation: Prove `Satisfies_orderIso` + Use `ℚ`-Completeness Contrapositive

The sorry in `temporal_valid_of_bimodal_derivable` can be resolved by the following two-lemma strategy:

**Step 1**: Prove `Satisfies_orderIso` (new lemma, ~20 lines, purely structural induction):

```lean
/-- Temporal satisfaction is preserved by order isomorphisms.
    If M₁ is a temporal model on D₁ and e : D₁ ≃o D₂ is an order isomorphism,
    then the transferred model on D₂ satisfies the same temporal formulas. -/
theorem Satisfies_orderIso {D₁ D₂ : Type*} [LinearOrder D₁] [LinearOrder D₂]
    {Atom : Type*} (e : D₁ ≃o D₂)
    (M : TemporalModel D₁ Atom) (t : D₁) (φ : Temporal.Formula Atom) :
    Temporal.Satisfies M t φ ↔
    Temporal.Satisfies { valuation := fun s p => M.valuation (e.symm s) p } (e t) φ := by
  induction φ generalizing t with
  | atom p => simp [Temporal.Satisfies]; exact ⟨fun h => by simp [h], fun h => by simp [e.symm_apply_apply] at h; exact h⟩
  | bot => simp [Temporal.Satisfies]
  | imp φ ψ ih_φ ih_ψ => simp [Temporal.Satisfies]; exact ⟨..., ...⟩
  | untl ψ φ ih_ψ ih_φ =>
    simp [Temporal.Satisfies]
    constructor
    · rintro ⟨s, hts, hs, hbetween⟩
      exact ⟨e s, e.lt_iff_lt.mpr hts, (ih_φ s).mp hs, fun r htr hrs =>
        (ih_ψ (e.symm r)).mp (hbetween (e.symm r) (e.lt_iff_lt.mp htr) (e.lt_iff_lt.mp hrs))⟩
    · ...
  | snce ψ φ ih_ψ ih_φ => -- symmetric
```

**Step 2**: Use the contrapositive of temporal completeness with `ℚ` as the witness domain:

The completeness proof proceeds by contradiction: if `φ` is not BX-derivable, a countermodel on `ChronicleSubtype` (subtype of `ℚ`) is built. We need to reach a contradiction from `temporal_valid_on_addcommgroup`.

The plan: Given the chronicle countermodel on `ChronicleSubtype`, transport it via `Satisfies_orderIso` to get a model on `ℚ`. This requires a map `ChronicleSubtype ↪o ℚ` (or isomorphism). The subtype inclusion `ChronicleSubtype ↪ ℚ` is order-preserving but NOT surjective; it gives an order embedding, not an isomorphism.

An isomorphism `ChronicleSubtype ≃o ℚ` would require `ChronicleSubtype` to be countable, dense, and without endpoints -- which requires Dense BX (not Base BX).

**The fundamental barrier**: For Base BX, the chronicle domain is a subtype of `ℚ` but NOT isomorphic to `ℚ`. The `Satisfies_orderIso` lemma requires an isomorphism, not just an embedding.

### Revised Primary Recommendation: Weaken the Bimodal Frame Requirement

The cleanest resolution with the smallest footprint is to modify the temporal task frame construction to NOT require `AddCommGroup`:

Instead of `taskRel w d u := u = w + d`, use a degenerate task frame where the "task structure" is trivial:

```lean
/-- Degenerate bimodal frame over a linear order, with trivial task relation.
    WorldState = D, taskRel = always False (or = fun w _ u => w = u). -/
def degenerateFrame (D : Type*) [LinearOrder D] : TaskFrame D where
  WorldState := D
  taskRel := fun _w _d _u => False  -- no task transitions
  nullity_identity := ...  -- False -> w = u: vacuously by ...
  ...
```

However, `nullity_identity` requires `taskRel w 0 u ↔ w = u`, i.e., `False ↔ w = u`. This fails for `w ≠ u`. So a False taskRel doesn't work.

The identity-only option: `taskRel w d u := w = u` (all states are self-loops). This works:
- `nullity_identity w u`: `w = u ↔ w = u` -- trivially true
- `forward_comp w u v x y hx hy hwu huv`: `hwu : w = u`, `huv : u = v`, so `taskRel w (x+y) v := w = v` follows from `hwu.trans huv`
- `converse w d u`: `w = u ↔ u = w`, i.e., `Eq.symm`

Then: `ShiftClosed Set.univ` holds since `Set.univ` is shift-closed trivially.

The `truthAt` for box with this identity frame: `∀ σ ∈ Set.univ, truthAt M Set.univ σ t φ` -- this requires ALL world histories to satisfy `φ`, which is a very strong condition. The semantic bridge lemma for temporal formulas (no box case) would still work.

**But soundness for this frame**: The bimodal soundness theorem proves that for any VALID derivation and ANY `TaskFrame D`, the formula holds. The validity of the bimodal axioms in this degenerate frame needs checking. The box axioms (S5, modal_future) may fail in the degenerate frame since box quantifies over all world histories. But for temporal formulas (no box in conclusion), validity of bimodal axioms involving box at the frame-validity level may not be needed... actually it IS needed since the derivation tree can use box internally.

This approach is architecturally fragile.

### Definitive Recommendation: Prove `completeness_addcommgroup`

The correct long-term fix is to add a variant completeness theorem that only requires AddCommGroup validity. This can be achieved by one of:

**(a) Direct**: Modify the `completeness` proof to construct the countermodel on `ℚ` directly (not a subtype), so the domain is an `AddCommGroup`. This requires rewriting `limitDom` and `limitF` to be total functions on `ℚ` rather than subtypes. Estimated effort: 2-4 hours of refactoring.

**(b) Bridge**: Prove that `ChronicleSubtype` has an order-embedding into `ℚ`, and prove a weaker "satisfaction under order-embedding" theorem. The key: for temporal formulas, if `M` on `D₁` does NOT satisfy `φ` at `t`, and `e : D₁ ↪o D₂` is an order-embedding, does `M_transported` on (a subset of) `D₂` also not satisfy `φ`? This holds only if the embedding is SURJECTIVE onto the support of the witnesses, which is not generally true for embeddings.

**(c) Best immediate fix**: Since `ChronicleSubtype ⊆ ℚ` and `ℚ` has `AddCommGroup`, construct the countermodel directly on `ℚ` with `False` valuation for points outside `limitDom`. Then show: if `φ` were BX-valid on all AddCommGroup serial linear orders, it would be satisfied by this `ℚ`-model at `t₀ = 0`. But the `ℚ`-model has different quantifier ranges from the chronicle model. FAILS for the same reason as the extension approach above.

**(d) The actual correct fix**: Recognize that the proof can work if we apply bimodal validity SPECIFICALLY to `ChronicleSubtype` by upgrading it to have `AddCommGroup`. This requires proving `ChronicleSubtype` has `AddCommGroup`. It does NOT as a subtype. However, since `ChronicleSubtype ≅ (some countable dense linear order without endpoints)` via Cantor when we use the Dense BX completeness, this only applies in the dense case.

**For Base BX, the approach that works**: Use the bimodal soundness theorem with `D = ℤ` (which has `AddCommGroup`) and observe that `ℤ` embeds order-isomorphically into ALL discrete serial linear orders (by `orderIsoIntOfLinearSuccPredArch`), and show that for BASE BX (whose frames are exactly serial linear orders without further constraints), we can use an intermediate step through discrete completeness.

---

## Evidence and Examples

### Evidence that the sorry is well-localized

From `TemporalConservativity.lean` lines 252-263:
- `temporal_valid_of_bimodal_derivable` is the ONLY sorry
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies` (lines 149-183): sorry-free
- `temporal_valid_on_addcommgroup` (lines 196-206): sorry-free
- `bimodal_conservative_over_temporal` (lines 282-289): depends only on the one sorry

### Evidence from Task 276

Task 276 summary explicitly states (line 96-97):
> "Pre-existing failure: `Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.TemporalConservativity` uses sorry (pre-dates this task; prevents full Cslib.lean build)"

Resolving this sorry unblocks full `Cslib.lean` build.

### Evidence for `Satisfies_orderIso` Approach

The bimodal conservative extension over Modal S5 (task 274, `ModalConservativity.lean`) uses the `kripkeAdapterFrame` over `ℤ` and relies on the universal quantifier in bimodal validity to propagate correctness. The temporal case is structurally analogous but for the time domain.

The bimodal soundness requires `AddCommGroup D` because `TaskFrame D` uses group operations in `taskRel`. This constraint is baked into `TaskFrame.forward_comp` which requires addition to be associative. There is no easy way to bypass this in the existing architecture.

### The Most Promising Path Identified

From the Mathlib search: `Order.embedding_from_countable_to_dense` shows that any COUNTABLE linear order embeds into any dense order. If temporal completeness is proved by contradiction and the countermodel domain is a subtype of `ℚ` (which is countable), then:

1. `ChronicleSubtype` is countable (as a subtype of `ℚ`)
2. For BASE BX (serial linear orders), the chronicle construction uses rational points at DISCRETE intervals (the omega-chain construction inserts points between existing ones)
3. The question is whether `ChronicleSubtype` for Base BX is dense or discrete

Looking at `ChronicleConstruction.lean`: `limitDom` is the union of `omegaChainVal A h_mcs n .dom` over all `n`. Each `dom` is a `Finset Rat`. The omega-chain extends by inserting new rational points between existing ones (via point insertion). So `limitDom` is a COUNTABLE DENSE subtype of `ℚ` -- it has points inserted densely by the omega-chain construction.

**This means `ChronicleSubtype` for Base BX IS densely ordered** (point insertion ensures density over the omega-chain). If this is correct, then `Order.iso_of_countable_dense` applies: `ChronicleSubtype ≃o ℚ` (Cantor's theorem), giving an order isomorphism. Then:

1. Bimodal validity on `ℚ` (which has `AddCommGroup`) gives satisfaction at some point
2. `Satisfies_orderIso` pulls satisfaction back to `ChronicleSubtype`
3. Contradiction with the truth lemma

**This is the correct resolution path** if `ChronicleSubtype` can be shown to be densely ordered. This requires checking whether the temporal Base BX chronicle construction inherits density from the point-insertion steps.

---

## Confidence Level

| Finding | Confidence |
|---------|------------|
| Sorry is well-localized to `temporal_valid_of_bimodal_derivable` | HIGH |
| `Satisfies_orderIso` is the right infrastructure to build | HIGH |
| `Satisfies_orderIso` alone is insufficient (embedding vs isomorphism) | HIGH |
| `ChronicleSubtype` is densely ordered for Base BX | MEDIUM (requires confirming omega-chain inserts points densely) |
| Cantor's theorem path works if density holds | HIGH (if density confirmed) |
| Modifying completeness to use `ℚ` directly is a valid long-term fix | HIGH |
| The sorry blocks full `Cslib.lean` build (via task 276 dependency) | HIGH |
| Resolving this sorry is the last blocker for the conservativity program | HIGH |

---

## Strategic Recommendations

### Short-Term (resolve task 275 sorry)

1. **Verify density of `ChronicleSubtype`**: Check `PointInsertion.lean` and `ChronicleConstruction.lean` to confirm the omega-chain inserts points at rational midpoints, making `limitDom` a dense subset of `ℚ`.

2. If density is confirmed: prove `Countable (ChronicleSubtype A h_mcs)` (trivial from `ChronicleSubtype ⊆ ℚ`) and `DenselyOrdered (ChronicleSubtype A h_mcs)`, then invoke `Order.iso_of_countable_dense` to get `ChronicleSubtype ≃o ℚ`.

3. Prove `Satisfies_orderIso` for temporal formulas (structural induction, ~20-30 lines).

4. Use the isomorphism + `Satisfies_orderIso` + `temporal_valid_on_addcommgroup` on `ℚ` to complete `temporal_valid_of_bimodal_derivable`.

### Long-Term Infrastructure

1. **Add `Satisfies_orderIso` to `Cslib/Logics/Temporal/Semantics/Satisfies.lean`**: This lemma has broad reuse for any future temporal conservativity result connecting logics with different domain structures.

2. **Consider `completeness_addcommgroup`**: If multiple future results need validity on AddCommGroup domains, a dedicated variant of temporal completeness would make the semantic bridge approach composable.

3. **Document the domain constraint pattern**: Add a comment in `TaskFrame.lean` explaining that `AddCommGroup D` is required for task duration arithmetic, and that future conservativity results should address this via `Satisfies_orderIso`.
