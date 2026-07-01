# Research Report — Task 445: Close the domain-mismatch `sorry` in TemporalConservativity

**File**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`
**Target**: `temporal_valid_of_bimodal_derivable` (line 261, `sorry` at line 269), with
`set_option warn.sorry false in` (line 248) to be removed.
**Downstream**: `bimodal_conservative_over_temporal` (line 289) depends on it.

## TL;DR (feasibility verdict)

The `sorry` cannot be closed by the transfer route literally described in the task
("transport a countermodel via an order-embedding into an ordered abelian group, preserving
`Satisfies`"). That route is **mathematically unsound as stated**: temporal `Satisfies` is
*not* preserved by order-*embeddings* (only by order-*isomorphisms*), and the open goal is
over an **arbitrary** serial linear order `D` (not countable, not dense, not homogeneous), which
is provably **not** order-isomorphic to any `AddCommGroup` order in general.

Closing the hole requires one of three substantial routes (Section 5). The most promising
bounded route (OrderIso-transfer + Löwenheim–Skolem to a countable submodel + Cantor) still has
an unresolved **non-dense** sub-case. A fully general, sorry-free proof appears to be
**research-level** and its very truth reduces to an open-in-this-repo completeness meta-theorem
(base BX complete w.r.t. `AddCommGroup` serial orders). This report supplies (a) the exact open
goal, (b) verified Mathlib candidate lemmas, (c) a correct + reusable `OrderIso` transport
lemma sketch (the "ambitious refactor" scaffolding), and (d) an escalation package per the
task's own escalation clause.

## 1. Exact current state and open goal

`lean_goal` at line 269 (verbatim):

```
Atom : Type u_1
inst✝⁵ : Infinite Atom
inst✝⁴ : DecidableEq Atom
φ  : Temporal.Formula Atom
h  : Bimodal.ThDerivable φ.toBimodal
D  : Type
inst✝³ : LinearOrder D
inst✝² : Nontrivial D
inst✝¹ : NoMaxOrder D
inst✝  : NoMinOrder D
M  : Temporal.TemporalModel D Atom
t  : D
⊢ Temporal.Satisfies M t φ
```

Key relevant declarations (all in the target file unless noted):

- `temporal_valid_on_addcommgroup` (line 202): for `[AddCommGroup D] [LinearOrder D]
  [IsOrderedAddMonoid D] [Nontrivial D]`, `Bimodal.ThDerivable φ.toBimodal → ∀ M t,
  Temporal.Satisfies M t φ`. **Proven, sorry-free.**
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies` (line 149): the semantic bridge,
  requires the same `AddCommGroup`/`IsOrderedAddMonoid`/`Nontrivial` instances. **Proven.**
- `temporalTaskFrame`/`temporalWorldHistory`/`temporalTaskModel` (lines 83–124): the bimodal
  countermodel construction. All require `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]`.

**Structural fact (the source of the mismatch):**
`Cslib/Logics/Bimodal/Semantics/TaskFrame.lean:51` declares
`structure TaskFrame (D : Type*) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]`.
`WorldHistory` (`WorldHistory.lean:52`) uses `t - s` in `respects_task`. So the *entire*
bimodal time/duration domain is intrinsically an ordered abelian group. There is no
"durations ≠ world-states" escape hatch: `taskRel : WorldState → D → WorldState → Prop` uses
the same `D`, and histories are indexed by `D`.

**Completeness demand (`Temporal.completeness`, `Metalogic/Completeness.lean:101`):** its
hypothesis quantifies over **all** `(D : Type) [LinearOrder D] [Nontrivial D] [NoMaxOrder D]
[NoMinOrder D]`. `bimodal_conservative_over_temporal` (line 289) discharges that hypothesis via
`temporal_valid_of_bimodal_derivable h D M t`, so the theorem genuinely must hold for arbitrary
serial `D`. `Temporal.ThDerivable` is `FrameClass.Base` (`Metalogic/DerivationTree.lean:102`).

## 2. Concrete demonstration of the gap (verified via `lean_multi_attempt`)

`temporal_valid_on_addcommgroup h (D := ℚ)` **type-checks** and produces
`∀ (M : TemporalModel ℚ Atom) (t : ℚ), Temporal.Satisfies M t φ` — i.e. φ is fully valid on ℚ
(a dense `AddCommGroup` serial order; ℚ has `AddCommGroup`, `IsOrderedAddMonoid`, `Nontrivial`).
`exact?` from there **cannot** close `Temporal.Satisfies M t φ` (M is over the abstract `D`), and
`exact temporal_valid_on_addcommgroup (D := ℚ) h M t` fails with a type mismatch
(`TemporalModel D Atom` vs `TemporalModel ℚ Atom`). So we have ℚ-validity in hand but no route
to arbitrary-`D` validity — the missing content is exactly a model transfer.

## 3. Why the described (order-embedding) transfer is unsound

The module's own "Domain Mismatch Resolution" prose (lines 214–246) already flags this, and it
is correct: pushing a temporal model along an order-*embedding* `e : D ↪ D'` does **not**
preserve `Satisfies`, because `untl`/`snce`/`allFuture`/`allPast` quantify over the *target*
domain, so new points of `D' \ e(D)` create spurious witnesses (for existentials) or break
guards/universals. Concretely, a "block/retraction" model (each `D`-point blown up to a convex
interval of constant valuation) fails `untl`: an interval after `e(t)` forces the guard `ψ` to
hold *at* `t`'s own value, which the open interval `(t,s)` in `D` does not require. Only when
`e` is an order-*isomorphism* (singleton fibers) does satisfaction transfer.

**Homogeneity obstruction.** Every `AddCommGroup` linear order is *homogeneous* (translation
`x ↦ x + (b-a)` is an order-automorphism sending `a ↦ b`). Many serial linear orders are **not**
homogeneous — e.g. the "doubled rationals" `ℚ ×ₗ {0,1}` (each `q` split into `q⁻ < q⁺`): it is
countable, serial (`NoMax`/`NoMin`), but `q⁻` has an immediate successor while other points do
not, so it is **not** order-isomorphic to any ordered abelian group. Hence there is no
order-iso transfer for arbitrary (or even arbitrary countable) serial `D`.

**Non-dense chronicle.** The base completeness countermodel lives on
`ChronicleSubtype = {x : ℚ // x ∈ limitDom …}` (`Chronicle/ChronicleToCountermodel.lean:53`):
countable, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`, but **not** proven `DenselyOrdered` (a
`DenselyOrdered` instance exists *only* for the Dense-MCS case, `DenseCompleteness.lean:229`
`chronicleDenselyOrderedDense`). So even after reducing to the chronicle, Cantor's theorem does
not apply.

## 4. Verified Mathlib candidate lemmas (fully-qualified, via `lean_leansearch`)

- `Order.iso_of_countable_dense` (`Mathlib.Order.CountableDenseLinearOrder`): for
  `[Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]` and likewise `β`,
  `Nonempty (α ≃o β)`. **Cantor's theorem.** Usable to get `S ≃o ℚ` **only when `S` is dense**.
- `Order.embedding_from_countable_to_dense` (same module): `[Countable α] [DenselyOrdered β]
  [Nontrivial β] → Nonempty (α ↪o β)`. An order *embedding* only — insufficient (Section 3).
- `Rat.castOrderEmbedding` (`Mathlib.Data.Rat.Cast.Order`): `ℚ ↪o K` into a linear ordered field.
- ℚ instances: ℚ is `AddCommGroup`, `IsOrderedAddMonoid`, `LinearOrder`, `Nontrivial`,
  `NoMaxOrder`, `NoMinOrder`, `DenselyOrdered`, `Countable` — verified indirectly by the fact
  that `temporal_valid_on_addcommgroup (D := ℚ)` elaborates.
- Model-theory (context, likely not directly usable): `FirstOrder.Language.dlo_isComplete`,
  `aleph0_categorical_dlo` (`Mathlib.ModelTheory.Order`) — DLO is complete/ℵ₀-categorical;
  confirms the dense case is well-behaved but says nothing about the non-dense case.

No existing `OrderIso`-based `Satisfies`-transfer lemma exists in the repo (grep of
`Cslib/Logics/Temporal` + `Cslib/Logics/Bimodal` for `OrderIso`/`≃o` returns only this file and
an unrelated chronicle-basic file). One must be written.

## 5. Candidate proof routes and feasibility

### Route A — OrderIso transport + Löwenheim–Skolem + case-split on density
1. Prove a reusable lemma `satisfies_orderIso` (correct; ~40–70 lines): given `e : D ≃o D'` and
   `M : TemporalModel D Atom`, with `M' := ⟨fun x p => M.valuation (e.symm x) p⟩`, then
   `∀ φ t, Satisfies M' (e t) φ ↔ Satisfies M t φ` (induction on φ; `e`/`e.symm` are strict-mono
   bijections so witnesses/guards correspond exactly). This is the "ambitious refactor"
   scaffolding and is genuinely reusable.
2. Prove a temporal Löwenheim–Skolem: from `¬ Satisfies M t φ` on arbitrary serial `D`, extract a
   **countable** serial suborder `S ⊆ D` (Skolem hull closed under the finitely many
   subformulas' existential witnesses + universal counter-witnesses, plus cofinal/coinitial
   sequences to keep `NoMax`/`NoMin`) with `¬ Satisfies (M|S) t φ`. **~150–300 lines, delicate.**
3. If `S` is dense: `Order.iso_of_countable_dense` gives `S ≃o ℚ`; transport (step 1) to a
   ℚ-countermodel, contradicting `temporal_valid_on_addcommgroup (D := ℚ)`.
4. **Unresolved:** if `S` is *not* dense (e.g. doubled-rationals), there is no known
   order-iso to an `AddCommGroup` order (Section 3 homogeneity). **This sub-case is the residual
   obstruction; Route A does not close it.**

Feasibility: **partial / blocked** on the non-dense sub-case. Do not attempt as a "plug".

### Route B — Base BX complete w.r.t. `AddCommGroup` serial orders (meta-theorem)
Prove directly: every base-BX countermodel is realizable on some `AddCommGroup` serial order
(equivalently, the tense logic of ordered abelian groups = base BX). This is the honest content
needed. It is **not** reducible to order-iso of the existing chronicle and appears to be
**research-level**; there is even genuine uncertainty whether it is *true* as stated (if false,
TM would be non-conservative over base BX at this semantics and the `sorry` would be
unclosable). Feasibility: **research-level / uncertain.**

### Route C — Syntactic (proof-theoretic) conservativity
Bypass semantics: prove `TM ⊢ φ.toBimodal → BX ⊢ φ` by induction on the TM derivation.
`toBimodal` is purely structural over the temporal fragment and introduces **no** bimodal `box`
(`Embedding/TemporalEmbedding.lean:35–41`), but a TM derivation of a box-free endpoint may still
route through box-bearing intermediate formulas, so back-translation is not structural. The
repo's `Metalogic/Separation.lean` may hold relevant box-separation machinery. Feasibility:
**large, self-contained, uncertain** — but it is the one route that never touches the domain
mismatch.

## 6. Recommendation

1. **Land the reusable `satisfies_orderIso` transport lemma** (Route A step 1) regardless — it is
   correct, sorry-free, and demanded by the "factor out satisfaction-transport as a named,
   docstringed lemma" refactor goal. Place it near `Temporal.Satisfies` (Semantics/Satisfies.lean)
   or in a new `Semantics/Transfer.lean`.
2. **Do NOT** implement the order-*embedding* transfer or any block/retraction model — it is
   unsound and would only produce a proof that does not typecheck or a disguised gap.
3. Given the residual non-dense obstruction (Route A step 4) and the research-level status of
   Routes B/C, this qualifies as a **genuinely load-bearing mathematical obstruction** under the
   task's escalation clause. Recommended action for the implementer: attempt Routes A(1–3) + a
   focused push on the non-dense case; if the non-dense case resists, **escalate to the user**
   with the exact open goal (Section 1), the candidate lemmas (Section 4), and the three-route
   assessment — **without** reintroducing a `sorry` or any vacuous placeholder. Marking the
   implementation task `[BLOCKED]` pending user decision (accept Dense-only restructure? pursue
   Route C? treat as research?) is the zero-debt-compliant outcome if no full proof is found.
4. Zero-debt / lint notes for whatever lands: new lemmas need docstrings (docBlame), use
   `theorem`/`lemma` for Props (defLemma), lowerCamelCase names (defsWithUnderscore), keep section
   variables minimal (`omit` unused), and remove `set_option warn.sorry false in` (line 248) only
   once line 269 is genuinely proof-complete.

## 7. Reusable transport lemma sketch (correct; verify during implementation)

```lean
/-- Temporal satisfaction transports along an order isomorphism of time domains. -/
theorem Satisfies.orderIso {D D' : Type*} [LinearOrder D] [LinearOrder D'] {Atom : Type*}
    (e : D ≃o D') (M : TemporalModel D Atom) (t : D) (φ : Formula Atom) :
    Satisfies (⟨fun x p => M.valuation (e.symm x) p⟩ : TemporalModel D' Atom) (e t) φ
      ↔ Satisfies M t φ := by
  induction φ generalizing t with
  | atom p => simp [Satisfies]        -- e.symm (e t) = t
  | bot => simp [Satisfies]
  | imp φ ψ ihφ ihψ => simp only [Satisfies]; rw [ihφ, ihψ]
  | untl ψ φ ihψ ihφ =>
    -- ∃ s' > e t … ↔ ∃ s > t …  via s' = e s, using e strict-mono bijection
    -- and (e r) ranges over (e t, e s) exactly as r ranges over (t, s)
    sorry -- fill with e.lt_iff_lt, e.symm_apply_apply, e.surjective
  | snce ψ φ ihψ ihφ => sorry
  | allFuture φ ih => sorry  -- ∀ s' > e t ↔ ∀ s > t
  | allPast φ ih => sorry
```
(The `sorry`s above are illustrative placeholders **for the implementer's scratch only** — the
final landed lemma must be fully closed; `e.lt_iff_lt`, `e.symm_apply_apply`,
`e.apply_symm_apply`, `EquivLike.surjective` are the load-bearing facts.)
