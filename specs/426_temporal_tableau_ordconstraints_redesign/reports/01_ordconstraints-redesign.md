# Research Report — Task 426: Temporal Tableau Time-Ordering Redesign

**Task**: Redesign the time-ordering scheme in the temporal tableau so the ordering
invariants hold, then prove the corrected `ordConstraints` lemma sorry-free.
**Decomposed from**: task 301, blocker A. **Independent of**: tasks 424, 425.
**Green base commit**: `7f052834` (verified present).
**Date**: 2026-06-30

---

## 1. The Bug: `ordConstraints_strict` Is False As Stated

### 1.1 Current (commented-out) claim

`Cslib/Logics/Temporal/Tableau/Completeness.lean` lines 254–262:

```lean
-- BLOCKED (design issue): ordConstraints_strict is false for branches using addPast.
-- The addPast rule adds (tNew, t) where tNew = branchNextTime b > t.
-- This makes (tNew, t) ∈ constraints but tNew > t, violating the claimed invariant.
--
-- lemma ordConstraints_strict (φ : Formula Atom) (b : TBranch Atom) (ord : TimeOrdering)
--     (hresult : temporalTableau φ = .openBranch b ord) :
--     ∀ t t', (t, t') ∈ ord.constraints → t < t' := ...
```

The lemma asserts `(t, t') ∈ ord.constraints → t < t'`, i.e. that the *constraint pair's
Nat ordering coincides with the semantic "before" relation*.

### 1.2 The constraint-adding functions

`Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` lines 50–73:

```lean
structure TimeOrdering where
  /-- Each entry `(a, b)` represents the constraint `a < b`. -/
  constraints : List (Nat × Nat)

def addFuture (ord : TimeOrdering) (t tNew : Nat) : TimeOrdering :=
  ⟨(t, tNew) :: ord.constraints⟩          -- records  t  <  tNew  (semantic)

def addPast (ord : TimeOrdering) (t tNew : Nat) : TimeOrdering :=
  ⟨(tNew, t) :: ord.constraints⟩          -- records  tNew < t    (semantic)
```

### 1.3 Where `tNew` comes from

`Cslib/Logics/Temporal/Tableau/Rules.lean`:

```lean
def branchNextTime (b : TBranch Atom) : TimeIndex := branchMaxTime b + 1

lemma branchNextTime_gt (b) (sf) (hmem : sf ∈ b) : sf.label < branchNextTime b := ...
```

Every existential rule sets `t' := branchNextTime b`, a **fresh Nat strictly greater than
every label already on the branch** (Rules.lean lines 249, 258, 267, 277, 313, 339). In
particular `t' > t` numerically, *always*.

### 1.4 Why the invariant is violated — confirmed

- **`addFuture t t'`** pushes `(t, t')`. Semantic: `t < t'`. Numeric: `t < t'` (fresh). ✓ consistent.
- **`addPast t t'`** pushes `(t', t)`. Semantic: `t' < t`. Numeric: `t' > t` (fresh, `branchNextTime_gt`). ✗

So for any branch that fires a `somePast` / `snce` / `snceNeg` rule (Rules.lean 258, 278, 340),
the store contains a pair `(t', t)` with `t' > t`. The universally-quantified claim
`∀ (a,b) ∈ constraints, a < b` therefore has an explicit counterexample. The lemma is **false**,
not merely hard. Confirmed exactly as documented at Completeness.lean lines 234–246.

---

## 2. The Real Requirement (downstream consumer analysis)

`ordConstraints_strict` is **not the lemma the completeness proof actually needs.** The genuine
obligation comes from `branchSat` in `Cslib/Logics/Temporal/Tableau/Soundness.lean` lines 79–87:

```lean
def branchSat (b : TBranch Atom) (ord : TimeOrdering) : Prop :=
  ∃ (D : Type) (_ : LinearOrder D) (_ : Nontrivial D) (M : TemporalModel D Atom)
    (f : TimeIndex → D),
    (∀ t t', (t, t') ∈ ord.constraints → f t < f t') ∧        -- ← order-preservation
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies M (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies M (f sf.label) sf.formula)
```

**Key observation:** `branchSat` existentially quantifies over the time domain `D` *and* the
assignment `f : TimeIndex → D`. It does **not** require `f = id` or `D = Nat`. The only thing
needed is **some** order-preserving `f`:

> `∀ t t', (t, t') ∈ ord.constraints → f t < f t'`.

The blocked `openBranch_branchSat` sketch (Completeness.lean 329–339) hard-codes
`D = Nat, f = id`, which is exactly why it needs the false `ordConstraints_strict`. The fix is to
**drop the `f = id` choice** and supply a genuine order-preserving assignment.

### Downstream consumers the redesign must keep satisfying

| Consumer | Location | What it needs from the ordering |
|---|---|---|
| `branchSat` | Soundness.lean 79–87 | existence of order-preserving `f : TimeIndex → D`, `D` a nontrivial `LinearOrder` |
| `openBranch_branchSat` (blocked) | Completeness.lean 329–339 | provide `⟨D, _, _, extractModel b, f, hf, …⟩` with `hf` the order-preservation proof |
| `extractModel` | Completeness.lean 102–105 | valuation currently keyed on Nat label `t` directly; if `D ≠ Nat`, valuation must be re-keyed through `f` (see §5 caveat) |
| `extractModel_atom_sat_iff` etc. | Completeness.lean 110–127 | unaffected by ordering choice (purely about `valuation`) |
| `temporalTableau` result | Saturation.lean 68, 241 | `openBranch : TBranch → TimeOrdering → Result`; any change to `TimeOrdering` reverberates through Saturation.lean threading (lines 143, 183, 192, 216, 261) |

The `classicallyClosed_unsat` / soundness direction (Soundness.lean 97+) destructures `branchSat`
and never inspects `constraints` content, so it is **insensitive** to the redesign.

---

## 3. Redesign Options (with Lean-feasibility)

The invariant that *actually holds* is **not** "`a < b` numerically" but rather:

> **The constraint graph admits an order-preserving embedding into a linear order.**

Equivalently the constraint relation is *acyclic*. This is true because of the **forest
structure** of constraint creation: every `addFuture`/`addPast` introduces exactly **one** new
edge incident to the **fresh** vertex `tNew` (which never appeared before, being
`> branchMaxTime`). Each fresh vertex therefore attaches to the existing graph by a single edge
⇒ the underlying undirected graph is a forest ⇒ the directed constraint graph is a DAG.

Three concrete ways to exploit this:

### Option A — Acyclicity + Mathlib linear extension (Szpilrajn)

Prove the reflexive-transitive closure of `constraints` is a partial order (antisymmetric =
acyclic), then invoke Mathlib's order-extension principle.

Grounded Mathlib API (verified via loogle, module `Mathlib.Order.Extension.Linear`):

```
LinearExtension (α : Type u) : Type u
instLinearOrderLinearExtensionOfPartialOrder : [PartialOrder α] → LinearOrder (LinearExtension α)
toLinearExtension : [PartialOrder α] → α →o LinearExtension α     -- monotone embedding
```

- **Feasibility**: medium-high effort. Requires (1) building a `PartialOrder` on the set of
  times from `Relation.ReflTransGen (constraints-as-relation)`, (2) proving antisymmetry via the
  forest/freshness argument — a non-trivial tableau-run invariant ("each time has at most one
  incident creating-edge to a smaller-created vertex"), (3) wiring `toLinearExtension` as `f`.
- **Risk**: the antisymmetry proof is the hard part and essentially re-derives acyclicity from
  the run structure. `LinearExtension` only extends `≤` of a `PartialOrder`; mapping the *strict*
  constraint into `<` of the extension needs `toLinearExtension` strict-mono on related pairs,
  which holds but needs the partial order to be *strict* on constraint pairs (i.e. `a ≠ b` for
  every constraint — true, since `tNew` is fresh).
- **Verdict**: viable fallback but heaviest; needs a global acyclicity invariant.

### Option B — Relative integer "instant" assigned at creation  ★ RECOMMENDED

Augment the ordering with an integer **instant** per time label, fixed at the moment the label is
created, consistent with the edge's semantic direction:

- `addFuture t tNew`: `instant tNew := instant t + 1`  (so `instant t < instant tNew`)
- `addPast   t tNew`: `instant tNew := instant t − 1`  (so `instant tNew < instant t`)

Then `D := ℤ`, `f := instant`, and the **replacement lemma** is:

> `ordInstants_strict : ∀ a b, (a, b) ∈ ord.constraints → instant a < instant b`

This holds by a **local, immutable invariant**: at the moment each edge is added, exactly one
endpoint is fresh and its instant is set to satisfy the inequality relative to the existing
endpoint; instants are never mutated afterwards, and the existing endpoint's instant was fixed
earlier. **No global acyclicity / forest argument is required** — the invariant is maintained
edge-by-edge by simple induction over the constraint list.

- **Feasibility**: highest. `ℤ` already supplies `LinearOrder` and `Nontrivial` by
  `inferInstance` (and ℤ is already used as a temporal time domain at
  `ConservativeExtension.lean:67`, `Satisfies (TemporalModel.constant v) (0 : ℤ) ψ`). The proof
  is a `List.foldl`/`cons` induction mirroring the already-present `freshTime_gt`,
  `branchNextTime_gt`, and `mem_futureOf_iff` proofs.
- **Cost**: moderate, mechanical. Requires storing the instant map (see §4 for two encodings) and
  threading it through `addFuture`/`addPast`. The `Rules.lean` call sites already call
  `ord.addFuture t t'` / `ord.addPast t t'` with both arguments, so the signatures need no new
  arguments — the instant of `t` is read from the store and `tNew`'s is derived.
- **Verdict**: cleanest path to a sorry-free corrected lemma; no Mathlib order-extension
  machinery, no acyclicity proof. **Recommended.**

### Option C — Post-hoc instant from the constraint list (no structure change)

Define `instant : Nat → ℤ` by recursion/topological walk over `constraints` after the fact.
Rejected: reconstructing a consistent assignment post-hoc is a topological sort and *re-introduces*
the need to prove "each non-root time has exactly one creating edge to a smaller-created label"
(the same forest invariant as Option A). More work than Option B for no benefit.

---

## 4. Recommended Implementation Sketch (Option B)

Two encodings; **B-encoding-1 is preferred** (keeps a total function, simplest proofs).

### Encoding 1 — store an instant function alongside constraints

```lean
structure TimeOrdering where
  constraints : List (Nat × Nat)
  /-- Integer position of each created time label; default 0 for the initial label. -/
  instant : Nat → ℤ := fun _ => 0

namespace TimeOrdering

def empty : TimeOrdering := { constraints := [], instant := fun _ => 0 }

def addFuture (ord : TimeOrdering) (t tNew : Nat) : TimeOrdering :=
  { constraints := (t, tNew) :: ord.constraints
    instant := Function.update ord.instant tNew (ord.instant t + 1) }

def addPast (ord : TimeOrdering) (t tNew : Nat) : TimeOrdering :=
  { constraints := (tNew, t) :: ord.constraints
    instant := Function.update ord.instant tNew (ord.instant t - 1) }
```

**Invariant carried through the tableau run** (the corrected lemma, proved by induction over the
list of `addFuture`/`addPast` operations — i.e. as a property preserved from `empty`):

```lean
def InstantStrict (ord : TimeOrdering) : Prop :=
  ∀ a b, (a, b) ∈ ord.constraints → ord.instant a < ord.instant b

lemma InstantStrict.empty : InstantStrict .empty := by
  intro a b h; simp [TimeOrdering.empty] at h

lemma InstantStrict.addFuture (ord) (h : InstantStrict ord)
    (hfresh : ∀ s, (s = t ∨ (∃ x, (t, x) ∈ ord.constraints ∨ (x, t) ∈ ord.constraints))
                   → t ≠ tNew)        -- tNew fresh: not mentioned in ord
    (hfresh' : ord.instant tNew = 0 ∨ tNew ∉ ord.allTimes) :
    InstantStrict (ord.addFuture t tNew) := by
  intro a b hab
  simp only [TimeOrdering.addFuture, List.mem_cons] at hab
  rcases hab with h0 | h0
  · -- new edge (t, tNew): instant t < instant t + 1, with update at tNew only
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h0   -- a = t, b = tNew
    simp [Function.update, (show t ≠ tNew from …)]  -- instant t < instant t + 1
    omega
  · -- old edge: instants of a,b unchanged because tNew is fresh (∉ {a,b})
    have := h a b h0
    simpa [Function.update, (show a ≠ tNew from …), (show b ≠ tNew from …)]
```

The two `…` freshness side-conditions are discharged from the tableau-run fact that
`tNew = branchNextTime b` is `> branchMaxTime`, hence `≠` any label already constrained
(uses `branchNextTime_gt` + the existing `mem_futureOf_iff` / `mem_pastOf_iff`). `addPast` is
symmetric (`instant t - 1 < instant t`, closed by `omega`).

### Final assembly of `branchSat` (replacing the blocked sketch at Completeness.lean 329–339)

```lean
lemma openBranch_branchSat
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hH : temporalHintikkaSet b ord tracker)
    (hInst : InstantStrict ord) :          -- carried from temporalTableau run
    branchSat b ord :=
  ⟨ℤ, inferInstance, inferInstance, extractModelℤ b ord, ord.instant,
   fun t t' hc => hInst t t' hc,           -- ← order-preservation, NOW PROVABLE
   fun sf hmem => temporalTruthLemma … ⟩   -- (still blocked on FMP, separate task)
```

`ℤ`'s `LinearOrder` and `Nontrivial` are `inferInstance` (no new imports).

### Mathlib / local API candidates (grounded)

| Need | Candidate | Source |
|---|---|---|
| time domain `LinearOrder` + `Nontrivial` | `ℤ` via `inferInstance` | already used `ConservativeExtension.lean:67` |
| pointwise instant update | `Function.update` | Mathlib `Mathlib.Logic.Function.Basic` |
| `instant t + 1 < / -1 <` discharge | `omega` | core |
| freshness of `tNew` | `branchNextTime_gt` | Rules.lean:73 (exists) |
| membership ↔ constraint | `mem_futureOf_iff`, `mem_pastOf_iff` | TimeOrdering.lean:133,149 (exist) |
| list-induction template | `freshTime_gt` proof shape | TimeOrdering.lean:204 (exists) |
| Option-A fallback | `LinearExtension`, `toLinearExtension`, `instLinearOrderLinearExtensionOfPartialOrder` | `Mathlib.Order.Extension.Linear` (loogle-verified) |

---

## 5. Caveat: `extractModel` valuation must be re-keyed through `f`

`extractModel` (Completeness.lean 102–105) currently builds `TemporalModel Nat Atom` with
`valuation t p := b.any (… sf.label == t …)` — valuation indexed by **Nat label**. If the model
domain becomes `D = ℤ` and `f = ord.instant`, the valuation must be indexed by **ℤ instant**, e.g.

```lean
def extractModelℤ (b : TBranch Atom) (ord : TimeOrdering) : TemporalModel ℤ Atom where
  valuation z p := b.any fun sf =>
    sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p
```

This is well-defined but introduces a subtlety the **plan/implementation** must handle: distinct
labels can share an instant (the instant map need not be injective). For the *atom* lemmas this is
harmless (the existing `extractModel_atom_*` lemmas survive with `f sf.label` substituted), but the
truth lemma for `untl`/`snce` quantifies over *all* `s : ℤ` — that difficulty is **already** the
separately-blocked FMP obligation (`temporalTruthLemma_untl/snce`, Completeness.lean 296–325) and
is **out of scope for task 426**. Task 426's deliverable is precisely the order-preservation
component (`hInst`/`InstantStrict`) plus the `D/f` choice, which §4 discharges sorry-free.

**Scope boundary**: Task 426 = (a) redesign ordering to carry instants, (b) prove
`InstantStrict` sorry-free, (c) re-key `extractModel`→`extractModelℤ` and re-prove the *atom*
properties. It does **not** include the FMP-blocked Until/Since fulfilment lemmas.

---

## 6. Reuse Notes

- **Bimodal `TimeOrdering` infrastructure**: the temporal `TimeOrdering` is explicitly modeled on
  the bimodal algorithm template (TimeOrdering.lean docstring line 36 cites bimodal
  `Decidability/SignedFormula.lean` 684–720). The bimodal countermodel extraction lives at
  `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean` and
  `…/Decidability/Tableau.lean` — worth a direct read during planning to see whether bimodal
  already assigns explicit integer/ordinal positions to its time points (a ready-made instant
  scheme to copy). Grep showed both files reference `TimeOrdering`-style machinery; no explicit
  `instant`/`LinearExtension` symbol was found there, so bimodal likely faces (or finessed) the
  same issue — confirm during planning.
- **Task 421 (`min_fmp_decidability`)**: no `specs/*421*` directory exists in this checkout, so no
  artifact-level reuse is available here. Its relevance is to the *separately-blocked* FMP truth
  lemmas (Until/Since fulfilment), **not** to the ordering redesign that is task 426's scope. If
  421's FMP results land, they unblock the downstream `temporalTruthLemma_*`, but task 426 can and
  should complete independently (order-preservation only).
- **Existing reusable lemmas** (no new infra needed): `branchNextTime_gt` (Rules.lean:73),
  `mem_futureOf_iff` / `mem_pastOf_iff` (TimeOrdering.lean:133/149), `freshTime_gt`
  (TimeOrdering.lean:204) as a proof-shape template, and the ℤ-as-time-domain precedent at
  `ConservativeExtension.lean:67`.

---

## 7. Recommendation Summary

1. **Adopt Option B** (relative integer instants assigned at creation; `D = ℤ`, `f = instant`).
   Cleanest, no acyclicity proof, no order-extension machinery, reuses existing freshness lemmas.
2. **Do not attempt to prove `ordConstraints_strict`** — it is genuinely false. Replace it with
   `InstantStrict : ∀ a b, (a,b) ∈ constraints → instant a < instant b`, an invariant maintained
   inductively from `TimeOrdering.empty` through every `addFuture`/`addPast`.
3. **Touch points** the plan must cover: `TimeOrdering` structure + `empty`/`addFuture`/`addPast`
   (TimeOrdering.lean 50–73); the `InstantStrict` invariant lemmas; threading the invariant proof
   through `temporalTableau` (Saturation.lean 241) so `openBranch_branchSat` receives `hInst`;
   re-key `extractModel`→`extractModelℤ` and re-prove the atom lemmas.
4. **Out of scope** (keep BLOCKED, do not introduce sorry/axioms): FMP-dependent
   `temporalTruthLemma_untl/snce` and the full `temporalTruthLemma`. Zero-debt: the corrected
   ordering lemma is provable sorry-free; if any threading obstacle forces a sorry, mark
   **[BLOCKED]** for user review rather than deferring.
5. **Fallback**: if structure-threading proves too invasive, Option A (`LinearExtension` +
   acyclicity) is the documented alternative, at higher proof cost.
