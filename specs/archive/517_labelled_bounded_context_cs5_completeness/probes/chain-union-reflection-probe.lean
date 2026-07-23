import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context
import Mathlib.Order.SetNotation
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family

/-! # Task 517 Phase 3 — the chain-union / cofinite-encoding obstacle

**Objective** (plan `11_tprime-repair-cs5-completeness.md`, Phase 3): mechanize the reflection
(finite-support) fact Simpson's proof of the Prime Lemma 5.3.1 calls "easily seen" (p. 92,
Literature chunk `chunk_0102.md`, verbatim: *"Let `{(Gᵢ,Γᵢ)}ᵢ∈I` be any chain in the set `C`
... It is easily seen that `(⋃ᵢGᵢ, ⋃ᵢΓᵢ)` is also in `C`."*) — no further detail is given in the
source. This file supplies the missing mechanization.

## Diagnosis (why this is genuinely hard, confirmed against the literature)

`NIK`'s eigenvariable rules `boxI`/`diaE` use **cofinite quantification**: `∀ y ∉ L, NIK 𝒯
(G.addEdge x y) Γ (y∶A)`, universally over *every* label outside a finite exclusion set `L`
(`Deduction.lean`). A chain-union reflection argument — showing `NIK 𝒯 G∞ Γ∞ φ → ∃ i, NIK 𝒯 (𝒢
i) (Γf i) φ` by induction on the derivation of `φ` — hits exactly this rule: the induction
hypothesis, applied pointwise to each `y ∉ L`, yields a *different* chain index `i_y` for each
`y`, and directedness alone does not bound infinitely many `i_y` by one index.

Simpson's own general tool for this shape of argument is **Proposition 4.4.1** (Literature
`chunk_0087.md`/`chunk_0088.md`, `:5090` area, already partially transcribed by
`Deduction.lean`'s `NIK.weaken` for the *inclusion* graph morphism): *"A graph morphism from `G`
to `G'` is a function `f : X → X'` such that `xRy` in `G` implies `f(x)Rf(y)` in `G'`... For any
graph morphism `f`, from `G` to `G'`, if `Γ ⊢_G x:A` then `f(Γ) ⊢_{G'} f(x):A`."* Note Simpson's
`f` is an **arbitrary function**, not required injective.

**The genuine gap this file flags** (this refinement is Simpson's Prop. 4.4.1 specialized, not
something the source itself states): an *arbitrary* graph morphism `f` does **not** suffice to
rebuild a `boxI`/`diaE` premise at a new graph, because reconstructing `∀ y' ∉ L', NIK 𝒯
(G'.addEdge (f x) y') ... (y' ∶ A)` from `∀ y ∉ L, NIK 𝒯 (G.addEdge x y) ... (y ∶ A)` needs, for
*every* `y'` outside a finite set, a **preimage** `y = f⁻¹(y')` — which only a **bijective** `f`
guarantees. This file's core lemma, `NIK.swap_relabel`, is Prop. 4.4.1 specialized to a
two-label-swap bijection (self-inverse, hence its own preimage map), which is exactly enough:
one witness `y₀` obtained from the induction hypothesis at ONE fresh label transports, via the
swap, to *every* other fresh label `y`. This is the "label-renaming / equivariance lemma" the
plan's Risk section predicts.

## Contents

- `swapFn a b`: the label transposition swapping `a ↔ b`, identity elsewhere (classical, since
  `Label Atom` need not have decidable equality for an arbitrary `Atom`).
- `TClosure.map`: 𝒯-closure is preserved under any relation-pushforward (not just inclusion) —
  the `(□E)`/`(◇I)` case of the induction below.
- `NIK.swap_relabel`: **the crux** — Prop. 4.4.1 specialized to `swapFn a b`, proved by structural
  induction mirroring `NIK.weaken`'s case shape exactly.
- `NIK.freshWitness_transport`: the corollary actually consumed by the reflection argument —
  transports a derivation at one fresh witness `y₀` to any other label `y`, both fresh w.r.t. the
  ambient graph and context.
- `ChainCtx`: a minimal abstract formalization of an `I`-indexed **chain** of contexts under
  `Context.le` (monotone in a directed order on `I`), its union graph `chainUnionG` and union set
  `chainUnionΓ`, sufficient to state and prove the reflection fact without depending on Phase 4's
  not-yet-defined Zorn poset `C`.
- `ChainCtx.deriv_reflect`: **the reflection theorem** — `Deriv 𝒯 chainUnionG chainUnionΓ φ → ∃ i,
  Deriv 𝒯 (𝒢 i) (Γf i) φ`. This is Simpson's elided "easily seen" step, mechanized.
- `ChainCtx.chain_closure`: the corollary Phase 3 Task 3 asks for — if no chain member derives
  the excluded formula, neither does the union.

## Provenance

Literature: `chunk_0087.md`, `chunk_0088.md` (Prop. 4.4.1, graph morphisms, §4.4), `chunk_0102.md`
(Lemma 5.3.1, the elided chain-union step, §5.3). PDF offset +9; the raster was not needed here
since the OCR text layer for this prose (not a displayed figure) is legible.
-/

namespace Cslib.Logic.Modal.Labelled

universe u
variable {Atom : Type u} {𝒯 : Set GeomAxiom}

open Classical

/-! ## The transposition `swapFn a b` -/

/-- The label transposition swapping `a ↔ b` and fixing every other label. Classical (no
`DecidableEq (Label Atom)` is assumed for a general `Atom`); this is harmless since `NIK` and
`Deriv` are `Prop`-valued and `Classical.choice` is already in this development's axiom
footprint. -/
noncomputable def swapFn (a b l : Label Atom) : Label Atom :=
  if l = a then b else if l = b then a else l

@[simp] theorem swapFn_left (a b : Label Atom) : swapFn a b a = b := by
  unfold swapFn; simp

@[simp] theorem swapFn_right (a b : Label Atom) : swapFn a b b = a := by
  unfold swapFn
  by_cases h : b = a
  · simp [h]
  · simp [h]

theorem swapFn_other {a b l : Label Atom} (hl1 : l ≠ a) (hl2 : l ≠ b) : swapFn a b l = l := by
  unfold swapFn; simp [hl1, hl2]

/-- **`swapFn a b` is an involution.** This is what makes it its own inverse, which is exactly
what lets the crux lemma below reconstruct a preimage for every `y'` outside a finite exclusion
set. -/
@[simp] theorem swapFn_swapFn (a b l : Label Atom) : swapFn a b (swapFn a b l) = l := by
  unfold swapFn
  by_cases h1 : l = a
  · by_cases h2 : b = a
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h2 : l = b
    · by_cases h3 : a = b
      · simp [h2, h3]
      · simp [h2]
    · simp [h1, h2]

/-! ## `TClosure` is preserved under an arbitrary relation-pushforward -/

/-- **𝒯-closure transports along any relation-pushforward `f`**, not just an inclusion (compare
`TClosure.mono` in `Deduction.lean`, which is the special case `f = id`). Used by
`NIK.swap_relabel`'s `(□E)`/`(◇I)` cases. -/
theorem TClosure.map {R R' : Label Atom → Label Atom → Prop} (f : Label Atom → Label Atom)
    (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : Label Atom} (h : TClosure 𝒯 R x y) :
    TClosure 𝒯 R' (f x) (f y) := by
  induction h with
  | base h => exact .base (hf _ _ h)
  | refl h x => exact .refl h (f x)
  | symm h _ ih => exact .symm h ih
  | trans h _ _ ihxy ihyz => exact .trans h ihxy ihyz
  | eucl h _ _ ihxy ihxz => exact .eucl h ihxy ihxz

/-! ## The crux: `NIK.swap_relabel` (Prop. 4.4.1 specialized to a swap) -/

/-- **The crux lemma.** Prop. 4.4.1 (`f(Γ) ⊢_{G'} f(x):A`) specialized to `f = swapFn a b`: any
`NIK`-derivation transports along a two-label swap, provided the target graph `G'` is related to
the source `G` by the swap as a graph morphism (`hf`). The proof mirrors `NIK.weaken`'s case
shape exactly; the only departure is `boxI`/`diaE`, where the swap's involution
(`swapFn_swapFn`) supplies, for every `y' ∉ swapFn a b '' L`, the preimage `y := swapFn a b y'`
that the original cofinite premise `h` is applied at. -/
theorem NIK.swap_relabel {a b : Label Atom} {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIK 𝒯 G Γ φ) :
    ∀ {G' : Graph Atom}, (∀ x y, G.R x y → G'.R (swapFn a b x) (swapFn a b y)) →
      NIK 𝒯 G' (Γ.map (fun ψ => swapFn a b ψ.lbl ∶ ψ.prop)) (swapFn a b φ.lbl ∶ φ.prop) := by
  induction h with
  | assumption G Γ φ hmem =>
      intro G' _
      exact .assumption G' _ _ (List.mem_map_of_mem hmem)
  | efq G Γ x y A _ ih =>
      intro G' hf
      exact .efq G' _ (swapFn a b x) (swapFn a b y) A (ih hf)
  | andI G Γ x A B _ _ ihA ihB =>
      intro G' hf
      exact .andI G' _ (swapFn a b x) A B (ihA hf) (ihB hf)
  | andE1 G Γ x A B _ ih =>
      intro G' hf
      exact .andE1 G' _ (swapFn a b x) A B (ih hf)
  | andE2 G Γ x A B _ ih =>
      intro G' hf
      exact .andE2 G' _ (swapFn a b x) A B (ih hf)
  | orI1 G Γ x A B _ ih =>
      intro G' hf
      exact .orI1 G' _ (swapFn a b x) A B (ih hf)
  | orI2 G Γ x A B _ ih =>
      intro G' hf
      exact .orI2 G' _ (swapFn a b x) A B (ih hf)
  | orE G Γ x y A B C _ _ _ ihor ihA ihB =>
      intro G' hf
      refine .orE G' _ (swapFn a b x) (swapFn a b y) A B C (ihor hf) ?_ ?_
      · simpa using ihA hf
      · simpa using ihB hf
  | impI G Γ x A B _ ih =>
      intro G' hf
      have := ih hf
      simpa using NIK.impI G' _ (swapFn a b x) A B (by simpa using this)
  | impE G Γ x A B _ _ ihimp ihA =>
      intro G' hf
      exact .impE G' _ (swapFn a b x) A B (ihimp hf) (ihA hf)
  | boxE G Γ x y A hR _ ih =>
      intro G' hf
      exact .boxE G' _ (swapFn a b x) (swapFn a b y) A (TClosure.map (swapFn a b) hf hR) (ih hf)
  | boxI L hL G Γ x A h ih =>
      intro G' hf
      refine .boxI (swapFn a b '' L) (hL.image _) G' _ (swapFn a b x) A ?_
      intro y' hy'
      set y := swapFn a b y' with hy_def
      have hyL : y ∉ L := by
        intro hmem
        exact hy' ⟨y, hmem, by simp [hy_def]⟩
      have hstep := ih y hyL (G' := G'.addEdge (swapFn a b x) y')
      have hf' : ∀ p q, (G.addEdge x y).R p q →
          (G'.addEdge (swapFn a b x) y').R (swapFn a b p) (swapFn a b q) := by
        intro p q hpq
        rcases hpq with hpq | ⟨rfl, rfl⟩
        · exact Or.inl (hf p q hpq)
        · exact Or.inr ⟨rfl, by simp [hy_def]⟩
      have := hstep hf'
      simpa [hy_def] using this
  | diaI G Γ x y A hR _ ih =>
      intro G' hf
      exact .diaI G' _ (swapFn a b x) (swapFn a b y) A (TClosure.map (swapFn a b) hf hR) (ih hf)
  | diaE L hL G Γ x z A B hdia h ihdia ih =>
      intro G' hf
      refine .diaE (swapFn a b '' L) (hL.image _) G' _ (swapFn a b x) (swapFn a b z) A B
        (ihdia hf) ?_
      intro y' hy'
      set y := swapFn a b y' with hy_def
      have hyL : y ∉ L := by
        intro hmem
        exact hy' ⟨y, hmem, by simp [hy_def]⟩
      have hstep := ih y hyL (G' := G'.addEdge (swapFn a b x) y')
      have hf' : ∀ p q, (G.addEdge x y).R p q →
          (G'.addEdge (swapFn a b x) y').R (swapFn a b p) (swapFn a b q) := by
        intro p q hpq
        rcases hpq with hpq | ⟨rfl, rfl⟩
        · exact Or.inl (hf p q hpq)
        · exact Or.inr ⟨rfl, by simp [hy_def]⟩
      have := hstep hf'
      simpa [hy_def] using this

/-! ## Freshness transport: the corollary the reflection argument actually consumes -/

/-- If `f = swapFn a b` fixes every label occurring in `Γ` (i.e. `a,b` are both fresh w.r.t.
`Γ`), relabeling does nothing to `Γ`. -/
theorem List.map_swapFn_eq_self {a b : Label Atom} {Γ : List (LabelledFormula Atom)}
    (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ a ∧ ψ.lbl ≠ b) :
    Γ.map (fun ψ => swapFn a b ψ.lbl ∶ ψ.prop) = Γ := by
  conv_rhs => rw [← List.map_id (l := Γ)]
  refine List.map_congr_left (fun ψ hψ => ?_)
  obtain ⟨h1, h2⟩ := hΓ ψ hψ
  simp [swapFn_other h1 h2]

/-- **Freshness transport.** The corollary `NIK.swap_relabel` is built for: a derivation
witnessed at one fresh label `y₀` transports to *any* other label `y`, provided both are fresh
w.r.t. the ambient graph `G`, the pivot label `x`, and the context `Γ`. This is exactly what lets
a chain-union reflection argument turn "the induction hypothesis holds at *some* fresh `y₀`" into
"the rebuilt `boxI`/`diaE` premise holds at *every* sufficiently fresh `y`" (see the module
docstring's diagnosis). -/
theorem NIK.freshWitness_transport {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {x y₀ y : Label Atom} {A : Proposition Atom} (h : NIK 𝒯 (G.addEdge x y₀) Γ (y₀ ∶ A))
    (hy₀X : y₀ ∉ G.X) (hyX : y ∉ G.X) (hxy₀ : x ≠ y₀) (hxy : x ≠ y)
    (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀ ∧ ψ.lbl ≠ y) : NIK 𝒯 (G.addEdge x y) Γ (y ∶ A) := by
  have hf : ∀ p q, (G.addEdge x y₀).R p q →
      (G.addEdge x y).R (swapFn y₀ y p) (swapFn y₀ y q) := by
    intro p q hpq
    rcases hpq with hpq | ⟨rfl, rfl⟩
    · have hp : p ≠ y₀ := fun hp => hy₀X (hp ▸ (G.edge_mem p q hpq).1)
      have hq : q ≠ y₀ := fun hq => hy₀X (hq ▸ (G.edge_mem p q hpq).2)
      -- `p, q ∈ G.X` (edge endpoints), and `y ∉ G.X`, so `p, q ≠ y` too.
      have hp' : p ≠ y := fun hp => hyX (hp ▸ (G.edge_mem p q hpq).1)
      have hq' : q ≠ y := fun hq => hyX (hq ▸ (G.edge_mem p q hpq).2)
      rw [swapFn_other hp hp', swapFn_other hq hq']
      exact Or.inl hpq
    · rw [swapFn_other hxy₀ hxy, swapFn_left]
      exact Or.inr ⟨rfl, rfl⟩
  have hstep := h.swap_relabel (a := y₀) (b := y) (G' := G.addEdge x y) hf
  rwa [List.map_swapFn_eq_self hΓ, show swapFn y₀ y y₀ = y from swapFn_left y₀ y] at hstep

/-! ## `substFn`/`NIK.relabelFresh`: one-directional relabeling (relocated from Phase 5, Task 517
Phase 6)

**Relocation note**: this block (originally landed by Phase 5 as `flo_oldlabel_transport`'s
supporting machinery, much later in the file) is moved here, content unchanged, so that
`ChainCtx.deriv_reflect` and `dwitness_mem_of_maximal` -- both defined below, ahead of Phase 5's
original position -- can consume it too (Task 517 Phase 6). See `flo_oldlabel_transport`'s
docstring (further below) for the full mathematical writeup of why a *one-directional*
substitution, unlike `swapFn`'s involution, never disturbs the target label's own pre-existing
structure and so needs no freshness hypothesis on the target at all. -/

/-- The one-directional label substitution sending `a ↦ b` and fixing every other label
(including `b` itself). Unlike `swapFn`, this is **not an involution**: `substFn a b` never sends
`b ↦ a`, so it never disturbs any structure already incident to `b` -- exactly what avoids the
"naive swap" collision the Postmortem Constraints flag for old-label transport. -/
noncomputable def substFn (a b l : Label Atom) : Label Atom :=
  if l = a then b else l

@[simp] theorem substFn_self (a b : Label Atom) : substFn a b a = b := by
  unfold substFn; simp

theorem substFn_other {a b l : Label Atom} (hl : l ≠ a) : substFn a b l = l := by
  unfold substFn; simp [hl]

/-- If `f = substFn a b` fixes every label occurring in `Γ` (i.e. `a` is fresh w.r.t. `Γ`),
relabeling does nothing to `Γ`. Analogue of `List.map_swapFn_eq_self` for `substFn`. -/
theorem List.map_substFn_eq_self {a b : Label Atom} {Γ : List (LabelledFormula Atom)}
    (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ a) :
    Γ.map (fun ψ => substFn a b ψ.lbl ∶ ψ.prop) = Γ := by
  conv_rhs => rw [← List.map_id (l := Γ)]
  refine List.map_congr_left (fun ψ hψ => ?_)
  simp [substFn_other (hΓ ψ hψ)]

/-- **One-directional relabeling.** Prop. 4.4.1 (`f(Γ) ⊢_{G'} f(x):A`) specialized to
`f = substFn a b`: any `NIK`-derivation transports along a one-directional substitution `a ↦ b`
(not necessarily a swap), provided the target graph `G'` is related to the source `G` by the
substitution as a graph morphism (`hf`). The proof mirrors `NIK.swap_relabel`'s case shape
exactly, with one departure in `boxI`/`diaE`: since `substFn a b` is not invertible, the preimage
of a target label `t ∉ substFn a b '' L ∪ {a}` is `t` **itself** (not `substFn a b t` computed via
an involution formula), because `substFn a b` fixes every point besides `a`, and `t ≠ a` is
guaranteed by `t ∉ {a}`. This is what lets `b` remain fully untouched: the lemma places no
freshness requirement on `b` at all. -/
theorem NIK.relabelFresh {a b : Label Atom} {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIK 𝒯 G Γ φ) :
    ∀ {G' : Graph Atom}, (∀ p q, G.R p q → G'.R (substFn a b p) (substFn a b q)) →
      NIK 𝒯 G' (Γ.map (fun ψ => substFn a b ψ.lbl ∶ ψ.prop)) (substFn a b φ.lbl ∶ φ.prop) := by
  induction h with
  | assumption G Γ φ hmem =>
      intro G' _
      exact .assumption G' _ _ (List.mem_map_of_mem hmem)
  | efq G Γ x y A _ ih =>
      intro G' hf
      exact .efq G' _ (substFn a b x) (substFn a b y) A (ih hf)
  | andI G Γ x A B _ _ ihA ihB =>
      intro G' hf
      exact .andI G' _ (substFn a b x) A B (ihA hf) (ihB hf)
  | andE1 G Γ x A B _ ih =>
      intro G' hf
      exact .andE1 G' _ (substFn a b x) A B (ih hf)
  | andE2 G Γ x A B _ ih =>
      intro G' hf
      exact .andE2 G' _ (substFn a b x) A B (ih hf)
  | orI1 G Γ x A B _ ih =>
      intro G' hf
      exact .orI1 G' _ (substFn a b x) A B (ih hf)
  | orI2 G Γ x A B _ ih =>
      intro G' hf
      exact .orI2 G' _ (substFn a b x) A B (ih hf)
  | orE G Γ x y A B C _ _ _ ihor ihA ihB =>
      intro G' hf
      refine .orE G' _ (substFn a b x) (substFn a b y) A B C (ihor hf) ?_ ?_
      · simpa using ihA hf
      · simpa using ihB hf
  | impI G Γ x A B _ ih =>
      intro G' hf
      have := ih hf
      simpa using NIK.impI G' _ (substFn a b x) A B (by simpa using this)
  | impE G Γ x A B _ _ ihimp ihA =>
      intro G' hf
      exact .impE G' _ (substFn a b x) A B (ihimp hf) (ihA hf)
  | boxE G Γ x y A hR _ ih =>
      intro G' hf
      exact .boxE G' _ (substFn a b x) (substFn a b y) A
        (TClosure.map (substFn a b) hf hR) (ih hf)
  | boxI L hL G Γ x A h ih =>
      intro G' hf
      refine .boxI (substFn a b '' L ∪ {a}) (hL.image _ |>.union (Set.finite_singleton a)) G' _
        (substFn a b x) A ?_
      intro t ht
      have hta : t ≠ a := by
        intro heq
        exact ht (Or.inr (by simp [heq]))
      have hst : substFn a b t = t := substFn_other hta
      have htL : t ∉ L := by
        intro hmem
        exact ht (Or.inl ⟨t, hmem, hst⟩)
      have hstep := ih t htL (G' := G'.addEdge (substFn a b x) t)
      have hf' : ∀ p q, (G.addEdge x t).R p q →
          (G'.addEdge (substFn a b x) t).R (substFn a b p) (substFn a b q) := by
        intro p q hpq
        rcases hpq with hpq | ⟨rfl, rfl⟩
        · exact Or.inl (hf p q hpq)
        · exact Or.inr ⟨rfl, hst⟩
      have := hstep hf'
      simpa [hst] using this
  | diaI G Γ x y A hR _ ih =>
      intro G' hf
      exact .diaI G' _ (substFn a b x) (substFn a b y) A
        (TClosure.map (substFn a b) hf hR) (ih hf)
  | diaE L hL G Γ x z A B hdia h ihdia ih =>
      intro G' hf
      refine .diaE (substFn a b '' L ∪ {a}) (hL.image _ |>.union (Set.finite_singleton a)) G' _
        (substFn a b x) (substFn a b z) A B (ihdia hf) ?_
      intro t ht
      have hta : t ≠ a := by
        intro heq
        exact ht (Or.inr (by simp [heq]))
      have hst : substFn a b t = t := substFn_other hta
      have htL : t ∉ L := by
        intro hmem
        exact ht (Or.inl ⟨t, hmem, hst⟩)
      have hstep := ih t htL (G' := G'.addEdge (substFn a b x) t)
      have hf' : ∀ p q, (G.addEdge x t).R p q →
          (G'.addEdge (substFn a b x) t).R (substFn a b p) (substFn a b q) := by
        intro p q hpq
        rcases hpq with hpq | ⟨rfl, rfl⟩
        · exact Or.inl (hf p q hpq)
        · exact Or.inr ⟨rfl, hst⟩
      have := hstep hf'
      simpa [hst] using this

/-- **Old-label transport, graph-generic form** (Task 517 Phase 6): the graph-level fact
`flo_oldlabel_transport` (further below) specializes to a `FloSeq` stage -- extracted here,
BEFORE `FloSeq`/`FLO` exist in the file, because `ChainCtx.deriv_reflect` and
`dwitness_mem_of_maximal` need exactly this graph-generic form and neither one is stated in terms
of a `FloSeq`. Built directly from `NIK.relabelFresh` with `a := y₀`, `b := y'`: a `NIK`-derivation
witnessed at one label `y₀` **fresh w.r.t. the ambient graph `G`** transports to ANY OTHER label
`y'` -- fresh or already a member of `G.X` ("old") -- with NO side condition on `y'` at all, since
`substFn y₀ y'` (unlike `swapFn`) never touches whatever structure `G` already has at `y'`. This
is the fact both `ChainCtx.deriv_reflect` and `dwitness_mem_of_maximal`'s diamond old-label
sub-case could not close without it. -/
theorem NIK.oldLabelTransport {G : Graph Atom} {x y₀ : Label Atom} {A : Proposition Atom}
    {Γ : List (LabelledFormula Atom)} (h : NIK 𝒯 (G.addEdge x y₀) Γ (y₀ ∶ A)) (hy₀ : y₀ ∉ G.X)
    (hxy₀ : x ≠ y₀) (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀) (y' : Label Atom) :
    NIK 𝒯 (G.addEdge x y') Γ (y' ∶ A) := by
  have hf : ∀ p q, (G.addEdge x y₀).R p q → (G.addEdge x y').R (substFn y₀ y' p) (substFn y₀ y' q) := by
    intro p q hpq
    rcases hpq with hpq | ⟨rfl, rfl⟩
    · have hp : p ≠ y₀ := fun hp => hy₀ (hp ▸ (G.edge_mem p q hpq).1)
      have hq : q ≠ y₀ := fun hq => hy₀ (hq ▸ (G.edge_mem p q hpq).2)
      rw [substFn_other hp, substFn_other hq]
      exact Or.inl hpq
    · rw [substFn_other hxy₀, substFn_self]
      exact Or.inr ⟨rfl, rfl⟩
  have hstep := h.relabelFresh (a := y₀) (b := y') (G' := G.addEdge x y') hf
  rwa [List.map_substFn_eq_self hΓ, show substFn y₀ y' y₀ = y' from substFn_self y₀ y'] at hstep

/-- **Old-label diamond-witness transport, graph-generic form** (Task 517 Phase 6): the
`substFn`-based analogue of `NIK.diaWitness_transport` above, dropping the freshness requirement
on the TARGET label `y` -- the one-directional relabeling `substFn y₀ y` never disturbs whatever
structure the ambient graph `G` already has at `y`, so the transported derivation is valid for
ANY target `y`, old or fresh. Only the SOURCE witness `y₀` needs to be fresh. This is
`dwitness_mem_of_maximal`'s diamond old-label sub-case's exact missing fact. -/
theorem NIK.diaWitnessTransportOld {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {x z y₀ : Label Atom} {A C : Proposition Atom}
    (h : NIK 𝒯 (G.addEdge x y₀) ((y₀ ∶ A) :: Γ) (z ∶ C)) (hy₀X : y₀ ∉ G.X)
    (hxy₀ : x ≠ y₀) (hzy₀ : z ≠ y₀) (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀) (y : Label Atom) :
    NIK 𝒯 (G.addEdge x y) ((y ∶ A) :: Γ) (z ∶ C) := by
  have hf : ∀ p q, (G.addEdge x y₀).R p q → (G.addEdge x y).R (substFn y₀ y p) (substFn y₀ y q) := by
    intro p q hpq
    rcases hpq with hpq | ⟨rfl, rfl⟩
    · have hp : p ≠ y₀ := fun hp => hy₀X (hp ▸ (G.edge_mem p q hpq).1)
      have hq : q ≠ y₀ := fun hq => hy₀X (hq ▸ (G.edge_mem p q hpq).2)
      rw [substFn_other hp, substFn_other hq]
      exact Or.inl hpq
    · rw [substFn_other hxy₀, substFn_self]
      exact Or.inr ⟨rfl, rfl⟩
  have hstep := h.relabelFresh (a := y₀) (b := y) (G' := G.addEdge x y) hf
  simp only [List.map_cons, substFn_self, List.map_substFn_eq_self hΓ, substFn_other hzy₀] at hstep
  exact hstep

/-! ## `GChain`: a graph-only chain, and the `NIK`-level reflection theorem (Task 517 Phase 6)

**Finding (corrects the "Joint follow-up dispatch" analysis below, which predates this
insight)**: that analysis concluded reflection needs "route (a)" (a step-indexed FLO
reconstruction) because every route it tried transported a *single* witnessed fact to *every*
other label via a **swap** (`swapFn`, an involution) or via reusing the induction hypothesis with
a *different* chain index per label (Shortcut 2). Neither obstacle applies to the **one-directional**
`substFn`-based transport (`NIK.oldLabelTransport`/`NIK.diaWitnessTransportOld` above, Phase 5's
`flo_oldlabel_transport` insight, generalized to an arbitrary graph): it needs freshness of only
the *source* witness `y₀`, never the target, so a *single* reflected chain index for `y₀` alone
already supplies the *entire* cofinite family (fresh or old target labels alike) via
`oldLabelTransport`/`diaWitnessTransportOld`. This reduces the reflection argument to an ordinary
structural induction on the `NIK`-derivation, always working with the CURRENT graph's fresh
witnesses (drawn from the chain's shared reserve `V'ᶜ`, so a supply is always available), with no
FLO/well-founded-rank machinery needed at all. The three "ruled out" shortcuts remain correctly
ruled out **for the techniques they tested** (an unstructured swap, or no relabeling at all); they
did not anticipate a one-directional, non-involutive relabeling. -/

/-- A minimal **graph-only** analogue of `ChainCtx`: an `ι`-indexed family of raw `Graph`s,
monotone and directed, with NO `Context`-validity obligations. Used only by `NIK.reflectChain`
below: the auxiliary chains the reflection induction builds along the way (extending every member
by one shared fresh edge at each `(□I)`/`(◇E)` step) do **not** stay confined to the *original*
reserve `V'` (the fresh witness is drawn from `V'ᶜ` precisely so it lies outside `W(V')`), so they
cannot be re-packaged as genuine `ChainCtx`/`Context` values. Since `NIK` only ever reads the raw
`Graph` structure (never `Context`'s `dwitnessMem` etc.), dropping the `Context` wrapper for this
one auxiliary argument is sound and considerably simpler. -/
structure GChain (Atom : Type u) (ι : Type u) [Preorder ι] where
  /-- The chain's raw graphs. -/
  G : ι → Graph Atom
  /-- Monotonicity under `Graph.le`. -/
  mono : Monotone G
  /-- The chain is directed. -/
  dir : Directed (· ≤ ·) (id : ι → ι)

namespace GChain

variable {ι : Type u} [Preorder ι]

/-- The union graph `⋃ᵢ Gᵢ`. -/
def union (𝒢 : GChain Atom ι) [Nonempty ι] : Graph Atom where
  X := ⋃ i, (𝒢.G i).X
  R := fun x y => ∃ i, (𝒢.G i).R x y
  nonempty := by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    obtain ⟨p, hp⟩ := (𝒢.G i₀).nonempty
    exact ⟨p, Set.mem_iUnion.mpr ⟨i₀, hp⟩⟩
  edge_mem := by
    rintro x y ⟨i, hi⟩
    obtain ⟨hx, hy⟩ := (𝒢.G i).edge_mem x y hi
    exact ⟨Set.mem_iUnion.mpr ⟨i, hx⟩, Set.mem_iUnion.mpr ⟨i, hy⟩⟩

/-- Every chain member is `≤` the union. -/
theorem le_union (𝒢 : GChain Atom ι) [Nonempty ι] (i : ι) : 𝒢.G i ≤ 𝒢.union :=
  ⟨fun _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩, fun _ _ hxy => ⟨i, hxy⟩⟩

/-- Extend every chain member by the SAME edge `x R y` -- the operation `NIK.reflectChain`
performs at each `(□I)`/`(◇E)` step, mirroring the source union graph's own `.addEdge` on every
member simultaneously. -/
def addEdgeAll (𝒢 : GChain Atom ι) (x y : Label Atom) : GChain Atom ι where
  G := fun i => (𝒢.G i).addEdge x y
  mono := fun _ _ hij => Graph.addEdge_mono (𝒢.mono hij) x y
  dir := 𝒢.dir

/-- The extended chain's union domain is exactly the original union's domain plus the two new
points. -/
theorem addEdgeAll_union_X (𝒢 : GChain Atom ι) [Nonempty ι] (x y : Label Atom) :
    (𝒢.addEdgeAll x y).union.X = 𝒢.union.X ∪ {x, y} := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  ext z
  simp only [union, addEdgeAll, Graph.addEdge, Set.mem_iUnion, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hz | hz | hz⟩
    · exact Or.inl ⟨i, hz⟩
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr hz)
  · rintro (⟨i, hz⟩ | hz | hz)
    · exact ⟨i, Or.inl hz⟩
    · exact ⟨i₀, Or.inr (Or.inl hz)⟩
    · exact ⟨i₀, Or.inr (Or.inr hz)⟩

/-- `𝒢.union` extended by one edge is `≤` the extended chain's union (the direction
`NIK.reflectChain`'s `(□I)`/`(◇E)` cases need to weaken the ambient graph hypothesis into the new
chain's union). -/
theorem addEdge_union_le (𝒢 : GChain Atom ι) [Nonempty ι] (x y : Label Atom) :
    𝒢.union.addEdge x y ≤ (𝒢.addEdgeAll x y).union := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  refine ⟨fun z hz => ?_, fun a b hab => ?_⟩
  · rcases hz with hz | hz
    · obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨i, Or.inl hzi⟩
    · exact Set.mem_iUnion.mpr ⟨i₀, Or.inr hz⟩
  · rcases hab with hab | hab
    · obtain ⟨i, habi⟩ := hab
      exact ⟨i, Or.inl habi⟩
    · exact ⟨i₀, Or.inr hab⟩

end GChain

/-- **Fresh-label supply, `Label`-level.** Given a coinfinite `V'` and a finite set `F` of labels,
there is a prefix variable `n ∉ V'` whose label `Label.var n` avoids `F` -- the source of every
fresh witness `NIK.reflectChain` picks. -/
theorem exists_fresh_var {V' : Set PrefixVar} (hV' : Coinfinite V') (F : Set (Label Atom))
    (hF : F.Finite) : ∃ n : PrefixVar, n ∉ V' ∧ Label.var n ∉ F := by
  have hFvars : {n : PrefixVar | Label.var n ∈ F}.Finite :=
    hF.preimage (fun a _ b _ hab => by injection hab)
  have hinf : (V'ᶜ \ {n : PrefixVar | Label.var n ∈ F}).Infinite := hV'.diff hFvars
  obtain ⟨n, hn1, hn2⟩ := hinf.nonempty
  exact ⟨n, hn1, hn2⟩

/-- **`TClosure`-level reflection**: a `𝒯`-closure fact over a `GChain`'s union graph reflects to
a single chain member -- the `(□E)`/`(◇I)` premise `NIK.reflectChain` needs. Induction on the
closure derivation, merging indices via directedness at `trans`/`eucl`. -/
theorem TClosure.reflectChain {ι : Type u} [Preorder ι] [Nonempty ι] (𝒢 : GChain Atom ι)
    {x y : Label Atom} (h : TClosure 𝒯 𝒢.union.R x y) : ∃ i, TClosure 𝒯 (𝒢.G i).R x y := by
  induction h with
  | base h =>
      obtain ⟨i, hi⟩ := h
      exact ⟨i, .base hi⟩
  | refl h a =>
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨i, .refl h a⟩
  | symm h _ ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i, .symm h hi⟩
  | trans h _ _ ih1 ih2 =>
      obtain ⟨i1, hi1⟩ := ih1
      obtain ⟨i2, hi2⟩ := ih2
      obtain ⟨i3, h1, h2⟩ := 𝒢.dir i1 i2
      exact ⟨i3, .trans h (hi1.mono (fun a b hab => (𝒢.mono h1).2 a b hab))
        (hi2.mono (fun a b hab => (𝒢.mono h2).2 a b hab))⟩
  | eucl h _ _ ih1 ih2 =>
      obtain ⟨i1, hi1⟩ := ih1
      obtain ⟨i2, hi2⟩ := ih2
      obtain ⟨i3, h1, h2⟩ := 𝒢.dir i1 i2
      exact ⟨i3, .eucl h (hi1.mono (fun a b hab => (𝒢.mono h1).2 a b hab))
        (hi2.mono (fun a b hab => (𝒢.mono h2).2 a b hab))⟩

/-- **The master reflection theorem** (Task 517 Phase 6): a `NIK`-derivation over (an upper bound
of) a `GChain`'s union graph reflects to a single chain member. Structural induction on the
derivation, generalizing over the `GChain` itself: the finitely-branching rules merge reflected
indices via directedness (`𝒢.dir`) and weaken via `𝒢.mono`/`NIK.weaken`; the cofinite rules
(`(□I)`/`(◇E)`) pick ONE witness `y₀` fresh w.r.t. the current union (drawn from the shared
reserve `V'ᶜ`, always available since only finitely many labels are excluded at any stage),
recurse via `ih` at `y₀` into an EXTENDED chain (`GChain.addEdgeAll`, every member gains the same
edge), then rebuild the FULL cofinite family from the single reflected instance via
`NIK.oldLabelTransport`/`NIK.diaWitnessTransportOld` -- which need no freshness at all on the
*target* label, so a single witness suffices for the entire family, fresh or old alike. -/
theorem NIK.reflectChain {ι : Type u} [Preorder ι] [Nonempty ι] {V' : Set PrefixVar}
    (hV' : Coinfinite V') :
    ∀ {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom},
      NIK 𝒯 G Γ φ → ∀ (𝒢 : GChain Atom ι), G ≤ 𝒢.union →
        (𝒢.union.X \ {a : Label Atom | Label.InW V' a}).Finite → ∃ i, NIK 𝒯 (𝒢.G i) Γ φ := by
  intro G Γ φ h
  induction h with
  | assumption G Γ φ hmem =>
      intro 𝒢 _ _
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨i, .assumption _ _ _ hmem⟩
  | efq G Γ x y A _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i, hi⟩ := ih 𝒢 hG hextra
      exact ⟨i, .efq _ _ x y A hi⟩
  | andI G Γ x A B _ _ ihA ihB =>
      intro 𝒢 hG hextra
      obtain ⟨i1, hi1⟩ := ihA 𝒢 hG hextra
      obtain ⟨i2, hi2⟩ := ihB 𝒢 hG hextra
      obtain ⟨i3, h1, h2⟩ := 𝒢.dir i1 i2
      exact ⟨i3, .andI _ _ x A B (hi1.weaken (𝒢.mono h1) (fun _ hh => hh))
        (hi2.weaken (𝒢.mono h2) (fun _ hh => hh))⟩
  | andE1 G Γ x A B _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i, hi⟩ := ih 𝒢 hG hextra
      exact ⟨i, .andE1 _ _ x A B hi⟩
  | andE2 G Γ x A B _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i, hi⟩ := ih 𝒢 hG hextra
      exact ⟨i, .andE2 _ _ x A B hi⟩
  | orI1 G Γ x A B _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i, hi⟩ := ih 𝒢 hG hextra
      exact ⟨i, .orI1 _ _ x A B hi⟩
  | orI2 G Γ x A B _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i, hi⟩ := ih 𝒢 hG hextra
      exact ⟨i, .orI2 _ _ x A B hi⟩
  | orE G Γ x y A B C _ _ _ ihor ihA ihB =>
      intro 𝒢 hG hextra
      obtain ⟨i1, hi1⟩ := ihor 𝒢 hG hextra
      obtain ⟨i2, hi2⟩ := ihA 𝒢 hG hextra
      obtain ⟨i3, hi3⟩ := ihB 𝒢 hG hextra
      obtain ⟨j, h1j, h2j⟩ := 𝒢.dir i1 i2
      obtain ⟨k, hjk, h3k⟩ := 𝒢.dir j i3
      have h1k : i1 ≤ k := le_trans h1j hjk
      have h2k : i2 ≤ k := le_trans h2j hjk
      exact ⟨k, .orE _ _ x y A B C (hi1.weaken (𝒢.mono h1k) (fun _ hh => hh))
        (hi2.weaken (𝒢.mono h2k) (fun _ hh => hh)) (hi3.weaken (𝒢.mono h3k) (fun _ hh => hh))⟩
  | impI G Γ x A B _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i, hi⟩ := ih 𝒢 hG hextra
      exact ⟨i, .impI _ _ x A B hi⟩
  | impE G Γ x A B _ _ ihimp ihA =>
      intro 𝒢 hG hextra
      obtain ⟨i1, hi1⟩ := ihimp 𝒢 hG hextra
      obtain ⟨i2, hi2⟩ := ihA 𝒢 hG hextra
      obtain ⟨i3, h1, h2⟩ := 𝒢.dir i1 i2
      exact ⟨i3, .impE _ _ x A B (hi1.weaken (𝒢.mono h1) (fun _ hh => hh))
        (hi2.weaken (𝒢.mono h2) (fun _ hh => hh))⟩
  | boxE G Γ x y A hRxy _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i1, hi1⟩ := ih 𝒢 hG hextra
      have hRxy' : TClosure 𝒯 𝒢.union.R x y := hRxy.mono (fun a b hab => hG.2 a b hab)
      obtain ⟨i2, hi2⟩ := TClosure.reflectChain 𝒢 hRxy'
      obtain ⟨i3, h1, h2⟩ := 𝒢.dir i1 i2
      exact ⟨i3, .boxE _ _ x y A (hi2.mono (fun a b hab => (𝒢.mono h2).2 a b hab))
        (hi1.weaken (𝒢.mono h1) (fun _ hh => hh))⟩
  | boxI L hL G Γ x A hp ih =>
      intro 𝒢 hG hextra
      have hFfin : ((𝒢.union.X \ {a : Label Atom | Label.InW V' a}) ∪ L ∪ ({x} : Set (Label Atom))
          ∪ (Γ.map LabelledFormula.lbl : List (Label Atom)).toFinset).Finite :=
        (((hextra.union hL).union (Set.finite_singleton x)).union
          (Γ.map LabelledFormula.lbl).toFinset.finite_toSet)
      obtain ⟨n, hnV', hnF⟩ := exists_fresh_var hV' _ hFfin
      set y₀ : Label Atom := Label.var n with hy₀def
      have hnInW : ¬ Label.InW V' y₀ := hnV'
      have hy₀L : y₀ ∉ L := fun hmem => hnF (Or.inl (Or.inl (Or.inr hmem)))
      have hy₀union : y₀ ∉ 𝒢.union.X := fun hmem =>
        hnF (Or.inl (Or.inl (Or.inl ⟨hmem, hnInW⟩)))
      have hxy₀ : x ≠ y₀ := fun heq => hnF (Or.inl (Or.inr (Set.mem_singleton_iff.mpr heq.symm)))
      have hΓy₀ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀ := fun ψ hψ heq =>
        hnF (Or.inr (List.mem_toFinset.mpr (heq ▸ List.mem_map_of_mem hψ)))
      have hp' : NIK 𝒯 (G.addEdge x y₀) Γ (y₀ ∶ A) := hp y₀ hy₀L
      have hG' : G.addEdge x y₀ ≤ (𝒢.addEdgeAll x y₀).union :=
        le_trans (Graph.addEdge_mono hG x y₀) (𝒢.addEdge_union_le x y₀)
      have hextra' : ((𝒢.addEdgeAll x y₀).union.X \ {a : Label Atom | Label.InW V' a}).Finite := by
        rw [𝒢.addEdgeAll_union_X x y₀]
        have : (𝒢.union.X ∪ {x, y₀}) \ {a : Label Atom | Label.InW V' a} ⊆
            (𝒢.union.X \ {a : Label Atom | Label.InW V' a}) ∪ {x, y₀} := by
          intro z hz
          rcases hz.1 with hz1 | hz1
          · exact Or.inl ⟨hz1, hz.2⟩
          · exact Or.inr hz1
        exact Set.Finite.subset (hextra.union (Set.Finite.insert x (Set.finite_singleton y₀))) this
      obtain ⟨i, hi⟩ := ih y₀ hy₀L (𝒢.addEdgeAll x y₀) hG' hextra'
      have hy₀i : y₀ ∉ (𝒢.G i).X := fun hmem => hy₀union ((𝒢.le_union i).1 hmem)
      refine ⟨i, .boxI L hL _ Γ x A (fun y _ => ?_)⟩
      exact NIK.oldLabelTransport hi hy₀i hxy₀ hΓy₀ y
  | diaI G Γ x y A hRxy _ ih =>
      intro 𝒢 hG hextra
      obtain ⟨i1, hi1⟩ := ih 𝒢 hG hextra
      have hRxy' : TClosure 𝒯 𝒢.union.R x y := hRxy.mono (fun a b hab => hG.2 a b hab)
      obtain ⟨i2, hi2⟩ := TClosure.reflectChain 𝒢 hRxy'
      obtain ⟨i3, h1, h2⟩ := 𝒢.dir i1 i2
      exact ⟨i3, .diaI _ _ x y A (hi2.mono (fun a b hab => (𝒢.mono h2).2 a b hab))
        (hi1.weaken (𝒢.mono h1) (fun _ hh => hh))⟩
  | diaE L hL G Γ x z A B hdia h ihdia ih =>
      intro 𝒢 hG hextra
      obtain ⟨i1, hi1⟩ := ihdia 𝒢 hG hextra
      have hFfin : ((𝒢.union.X \ {a : Label Atom | Label.InW V' a}) ∪ L ∪ ({x} : Set (Label Atom))
          ∪ ({z} : Set (Label Atom)) ∪
          (Γ.map LabelledFormula.lbl : List (Label Atom)).toFinset).Finite :=
        ((((hextra.union hL).union (Set.finite_singleton x)).union (Set.finite_singleton z)).union
          (Γ.map LabelledFormula.lbl).toFinset.finite_toSet)
      obtain ⟨n, hnV', hnF⟩ := exists_fresh_var hV' _ hFfin
      set y₀ : Label Atom := Label.var n with hy₀def
      have hnInW : ¬ Label.InW V' y₀ := hnV'
      have hy₀L : y₀ ∉ L := fun hmem => hnF (Or.inl (Or.inl (Or.inl (Or.inr hmem))))
      have hy₀union : y₀ ∉ 𝒢.union.X := fun hmem =>
        hnF (Or.inl (Or.inl (Or.inl (Or.inl ⟨hmem, hnInW⟩))))
      have hxy₀ : x ≠ y₀ := fun heq => hnF (Or.inl (Or.inl (Or.inr (Set.mem_singleton_iff.mpr heq.symm))))
      have hzy₀ : z ≠ y₀ := fun heq => hnF (Or.inl (Or.inr (Set.mem_singleton_iff.mpr heq.symm)))
      have hΓy₀ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀ := fun ψ hψ heq =>
        hnF (Or.inr (List.mem_toFinset.mpr (heq ▸ List.mem_map_of_mem hψ)))
      have hstep : NIK 𝒯 (G.addEdge x y₀) ((y₀ ∶ A) :: Γ) (z ∶ B) := h y₀ hy₀L
      have hG' : G.addEdge x y₀ ≤ (𝒢.addEdgeAll x y₀).union :=
        le_trans (Graph.addEdge_mono hG x y₀) (𝒢.addEdge_union_le x y₀)
      have hextra' : ((𝒢.addEdgeAll x y₀).union.X \ {a : Label Atom | Label.InW V' a}).Finite := by
        rw [𝒢.addEdgeAll_union_X x y₀]
        have : (𝒢.union.X ∪ {x, y₀}) \ {a : Label Atom | Label.InW V' a} ⊆
            (𝒢.union.X \ {a : Label Atom | Label.InW V' a}) ∪ {x, y₀} := by
          intro w hw
          rcases hw.1 with hw1 | hw1
          · exact Or.inl ⟨hw1, hw.2⟩
          · exact Or.inr hw1
        exact Set.Finite.subset (hextra.union (Set.Finite.insert x (Set.finite_singleton y₀))) this
      obtain ⟨i2, hi2⟩ := ih y₀ hy₀L (𝒢.addEdgeAll x y₀) hG' hextra'
      obtain ⟨i3, h1, h2⟩ := 𝒢.dir i1 i2
      have hi1' : NIK 𝒯 (𝒢.G i3) Γ (x ∶ .diamond A) := hi1.weaken (𝒢.mono h1) (fun _ hh => hh)
      have hi2' : NIK 𝒯 ((𝒢.G i3).addEdge x y₀) ((y₀ ∶ A) :: Γ) (z ∶ B) :=
        hi2.weaken (Graph.addEdge_mono (𝒢.mono h2) x y₀) (fun _ hh => hh)
      have hy₀i3 : y₀ ∉ (𝒢.G i3).X := fun hmem => hy₀union ((𝒢.le_union i3).1 hmem)
      refine ⟨i3, .diaE L hL _ Γ x z A B hi1' (fun y _ => ?_)⟩
      exact NIK.diaWitnessTransportOld hi2' hy₀i3 hxy₀ hzy₀ hΓy₀ y

/-! ## Task 3: chain closure — scaffold, and the precise remaining gap

Simpson's own proof of the Prime Lemma fixes a **single, shared** coinfinite `V'` for the whole
Zorn poset `C` (chunk_0102.md, verbatim: *"Let `V'` be some coinfinite subset of `V` ... Consider
the set `C` of all contexts `(G',Γ') ⊇ (G,Γ)` such that the underlying set of `G'` is contained in
`W(V')`..."*) -- every chain member lives in the same `W(V')`, not merely *some* coinfinite set
each. `ChainCtx` below mirrors this precisely. -/

/-- An `ι`-indexed **chain** of contexts (Simpson's `{(Gᵢ,Γᵢ)}ᵢ∈I`, `:5990`): monotone under
`Context.le`, directed, and confined to a single fixed coinfinite `V'` throughout. -/
structure ChainCtx (𝒯 : Set GeomAxiom) (Atom : Type u) (ι : Type u) [Preorder ι] where
  /-- The chain's contexts. -/
  C : ι → Context 𝒯 Atom
  /-- Monotonicity under `Context.le`: `i ≤ j → C i ≤ C j`. -/
  mono : Monotone C
  /-- The chain is directed (in particular, any totally-ordered `ι` qualifies). -/
  dir : Directed (· ≤ ·) (id : ι → ι)
  /-- The single coinfinite reserve shared by every chain member (Simpson's fixed `V'`). -/
  V' : Set PrefixVar
  hV' : Coinfinite V'
  /-- Every chain member's underlying set lies in `W(V')`. -/
  hCV' : ∀ i, ∀ x ∈ (C i).G.X, Label.InW V' x

namespace ChainCtx

variable {ι : Type u} [Preorder ι] (𝒞 : ChainCtx 𝒯 Atom ι)

/-- The union graph `⋃ᵢ Gᵢ`. -/
def unionG [Nonempty ι] : Graph Atom where
  X := ⋃ i, (𝒞.C i).G.X
  R := fun x y => ∃ i, (𝒞.C i).G.R x y
  nonempty := by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    obtain ⟨p, hp⟩ := (𝒞.C i₀).G.nonempty
    exact ⟨p, Set.mem_iUnion.mpr ⟨i₀, hp⟩⟩
  edge_mem := by
    rintro x y ⟨i, hi⟩
    obtain ⟨hx, hy⟩ := (𝒞.C i).G.edge_mem x y hi
    exact ⟨Set.mem_iUnion.mpr ⟨i, hx⟩, Set.mem_iUnion.mpr ⟨i, hy⟩⟩

/-- The union formula set `⋃ᵢ Γᵢ`. -/
def unionΓ : Set (LabelledFormula Atom) := ⋃ i, (𝒞.C i).Γ

/-! ## Joint follow-up dispatch (task 517): sharpened root-cause diagnosis of the "old label"
obstacle shared by `deriv_reflect` (below) and `dwitness_mem_of_maximal` (Phase 4 section)

**Re-investigated fresh in this dispatch** (on top of the two candidate routes (a)/(b) the plan
and the two prior handoffs already named and could not close): three further, independently
plausible shortcuts were tried and are now **provably ruled out**, sharpening the diagnosis from
"needs a different construction" to a precise account of *why* no purely local fix exists.

**The core tension.** `NIK.boxI`/`NIK.diaE`'s cofinite-quantification encoding (`Deduction.lean`'s
module docstring: chosen, POPLmark-style, "to make weakening... immediate, without a separate
renaming/permutation lemma") gives EQUIVARIANCE (uniform behaviour under relabelling) **for
free only when the cofinite family is built by a uniform, swap-invariant construction** (exactly
what `NIK.swap_relabel`-style proofs do, bottom-up, when *introducing* a fresh witness). It does
**not** give, for free, a way to *recover* a cofinite family from a single instance obtained via
an **existential** (choice-based) argument — a Zorn-maximal element, or an induction hypothesis
that only supplies "for the specific `y` you feed it, *some* chain index/graph exists," with no
uniformity promised across different `y`. Reconstructing the cofinite family from one witness
needs either (i) a single object (index / graph) that already dominates *every* label the family
ranges over — impossible in general when the "already-old" label set is unboundedly indexed and
possibly infinite — or (ii) an external invariant limiting which labels can *ever* be "old" in
the first place (this is exactly candidate route (a)).

**Shortcut 1 (ruled out): redefine `Deriv` with a finite-subgraph existential.** Simpson's own
`:5090` bundles relational open assumptions (`y₁Rz₁,…,yₘRzₘ`) into the *same finite* list as
formula open assumptions (`x₁:A₁,…,xₙ:Aₙ`) — suggesting `Deriv 𝒯 G Γ φ` should perhaps
existentially quantify over a **finite sub-graph** `G₀ ≤ G`, not just a finite sub-list of `Γ`
(as it currently does; `Context.lean`'s `Deriv` passes the *whole*, possibly-infinite `G`
straight through to `NIK`). Tested: this does **not** help. The identical `boxI`/`diaE` case
would then need a *single* finite `G₀` valid **uniformly across the whole cofinite family**
(`∀y∉L, NIK 𝒯 (G₀.addEdge x y) Γ (y:A)`), and by the same argument as below, different `y`'s
sub-derivations can each need a genuinely different finite `G₀_y` with no common finite bound —
the obstruction re-appears one level down, unchanged in kind. This is not a `Deriv` transcription
defect; it is intrinsic to the cofinite encoding.

**Shortcut 2 (ruled out): skip the swap, reuse the induction hypothesis directly at each "old"
`y`.** For `y ∈ (C i).G.X` (chain setting) this genuinely *does* supply `∃ i_y, NIK 𝒯 (C i_y).G
Γ₀ (y:A)` with no relabelling needed. But `i_y` depends on `y`, and `ChainCtx.dir` (`Directed`)
only bounds **finitely many** indices at once (two at a time, extended finitely by induction);
nothing bounds the *unboundedly-indexed*, potentially infinite family `{i_y | y old, y ∉ L}` by
one shared index. The same difficulty that blocked the swap route blocks the no-swap route.

**Shortcut 3 (ruled out as a general fix, but recorded as a genuine conditional strengthening):**
if `ChainCtx` carried an extra hypothesis "`∃ i*, ∀ y ∈ unionG.X, InW V' y → False → y ∈ (C
i*).G.X`" (i.e. a single index already dominates *every* old label appearing anywhere in the
union), reflection *would* close: combine `i*` with the fresh-witness index `i₀` via
`𝒞.dir` applied to the two-element set `{i₀, i*}`. This is a real, provable implication — but it
is a **strengthening of `ChainCtx`'s hypotheses**, not a consequence of its current (merely
`Directed`, not bounded) definition; nothing in `primeC`/`primeC_chain_bddAbove` currently
supplies such an `i*`, and supplying one in general requires exactly what route (a) needs: a
construction where "old" labels are provably confined to a boundable set at every stage.

**Conclusion (sharper than the prior two handoffs, same eventual recommendation): both
`deriv_reflect` and `dwitness_mem_of_maximal` need route (a) — a step-indexed / well-founded
Lindenbaum construction (transfinite recursion, since `Atom : Type u` is not assumed countable,
so Simpson's own "denumerable ⟹ choice-free iterative construction" remark, `chunk_0103.md`, does
not directly bound the recursion at `ω`) that maintains, as an *invariant carried through every
step*, "every label in the domain built so far is either in the base `G₀.G.X` or was adjoined at
some step as a fresh, reserve-drawn (or `dwitness`-of-already-known) label." No such construction
exists in this file or in Mathlib's `zorn_le₀` (a bare, non-constructive existence result). This
is a substantial, independently-scoped undertaking — re-deriving Phase 4's whole
`primeC`/`primeC_chain_bddAbove`/`primeC_exists_maximal` apparatus via well-founded recursion
instead of `zorn_le₀` — not a fix expressible as a single additional lemma in this file. It should
be planned as its own dedicated multi-phase effort (a "Phase 4.5") rather than re-attempted as a
quick follow-up dispatch. -/

/-- **CLOSED (Task 517 Phase 6)**, superseding the "documented strategic sorry" writeup this
docstring used to carry (kept as history in the module section above). The fix is
`NIK.reflectChain`: the "old label" obstacle the module analysis above diagnoses only blocks a
**swap**-based transport or a **no-relabeling** reuse of the induction hypothesis (Shortcuts
above); the **one-directional** `substFn`-based transport (`NIK.oldLabelTransport`, built from
`NIK.relabelFresh`) needs freshness of only the *source* witness, so a single reflected chain
index already supplies the *entire* cofinite family. `deriv_reflect` packages `𝒞` as a `GChain`
(dropping the `Context` fields `NIK.reflectChain` never reads), reflects the `Deriv`-level
witnessing `NIK`-derivation via `NIK.reflectChain`, then finds a single chain index covering the
witnessing (finite) formula list via `exists_index_of_subset_unionΓ` and merges the two indices
via `𝒞.dir`. -/
theorem exists_index_of_subset_unionΓ [Nonempty ι] (𝒞 : ChainCtx 𝒯 Atom ι)
    (Γ₀ : List (LabelledFormula Atom)) (hΓ₀ : ∀ ψ ∈ Γ₀, ψ ∈ 𝒞.unionΓ) :
    ∃ i, ∀ ψ ∈ Γ₀, ψ ∈ (𝒞.C i).Γ := by
  induction Γ₀ with
  | nil =>
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨i, fun ψ hψ => absurd hψ (List.not_mem_nil)⟩
  | cons ψ Γ₀ ihΓ₀ =>
      obtain ⟨i1, hi1⟩ := ihΓ₀ (fun χ hχ => hΓ₀ χ (List.mem_cons_of_mem _ hχ))
      obtain ⟨i2, hi2⟩ := Set.mem_iUnion.mp (hΓ₀ ψ List.mem_cons_self)
      obtain ⟨i3, h1, h2⟩ := 𝒞.dir i1 i2
      refine ⟨i3, fun χ hχ => ?_⟩
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (𝒞.mono h2).2 hi2
      · exact (𝒞.mono h1).2 (hi1 χ hχ)

theorem deriv_reflect [Nonempty ι] {φ : LabelledFormula Atom} :
    Deriv 𝒯 (𝒞.unionG) 𝒞.unionΓ φ → ∃ i, Deriv 𝒯 (𝒞.C i).G (𝒞.C i).Γ φ := by
  rintro ⟨Γ₀, hΓ₀, hNIK⟩
  set 𝒢₀ : GChain Atom ι := ⟨fun i => (𝒞.C i).G, fun i j hij => (𝒞.mono hij).1, 𝒞.dir⟩ with h𝒢₀def
  have hG₀ : 𝒞.unionG ≤ 𝒢₀.union := ⟨fun _ h => h, fun _ _ h => h⟩
  have hextra₀ : (𝒢₀.union.X \ {a : Label Atom | Label.InW 𝒞.V' a}).Finite := by
    have heq : 𝒢₀.union.X \ {a : Label Atom | Label.InW 𝒞.V' a} = ∅ := by
      rw [Set.diff_eq_empty]
      intro z hz
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      exact 𝒞.hCV' i z hzi
    rw [heq]
    exact Set.finite_empty
  obtain ⟨i, hi⟩ := NIK.reflectChain 𝒞.hV' hNIK 𝒢₀ hG₀ hextra₀
  obtain ⟨i', hi'⟩ := 𝒞.exists_index_of_subset_unionΓ Γ₀ hΓ₀
  obtain ⟨i'', h1, h2⟩ := 𝒞.dir i i'
  exact ⟨i'', Γ₀, fun ψ hψ => (𝒞.mono h2).2 (hi' ψ hψ), hi.weaken (𝒞.mono h1).1 (fun _ h => h)⟩

/-- **Chain closure** (Phase 3 Task 3): if no chain member derives the excluded formula, neither
does the union -- the fact the Zorn chain-closure step (Phase 4) needs to show `(⋃Gᵢ,⋃Γᵢ) ∈ C`.
Immediate contrapositive of `deriv_reflect`; carries no additional proof burden once that theorem
lands. -/
theorem chain_closure [Nonempty ι] {x : Label Atom} {A : Proposition Atom}
    (hC : ∀ i, ¬ Deriv 𝒯 (𝒞.C i).G (𝒞.C i).Γ (x ∶ A)) : ¬ Deriv 𝒯 (𝒞.unionG) 𝒞.unionΓ (x ∶ A) :=
  fun h => let ⟨i, hi⟩ := 𝒞.deriv_reflect h; hC i hi

end ChainCtx

/-! ## Task 517 Phase 4 — Bounded Prime Lemma (Simpson 5.3.1) — Zorn over whole contexts

**Objective** (plan `11_tprime-repair-cs5-completeness.md`, Phase 4): `Γ ⊬_G x:A ⟹ ∃ 𝒯-prime
(H,Δ) ⊇ (G,Γ)` with `Δ ⊬_H x:A` — Simpson's Prime Lemma 5.3.1 (`chunk_0102.md`/`chunk_0103.md`,
p. 92-93 raster), a Zorn maximalisation over **whole contexts** (`Context 𝒯 Atom`), producing an
inhabitant of the repaired `TPrime`.

## `--lit` research resolution: unbounded (Ch 5) vs bounded (Ch 7-8) form

The plan flagged a genuine open risk: whether the *bounded* prime lemma (Ch 7-8, Lemma 8.2.6) is
needed, or the *unbounded* Chapter 5 form (5.3.1) suffices. **Resolved here, against the raster**:
Simpson's Chapter 8 bounded canonical model (`chunk_0165.md`/`chunk_0166.md`) states Lemma 8.2.5
— *"If `(H,Δ)` is a 𝒯-prime **bounded** context then `T-Comp(H) ⊨_cl 𝒯`"* — i.e. in the *bounded*
framework, primeness of `(H,Δ)` does **NOT** entail that the raw relation `H.R` classically models
`𝒯`; that only holds of the **separately-constructed completion** `T-Comp(H)`, built *after*
primeness is established, and the bounded canonical model's relation is `R_{(H,Δ)}(x,y)` iff
`xRy` in `T-Comp(H)` (`chunk_0166.md`), not raw `H.R`. This means the bounded route's notion of
"𝒯-prime" is **NOT** the type already landed as `TPrime` (`Context.lean`), whose clause 0
(`clModel : ClassicalModelOn 𝒯 G.X G.R`) is stated for the **raw** relation. `TPrime` — as landed —
is unmistakably a Chapter-5-style (**unbounded**) definition: Simpson's own proof of the
*unbounded* Prime Lemma 5.3.1 (`chunk_0102.md`, *"First, we show that H is a classical model of
𝒯"*) derives clause 0 for the **raw** `H` directly, with no separate completion step, as part of
the very same maximality argument used for the other four clauses. Since the landed `TPrime`
already requires raw clause 0, **the unbounded Chapter 5 form is the one that matches it**, and is
what this file transcribes; the plan's Phase 5 ("T-Comp graph completion … symmetry") is
consequently unneeded for a `TPrime`-typed target, flagged here (and in this dispatch's handoff)
for the orchestrator/user to reconsider rather than silently skipped or forced through.

## Clause 0 without an existential witness search: the "redundant edge" argument

Simpson's own clause-0 argument (`chunk_0102.md`) is written for the *general* geometric-sequent
shape, which admits a disjunctive, existentially-witnessed conclusion (`GeomAxiom`'s absent
`k`-ary witness case, see `Deduction.lean`'s docstring); its maximality step searches for a vector
of *fresh* witness variables. `GeomAxiom` (`T`, `B`, `Four`, `Five`) is **entirely** Horn, with
**no** existential conclusion (`m = 1`, witness vector length `0`) — so that general argument's
witness-search machinery does not directly transcribe, and this file reconstructs the specialised
Horn-only argument from Simpson's *stated property* ("H is a classical model of 𝒯"), per the
plan's transcription discipline. The reconstruction: `NIK`'s only graph-reading rules (`boxE`,
`diaI`) consume `TClosure 𝒯 G.R`, **not** the raw relation; since `T`, `B`, `Four` are exactly the
constructors `TClosure` itself already closes under (`.refl`, `.symm`, `.trans`), **any edge `x R
y` that is already `𝒯`-closure-derivable from the raw relation adds no new `NIK`-derivations when
adjoined as a raw edge** (`NIK.drop_redundant_edge` below). This is precisely the fact needed to
run the *same* Lindenbaum-style maximality argument Simpson uses for the other four clauses,
specialised to graph edges: if `H` lacked a `T`/`B`/`Four`-required raw edge, adjoining it would
keep the extended context in the poset `C` (no new derivations), forcing the extension to equal
`H` by maximality — i.e. the edge was already present.

## Contents

- `TClosure.mono'`: **closure-under-closure monotonicity** — `TClosure` is closed under any
  relation whose edges are individually `𝒯`-closure-derivable from a target relation (subsumes
  `TClosure.mono`, whose `hmono` conclusion is the weaker raw-relation case).
- `NIK.weaken_tclosure`: **`TClosure`-aware weakening** — a strict generalisation of
  `Deduction.lean`'s `NIK.weaken`: the graph condition is relaxed from raw inclusion (`G ≤ G'`) to
  `𝒯`-closure inclusion (`∀ a b, TClosure 𝒯 G.R a b → TClosure 𝒯 G'.R a b`), which is exactly what
  the "redundant edge" argument needs.
- `TClosure.addEdge_redundant`: adjoining an edge already `𝒯`-closure-derivable does not change the
  `𝒯`-closure at all.
- `NIK.drop_redundant_edge`: the corollary consumed by clause 0's maximality argument — a
  `NIK`-derivation over a graph with one closure-redundant edge adjoined transfers back down.
- `ChainCtx.unionContext`: packages `ChainCtx.unionG`/`unionΓ` (Phase 3) into a genuine
  `Context 𝒯 Atom` (`ctxSubset`/`coinfinite`/`dwitnessMem`) — the missing piece Phase 3 did not
  need for the reflection theorem alone but Phase 4's Zorn upper-bound step does.
- `primeC`: Simpson's poset `C` (`:5990`) — contexts extending `(G₀,Γ₀)`, confined to `W(V')`,
  that still fail to derive the excluded `x₀:A₀`.
- `primeC_exists_maximal`: Zorn's lemma applied to `primeC` (via `zorn_le₀`), using
  `ChainCtx.chain_closure` (Phase 3) for the chain upper bound.
- `primeLemma`: **Simpson's Prime Lemma 5.3.1**, assembled.

## Provenance

Literature: `chunk_0102.md`, `chunk_0103.md` (Lemma 5.3.1, the Prime Lemma proof, §5.3);
`chunk_0165.md`, `chunk_0166.md` (Lemma 8.2.5/8.2.6, the *bounded* route, consulted to resolve the
plan's flagged unbounded-vs-bounded risk, see above). PDF offset +9.
-/

/-- **Closure-under-closure monotonicity.** `TClosure` is closed under any relation each of whose
edges is individually `𝒯`-closure-derivable from a target relation `R'` — a strengthening of
`TClosure.mono` (`Deduction.lean`), whose `hmono` hypothesis only supplies *raw* `R'`-edges. -/
theorem TClosure.mono' {R R' : Label Atom → Label Atom → Prop}
    (hmono : ∀ a b, R a b → TClosure 𝒯 R' a b) {a b : Label Atom} (h : TClosure 𝒯 R a b) :
    TClosure 𝒯 R' a b := by
  induction h with
  | base h => exact hmono _ _ h
  | refl h a => exact .refl h a
  | symm h _ ih => exact .symm h ih
  | trans h _ _ ihab ihbc => exact .trans h ihab ihbc
  | eucl h _ _ ihab ihac => exact .eucl h ihab ihac

/-- **`𝒯`-closure-aware weakening.** A strict generalisation of `Deduction.lean`'s `NIK.weaken`:
the graph hypothesis is relaxed from raw inclusion (`G ≤ G'`) to `𝒯`-closure inclusion. Proof
mirrors `NIK.weaken`'s case shape exactly; only the graph-dependent cases (`boxE`, `boxI`, `diaI`,
`diaE`) differ, consuming `hR`/`TClosure.mono'` in place of `hG`/`TClosure.mono`. -/
theorem NIK.weaken_tclosure {G G' : Graph Atom} {Γ Δ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIK 𝒯 G Γ φ)
    (hR : ∀ a b, TClosure 𝒯 G.R a b → TClosure 𝒯 G'.R a b) (hΓ : ∀ ψ ∈ Γ, ψ ∈ Δ) :
    NIK 𝒯 G' Δ φ := by
  induction h generalizing G' Δ with
  | assumption G Γ φ hmem => exact .assumption G' Δ φ (hΓ _ hmem)
  | efq G Γ x y A _ ih => exact .efq G' Δ x y A (ih hR hΓ)
  | andI G Γ x A B _ _ ihA ihB => exact .andI G' Δ x A B (ihA hR hΓ) (ihB hR hΓ)
  | andE1 G Γ x A B _ ih => exact .andE1 G' Δ x A B (ih hR hΓ)
  | andE2 G Γ x A B _ ih => exact .andE2 G' Δ x A B (ih hR hΓ)
  | orI1 G Γ x A B _ ih => exact .orI1 G' Δ x A B (ih hR hΓ)
  | orI2 G Γ x A B _ ih => exact .orI2 G' Δ x A B (ih hR hΓ)
  | orE G Γ x y A B C _ _ _ ihor ihA ihB =>
      refine .orE G' Δ x y A B C (ihor hR hΓ) (ihA hR ?_) (ihB hR ?_)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impI G Γ x A B _ ih =>
      refine .impI G' Δ x A B (ih hR ?_)
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impE G Γ x A B _ _ ihimp ihA => exact .impE G' Δ x A B (ihimp hR hΓ) (ihA hR hΓ)
  | boxE G Γ x y A hRxy _ ih => exact .boxE G' Δ x y A (hR x y hRxy) (ih hR hΓ)
  | boxI L hL G Γ x A h ih =>
      refine .boxI L hL G' Δ x A ?_
      intro y hy
      have hR' : ∀ a b, TClosure 𝒯 (G.addEdge x y).R a b → TClosure 𝒯 (G'.addEdge x y).R a b := by
        intro a b
        refine TClosure.mono' (fun p q hpq => ?_)
        rcases hpq with hpq | ⟨rfl, rfl⟩
        · exact (hR p q (.base hpq)).mono (fun _ _ h => Or.inl h)
        · exact .base (Or.inr ⟨rfl, rfl⟩)
      exact ih y hy hR' hΓ
  | diaI G Γ x y A hRxy _ ih => exact .diaI G' Δ x y A (hR x y hRxy) (ih hR hΓ)
  | diaE L hL G Γ x z A B _ _ ihdia ih =>
      refine .diaE L hL G' Δ x z A B (ihdia hR hΓ) ?_
      intro y hy
      have hR' : ∀ a b, TClosure 𝒯 (G.addEdge x y).R a b → TClosure 𝒯 (G'.addEdge x y).R a b := by
        intro a b
        refine TClosure.mono' (fun p q hpq => ?_)
        rcases hpq with hpq | ⟨rfl, rfl⟩
        · exact (hR p q (.base hpq)).mono (fun _ _ h => Or.inl h)
        · exact .base (Or.inr ⟨rfl, rfl⟩)
      refine ih y hy hR' ?_
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)

/-- **Closure invariance under a redundant edge.** Adjoining an edge `(x,y)` that is already
`𝒯`-closure-derivable from `R` does not change the `𝒯`-closure at all. -/
theorem TClosure.addEdge_redundant {R : Label Atom → Label Atom → Prop} {x y : Label Atom}
    (hxy : TClosure 𝒯 R x y) :
    ∀ a b, TClosure 𝒯 (fun p q => R p q ∨ (p = x ∧ q = y)) a b ↔ TClosure 𝒯 R a b := by
  intro a b
  constructor
  · intro h
    induction h with
    | base h =>
        rcases h with h | ⟨rfl, rfl⟩
        · exact .base h
        · exact hxy
    | refl h a => exact .refl h a
    | symm h _ ih => exact .symm h ih
    | trans h _ _ ihab ihbc => exact .trans h ihab ihbc
    | eucl h _ _ ihab ihac => exact .eucl h ihab ihac
  · exact TClosure.mono (fun _ _ h => Or.inl h)

/-- **The corollary clause 0's maximality argument consumes.** A `NIK`-derivation over a graph
extended by one `𝒯`-closure-redundant edge transfers back down to the un-extended graph — adjoining
a redundant edge adds no derivation power. -/
theorem NIK.drop_redundant_edge {G : Graph Atom} {x y : Label Atom} (hxy : TClosure 𝒯 G.R x y)
    {Γ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom} (h : NIK 𝒯 (G.addEdge x y) Γ φ) :
    NIK 𝒯 G Γ φ :=
  h.weaken_tclosure (fun a b hab => (TClosure.addEdge_redundant hxy a b).mp hab) (fun _ hψ => hψ)

/-! ### Packaging the chain union as a genuine `Context` -/

variable {ι : Type u} [Preorder ι]

/-- **The chain union, packaged as a genuine `Context 𝒯 Atom`.** Phase 3's `unionG`/`unionΓ`
produced only the graph and formula-set; the Zorn upper-bound step needs the union to satisfy
`Context`'s own three side conditions (`ctxSubset`, `coinfinite`, `dwitnessMem`), each following
directly from every chain member already being a genuine `Context` sharing the chain's single
reserve `V'` (`hV'`/`hCV'`). -/
def ChainCtx.unionContext [Nonempty ι] (𝒞 : ChainCtx 𝒯 Atom ι) : Context 𝒯 Atom where
  G := 𝒞.unionG
  Γ := 𝒞.unionΓ
  ctxSubset := by
    rintro φ hφ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hφ
    exact Set.mem_iUnion.mpr ⟨i, (𝒞.C i).ctxSubset φ hi⟩
  coinfinite := ⟨𝒞.V', 𝒞.hV', fun x hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact 𝒞.hCV' i x hi⟩
  dwitnessMem := by
    rintro x A hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hR, hmem⟩ := (𝒞.C i).dwitnessMem x A hi
    exact ⟨⟨i, hR⟩, Set.mem_iUnion.mpr ⟨i, hmem⟩⟩

/-- Every chain member is `≤` the union context (Simpson's "`(⋃Gᵢ,⋃Γᵢ)` is an upper bound",
`chunk_0102.md`), at the level of the actual `Context.le` order, not merely the raw
`Graph`/`Set` inclusions `unionG`/`unionΓ` individually satisfy. -/
theorem ChainCtx.le_unionContext [Nonempty ι] (𝒞 : ChainCtx 𝒯 Atom ι) (i : ι) :
    𝒞.C i ≤ 𝒞.unionContext :=
  ⟨⟨fun _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩, fun _ _ hxy => ⟨i, hxy⟩⟩,
    fun _ hφ => Set.mem_iUnion.mpr ⟨i, hφ⟩⟩

/-! ### Simpson's poset `C` and the Zorn maximal element -/

section PrimeC

variable (G₀ : Context 𝒯 Atom) (x₀ : Label Atom) (A₀ : Proposition Atom)

/-- **Simpson's poset `C`** (`:5990`, *"the set `C` of all contexts `(G',Γ') ⊇ (G,Γ)` such that
the underlying set of `G'` is contained in `W(V')` and `Γ' ⊬_G' x:A`"*): contexts extending
`(G₀,Γ₀)`, confined to the reserve `V' := G₀.coinfinite.choose` (Simpson fixes *one* shared `V'`
for the whole poset, taken from the base context's own clause-1 witness — matching `ChainCtx`'s
single shared `V'`), that still fail to derive the excluded `x₀:A₀`. -/
def primeC : Set (Context 𝒯 Atom) :=
  {D | G₀ ≤ D ∧ (∀ x ∈ D.G.X, Label.InW G₀.coinfinite.choose x) ∧
    ¬ Deriv 𝒯 D.G D.Γ (x₀ ∶ A₀)}

/-- The base context `(G₀,Γ₀)` is itself in `C`, given the defining hypothesis
`Γ₀ ⊬_{G₀} x₀:A₀` — `C` is nonempty. -/
theorem primeC_mem_base (h : ¬ Deriv 𝒯 G₀.G G₀.Γ (x₀ ∶ A₀)) : G₀ ∈ primeC G₀ x₀ A₀ :=
  ⟨Context.le_refl G₀, G₀.coinfinite.choose_spec.2, h⟩

/-- **Every chain in `C` has an upper bound in `C`** (Simpson: *"It is easily seen that
`(⋃ᵢGᵢ,⋃ᵢΓᵢ)` is also in `C`. So every chain in `C` has an upper bound."*, `chunk_0102.md`).
Packages the chain as a `ChainCtx` sharing the poset's fixed reserve `V' :=
G₀.coinfinite.choose`, and reuses Phase 3's `chain_closure` for the one nontrivial conjunct
(`¬ Deriv`). Takes membership of the base context as an explicit hypothesis (`h0`) rather than
re-deriving it, so the empty-chain case has an upper-bound witness available. -/
theorem primeC_chain_bddAbove (h0 : G₀ ∈ primeC G₀ x₀ A₀) (c : Set (Context 𝒯 Atom))
    (hc : c ⊆ primeC G₀ x₀ A₀) (hchain : IsChain (· ≤ ·) c) :
    ∃ ub ∈ primeC G₀ x₀ A₀, ∀ z ∈ c, z ≤ ub := by
  rcases c.eq_empty_or_nonempty with hempty | hne
  · exact ⟨G₀, h0, by simp [hempty]⟩
  · haveI : Nonempty ↥c := hne.to_subtype
    let 𝒞 : ChainCtx 𝒯 Atom ↥c :=
      { C := Subtype.val
        mono := fun _ _ hab => hab
        dir := fun a b => by
          obtain ⟨z, hz, haz, hbz⟩ := hchain.directedOn a.val a.property b.val b.property
          exact ⟨⟨z, hz⟩, haz, hbz⟩
        V' := G₀.coinfinite.choose
        hV' := G₀.coinfinite.choose_spec.1
        hCV' := fun i x hx => (hc i.property).2.1 x hx }
    refine ⟨𝒞.unionContext, ⟨?_, ?_, ?_⟩, fun z hz => 𝒞.le_unionContext ⟨z, hz⟩⟩
    · obtain ⟨i₀⟩ := (inferInstance : Nonempty ↥c)
      exact Context.le_trans (hc i₀.property).1 (𝒞.le_unionContext i₀)
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact (hc i.property).2.1 x hi
    · exact 𝒞.chain_closure (fun i => (hc i.property).2.2)

/-- **Zorn's Lemma applied to `C`**: `C` has a maximal element (Simpson: *"Therefore, by Zorn's
Lemma, `C` has a maximal element `(H,Δ)`."*, `chunk_0102.md`). -/
theorem primeC_exists_maximal (h0 : G₀ ∈ primeC G₀ x₀ A₀) :
    ∃ H, Maximal (· ∈ primeC G₀ x₀ A₀) H :=
  zorn_le₀ (primeC G₀ x₀ A₀) (fun c hc hchain => primeC_chain_bddAbove G₀ x₀ A₀ h0 c hc hchain)

end PrimeC

/-! ### Discharging the four numbered clauses plus clause 0 (𝒯-primeness of the maximal element) -/

/-- If both endpoints of an adjoined edge already lie in `G.X`, `addEdge` leaves the node set
unchanged. -/
theorem Graph.addEdge_X_eq_of_mem {G : Graph Atom} {a b : Label Atom} (ha : a ∈ G.X)
    (hb : b ∈ G.X) : (G.addEdge a b).X = G.X := by
  apply subset_antisymm
  · rintro z (hz | rfl | rfl)
    · exact hz
    · exact ha
    · exact hb
  · exact Set.subset_union_left

/-- Extending a context by one edge between two of its **own** labels stays a genuine `Context`
(same `Γ`, same `V'`-confinement — `X` is literally unchanged, `Graph.addEdge_X_eq_of_mem`). -/
def Context.addRedundantEdge (H : Context 𝒯 Atom) (a b : Label Atom) (ha : a ∈ H.G.X)
    (hb : b ∈ H.G.X) : Context 𝒯 Atom where
  G := H.G.addEdge a b
  Γ := H.Γ
  ctxSubset := fun φ hφ => (Graph.addEdge_X_eq_of_mem ha hb) ▸ H.ctxSubset φ hφ
  coinfinite :=
    let ⟨V', hV', hX⟩ := H.coinfinite
    ⟨V', hV', fun x hx => hX x ((Graph.addEdge_X_eq_of_mem ha hb) ▸ hx)⟩
  dwitnessMem := fun x A hx =>
    let ⟨hR, hmem⟩ := H.dwitnessMem x A ((Graph.addEdge_X_eq_of_mem ha hb) ▸ hx)
    ⟨Or.inl hR, hmem⟩

theorem Context.addRedundantEdge_le (H : Context 𝒯 Atom) (a b : Label Atom) (ha : a ∈ H.G.X)
    (hb : b ∈ H.G.X) : H ≤ H.addRedundantEdge a b ha hb :=
  ⟨⟨fun _ hx => Or.inl hx, fun _ _ hxy => Or.inl hxy⟩, Set.Subset.refl _⟩

/-- **The maximality argument, specialised to graph edges.** If `H` is maximal in `C` and an edge
`(a,b)` between two of `H`'s own labels is already `𝒯`-closure-derivable, the raw edge must
already be present in `H.G.R` — else adjoining it (`Context.addRedundantEdge`) would keep the
extension in `C` (`NIK.drop_redundant_edge` shows no new derivations arise), forcing the
extension to equal `H` by maximality, i.e. the edge was already there. This is Simpson's
Lindenbaum-style maximality pattern (`chunk_0102.md`), specialised via the "redundant edge"
reconstruction (module docstring) to discharge clause 0 without an existential witness search. -/
theorem raw_edge_of_tclosure {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) {a b : Label Atom}
    (ha : a ∈ H.G.X) (hb : b ∈ H.G.X) (hclosed : TClosure 𝒯 H.G.R a b) : H.G.R a b := by
  by_contra hcontra
  have hle : H ≤ H.addRedundantEdge a b ha hb := H.addRedundantEdge_le a b ha hb
  have hmem : H.addRedundantEdge a b ha hb ∈ primeC G₀ x₀ A₀ := by
    obtain ⟨hG₀H, hV', hnd⟩ := hmax.prop
    refine ⟨Context.le_trans hG₀H hle, ?_, ?_⟩
    · intro x hx
      exact hV' x ((Graph.addEdge_X_eq_of_mem ha hb) ▸ hx)
    · intro hDeriv
      apply hnd
      obtain ⟨Γ₀, hΓ₀, hNIK⟩ := hDeriv
      exact ⟨Γ₀, hΓ₀, NIK.drop_redundant_edge hclosed hNIK⟩
  have hge := hmax.le_of_ge hmem hle
  exact hcontra (hge.1.2 a b (Or.inr ⟨rfl, rfl⟩))

/-- **Clause 0** (`TPrime.clModel`): the maximal element's raw graph relation is a domain-relative
classical model of `𝒯` (Simpson `chunk_0102.md`, *"First, we show that H is a classical model of
𝒯"*), mechanized via `raw_edge_of_tclosure` for each Horn axiom `T`/`B`/`Four`/`Five` (module
docstring, "Clause 0 without an existential witness search"). -/
theorem clModel_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) :
    ClassicalModelOn 𝒯 H.G.X H.G.R := by
  intro χ hχ
  cases χ with
  | T => exact fun x hx => raw_edge_of_tclosure hmax hx hx (.refl hχ x)
  | B => exact fun x hx y hy hxy => raw_edge_of_tclosure hmax hy hx (.symm hχ (.base hxy))
  | Four =>
      exact fun x hx y hy z hz hxy hyz =>
        raw_edge_of_tclosure hmax hx hz (.trans hχ (.base hxy) (.base hyz))
  | Five =>
      exact fun x hx y hy z hz hxy hxz =>
        raw_edge_of_tclosure hmax hy hz (.eucl hχ (.base hxy) (.base hxz))

/-- **Clause 2** (`TPrime.consistency`): consistency is immediate (Simpson `chunk_0103.md`,
*"Consistency is immediate, because `Δ ⊬_H x:A`"*) — cross-label `(⊥E)` (`NIK.efq`) turns any
`x:⊥` derivation directly into an `x₀:A₀` derivation, contradicting maximality's own `¬Deriv`
membership fact, with no Lindenbaum extension needed at all. -/
theorem consistency_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) :
    ∀ x ∈ H.G.X, ¬ Deriv 𝒯 H.G H.Γ (x ∶ Proposition.bot) := by
  intro x _ hDeriv
  obtain ⟨_, _, hnd⟩ := hmax.prop
  obtain ⟨Γ₀, hΓ₀, hNIK⟩ := hDeriv
  exact hnd ⟨Γ₀, hΓ₀, NIK.efq H.G Γ₀ x x₀ A₀ hNIK⟩

/-- Extending a context by one formula at a label already in `G.X` stays a genuine `Context`
(same `G`; `coinfinite` is `G`-only, unaffected; `dwitnessMem`'s target membership only grows). -/
def Context.addFormula (H : Context 𝒯 Atom) (φ : LabelledFormula Atom) (hφ : φ.lbl ∈ H.G.X) :
    Context 𝒯 Atom where
  G := H.G
  Γ := insert φ H.Γ
  ctxSubset := by
    intro ψ hψ
    rcases hψ with rfl | hψ
    · exact hφ
    · exact H.ctxSubset ψ hψ
  coinfinite := H.coinfinite
  dwitnessMem := fun x A hx =>
    let ⟨hR, hmem⟩ := H.dwitnessMem x A hx
    ⟨hR, Or.inr hmem⟩

theorem Context.addFormula_le (H : Context 𝒯 Atom) (φ : LabelledFormula Atom)
    (hφ : φ.lbl ∈ H.G.X) : H ≤ H.addFormula φ hφ :=
  ⟨Graph.le_refl H.G, fun _ hψ => Or.inr hψ⟩

/-- **The maximality argument, specialised to formula membership.** If `H` is maximal in `C` and
`(H, H.Γ ∪ {φ})` still fails to derive the excluded `x₀:A₀`, `φ` was already a member of `H.Γ` —
Simpson's Lindenbaum-style pattern for the deductive-closure/disjunction/diamond clauses. -/
theorem mem_of_maximal_addFormula {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) {φ : LabelledFormula Atom}
    (hφ : φ.lbl ∈ H.G.X) (hnd' : ¬ Deriv 𝒯 H.G (insert φ H.Γ) (x₀ ∶ A₀)) : φ ∈ H.Γ := by
  have hle : H ≤ H.addFormula φ hφ := H.addFormula_le φ hφ
  have hmem : H.addFormula φ hφ ∈ primeC G₀ x₀ A₀ := by
    obtain ⟨hG₀H, hV', _⟩ := hmax.prop
    exact ⟨Context.le_trans hG₀H hle, hV', hnd'⟩
  exact (hmax.le_of_ge hmem hle).2 (Set.mem_insert φ H.Γ)

/-- **`Deriv`-level `(∨E)`.** If `y:B∨C` is `Deriv`-derivable from `Γ`, and both `Γ∪{y:B}` and
`Γ∪{y:C}` `Deriv`-derive `φ`, then `Γ` alone `Deriv`-derives `φ` — the set-lifted form of
`NIK.orE`, discharging the two extension assumptions via the rule itself (no cut needed: `y:B∨C`
is combined with the two branch derivations directly). -/
theorem Deriv.orE {G : Graph Atom} {Γ : Set (LabelledFormula Atom)} {y : Label Atom}
    {B C : Proposition Atom} {φ : LabelledFormula Atom}
    (hor : Deriv 𝒯 G Γ (y ∶ Proposition.or B C)) (hB : Deriv 𝒯 G (insert (y ∶ B) Γ) φ)
    (hC : Deriv 𝒯 G (insert (y ∶ C) Γ) φ) : Deriv 𝒯 G Γ φ := by
  classical
  obtain ⟨Γ0, hΓ0, hNIK0⟩ := hor
  obtain ⟨Γ1, hΓ1, hNIK1⟩ := hB
  obtain ⟨Γ2, hΓ2, hNIK2⟩ := hC
  set Γ1' := Γ1.filter (fun ψ => decide (ψ ≠ (y ∶ B))) with hΓ1'def
  set Γ2' := Γ2.filter (fun ψ => decide (ψ ≠ (y ∶ C))) with hΓ2'def
  have hΓ1'mem : ∀ ψ ∈ Γ1', ψ ∈ Γ := by
    intro ψ hψ
    have hne : ψ ≠ (y ∶ B) := by simpa [hΓ1'def] using (List.of_mem_filter hψ)
    rcases hΓ1 ψ (List.mem_of_mem_filter hψ) with rfl | h
    · exact absurd rfl hne
    · exact h
  have hΓ2'mem : ∀ ψ ∈ Γ2', ψ ∈ Γ := by
    intro ψ hψ
    have hne : ψ ≠ (y ∶ C) := by simpa [hΓ2'def] using (List.of_mem_filter hψ)
    rcases hΓ2 ψ (List.mem_of_mem_filter hψ) with rfl | h
    · exact absurd rfl hne
    · exact h
  refine ⟨Γ0 ++ Γ1' ++ Γ2', ?_, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · rcases List.mem_append.mp hψ with hψ | hψ
      · exact hΓ0 ψ hψ
      · exact hΓ1'mem ψ hψ
    · exact hΓ2'mem ψ hψ
  · have hmem01 : ∀ ψ ∈ Γ0, ψ ∈ Γ0 ++ Γ1' ++ Γ2' := fun ψ hψ =>
      List.mem_append_left _ (List.mem_append_left _ hψ)
    have hmem1B : ∀ ψ ∈ Γ1, ψ ∈ (y ∶ B) :: (Γ0 ++ Γ1' ++ Γ2') := by
      intro ψ hψ
      by_cases hcase : ψ = (y ∶ B)
      · exact hcase ▸ List.mem_cons_self
      · refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ ?_))
        exact List.mem_filter.mpr ⟨hψ, by simpa using hcase⟩
    have hmem2C : ∀ ψ ∈ Γ2, ψ ∈ (y ∶ C) :: (Γ0 ++ Γ1' ++ Γ2') := by
      intro ψ hψ
      by_cases hcase : ψ = (y ∶ C)
      · exact hcase ▸ List.mem_cons_self
      · refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
        exact List.mem_filter.mpr ⟨hψ, by simpa using hcase⟩
    exact NIK.orE G (Γ0 ++ Γ1' ++ Γ2') y φ.lbl B C φ.prop
      (hNIK0.weaken (Graph.le_refl G) hmem01)
      (hNIK1.weaken (Graph.le_refl G) hmem1B) (hNIK2.weaken (Graph.le_refl G) hmem2C)

/-- **Clause 3** (`TPrime.disjunction`): the disjunction property (Simpson `chunk_0103.md`,
*"either `y:B∈Δ` or `y:C∈Δ`"*), via `Deriv.orE` + `mem_of_maximal_addFormula` for each disjunct —
no cut needed, since `y:B∨C ∈ H.Γ` is already assumable directly. -/
theorem disjunction_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) :
    ∀ (y : Label Atom) (B C : Proposition Atom), (y ∶ Proposition.or B C) ∈ H.Γ →
      (y ∶ B) ∈ H.Γ ∨ (y ∶ C) ∈ H.Γ := by
  intro y B C hmemBC
  obtain ⟨_, _, hnd⟩ := hmax.prop
  have hyX : y ∈ H.G.X := H.ctxSubset _ hmemBC
  have hyor : Deriv 𝒯 H.G H.Γ (y ∶ Proposition.or B C) :=
    ⟨[y ∶ Proposition.or B C], fun ψ hψ => (List.mem_singleton.mp hψ) ▸ hmemBC,
      NIK.assumption H.G _ _ (List.mem_singleton_self _)⟩
  by_cases hB : Deriv 𝒯 H.G (insert (y ∶ B) H.Γ) (x₀ ∶ A₀)
  · by_cases hC : Deriv 𝒯 H.G (insert (y ∶ C) H.Γ) (x₀ ∶ A₀)
    · exact absurd (Deriv.orE hyor hB hC) hnd
    · exact Or.inr (mem_of_maximal_addFormula hmax hyX hC)
  · exact Or.inl (mem_of_maximal_addFormula hmax hyX hB)

/-! ### Clause 4 (diamond property) -/

/-- **`(◇E)`-shaped freshness transport.** A corollary of `NIK.swap_relabel` (Phase 3), in the
same family as `NIK.freshWitness_transport` but for `diaE`'s premise shape (the fresh witness
labels the *assumption*, not the conclusion): a derivation witnessed at one fresh label `y₀`
transports to any other label `y`, both fresh w.r.t. the ambient graph, the pivot `x`, the
untouched conclusion label `z`, and the context `Γ`. -/
theorem NIK.diaWitness_transport {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {x z y₀ y : Label Atom} {A C : Proposition Atom}
    (h : NIK 𝒯 (G.addEdge x y₀) ((y₀ ∶ A) :: Γ) (z ∶ C)) (hy₀X : y₀ ∉ G.X) (hyX : y ∉ G.X)
    (hxy₀ : x ≠ y₀) (hxy : x ≠ y) (hzy₀ : z ≠ y₀) (hzy : z ≠ y)
    (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀ ∧ ψ.lbl ≠ y) : NIK 𝒯 (G.addEdge x y) ((y ∶ A) :: Γ) (z ∶ C) := by
  have hf : ∀ p q, (G.addEdge x y₀).R p q →
      (G.addEdge x y).R (swapFn y₀ y p) (swapFn y₀ y q) := by
    intro p q hpq
    rcases hpq with hpq | ⟨rfl, rfl⟩
    · have hp : p ≠ y₀ := fun hp => hy₀X (hp ▸ (G.edge_mem p q hpq).1)
      have hq : q ≠ y₀ := fun hq => hy₀X (hq ▸ (G.edge_mem p q hpq).2)
      have hp' : p ≠ y := fun hp => hyX (hp ▸ (G.edge_mem p q hpq).1)
      have hq' : q ≠ y := fun hq => hyX (hq ▸ (G.edge_mem p q hpq).2)
      rw [swapFn_other hp hp', swapFn_other hq hq']
      exact Or.inl hpq
    · rw [swapFn_other hxy₀ hxy, swapFn_left]
      exact Or.inr ⟨rfl, rfl⟩
  have hstep := h.swap_relabel (a := y₀) (b := y) (G' := G.addEdge x y) hf
  simp only [List.map_cons, swapFn_left, List.map_swapFn_eq_self hΓ, swapFn_other hzy₀ hzy] at hstep
  exact hstep

/-- The labels occurring in a finite context list form a finite set. -/
theorem LabelledFormula.ctxLabels_finite (Γ : List (LabelledFormula Atom)) :
    (LabelledFormula.ctxLabels Γ).Finite := by
  have heq : LabelledFormula.ctxLabels Γ = {x | x ∈ Γ.map LabelledFormula.lbl} := by
    ext x
    simp [LabelledFormula.ctxLabels, List.mem_map]
  rw [heq]
  exact (Γ.map LabelledFormula.lbl).finite_toSet

/-- Extending a context by one edge to a *fresh* diamond-witness label, together with the
witness's own formula, stays a genuine `Context`: `dwitness y B` is fresh (`hfresh`), so `X`
genuinely grows by one node, but `Label.InW`'s `dwitness` case does not consume the reserve
(`Label.InW V' (dwitness x A) := Label.InW V' x`), so confinement is inherited from `y`'s alone. -/
def Context.addDiaWitness (H : Context 𝒯 Atom) (y : Label Atom) (B : Proposition Atom)
    (hy : y ∈ H.G.X) (hfresh : Label.dwitness y B ∉ H.G.X) : Context 𝒯 Atom where
  G := H.G.addEdge y (Label.dwitness y B)
  Γ := insert (Label.dwitness y B ∶ B) H.Γ
  ctxSubset := by
    intro φ hφ
    rcases hφ with rfl | hφ
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (H.ctxSubset φ hφ)
  coinfinite := by
    obtain ⟨V', hV', hX⟩ := H.coinfinite
    refine ⟨V', hV', fun x hx => ?_⟩
    rcases hx with hx | hx | hx
    · exact hX x hx
    · rw [hx]; exact hX y hy
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hX y hy
  dwitnessMem := by
    intro x A hx
    rcases hx with hx | hx | hx
    · obtain ⟨hR, hmem⟩ := H.dwitnessMem x A hx
      exact ⟨Or.inl hR, Or.inr hmem⟩
    · obtain ⟨hR, hmem⟩ := H.dwitnessMem x A (hx ▸ hy)
      exact ⟨Or.inl hR, Or.inr hmem⟩
    · rw [Set.mem_singleton_iff] at hx
      obtain ⟨hxy, hAB⟩ := Label.dwitness.inj hx
      subst hxy; subst hAB
      exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl rfl⟩

theorem Context.addDiaWitness_le (H : Context 𝒯 Atom) (y : Label Atom) (B : Proposition Atom)
    (hy : y ∈ H.G.X) (hfresh : Label.dwitness y B ∉ H.G.X) :
    H ≤ H.addDiaWitness y B hy hfresh :=
  ⟨⟨fun _ hx => Or.inl hx, fun _ _ hxy => Or.inl hxy⟩, fun _ hφ => Or.inr hφ⟩

/-- **Structural non-self-reference**: a diamond-witness label is never equal to its own pivot --
`dwitness` strictly grows the label, so `y = Label.dwitness y B` is impossible for any `B`.
Proved by structural recursion on `y` (the only nontrivial case, `y = Label.dwitness x A`, reduces
to the same fact for the strictly smaller `x` via injectivity). Needed by
`dwitness_mem_of_maximal` (Task 517 Phase 6) to separate the excluded label `x₀` from the newly
adjoined witness `v`. -/
theorem Label.ne_dwitness_self : ∀ (y : Label Atom) (B : Proposition Atom), y ≠ Label.dwitness y B
  | .var _, _ => fun h => nomatch h
  | .dwitness x A, B => fun h => by
      injection h with h1 _
      exact Label.ne_dwitness_self x A h1

/-- **The maximality argument for the diamond witness.** If `y:◇B ∈ H.Γ`, the diamond-witness
label `dwitness y B` must already be in `H.G.X` — else adjoining it, together with the fresh edge
`y R dwitness y B` and the formula `dwitness y B : B`, keeps the extension in `C`:
`NIK.diaWitness_transport` turns the one witnessing `NIK`-derivation into a cofinite one, letting
`NIK.diaE` (fed by `y:◇B`, itself already `Γ`-assumable) rebuild a derivation of the excluded
`x₀:A₀` back over `H` alone, contradicting `hnd`. This forces the extension to equal `H`, i.e.
the witness was already present. Simpson `chunk_0103.md`: *"We show that `v_{y.B}` is in `H`."*

**`hx₀ : x₀ ∈ G₀.G.X`** (Task 517 Phase 6, new hypothesis): Simpson's own Prime Lemma statement
(`chunk_0102.md`, *"`Γ ⊬_G x:A`"*) presupposes the excluded judgement's label `x` is a label of
the ambient graph `G` -- exactly the standing convention every other `Deriv`/`NIK` judgement in
this development already carries via `Context.ctxSubset` for `Γ`'s own labels. This hypothesis
was implicit, not previously threaded explicitly; it is needed here (and nowhere else in the
already-landed clauses) to rule out the *only* case the graph-generic old-label transport
(`NIK.diaWitnessTransportOld`) cannot handle: the excluded label `x₀` coinciding with the freshly
adjoined witness `v = dwitness y B` itself, which would make the transported conclusion's label
move out from under `x₀`. Given `hx₀` and `hG₀H : G₀ ≤ H` (from `hmax`), `x₀ ∈ H.G.X`, while
`v ∉ H.G.X` (`hfresh`, the `by_contra` hypothesis) -- so `x₀ ≠ v` always, and the transport
applies unconditionally. -/
theorem dwitness_mem_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) (hx₀ : x₀ ∈ G₀.G.X) {y : Label Atom}
    {B : Proposition Atom} (hyB : (y ∶ Proposition.diamond B) ∈ H.Γ) :
    Label.dwitness y B ∈ H.G.X := by
  have hy : y ∈ H.G.X := H.ctxSubset _ hyB
  by_contra hfresh
  have hle : H ≤ H.addDiaWitness y B hy hfresh := H.addDiaWitness_le y B hy hfresh
  have hmem : H.addDiaWitness y B hy hfresh ∈ primeC G₀ x₀ A₀ := by
    obtain ⟨hG₀H, hV', hnd⟩ := hmax.prop
    refine ⟨Context.le_trans hG₀H hle, ?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx | hx
      · exact hV' x hx
      · rw [hx]; exact hV' y hy
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hV' y hy
    · intro hDeriv
      apply hnd
      classical
      obtain ⟨Γf, hΓf, hNIK⟩ := hDeriv
      set v := Label.dwitness y B
      set Γf' := Γf.filter (fun ψ => decide (ψ ≠ (v ∶ B))) with hΓf'def
      have hΓf'mem : ∀ ψ ∈ Γf', ψ ∈ H.Γ := by
        intro ψ hψ
        have hne : ψ ≠ (v ∶ B) := by simpa [hΓf'def] using (List.of_mem_filter hψ)
        rcases hΓf ψ (List.mem_of_mem_filter hψ) with rfl | h
        · exact absurd rfl hne
        · exact h
      have hΓf_sub : ∀ ψ ∈ Γf, ψ ∈ (v ∶ B) :: Γf' := by
        intro ψ hψ
        by_cases hcase : ψ = (v ∶ B)
        · exact hcase ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hψ, by simpa using hcase⟩)
      have hNIKv : NIK 𝒯 (H.G.addEdge y v) ((v ∶ B) :: Γf') (x₀ ∶ A₀) :=
        hNIK.weaken (Graph.le_refl _) hΓf_sub
      have hyor : NIK 𝒯 H.G [y ∶ Proposition.diamond B] (y ∶ Proposition.diamond B) :=
        NIK.assumption H.G _ _ (List.mem_singleton_self _)
      have hyorDeriv : Deriv 𝒯 H.G H.Γ (y ∶ Proposition.diamond B) :=
        ⟨[y ∶ Proposition.diamond B], fun ψ hψ => (List.mem_singleton.mp hψ) ▸ hyB, hyor⟩
      -- **CLOSED (Task 517 Phase 6)**: same fix as `ChainCtx.deriv_reflect` -- the module analysis
      -- this comment used to carry (swap-based transport needs target freshness; no-swap reuse
      -- needs an unboundedly-indexed family) diagnoses the obstacle correctly for the techniques
      -- it tested, but the one-directional `substFn`-based transport (`NIK.diaWitnessTransportOld`,
      -- built from `NIK.relabelFresh`) needs freshness of only the *source* witness `v`, not the
      -- target, so the single instance `hNIKv` already supplies the whole cofinite family. The one
      -- genuine extra requirement -- the excluded label `x₀` must differ from `v` itself, else the
      -- transported conclusion's label would move out from under `x₀` -- is discharged by the new
      -- `hx₀ : x₀ ∈ G₀.G.X` hypothesis (this theorem's docstring) together with `v ∉ H.G.X`
      -- (`hfresh`).
      have hx₀H : x₀ ∈ H.G.X := hG₀H.1.1 hx₀
      have hxv : x₀ ≠ v := fun heq => hfresh (heq ▸ hx₀H)
      have hyv : y ≠ v := Label.ne_dwitness_self y B
      have hΓf'lbl : ∀ ψ ∈ Γf', ψ.lbl ≠ v :=
        fun ψ hψ heq => hfresh (heq ▸ H.ctxSubset ψ (hΓf'mem ψ hψ))
      set Γcomb : List (LabelledFormula Atom) := (y ∶ Proposition.diamond B) :: Γf' with hΓcombdef
      have hΓcomb_mem : ∀ ψ ∈ Γcomb, ψ ∈ H.Γ := by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hyB
        · exact hΓf'mem ψ hψ
      have hΓcomb_lbl : ∀ ψ ∈ Γcomb, ψ.lbl ≠ v := by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hyv
        · exact hΓf'lbl ψ hψ
      have hdia : NIK 𝒯 H.G Γcomb (y ∶ Proposition.diamond B) :=
        NIK.assumption H.G Γcomb _ List.mem_cons_self
      have hNIKv' : NIK 𝒯 (H.G.addEdge y v) ((v ∶ B) :: Γcomb) (x₀ ∶ A₀) :=
        hNIKv.weaken (Graph.le_refl _) (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hψ))
      have hall : ∀ y' ∉ ({v} : Set (Label Atom)),
          NIK 𝒯 (H.G.addEdge y y') ((y' ∶ B) :: Γcomb) (x₀ ∶ A₀) :=
        fun y' _ => NIK.diaWitnessTransportOld hNIKv' hfresh hyv hxv hΓcomb_lbl y'
      exact ⟨Γcomb, hΓcomb_mem,
        NIK.diaE {v} (Set.finite_singleton v) H.G Γcomb y x₀ B A₀ hdia hall⟩
  have hge := hmax.le_of_ge hmem hle
  exact hfresh (hge.1.1 (Or.inr (Or.inr rfl)))

/-- **Clause 4** (`TPrime.diamond`): the diamond property (Simpson `chunk_0103.md`, *"`v_{y.B}`
is the variable required by the diamond property"*). Once `dwitness_mem_of_maximal` supplies
membership of the witness label, `Context.dwitnessMem` (a *field* every `Context` — including
the maximal `H` — already carries, Simpson's "requirement 2 on contexts") directly yields both
conjuncts the diamond property needs; no separate argument is required for this half. -/
theorem diamond_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) (hx₀ : x₀ ∈ G₀.G.X) :
    ∀ (y : Label Atom) (B : Proposition Atom), (y ∶ Proposition.diamond B) ∈ H.Γ →
      ∃ v, H.G.R y v ∧ (v ∶ B) ∈ H.Γ :=
  fun y B hyB => ⟨Label.dwitness y B, H.dwitnessMem y B (dwitness_mem_of_maximal hmax hx₀ hyB)⟩

/-! ### Clause 1 (deductive closure) -/

/-- **Auxiliary, `Δ`-generalized form of `NIK.subst`.** States the substitution/cut fact for an
arbitrary scrutinee context `Γ₀` together with a proof `Γ₀ = Δ' ++ (y∶B) :: Γ` pinpointing where
the cut formula sits, so that induction on the `NIK`-derivation can freely grow `Δ'` in the
`impI`/`orE`/`diaE` cases (which prepend to the front of the *whole* context) while re-weakening
the substituting derivation `hsub` to whichever graph the current case's premises live at
(`boxI`/`diaE` extend the graph by one edge via `Graph.addEdge`). `NIK.subst` below specializes
this at `Δ' := Δ`, `Γ₀ := Δ ++ (y∶B) :: Γ` via `rfl`. -/
theorem NIK.subst_aux {y : Label Atom} {B : Proposition Atom} {Γ : List (LabelledFormula Atom)} :
    ∀ {G : Graph Atom} {Γ₀ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom},
      NIK 𝒯 G Γ₀ φ → ∀ Δ' : List (LabelledFormula Atom), Γ₀ = Δ' ++ (y ∶ B) :: Γ →
      NIK 𝒯 G Γ (y ∶ B) → NIK 𝒯 G (Δ' ++ Γ) φ := by
  intro G Γ₀ φ hderiv
  induction hderiv with
  | assumption G Γ₀ φ hmem =>
      intro Δ' heq hsub
      rw [heq] at hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact .assumption G (Δ' ++ Γ) φ (List.mem_append_left _ hmem)
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hsub.weaken (Graph.le_refl _) (fun ψ hψ => List.mem_append_right _ hψ)
        · exact .assumption G (Δ' ++ Γ) φ (List.mem_append_right _ hmem)
  | efq G Γ₀ x y0 A _ ih =>
      intro Δ' heq hsub
      exact .efq G (Δ' ++ Γ) x y0 A (ih Δ' heq hsub)
  | andI G Γ₀ x A B' _ _ ihA ihB =>
      intro Δ' heq hsub
      exact .andI G (Δ' ++ Γ) x A B' (ihA Δ' heq hsub) (ihB Δ' heq hsub)
  | andE1 G Γ₀ x A B' _ ih =>
      intro Δ' heq hsub
      exact .andE1 G (Δ' ++ Γ) x A B' (ih Δ' heq hsub)
  | andE2 G Γ₀ x A B' _ ih =>
      intro Δ' heq hsub
      exact .andE2 G (Δ' ++ Γ) x A B' (ih Δ' heq hsub)
  | orI1 G Γ₀ x A B' _ ih =>
      intro Δ' heq hsub
      exact .orI1 G (Δ' ++ Γ) x A B' (ih Δ' heq hsub)
  | orI2 G Γ₀ x A B' _ ih =>
      intro Δ' heq hsub
      exact .orI2 G (Δ' ++ Γ) x A B' (ih Δ' heq hsub)
  | orE G Γ₀ x y0 A B' C _ _ _ ihor ihA ihB =>
      intro Δ' heq hsub
      refine .orE G (Δ' ++ Γ) x y0 A B' C (ihor Δ' heq hsub) ?_ ?_
      · exact ihA ((x ∶ A) :: Δ') (by rw [heq, List.cons_append]) hsub
      · exact ihB ((x ∶ B') :: Δ') (by rw [heq, List.cons_append]) hsub
  | impI G Γ₀ x A B' _ ih =>
      intro Δ' heq hsub
      exact .impI G (Δ' ++ Γ) x A B' (ih ((x ∶ A) :: Δ') (by rw [heq, List.cons_append]) hsub)
  | impE G Γ₀ x A B' _ _ ihimp ihA =>
      intro Δ' heq hsub
      exact .impE G (Δ' ++ Γ) x A B' (ihimp Δ' heq hsub) (ihA Δ' heq hsub)
  | boxE G Γ₀ x y0 A hR _ ih =>
      intro Δ' heq hsub
      exact .boxE G (Δ' ++ Γ) x y0 A hR (ih Δ' heq hsub)
  | boxI L hLfin G Γ₀ x A _ ih =>
      intro Δ' heq hsub
      refine .boxI L hLfin G (Δ' ++ Γ) x A ?_
      intro w hw
      have hle : G ≤ G.addEdge x w := ⟨Set.subset_union_left, fun _ _ h => Or.inl h⟩
      have hsub' : NIK 𝒯 (G.addEdge x w) Γ (y ∶ B) := hsub.weaken hle (fun _ h => h)
      exact ih w hw Δ' heq hsub'
  | diaI G Γ₀ x y0 A hR _ ih =>
      intro Δ' heq hsub
      exact .diaI G (Δ' ++ Γ) x y0 A hR (ih Δ' heq hsub)
  | diaE L hLfin G Γ₀ x z A B' hdia _ ihdia ih =>
      intro Δ' heq hsub
      refine .diaE L hLfin G (Δ' ++ Γ) x z A B' (ihdia Δ' heq hsub) ?_
      intro w hw
      have hle : G ≤ G.addEdge x w := ⟨Set.subset_union_left, fun _ _ h => Or.inl h⟩
      have hsub' : NIK 𝒯 (G.addEdge x w) Γ (y ∶ B) := hsub.weaken hle (fun _ h => h)
      exact ih w hw ((w ∶ A) :: Δ') (by rw [heq, List.cons_append]) hsub'

/-- **`NIK`-level substitution / cut admissibility.** If `φ` is derivable from
`Δ ++ (y:B) :: Γ` and `y:B` is itself derivable from `Γ`, then `φ` is derivable from `Δ ++ Γ`
alone — the one fact Simpson's deductive-closure argument needs that the other three clauses do
not (Simpson `chunk_0103.md`, *"Then `Δ,y:B ⊬_H x:A` (for otherwise would contradict that
`Δ⊬_H x:A`)"* — the "otherwise" step is exactly this substitution). Proved by
`NIK.subst_aux`: induction on the derivation of `φ`, generalizing over the accumulating prefix
`Δ'` (needed because `impI`/`orE`/`diaE` prepend to the *whole* context during the induction) and
re-weakening `hsub` to each case's own graph (`boxI`/`diaE` extend the graph by one edge). -/
theorem NIK.subst {G : Graph Atom} {y : Label Atom} {B : Proposition Atom}
    {Γ Δ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    (h : NIK 𝒯 G (Δ ++ (y ∶ B) :: Γ) φ) (hsub : NIK 𝒯 G Γ (y ∶ B)) : NIK 𝒯 G (Δ ++ Γ) φ :=
  NIK.subst_aux h Δ rfl hsub

/-- The `Deriv`-level form of `NIK.subst`, lifted through finite witnessing sublists — the shape
`deductiveClosure_of_maximal` actually consumes. -/
theorem Deriv.subst {G : Graph Atom} {y : Label Atom} {B : Proposition Atom}
    {Γ : Set (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    (h : Deriv 𝒯 G (insert (y ∶ B) Γ) φ) (hsub : Deriv 𝒯 G Γ (y ∶ B)) : Deriv 𝒯 G Γ φ := by
  classical
  obtain ⟨Γf, hΓf, hNIK⟩ := h
  obtain ⟨Γs, hΓs, hNIKs⟩ := hsub
  set Γf' := Γf.filter (fun ψ => decide (ψ ≠ (y ∶ B))) with hΓf'def
  have hΓf'mem : ∀ ψ ∈ Γf', ψ ∈ Γ := by
    intro ψ hψ
    have hne : ψ ≠ (y ∶ B) := by simpa [hΓf'def] using (List.of_mem_filter hψ)
    rcases hΓf ψ (List.mem_of_mem_filter hψ) with rfl | hmem
    · exact absurd rfl hne
    · exact hmem
  have hΓf_sub : ∀ ψ ∈ Γf, ψ ∈ (y ∶ B) :: (Γf' ++ Γs) := by
    intro ψ hψ
    by_cases hcase : ψ = (y ∶ B)
    · exact hcase ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_filter.mpr ⟨hψ, by simpa using hcase⟩))
  have hNIKf' : NIK 𝒯 G ([] ++ (y ∶ B) :: (Γf' ++ Γs)) φ :=
    hNIK.weaken (Graph.le_refl _) hΓf_sub
  have hNIKs' : NIK 𝒯 G (Γf' ++ Γs) (y ∶ B) :=
    hNIKs.weaken (Graph.le_refl _) (fun ψ hψ => List.mem_append_right _ hψ)
  refine ⟨Γf' ++ Γs, fun ψ hψ => ?_, by simpa using hNIKf'.subst hNIKs'⟩
  rcases List.mem_append.mp hψ with hψ | hψ
  · exact hΓf'mem ψ hψ
  · exact hΓs ψ hψ

/-- **Clause 1** (`TPrime.deductiveClosure`): deductive closure (Simpson `chunk_0103.md`,
*"`y:B∈Δ` by the maximality of `(H,Δ)`"*). Combines `Deriv.subst` (cut, the fact this clause
alone needs) with `mem_of_maximal_addFormula`'s Lindenbaum-style extension argument. -/
theorem deductiveClosure_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom}
    {A₀ : Proposition Atom} {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) :
    ∀ x ∈ H.G.X, ∀ (B : Proposition Atom), Deriv 𝒯 H.G H.Γ (x ∶ B) → (x ∶ B) ∈ H.Γ := by
  intro y hyX B hderiv
  refine mem_of_maximal_addFormula hmax hyX ?_
  intro hDeriv'
  obtain ⟨_, _, hnd⟩ := hmax.prop
  exact hnd (hDeriv'.subst hderiv)

/-! ### Assembly: Simpson's Prime Lemma 5.3.1 -/

/-- **Simpson's Prime Lemma 5.3.1** (`chunk_0102.md`/`chunk_0103.md`, pp. 92-93): if `(G,Γ)` is a
context and `Γ ⊬_G x:A`, there is a `𝒯`-prime context `(H,Δ) ⊇ (G,Γ)` with `Δ ⊬_H x:A`. Assembles
`primeC_exists_maximal` (the Zorn maximalisation) with the five `TPrime` clause theorems above.

**FULLY SORRY-FREE (Task 517 Phase 6, the Phase 4.5 completion milestone)**: all five clauses --
`clModel`/`consistency`/`disjunction`/`deductiveClosure` (closed by a prior follow-up dispatch via
`NIK.subst_aux`) and now `diamond` (`dwitness_mem_of_maximal`, closed this phase via
`NIK.diaWitnessTransportOld`) -- are sorry-free. `lean_verify`: axioms `[propext,
Classical.choice, Quot.sound]`, no `sorryAx`.

**Note on the FLO reconstruction (Phases 1-5)**: `primeLemma` is assembled from
`primeC_exists_maximal` (the plain `zorn_le₀` Zorn maximalisation), NOT `primeC'_exists_maximal`
(the FLO-carrying reconstruction) -- it does not need FLO at all. The "old label" obstacle both
`deriv_reflect` and `dwitness_mem_of_maximal` hit turned out to be resolvable at the `NIK`/`Graph`
level alone (`NIK.oldLabelTransport`/`NIK.diaWitnessTransportOld`, built from `NIK.relabelFresh`),
independent of *how* the maximal `H` was constructed. The FLO apparatus (`Stage`/`FloSeq`/`FLO`/
`flo_succ`/`flo_limit`/`primeC'_exists_maximal`/`flo_oldlabel_transport`) remains landed (Postmortem
Constraints: preserved verbatim) but is not on `primeLemma`'s critical path; `primeC'_exists_maximal`'s
own remaining `Maximal`-conjunct sorry and `flo_succ`'s superseded `redundantEdge` sorry are
consequently non-blocking for this theorem. **New hypothesis `hx₀ : x₀ ∈ G₀.G.X`**: Simpson's own
statement of the judgement `Γ ⊬_G x:A` presupposes `x` is a label of `G` (the standing convention
every other `Deriv`/`NIK` judgement in this development already carries for `Γ`'s own labels via
`Context.ctxSubset`); it was implicit before this phase and is now threaded explicitly because
`dwitness_mem_of_maximal` needs it to separate the excluded label `x₀` from the freshly adjoined
diamond witness (see that theorem's docstring for the exact argument). -/
theorem primeLemma (G₀ : Context 𝒯 Atom) (x₀ : Label Atom) (A₀ : Proposition Atom)
    (hx₀ : x₀ ∈ G₀.G.X) (h0 : ¬ Deriv 𝒯 G₀.G G₀.Γ (x₀ ∶ A₀)) :
    ∃ P : TPrime 𝒯 Atom, G₀ ≤ P.toContext ∧ ¬ Deriv 𝒯 P.G P.Γ (x₀ ∶ A₀) := by
  obtain ⟨H, hmax⟩ := primeC_exists_maximal G₀ x₀ A₀ (primeC_mem_base G₀ x₀ A₀ h0)
  obtain ⟨hG₀H, _, hnd⟩ := hmax.prop
  exact ⟨{ H with
      clModel := clModel_of_maximal hmax
      deductiveClosure := deductiveClosure_of_maximal hmax
      consistency := consistency_of_maximal hmax
      disjunction := disjunction_of_maximal hmax
      diamond := diamond_of_maximal hmax hx₀ },
    hG₀H, hnd⟩

/-! ## Task 517 Plan v5 Phase 1 — the well-founded maximalisation carrier + the FLO invariant

**Objective** (plan `12_wellfounded-zorn-oldlabel-reconstruction.md`, Phase 1): land, in `probes/`,
the concrete Lean definitions of the stepped/well-founded construction and the FLO
("fresh-labels-only extension") invariant that Phases 2-6 use to replace `zorn_le₀` in
`primeC_exists_maximal` and discharge the shared "old label" root cause of `deriv_reflect`
(~line 295 above) and `dwitness_mem_of_maximal` (~line 942 above). This section produces
DEFINITIONS that typecheck plus two immediately-provable lemmas (`stepExt_le`, `rankOf_base`,
both sorry-free), and states the four downstream obligations (`flo_succ`, `flo_limit`,
`primeC'_exists_maximal`, `flo_oldlabel_transport`) as sorried theorem signatures per the plan's
"Done when" criterion -- proofs are Phases 2-6's job, not this one's.

## `--lit` grounding (plan Phase 1 Task 1)

Read `chunk_0102.md` (the Prime Lemma proof, confirming Simpson's own Zorn-over-chains argument
gives no step-indexed structure to reuse directly -- `"It is easily seen that (⋃Gᵢ,⋃Γᵢ) is also
in C"` is exactly the elided step `ChainCtx.deriv_reflect` mechanizes, and offers no hint about
*which* labels a chain member may already contain) and `chunk_0103.md` (confirming, verbatim, the
denumerable-vs-general remark: *"as the set of formulae and the set `W(V)` are both denumerable,
the prime lemma can actually be proved without using any form of the axiom of choice. However, in
a choice-free proof, `(H,Δ)` would have to be obtained by a laborious iterative construction."*).
This is the textual basis for the Postmortem Constraints' binding rule that the construction here
must be **transfinite, not `ω`-indexed**: Simpson's own remark is conditioned on `W(V)`
denumerability, which holds for his fixed countable `PrefixVar := ℕ` but does **not** transfer to
this file's `Atom : Type u` (an arbitrary type), so the recursion cannot be bounded at `ω`.

## Mechanism decision (Risk "the crux", SETTLED for Phases 2-6)

**Route (i): explicit well-founded/`Ordinal`-indexed recursion**, producing a genuine staged
sequence `H : Stage → Context 𝒯 Atom` (`FloSeq` below). **Rejected**: route (ii), `zorn_le₀` over
an FLO-enriched carrier. Reasons: (1) the plan's own Phase 1 task list asks for a genuine staged
sequence with successor/limit structure -- "the task enumeration..., the single-step extension
function, and the stage context `H_σ`" -- which route (i) supplies directly and route (ii) does
not (a Zorn existence result exposes no extension sequence, exactly the reason `zorn_le₀` over the
*plain* carrier was ruled out for `primeC_exists_maximal` itself); (2) route (ii) would still need
an equivalent birth-rank trace bundled into the FLO-enriched carrier's `≤`-chain-closure step to
make chain unions FLO-coherent, which duplicates this file's already-landed `ChainCtx` machinery
(above) for no simplification. Do not reopen this choice without a concrete counterexample
(Postmortem Constraints).

## Contents

- `Stage`: the construction's stage-index type (`Ordinal.{u}`, transfinite per the grounding
  above).
- `FloTask`: one single-step extension task, reusing `Context.addFormula`/`addDiaWitness`/
  `addRedundantEdge` (Phase 4, above) verbatim.
- `stepExt` / `stepExt_le`: the single-step extension function (total, via classical case-splits
  on each task's side conditions) and the proof that it never shrinks -- **sorry-free**.
- `FloSeq`: a staged FLO construction -- an ordinal-indexed sequence of contexts extending `G₀`,
  built by `stepExt` at successor stages and by raw chain-union at limit stages.
- `rankOf` / `rankOf_base`: the derived birth-rank function (least stage of membership) and the
  proof that base labels have rank `0` -- **sorry-free**.
- `FLO`: the fresh-labels-only extension invariant, bundling FLO-0/FLO-1/FLO-2 exactly as stated
  in the plan Overview, relative to a `FloSeq` and a stage. Confirmed non-vacuous (see the
  docstring on `FLO` below): it genuinely constrains `rankOf`, the birth-stage of every non-base
  label, and every edge's introduction stage -- it is not `:= True`/`Unit`.
- `flo_succ` / `flo_limit` / `primeC'_exists_maximal` / `flo_oldlabel_transport`: the four
  downstream obligations (Phases 2, 3, 4, 5 respectively), stated as sorried signatures.

## Provenance

Literature: `chunk_0102.md`, `chunk_0103.md` (Lemma 5.3.1, the Prime Lemma proof and the
denumerable-vs-general remark, §5.3). PDF offset +9.
-/

/-- **The stage-index type**: transfinite ordinals in the universe of `Atom`, not `ω` -- see the
`--lit` grounding above and the Postmortem Constraints (`Atom : Type u` is not assumed countable,
so Simpson's own denumerable-hence-choice-free remark, `chunk_0103.md`, does not bound the
recursion at `ω`). -/
abbrev Stage : Type (u + 1) := Ordinal.{u}

/-- **One single-step extension task**: which of the three landed `Context` extension operations
(`Context.addFormula`/`Context.addDiaWitness`/`Context.addRedundantEdge`, Phase 4 above) to
attempt at a given stage, or to skip (no obligation pending, or the precondition fails and
`stepExt` falls back to the identity). Encodes Simpson's Lindenbaum-style enumeration of
obligations: `formula` covers deductive-closure/disjunction test-additions (and clause 0's
"redundant edge" argument's own formula-level analogue), `diaWitness` covers the diamond property
(FLO-1(b)), and `redundantEdge` covers clause 0's maximality argument (`raw_edge_of_tclosure`,
above) directly. -/
inductive FloTask (𝒯 : Set GeomAxiom) (Atom : Type u) : Type u where
  /-- Test-add a formula `φ` at an existing label. -/
  | formula (φ : LabelledFormula Atom) : FloTask 𝒯 Atom
  /-- Adjoin the diamond witness `dwitness y B` for an existing label `y` (FLO-1(b)). -/
  | diaWitness (y : Label Atom) (B : Proposition Atom) : FloTask 𝒯 Atom
  /-- Adjoin a redundant edge `(a,b)` between two already-present labels; introduces no new
  label. -/
  | redundantEdge (a b : Label Atom) : FloTask 𝒯 Atom
  /-- No obligation pending at this stage (padding: the genuine obligations may be sparser than
  the enumeration index `Stage`). -/
  | skip : FloTask 𝒯 Atom

open Classical in
/-- **The single-step extension function**, made total via classical case-splits on each task's
side conditions -- defaulting to the identity extension (itself `≤`-trivial, `Context.le_refl`)
when a precondition fails, e.g. the formula's label is not (yet) in the domain, or the diamond
witness is already present. Reuses the three landed operations verbatim -- exactly the "reusing
the landed `Context.addFormula`/`Context.addDiaWitness`/`Context.addRedundantEdge` operations"
the plan's Phase 1 task list calls for. -/
noncomputable def stepExt (H : Context 𝒯 Atom) : FloTask 𝒯 Atom → Context 𝒯 Atom
  | .formula φ => if hφ : φ.lbl ∈ H.G.X then H.addFormula φ hφ else H
  | .diaWitness y B =>
      if hy : y ∈ H.G.X then
        if hfresh : Label.dwitness y B ∉ H.G.X then H.addDiaWitness y B hy hfresh else H
      else H
  | .redundantEdge a b =>
      if ha : a ∈ H.G.X then
        if hb : b ∈ H.G.X then H.addRedundantEdge a b ha hb else H
      else H
  | .skip => H

/-- **`stepExt` never shrinks**: every single step is a genuine `Context.le` extension (the
operative cases reuse the three landed `_le` lemmas; the fallback/skip cases are `Context.le_refl`
outright). Sorry-free: this is the H2 formal-proof-line bar for this dispatch. -/
theorem stepExt_le (H : Context 𝒯 Atom) (t : FloTask 𝒯 Atom) : H ≤ stepExt H t := by
  cases t with
  | formula φ =>
      simp only [stepExt]
      split
      · exact H.addFormula_le _ _
      · exact Context.le_refl H
  | diaWitness y B =>
      simp only [stepExt]
      split
      · split
        · exact H.addDiaWitness_le _ _ _ _
        · exact Context.le_refl H
      · exact Context.le_refl H
  | redundantEdge a b =>
      simp only [stepExt]
      split
      · split
        · exact H.addRedundantEdge_le _ _ _ _
        · exact Context.le_refl H
      · exact Context.le_refl H
  | skip => simp only [stepExt]; exact Context.le_refl H

variable (G₀ : Context 𝒯 Atom)

/-- **A staged FLO construction**: an ordinal-indexed sequence of contexts extending `G₀`, built
by `stepExt` (above) at successor stages and by raw chain-union at limit stages, together with a
fixed task-enumeration schedule. This is the concrete object Phase 4
(`primeC'_exists_maximal`) instantiates and Phases 2-3 (`flo_succ`/`flo_limit`) show is
FLO-coherent at every stage. The limit clause is stated directly via `Set` union (not by invoking
`ChainCtx.unionContext` at *definition* time, which would need `H` already proved `Monotone` on
`{τ // τ < σ}` -- a proof obligation, not a definitional one); Phase 3 shows this coincides with
`ChainCtx.unionContext` once `flo_succ`-style monotonicity is established. -/
structure FloSeq (𝒯 : Set GeomAxiom) (Atom : Type u) (G₀ : Context 𝒯 Atom) : Type (u + 1) where
  /-- The staged sequence of contexts, `H_σ`. -/
  H : Stage → Context 𝒯 Atom
  /-- The task performed at each successor step. -/
  task : Stage → FloTask 𝒯 Atom
  /-- Base stage: `H_0 = G₀`. -/
  base_eq : H 0 = G₀
  /-- Successor stages extend by one `stepExt` step. -/
  succ_eq : ∀ σ : Stage, H (σ + 1) = stepExt (H σ) (task σ)
  /-- Limit stages take the raw union of every earlier stage (Simpson's chain-union step,
  `chunk_0102.md`, specialised to the well-order below `σ`). -/
  limit_eq : ∀ σ : Stage, Order.IsSuccLimit σ →
    (H σ).G.X = ⋃ τ : {τ // τ < σ}, (H τ.1).G.X ∧
    (H σ).G.R = (fun a b => ∃ τ : {τ // τ < σ}, (H τ.1).G.R a b) ∧
    (H σ).Γ = ⋃ τ : {τ // τ < σ}, (H τ.1).Γ

variable {G₀}

/-- **The derived birth-rank function**: the least stage at which a label enters the staged
construction's domain. Junk-valued (defaults to `0`, `Ordinal`'s bottom) on labels that never
appear -- harmless, since `FLO`'s clauses below only ever constrain `rankOf` on labels actually
present at the stage in question. -/
noncomputable def rankOf (𝒮 : FloSeq 𝒯 Atom G₀) (x : Label Atom) : Stage :=
  sInf {σ : Stage | x ∈ (𝒮.H σ).G.X}

/-- **(FLO-0), sorry-free**: every base label has rank `0` -- immediate from `base_eq` and `0`
being `Stage`'s bottom element. This is the H2 second sorry-free landmark: `FLO`'s base clause is
not merely stated but already discharged for any `FloSeq`, independent of Phases 2-6. -/
theorem rankOf_base (𝒮 : FloSeq 𝒯 Atom G₀) {x : Label Atom} (hx : x ∈ G₀.G.X) :
    rankOf 𝒮 x = 0 := by
  have hmem : (0 : Stage) ∈ {σ : Stage | x ∈ (𝒮.H σ).G.X} := by
    show x ∈ (𝒮.H 0).G.X
    rw [𝒮.base_eq]
    exact hx
  exact le_antisymm (csInf_le ⟨0, fun _ _ => bot_le⟩ hmem) bot_le

/-- **The FLO invariant** (plan Overview, "The FLO invariant" section): fixes the base context
`G₀` and states, relative to a staged construction `𝒮` and a stage `σ`, that `rankOf 𝒮` is a
faithful extension history for `𝒮.H σ`:

- **(FLO-0) base**: every base label has rank `0` (already proved in general, `rankOf_base`, so
  restated here for bundling convenience rather than left as fresh proof burden).
- **(FLO-1) fresh at birth**: every label in `(𝒮.H σ).G.X` beyond `G₀.G.X` has a rank that is a
  *successor* stage `τ + 1`, was absent at the immediately preceding stage `τ`, and is either (a)
  not of `dwitness` form (a "prime"/formula-add step introducing a genuinely new label) or (b) is
  `Label.dwitness w B` for some `w` already present at stage `τ`. Case (a)'s precise source pool
  (the plan Overview's reserve `V'ᶜ`) is pinned down by Phase 2 as part of proving `stepExt`
  preserves `primeC`'s own `V'`-confinement side condition; this file states only the birth-stage
  freshness shape, per Phase 1's "DEFINITIONS, not proofs" scope.
- **(FLO-2) edge locality**: every edge `(x,y) ∈ (𝒮.H σ).G.R` first appears at stage
  `max (rankOf 𝒮 x) (rankOf 𝒮 y)`, and not before.

**Non-vacuity** (Phase 1's "Done when" gate): `FLO` is a genuine `structure` with three
independent constraints on `rankOf`/`𝒮.H`, never `:= True`/`Unit`/`trivial` -- FLO-0 forces
`rankOf` to vanish exactly on `G₀`'s domain, FLO-1 forces every other label's rank to be a
successor with a specific shape, and FLO-2 pins every edge's introduction stage exactly. A
`FloSeq` satisfying `FLO` at every stage is a strictly stronger object than an arbitrary
`Context.le`-monotone sequence. -/
structure FLO (𝒮 : FloSeq 𝒯 Atom G₀) (σ : Stage) : Prop where
  /-- (FLO-0), restated for bundling convenience (see `rankOf_base`, already sorry-free). -/
  flo0 : ∀ x ∈ G₀.G.X, rankOf 𝒮 x = 0
  /-- (FLO-1) fresh at birth. -/
  flo1 : ∀ x ∈ (𝒮.H σ).G.X, x ∉ G₀.G.X →
    ∃ τ : Stage, rankOf 𝒮 x = τ + 1 ∧ x ∉ (𝒮.H τ).G.X ∧
      ((∀ w B, x ≠ Label.dwitness w B) ∨ ∃ w B, x = Label.dwitness w B ∧ w ∈ (𝒮.H τ).G.X)
  /-- (FLO-2) edge locality. -/
  flo2 : ∀ x y, (𝒮.H σ).G.R x y →
    (max (rankOf 𝒮 x) (rankOf 𝒮 y) = sInf {τ : Stage | (𝒮.H τ).G.R x y})

/-- **Auxiliary monotonicity lemma** (Phase 2): the staged sequence `𝒮.H` is `Context.le`-monotone
in the stage order, purely from `succ_eq`/`limit_eq`/`stepExt_le` -- no dependence on `FLO`. This
is the fact `flo_succ`'s rank computations below need (a label absent at stage `σ` is absent at
every earlier stage), and the fact the Phase 1 summary flagged as needed before Phase 3 can
identify `FloSeq.limit_eq`'s raw union with `ChainCtx.unionContext`. Proved by transfinite
induction on the upper stage (`Ordinal.induction`), casing on whether the upper stage is
zero/successor/limit (`Ordinal.zero_or_succ_or_isSuccLimit`). -/
theorem FloSeq.mono (𝒮 : FloSeq 𝒯 Atom G₀) {τ σ : Stage} (h : τ ≤ σ) : 𝒮.H τ ≤ 𝒮.H σ := by
  induction σ using Ordinal.induction generalizing τ with
  | _ σ ih =>
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · rcases Ordinal.zero_or_succ_or_isSuccLimit σ with h0 | ⟨ρ, hρ⟩ | hlim
      · exact absurd (h0 ▸ hlt) (Ordinal.not_lt_zero τ)
      · have hσ : σ = ρ + 1 := by rw [Ordinal.add_one_eq_succ]; exact hρ.symm
        subst hσ
        have hτρ : τ ≤ ρ := by
          rw [Ordinal.add_one_eq_succ, Order.lt_succ_iff_eq_or_lt] at hlt
          rcases hlt with heq | hlt'
          · exact le_of_eq heq
          · exact le_of_lt hlt'
        have hρlt : ρ < ρ + 1 := by
          rw [Ordinal.add_one_eq_succ]; exact Order.lt_succ_iff_eq_or_lt.mpr (Or.inl rfl)
        have h1 : 𝒮.H τ ≤ 𝒮.H ρ := ih ρ hρlt hτρ
        have h2 : 𝒮.H ρ ≤ 𝒮.H (ρ + 1) := by
          rw [𝒮.succ_eq ρ]; exact stepExt_le (𝒮.H ρ) (𝒮.task ρ)
        exact Context.le_trans h1 h2
      · obtain ⟨hX, hR, hΓ⟩ := 𝒮.limit_eq σ hlim
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hX]; exact Set.subset_iUnion (fun τ' : {τ' // τ' < σ} => (𝒮.H τ'.1).G.X) ⟨τ, hlt⟩
        · intro a b hab
          rw [hR]; exact ⟨⟨τ, hlt⟩, hab⟩
        · rw [hΓ]; exact Set.subset_iUnion (fun τ' : {τ' // τ' < σ} => (𝒮.H τ'.1).Γ) ⟨τ, hlt⟩

/-- **Phase 2's target**: `stepExt` preserves `FLO`-coherence across a successor step, extending
`rankOf` by the newly-adjoined label(s) (if any) at the just-taken step. Not attempted here per
Phase 1's scope ("DEFINITIONS ... not proofs"); this signature is the sorried scaffolding Phase 2
discharges. -/
theorem flo_succ (𝒮 : FloSeq 𝒯 Atom G₀) (σ : Stage) (hflo : FLO 𝒮 σ) : FLO 𝒮 (σ + 1) := by
  obtain ⟨flo0, flo1, flo2⟩ := hflo
  have habsent : ∀ {x : Label Atom} {ρ : Stage}, ρ ≤ σ → x ∉ (𝒮.H σ).G.X → x ∉ (𝒮.H ρ).G.X :=
    fun {x ρ} hρσ hx hxρ => hx ((𝒮.mono hρσ).1.1 hxρ)
  have hstep : 𝒮.H (σ + 1) = stepExt (𝒮.H σ) (𝒮.task σ) := 𝒮.succ_eq σ
  generalize htask : 𝒮.task σ = t at hstep
  cases t with
  | formula φ =>
    simp only [stepExt] at hstep
    have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]; split <;> rfl
    have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]; split <;> rfl
    exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
      fun x y hxy => flo2 x y (hReq ▸ hxy)⟩
  | skip =>
    simp only [stepExt] at hstep
    have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]
    have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]
    exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
      fun x y hxy => flo2 x y (hReq ▸ hxy)⟩
  | redundantEdge a b =>
    simp only [stepExt] at hstep
    have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by
      rw [hstep]
      split
      · split
        · exact Graph.addEdge_X_eq_of_mem ‹_› ‹_›
        · rfl
      · rfl
    refine ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0, ?_⟩
    intro x y hxy
    rw [hstep] at hxy
    split at hxy
    · split at hxy
      · rcases hxy with hxy | ⟨rfl, rfl⟩
        · exact flo2 x y hxy
        · -- **STRATEGIC/LEAF SORRY** (documented per the anti-analysis five-condition test):
          --
          -- 1. Deliberate division boundary: `stepExt`'s `.redundantEdge a b` case, as landed in
          --    Phase 1, is *unconditional* on the pair `(a,b)` beyond `a,b ∈ H.G.X` -- it carries
          --    no side condition tying the stage of introduction to `max (rankOf a) (rankOf b)`.
          --    FLO-2 demands the edge first appear at EXACTLY that stage. For an adversarial
          --    `FloTask.redundantEdge a b` scheduled with `a,b` both already ranked ≪ σ (e.g.
          --    both base labels, rank 0) and the edge `(a,b)` genuinely absent before this step,
          --    the edge's true first-appearance stage is `σ+1`, so `max (rankOf a) (rankOf b) =
          --    sInf {τ | edge τ}` would force `0 = σ+1` (or generally `max(rank a,rank b) = σ+1`)
          --    -- impossible for an ordinal and its successor. `flo_succ` is genuinely FALSE for
          --    such an unconstrained `𝒮`; this is exactly the ambiguity the plan's own Phase 2
          --    task list flagged ("confirm this is admissible under FLO-2 or that redundant-edge
          --    additions are handled by the maximality argument rather than the construction
          --    trace") -- Phase 4's fair schedule is expected to invoke `.redundantEdge` only when
          --    `raw_edge_of_tclosure`'s maximality argument has already forced the edge to be
          --    present (making this branch a definitional no-op via the `hxy | ⟨rfl,rfl⟩` split
          --    above landing in the `hxy` branch instead), but `flo_succ`'s signature (Phase 1,
          --    preserved verbatim) does not carry that scheduling-fairness hypothesis, so the
          --    genuinely-new-edge sub-case cannot be discharged from `FLO 𝒮 σ` alone.
          -- 2. Tightly scoped: exactly this one sub-case (new edge from an unconstrained
          --    `redundantEdge` task) inside `flo_succ`'s FLO-2 clause; FLO-0, FLO-1, and every
          --    other task variant's FLO-2 obligation (`formula`/`diaWitness`/`skip`, plus the
          --    "edge already present" half of this very case) are proved sorry-free above.
          -- 3. Documented: this comment states the assumption (the new edge's timing coheres with
          --    `max (rankOf a) (rankOf b)`) and why it is deferred (no fairness/scheduling
          --    hypothesis is available in `flo_succ`'s signature to discharge it).
          -- 4. Tracked: recorded in `.orchestrator-handoff.json`'s `sorry_inventory` with
          --    `strategic: true` and a non-null `follow_up_task`.
          -- 5. Build-green: `sorry` typechecks; the probe remains build-green with this one
          --    documented gap.
          sorry
      · exact flo2 x y hxy
    · exact flo2 x y hxy
  | diaWitness y B =>
    simp only [stepExt] at hstep
    split at hstep
    · split at hstep
      · rename_i hy hfresh
        have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X ∪ {y, Label.dwitness y B} := by
          rw [hstep]; rfl
        have hReq : ∀ p q, (𝒮.H (σ + 1)).G.R p q ↔
            (𝒮.H σ).G.R p q ∨ (p = y ∧ q = Label.dwitness y B) := by
          intro p q; rw [hstep]; rfl
        have hnew_mem : Label.dwitness y B ∈ (𝒮.H (σ + 1)).G.X := by
          rw [hXeq]; exact Or.inr (Or.inr rfl)
        have hle_succ : σ ≤ σ + 1 := by
          rw [Ordinal.add_one_eq_succ]; exact Order.le_succ σ
        have hrank_new : rankOf 𝒮 (Label.dwitness y B) = σ + 1 := by
          have hleast : IsLeast {σ' : Stage | Label.dwitness y B ∈ (𝒮.H σ').G.X} (σ + 1) := by
            refine ⟨hnew_mem, ?_⟩
            intro σ' hσ'mem
            by_contra hcon
            push_neg at hcon
            have hσ'σ : σ' ≤ σ := by
              rw [Ordinal.add_one_eq_succ, Order.lt_succ_iff_eq_or_lt] at hcon
              rcases hcon with heq | hlt
              · exact le_of_eq heq
              · exact le_of_lt hlt
            exact (habsent hσ'σ hfresh) hσ'mem
          exact hleast.csInf_eq
        have hrank_y_le : rankOf 𝒮 y ≤ σ := by
          have hmemy : (σ : Stage) ∈ {σ' : Stage | y ∈ (𝒮.H σ').G.X} := hy
          exact csInf_le ⟨0, fun z _ => bot_le⟩ hmemy
        refine ⟨fun x hx => rankOf_base 𝒮 hx, ?_, ?_⟩
        · intro x hx hx0
          simp only [hXeq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with hx | rfl | rfl
          · exact flo1 x hx hx0
          · exact flo1 x hy hx0
          · exact ⟨σ, hrank_new, hfresh, Or.inr ⟨y, B, rfl, hy⟩⟩
        · intro x y' hxy'
          rw [hReq] at hxy'
          rcases hxy' with hxy' | ⟨rfl, rfl⟩
          · exact flo2 x y' hxy'
          · have hmax : max (rankOf 𝒮 x) (rankOf 𝒮 (Label.dwitness x B)) = σ + 1 := by
              rw [hrank_new]; exact max_eq_right (le_trans hrank_y_le hle_succ)
            rw [hmax]
            have hleast_edge : IsLeast {τ : Stage | (𝒮.H τ).G.R x (Label.dwitness x B)} (σ + 1) := by
              refine ⟨(hReq x (Label.dwitness x B)).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
              intro τ hτmem
              by_contra hcon
              push_neg at hcon
              have hτσ : τ ≤ σ := by
                rw [Ordinal.add_one_eq_succ, Order.lt_succ_iff_eq_or_lt] at hcon
                rcases hcon with heq | hlt
                · exact le_of_eq heq
                · exact le_of_lt hlt
              exact (habsent hτσ hfresh) (((𝒮.H τ).G.edge_mem x (Label.dwitness x B) hτmem).2)
            exact hleast_edge.csInf_eq.symm
      · rename_i hy hfresh
        have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]
        have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]
        exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
          fun x y hxy => flo2 x y (hReq ▸ hxy)⟩
    · rename_i hy
      have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]
      have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]
      exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
        fun x y hxy => flo2 x y (hReq ▸ hxy)⟩

/-- **Phase 3's target**: `FLO`-coherence is preserved at limit stages -- the raw chain-union
(`FloSeq.limit_eq`) of an `FLO`-coherent stretch of the construction is again `FLO`-coherent, with
`rankOf` extended coherently (every label keeps the birth stage it already had below `σ`). Not
attempted here; sorried scaffolding for Phase 3. -/
theorem flo_limit (𝒮 : FloSeq 𝒯 Atom G₀) (σ : Stage) (hlim : Order.IsSuccLimit σ)
    (hflo : ∀ τ < σ, FLO 𝒮 τ) : FLO 𝒮 σ := by
  obtain ⟨hX, hR, hΓ⟩ := 𝒮.limit_eq σ hlim
  refine ⟨fun x hx => rankOf_base 𝒮 hx, ?_, ?_⟩
  · -- (FLO-1): membership at the limit stage descends, via `limit_eq`, to some witnessing
    -- predecessor stage `τ < σ`; FLO-1's conclusion (an existential about `rankOf 𝒮 x` and
    -- membership in `(𝒮.H τ').G.X` for some `τ'`) does not mention `σ` at all, so `(hflo τ
    -- hτσ).flo1` at that predecessor stage closes the goal for `σ` directly.
    intro x hx hx0
    rw [hX] at hx
    obtain ⟨⟨τ, hτσ⟩, hxτ⟩ := Set.mem_iUnion.mp hx
    exact (hflo τ hτσ).flo1 x hxτ hx0
  · -- (FLO-2): symmetric descent argument. `(𝒮.H σ).G.R x y` unions existentially over `τ < σ`
    -- (`limit_eq`); FLO-2's conclusion `max (rankOf x) (rankOf y) = sInf {τ' | (𝒮.H τ').G.R x y}`
    -- is likewise independent of `σ`, so `(hflo τ hτσ).flo2` at the witnessing `τ` closes it.
    intro x y hxy
    rw [hR] at hxy
    obtain ⟨⟨τ, hτσ⟩, hxyτ⟩ := hxy
    exact (hflo τ hτσ).flo2 x y hxyτ

/-! ### Phase 4: assembling the maximal FLO context

Phase 2's finding (`sorry_inventory`, probe line 1518) is that `flo_succ`'s `redundantEdge`
branch is genuinely inadmissible for an *unconstrained* schedule. The fix, per that finding and
this dispatch's brief, is a schedule-fairness side condition: `.redundantEdge a b` is only ever
scheduled once `(a,b)` is already an edge. `flo_succ_fair`/`flo_holds_everywhere` below
mechanize that fix (sorry-free), without editing the preserved `flo_succ` itself. -/

/-- **Fair-schedule successor lemma** (Phase 4, resolving Phase 2's open `redundantEdge` finding
recorded at `sorry_inventory`, probe line 1518): identical to `flo_succ` in the `formula`/`skip`/
`diaWitness` branches, but additionally hypothesises `hRedundant` -- "the schedule only ever
performs `.redundantEdge a b` once `(a,b)` is *already* an edge of the stage" -- which lets the
previously-sorried "genuinely new edge" sub-case of `flo_succ`'s `redundantEdge` branch never
actually arise: whichever disjunct `rcases` produces for the newly-stepped edge, `hRedundant`
independently supplies `(𝒮.H σ).G.R a b`, so `flo2 a b` (from `hflo`) closes the goal exactly as
the "already present" disjunct does. `flo_succ` itself (Phase 2) is left untouched, per the
Postmortem Constraints ("MUST preserve ... Phase 2's ... `flo_succ` ... verbatim") -- this is a
genuinely new, sorry-free theorem for schedules satisfying the extra discipline, not an edit to
the preserved one. -/
theorem flo_succ_fair (𝒮 : FloSeq 𝒯 Atom G₀) (σ : Stage) (hflo : FLO 𝒮 σ)
    (hRedundant : ∀ a b, 𝒮.task σ = .redundantEdge a b → (𝒮.H σ).G.R a b) :
    FLO 𝒮 (σ + 1) := by
  obtain ⟨flo0, flo1, flo2⟩ := hflo
  have habsent : ∀ {x : Label Atom} {ρ : Stage}, ρ ≤ σ → x ∉ (𝒮.H σ).G.X → x ∉ (𝒮.H ρ).G.X :=
    fun {x ρ} hρσ hx hxρ => hx ((𝒮.mono hρσ).1.1 hxρ)
  have hstep : 𝒮.H (σ + 1) = stepExt (𝒮.H σ) (𝒮.task σ) := 𝒮.succ_eq σ
  generalize htask : 𝒮.task σ = t at hstep
  cases t with
  | formula φ =>
    simp only [stepExt] at hstep
    have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]; split <;> rfl
    have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]; split <;> rfl
    exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
      fun x y hxy => flo2 x y (hReq ▸ hxy)⟩
  | skip =>
    simp only [stepExt] at hstep
    have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]
    have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]
    exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
      fun x y hxy => flo2 x y (hReq ▸ hxy)⟩
  | redundantEdge a b =>
    simp only [stepExt] at hstep
    have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by
      rw [hstep]
      split
      · split
        · exact Graph.addEdge_X_eq_of_mem ‹_› ‹_›
        · rfl
      · rfl
    refine ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0, ?_⟩
    intro x y hxy
    rw [hstep] at hxy
    split at hxy
    · split at hxy
      · rcases hxy with hxy | ⟨rfl, rfl⟩
        · exact flo2 x y hxy
        · exact flo2 x y (hRedundant x y htask)
      · exact flo2 x y hxy
    · exact flo2 x y hxy
  | diaWitness y B =>
    simp only [stepExt] at hstep
    split at hstep
    · split at hstep
      · rename_i hy hfresh
        have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X ∪ {y, Label.dwitness y B} := by
          rw [hstep]; rfl
        have hReq : ∀ p q, (𝒮.H (σ + 1)).G.R p q ↔
            (𝒮.H σ).G.R p q ∨ (p = y ∧ q = Label.dwitness y B) := by
          intro p q; rw [hstep]; rfl
        have hnew_mem : Label.dwitness y B ∈ (𝒮.H (σ + 1)).G.X := by
          rw [hXeq]; exact Or.inr (Or.inr rfl)
        have hle_succ : σ ≤ σ + 1 := by
          rw [Ordinal.add_one_eq_succ]; exact Order.le_succ σ
        have hrank_new : rankOf 𝒮 (Label.dwitness y B) = σ + 1 := by
          have hleast : IsLeast {σ' : Stage | Label.dwitness y B ∈ (𝒮.H σ').G.X} (σ + 1) := by
            refine ⟨hnew_mem, ?_⟩
            intro σ' hσ'mem
            by_contra hcon
            push_neg at hcon
            have hσ'σ : σ' ≤ σ := by
              rw [Ordinal.add_one_eq_succ, Order.lt_succ_iff_eq_or_lt] at hcon
              rcases hcon with heq | hlt
              · exact le_of_eq heq
              · exact le_of_lt hlt
            exact (habsent hσ'σ hfresh) hσ'mem
          exact hleast.csInf_eq
        have hrank_y_le : rankOf 𝒮 y ≤ σ := by
          have hmemy : (σ : Stage) ∈ {σ' : Stage | y ∈ (𝒮.H σ').G.X} := hy
          exact csInf_le ⟨0, fun z _ => bot_le⟩ hmemy
        refine ⟨fun x hx => rankOf_base 𝒮 hx, ?_, ?_⟩
        · intro x hx hx0
          simp only [hXeq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with hx | rfl | rfl
          · exact flo1 x hx hx0
          · exact flo1 x hy hx0
          · exact ⟨σ, hrank_new, hfresh, Or.inr ⟨y, B, rfl, hy⟩⟩
        · intro x y' hxy'
          rw [hReq] at hxy'
          rcases hxy' with hxy' | ⟨rfl, rfl⟩
          · exact flo2 x y' hxy'
          · have hmax : max (rankOf 𝒮 x) (rankOf 𝒮 (Label.dwitness x B)) = σ + 1 := by
              rw [hrank_new]; exact max_eq_right (le_trans hrank_y_le hle_succ)
            rw [hmax]
            have hleast_edge : IsLeast {τ : Stage | (𝒮.H τ).G.R x (Label.dwitness x B)} (σ + 1) := by
              refine ⟨(hReq x (Label.dwitness x B)).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
              intro τ hτmem
              by_contra hcon
              push_neg at hcon
              have hτσ : τ ≤ σ := by
                rw [Ordinal.add_one_eq_succ, Order.lt_succ_iff_eq_or_lt] at hcon
                rcases hcon with heq | hlt
                · exact le_of_eq heq
                · exact le_of_lt hlt
              exact (habsent hτσ hfresh) (((𝒮.H τ).G.edge_mem x (Label.dwitness x B) hτmem).2)
            exact hleast_edge.csInf_eq.symm
      · rename_i hy hfresh
        have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]
        have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]
        exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
          fun x y hxy => flo2 x y (hReq ▸ hxy)⟩
    · rename_i hy
      have hXeq : (𝒮.H (σ + 1)).G.X = (𝒮.H σ).G.X := by rw [hstep]
      have hReq : (𝒮.H (σ + 1)).G.R = (𝒮.H σ).G.R := by rw [hstep]
      exact ⟨fun x hx => rankOf_base 𝒮 hx, fun x hx hx0 => flo1 x (hXeq ▸ hx) hx0,
        fun x y hxy => flo2 x y (hReq ▸ hxy)⟩

/-- **FLO holds at every stage of a redundant-edge-fair schedule** (Phase 4): combines the base
case (`FLO 𝒮 0`, proved directly here -- `rankOf_base`/`𝒮.base_eq`-immediate, not previously
named as its own lemma), `flo_succ_fair` (successor), and `flo_limit` (Phase 3, unconditional) via
transfinite induction (`Ordinal.induction`, the same pattern as `FloSeq.mono`). Sorry-free: this
is the dispatch's resolution of the Phase 2 `redundantEdge` finding along the schedule's actual
trace, for any schedule satisfying the fairness discipline `hRedundant`. -/
theorem flo_holds_everywhere (𝒮 : FloSeq 𝒯 Atom G₀)
    (hRedundant : ∀ σ a b, 𝒮.task σ = .redundantEdge a b → (𝒮.H σ).G.R a b) :
    ∀ σ : Stage, FLO 𝒮 σ := by
  intro σ
  induction σ using Ordinal.induction with
  | _ σ ih =>
    rcases Ordinal.zero_or_succ_or_isSuccLimit σ with h0 | ⟨ρ, hρ⟩ | hlim
    · subst h0
      refine ⟨fun x hx => rankOf_base 𝒮 hx, ?_, ?_⟩
      · intro x hx hx0
        exact absurd (𝒮.base_eq ▸ hx) hx0
      · intro x y hxy
        have hxy0 : G₀.G.R x y := 𝒮.base_eq ▸ hxy
        have hx0 : x ∈ G₀.G.X := (G₀.G.edge_mem x y hxy0).1
        have hy0 : y ∈ G₀.G.X := (G₀.G.edge_mem x y hxy0).2
        have hleast : IsLeast {τ : Stage | (𝒮.H τ).G.R x y} 0 :=
          ⟨hxy, fun τ _ => bot_le⟩
        rw [rankOf_base 𝒮 hx0, rankOf_base 𝒮 hy0, max_self]
        exact hleast.csInf_eq.symm
    · have hσ : σ = ρ + 1 := by rw [Ordinal.add_one_eq_succ]; exact hρ.symm
      subst hσ
      have hρlt : ρ < ρ + 1 := by
        rw [Ordinal.add_one_eq_succ]; exact Order.lt_succ_iff_eq_or_lt.mpr (Or.inl rfl)
      exact flo_succ_fair 𝒮 ρ (ih ρ hρlt) (hRedundant ρ)
    · exact flo_limit 𝒮 σ hlim (fun τ hτσ => ih τ hτσ)

/-- **Phase 4's target, revised**: the Phase 1 scaffolding's `hfair` alone under-determines
maximality (a task attempted exactly once, before its precondition becomes available, is never
retried after the precondition is later satisfied -- see the strategic sorry below for the exact
gap), and separately says nothing about *staying inside* `primeC` (formula/witness/edge additions
are not automatically `¬Deriv`-preserving). This revision adds two schedule-discipline hypotheses
Phase 4's "instantiate the recursion... discharge the obligations" task explicitly calls for:
`hRedundant` (this dispatch's CRITICAL fair-schedule finding, resolving Phase 2's open
`redundantEdge` branch along the real trace via `flo_holds_everywhere`, sorry-free) and `hprimeC`
(the schedule never leaves `primeC`, needed for `Maximal`'s own membership conjunct). `FLO 𝒮 σ₀`
at `σ₀` (a stage past which `hfair` guarantees every task has fired at least once) is now fully
sorry-free. The remaining maximality conjunct is ONE tightly-scoped, documented strategic sorry
(see below) -- `hfair`'s one-shot-per-task shape does not itself rule out a task whose
precondition becomes available only *after* its one guaranteed firing. -/
theorem primeC'_exists_maximal (x₀ : Label Atom) (A₀ : Proposition Atom)
    (h0 : G₀ ∈ primeC G₀ x₀ A₀) (𝒮 : FloSeq 𝒯 Atom G₀)
    (hfair : ∀ t : FloTask 𝒯 Atom, ∃ σ : Stage, 𝒮.task σ = t)
    (hRedundant : ∀ σ a b, 𝒮.task σ = .redundantEdge a b → (𝒮.H σ).G.R a b)
    (hprimeC : ∀ σ : Stage, 𝒮.H σ ∈ primeC G₀ x₀ A₀) :
    ∃ σ : Stage, Maximal (· ∈ primeC G₀ x₀ A₀) (𝒮.H σ) ∧ FLO 𝒮 σ := by
  set σ₀ : Stage := Ordinal.lsub (fun t : FloTask 𝒯 Atom => Classical.choose (hfair t)) with hσ₀def
  refine ⟨σ₀, ⟨hprimeC σ₀, ?_⟩, flo_holds_everywhere 𝒮 hRedundant σ₀⟩
  -- **STRATEGIC SORRY** (documented per the anti-analysis five-condition test):
  --
  -- 1. Deliberate division boundary: this is the maximality half of `primeC'_exists_maximal`,
  --    the one obligation this dispatch's own analysis (see the theorem docstring) found is NOT
  --    discharged by `hfair` as landed in Phase 1. `hfair` gives, for each task value `t`, ONE
  --    stage `σ_t` at which `𝒮.task σ_t = t`; `σ₀ := lsub (choose ∘ hfair)` is strictly past
  --    every `σ_t` (`Ordinal.lt_lsub`). But `stepExt`'s `.formula`/`.diaWitness` branches are
  --    NO-OPS when their precondition fails (label not yet present / witness already present),
  --    and a task's precondition can become newly satisfiable only AFTER its one guaranteed
  --    firing (e.g. `.formula φ` fired at `σ_φ` while `φ.lbl ∉ (𝒮.H σ_φ).G.X`, with `φ.lbl`
  --    entering the domain only at a LATER stage via an unrelated `.diaWitness` task) -- `hfair`
  --    does not guarantee a re-attempt, so `σ₀`'s `𝒮.H σ₀` need not be closed under every
  --    `primeC`-preserving one-step extension, hence need not be `primeC`-maximal.
  -- 2. Tightly scoped: exactly this one conjunct (`∀ D ∈ primeC, 𝒮.H σ₀ ≤ D → D ≤ 𝒮.H σ₀`) of
  --    `primeC'_exists_maximal`'s existential witness; the companion `FLO 𝒮 σ₀` conjunct and the
  --    `𝒮.H σ₀ ∈ primeC` conjunct are both proved above, sorry-free (`flo_holds_everywhere`,
  --    `hprimeC σ₀`).
  -- 3. Documented: the fix needs a *cofinal*, precondition-aware fairness hypothesis (e.g.
  --    `∀ σ' t, task-precondition-available-at σ' t → ∃ σ ≥ σ', 𝒮.task σ = t`) in place of the
  --    one-shot `hfair`, PLUS a cardinality/ordinal-stabilization argument (`Label Atom`/
  --    `Context` substructure has bounded cardinality in `Type u`, `Stage = Ordinal.{u}` has
  --    unboundedly many ordinals past that bound, so a cofinally-fair, monotone-growing schedule
  --    must stabilize before some bound) showing the stabilized stage is exactly the closure
  --    point -- genuinely deeper, separate proof content not attempted in this dispatch.
  -- 4. Tracked: recorded in `.orchestrator-handoff.json`'s `sorry_inventory` with
  --    `strategic: true` and a non-null `follow_up_task` (Phase 4 continuation / folded into
  --    Phase 5-6).
  -- 5. Build-green: `sorry` typechecks; the probe remains build-green with this one documented
  --    gap, and `FLO 𝒮 σ₀` plus `𝒮.H σ₀ ∈ primeC` are independently sorry-free.
  sorry

/-! ## Phase 5 — the shared old-label reflection lemma: `substFn` and `NIK.relabelFresh`

**Finding (documented deviation from the plan's anticipated proof shape, see the plan's Task 5.1
annotation)**: the plan's Overview and Task 5.1 anticipated needing a well-founded (rank-)
induction using FLO-2's edge-locality bound to avoid the "naive swap" collision the Postmortem
Constraints flag (`swapFn v y'` corrupts `y'`'s *own* pre-existing structure by relocating it onto
`v`, since `swapFn` is an involution and therefore also maps `y' ↦ v`). Closer analysis shows the
collision is avoided **by construction, not by bounding `y'`'s edges to a stage** (the "so the
swap/transport does not collide" clause Task 5.1 asks for, satisfied a different way than
anticipated): a **one-directional** relabeling `substFn a b` (`a ↦ b`, identity everywhere else,
in particular fixing `b`) never touches `b`'s own incident edges at all, because `substFn a b` is
NOT an involution -- unlike `swapFn a b`, it does not also send `b ↦ a`. The only freshness fact
this needs is that `a` (`y₀` at the call site) has NO incident edges in the ambient graph, which
`(𝒮.H σ).G.edge_mem` + `hy₀ : y₀ ∉ (𝒮.H σ).G.X` already supplies directly -- `FLO`/`rankOf`/FLO-2
are consequently not needed by this lemma's proof (`hflo` is threaded through the signature only
because Phase 1 fixed it there; the argument below never uses it). This subsumes Task 5.2 as
originally scoped ("apply the transport lemma to build the full cofinite premise... from the
fresh witness... plus old-label transport... plus the dwitness case"): because `substFn`-transport
does not case on whether `y'` is fresh or old, dwitness-shaped or not, `flo_oldlabel_transport`'s
single conclusion already covers every `y'` (fresh or old) uniformly, so no separate assembly step
combining the fresh-witness and old-label cases is required -- `NIK.freshWitness_transport`
(above) is in fact the special case of the lemma below where the extra hypothesis `y ∉ G.X` also
happens to hold. -/

/- `substFn`/`substFn_self`/`substFn_other`/`List.map_substFn_eq_self`/`NIK.relabelFresh`
(the one-directional relabeling family `flo_oldlabel_transport` below is built from) were
**relocated** (Task 517 Phase 6) to immediately after `NIK.freshWitness_transport`, ~line 253
above -- content unchanged, position only -- so that `ChainCtx.deriv_reflect` (~line 396) and
`dwitness_mem_of_maximal` (~line 944), both defined earlier in this file, can also consume them
via the new `NIK.oldLabelTransport`/`NIK.diaWitnessTransportOld` corollaries (Phase 6, module
section preceding `ChainCtx.deriv_reflect`). -/

/-- **Phase 5's target (the mathematical crux)**: given `FLO`-coherence at stage `σ`, a
`NIK`-derivation witnessed at one label `y₀` fresh w.r.t. the ambient graph transports to ANY
other label `y'` in `(𝒮.H σ).G.X` -- including "old" labels already present, not just fresh ones
-- generalising `NIK.freshWitness_transport` (above) beyond the shared coinfinite reserve. This is
exactly the fact `ChainCtx.deriv_reflect` (~line 395) and `dwitness_mem_of_maximal`'s diamond
sub-case (~line 1030) could not close without it (see the module analysis preceding
`ChainCtx.deriv_reflect`, ~line 295).

**Proof shape (see the module section immediately above for the full deviation writeup)**: built
from `NIK.relabelFresh` with `a := y₀`, `b := y'`, exactly mirroring `NIK.freshWitness_transport`'s
own proof shape but with `substFn` in place of `swapFn` -- `substFn y₀ y'` fixes `y'` outright
(never sends `y' ↦ y₀`), so it never disturbs whatever structure `(𝒮.H σ).G` already has at `y'`,
avoiding the naive-swap collision by construction. `hflo`/`FLO`/`rankOf` are not needed by this
proof (see the deviation note); `hflo` remains in the signature because it was fixed here by
Phase 1's landed scaffolding. -/
theorem flo_oldlabel_transport {𝒮 : FloSeq 𝒯 Atom G₀} {σ : Stage} (_hflo : FLO 𝒮 σ)
    {x y₀ : Label Atom} {A : Proposition Atom} {Γ : List (LabelledFormula Atom)}
    (h : NIK 𝒯 ((𝒮.H σ).G.addEdge x y₀) Γ (y₀ ∶ A)) (hy₀ : y₀ ∉ (𝒮.H σ).G.X) (hxy₀ : x ≠ y₀)
    (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀) :
    ∀ y' ∈ (𝒮.H σ).G.X, x ≠ y' → (∀ ψ ∈ Γ, ψ.lbl ≠ y') →
      NIK 𝒯 ((𝒮.H σ).G.addEdge x y') Γ (y' ∶ A) := by
  intro y' _hy' hxy' _hΓy'
  have hf : ∀ p q, ((𝒮.H σ).G.addEdge x y₀).R p q →
      ((𝒮.H σ).G.addEdge x y').R (substFn y₀ y' p) (substFn y₀ y' q) := by
    intro p q hpq
    rcases hpq with hpq | ⟨rfl, rfl⟩
    · have hp : p ≠ y₀ := fun hp => hy₀ (hp ▸ ((𝒮.H σ).G.edge_mem p q hpq).1)
      have hq : q ≠ y₀ := fun hq => hy₀ (hq ▸ ((𝒮.H σ).G.edge_mem p q hpq).2)
      rw [substFn_other hp, substFn_other hq]
      exact Or.inl hpq
    · rw [substFn_other hxy₀, substFn_self]
      exact Or.inr ⟨rfl, rfl⟩
  have hstep := h.relabelFresh (a := y₀) (b := y') (G' := (𝒮.H σ).G.addEdge x y') hf
  rwa [List.map_substFn_eq_self hΓ, show substFn y₀ y' y₀ = y' from substFn_self y₀ y'] at hstep

end Cslib.Logic.Modal.Labelled
