/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Zorn

/-! # The Prime Lemma (Simpson 5.3.1): constructive `𝒯`-prime extension

This module lands A. K. Simpson's **Prime Lemma** [Simpson1994], `chunk_0102.md` (§5.3, Lemma
5.3.1): given a context `(G₀,Γ₀)` that does not derive an excluded formula `x₀:A₀`, there is a
`𝒯`-prime context `(H,Δ) ≥ (G₀,Γ₀)` that still does not derive `x₀:A₀`. This is the
Lindenbaum-style maximalisation step the constructive canonical model (Simpson 5.3.2) reads truth
off from.

## Contents

- `swapFn`/`NIK.swap_relabel`/`NIK.freshWitness_transport`: the two-label-swap relabeling lemma
  (Simpson Prop. 4.4.1 specialized to a swap) and its corollary transporting a derivation
  witnessed at one fresh label to any other fresh label.
- `substFn`/`NIK.relabelFresh`: the one-directional analogue (`a ↦ b`, no freshness needed on the
  target `b`) used by the "old label" transport lemmas below.
- `NIK.oldLabelTransport`/`NIK.diaWitnessTransportOld`: the "old label" corollaries -- a
  cofinitely-quantified `NIK` premise witnessed at a fresh label transports to a label that is
  already a member of the ambient graph.
- `GChain`/`TClosure.reflectChain`/`NIK.reflectChain`: a graph-only chain abstraction and the
  `NIK`-level reflection theorem -- a derivation over a chain's union graph reflects to a single
  chain member (Simpson's elided "easily seen" step in the Prime Lemma proof, `chunk_0102.md`:
  *"Let `{(Gᵢ,Γᵢ)}ᵢ∈I` be any chain in the set `C` ... It is easily seen that `(⋃ᵢGᵢ,⋃ᵢΓᵢ)` is
  also in `C`."*).
- `ChainCtx`/`ChainCtx.deriv_reflect`/`ChainCtx.chain_closure`: the context-level packaging of the
  reflection theorem and the corollary the Zorn chain-bound argument below consumes.
- `primeC`/`primeC_mem_base`/`primeC_chain_bddAbove`/`primeC_exists_maximal`: the Zorn poset of
  `𝒯`-prime candidates confined to `G₀`'s fixed coinfinite reserve, and Zorn's Lemma applied to it
  (`zorn_le₀`).
- The five clause theorems discharging `TPrime`'s obligations at the maximal element:
  `clModel_of_maximal`, `deductiveClosure_of_maximal`, `consistency_of_maximal`,
  `disjunction_of_maximal`, `diamond_of_maximal` (the last via `dwitness_mem_of_maximal` and
  `NIK.subst`/`NIK.subst_aux`).
- `primeLemma`: the assembled result.

## Scope note

This file lands `primeLemma` and its **actual** sorry-free dependency closure: `primeLemma` is
fully sorry-free and axiom-clean, `lean_verify` ⊆ `[propext, Classical.choice, Quot.sound]`.
`primeLemma` is assembled via `primeC_exists_maximal` (plain `zorn_le₀`, this file) and does
**not** need the step-indexed "FLO" (fresh-labels-only extension) well-founded reconstruction
(`Stage`/`FloSeq`/`FLO`/`flo_succ`/`flo_limit`/`primeC'_exists_maximal`/`flo_oldlabel_transport`)
that was originally built to attack the "old label" obstacle: that obstacle is dissolved here
instead by the one-directional `substFn`/`NIK.relabelFresh` transport lemmas above, independently
of how the maximal context is constructed. The FLO apparatus remains correct, landed scaffolding
elsewhere but is **not transcribed to mainline**, since it still carries two open, documented,
non-blocking sorries (`flo_succ`'s superseded `redundantEdge` branch; `primeC'_exists_maximal`'s
`Maximal`-conjunct half) and is not on `primeLemma`'s dependency path -- transcribing it here
would violate this file's zero-debt requirement for no proof-theoretic benefit.

## Provenance

Literature: `chunk_0087.md`, `chunk_0088.md` (Prop. 4.4.1, graph morphisms, §4.4), `chunk_0102.md`
(Lemma 5.3.1, the Prime Lemma, §5.3). PDF offset +9.
-/

@[expose] public section

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

/-! ## `substFn`/`NIK.relabelFresh`: one-directional relabeling

**Placement note**: this block (supporting machinery for `flo_oldlabel_transport`, defined much
later in the file) is placed here, ahead of that original position, so that
`ChainCtx.deriv_reflect` and `dwitness_mem_of_maximal` -- both defined below -- can consume it
too. See `flo_oldlabel_transport`'s docstring (further below) for the full mathematical writeup
of why a *one-directional* substitution, unlike `swapFn`'s involution, never disturbs the target
label's own pre-existing structure and so needs no freshness hypothesis on the target at all. -/

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

/-- **Old-label transport, graph-generic form**: the graph-level fact
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
  have hf : ∀ p q, (G.addEdge x y₀).R p q →
      (G.addEdge x y').R (substFn y₀ y' p) (substFn y₀ y' q) := by
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

/-- **Old-label diamond-witness transport, graph-generic form**: the
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
  have hf : ∀ p q, (G.addEdge x y₀).R p q →
      (G.addEdge x y).R (substFn y₀ y p) (substFn y₀ y q) := by
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

/-! ## `GChain`: a graph-only chain, and the `NIK`-level reflection theorem

**Finding (corrects the superseded historical analysis below)**: that analysis concluded
reflection needs a step-indexed FLO reconstruction because every route it tried transported a
*single* witnessed fact to *every* other label via a **swap** (`swapFn`, an involution) or via
reusing the induction hypothesis with a *different* chain index per label. Neither obstacle
applies to the **one-directional** `substFn`-based transport (`NIK.oldLabelTransport`/
`NIK.diaWitnessTransportOld` above, generalizing the `flo_oldlabel_transport` insight to an
arbitrary graph): it needs freshness of only
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
  have hinf : (V'ᶜ \ {n : PrefixVar | Label.var n ∈ F}).Infinite := hV'.sdiff hFvars
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

/-- **The master reflection theorem**: a `NIK`-derivation over (an upper bound
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
      have hxy₀ : x ≠ y₀ := fun heq =>
        hnF (Or.inl (Or.inl (Or.inr (Set.mem_singleton_iff.mpr heq.symm))))
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

/-! ## Chains of contexts and their shared coinfinite reserve

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

/-! ## Superseded historical analysis of the "old label" obstacle

**Historical note, kept for context only: the diagnosis below concluded the "old label" obstacle
shared by `deriv_reflect` (below) and `dwitness_mem_of_maximal` needed a step-indexed /
well-founded Lindenbaum reconstruction. That conclusion is now known to be wrong** — see
`NIK.reflectChain`'s docstring above and `deriv_reflect` below for the actual fix, a
one-directional `substFn`-based transport that needs freshness of only the source witness. This
section is retained only because it records why three natural shortcuts (a finite-subgraph
existential in `Deriv`; reusing the induction hypothesis directly at each "old" label without
relabeling; a conditional strengthening of `ChainCtx`) each independently fail for a
**swap**-based or **no-relabeling** transport specifically — that negative result is genuine and
does not depend on the (mistaken) conclusion drawn from it. The core tension driving all three
attempts: `NIK.boxI`/`NIK.diaE`'s cofinite-quantification encoding gives equivariance (uniform
behaviour under relabeling) for free only when the cofinite family is built by a uniform,
swap-invariant construction; it does not give, for free, a way to *recover* a cofinite family
from a single instance obtained via an existential (choice-based) argument such as a Zorn-maximal
element. The one-directional `substFn`-based transport used by the actual fix sidesteps this
tension entirely, rather than resolving it within the swap/no-relabeling framework these three
shortcuts were confined to. -/

/-- `NIK.reflectChain` closes the "old label" obstacle discussed above. The "old label" obstacle
only blocks a **swap**-based transport or a **no-relabeling** reuse of the induction hypothesis;
the **one-directional** `substFn`-based transport (`NIK.oldLabelTransport`, built from
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
      rw [Set.sdiff_eq_empty]
      intro z hz
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      exact 𝒞.hCV' i z hzi
    rw [heq]
    exact Set.finite_empty
  obtain ⟨i, hi⟩ := NIK.reflectChain 𝒞.hV' hNIK 𝒢₀ hG₀ hextra₀
  obtain ⟨i', hi'⟩ := 𝒞.exists_index_of_subset_unionΓ Γ₀ hΓ₀
  obtain ⟨i'', h1, h2⟩ := 𝒞.dir i i'
  exact ⟨i'', Γ₀, fun ψ hψ => (𝒞.mono h2).2 (hi' ψ hψ), hi.weaken (𝒞.mono h1).1 (fun _ h => h)⟩

/-- **Chain closure**: if no chain member derives the excluded formula, neither does the union
-- the fact the Zorn chain-closure step below needs to show `(⋃Gᵢ,⋃Γᵢ) ∈ C`. Immediate
contrapositive of `deriv_reflect`; carries no additional proof burden once that theorem lands. -/
theorem chain_closure [Nonempty ι] {x : Label Atom} {A : Proposition Atom}
    (hC : ∀ i, ¬ Deriv 𝒯 (𝒞.C i).G (𝒞.C i).Γ (x ∶ A)) : ¬ Deriv 𝒯 (𝒞.unionG) 𝒞.unionΓ (x ∶ A) :=
  fun h => let ⟨i, hi⟩ := 𝒞.deriv_reflect h; hC i hi

end ChainCtx

/-! ## Bounded Prime Lemma (Simpson 5.3.1) — Zorn over whole contexts

**Objective**: `Γ ⊬_G x:A ⟹ ∃ 𝒯-prime (H,Δ) ⊇ (G,Γ)` with `Δ ⊬_H x:A` — Simpson's Prime Lemma
5.3.1 (`chunk_0102.md`/`chunk_0103.md`, p. 92-93 raster), a Zorn maximalisation over **whole
contexts** (`Context 𝒯 Atom`), producing an inhabitant of the repaired `TPrime`.

## `--lit` research resolution: unbounded (Ch 5) vs bounded (Ch 7-8) form

There is a genuine open question here: whether the *bounded* prime lemma (Ch 7-8, Lemma 8.2.6)
is needed, or the *unbounded* Chapter 5 form (5.3.1) suffices. **Resolved here, against the
raster**:
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
what this file transcribes; a "T-Comp graph completion … symmetry" step some earlier planning
considered is consequently unneeded for a `TPrime`-typed target -- flagged here rather than
silently skipped or forced through.

## Clause 0 without an existential witness search: the "redundant edge" argument

Simpson's own clause-0 argument (`chunk_0102.md`) is written for the *general* geometric-sequent
shape, which admits a disjunctive, existentially-witnessed conclusion (`GeomAxiom`'s absent
`k`-ary witness case, see `Deduction.lean`'s docstring); its maximality step searches for a vector
of *fresh* witness variables. `GeomAxiom` (`T`, `B`, `Four`, `Five`) is **entirely** Horn, with
**no** existential conclusion (`m = 1`, witness vector length `0`) — so that general argument's
witness-search machinery does not directly transcribe, and this file reconstructs the specialised
Horn-only argument from Simpson's *stated property* ("H is a classical model of 𝒯"), per the
literature-fidelity discipline. The reconstruction: `NIK`'s only graph-reading rules (`boxE`,
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
- `ChainCtx.unionContext`: packages `ChainCtx.unionG`/`unionΓ` (above) into a genuine
  `Context 𝒯 Atom` (`ctxSubset`/`coinfinite`/`dwitnessMem`) — the missing piece not needed for
  the reflection theorem alone but needed by the Zorn upper-bound step below.
- `primeC`: Simpson's poset `C` (`:5990`) — contexts extending `(G₀,Γ₀)`, confined to `W(V')`,
  that still fail to derive the excluded `x₀:A₀`.
- `primeC_exists_maximal`: Zorn's lemma applied to `primeC` (via `zorn_le₀`), using
  `ChainCtx.chain_closure` (above) for the chain upper bound.
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

/-- **The chain union, packaged as a genuine `Context 𝒯 Atom`.** `unionG`/`unionΓ` above
produce only the graph and formula-set; the Zorn upper-bound step needs the union to satisfy
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
G₀.coinfinite.choose`, and reuses `chain_closure` above for the one nontrivial conjunct
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

/-- **`(◇E)`-shaped freshness transport.** A corollary of `NIK.swap_relabel` (above), in the
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
`dwitness_mem_of_maximal` to separate the excluded label `x₀` from the newly adjoined witness
`v`. -/
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

**`hx₀ : x₀ ∈ G₀.G.X`**: Simpson's own Prime Lemma statement
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
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) (hx₀ : x₀ ∈ G₀.G.X)
    {y : Label Atom} {B : Proposition Atom} (hyB : (y ∶ Proposition.diamond B) ∈ H.Γ) :
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
      -- Same fix as `ChainCtx.deriv_reflect`: the one-directional `substFn`-based transport
      -- (`NIK.diaWitnessTransportOld`, built from `NIK.relabelFresh`) needs freshness of only the
      -- *source* witness `v`, not the target, so the single instance `hNIKv` already supplies the
      -- whole cofinite family. The one genuine extra requirement -- the excluded label `x₀` must
      -- differ from `v` itself, else the transported conclusion's label would move out from under
      -- `x₀` -- is discharged by the `hx₀ : x₀ ∈ G₀.G.X` hypothesis (this theorem's docstring)
      -- together with `v ∉ H.G.X` (`hfresh`).
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

**Fully sorry-free**: all five clauses -- `clModel`/`consistency`/`disjunction`/
`deductiveClosure` (via `NIK.subst_aux`) and `diamond` (`dwitness_mem_of_maximal`, via
`NIK.diaWitnessTransportOld`) -- are sorry-free. `lean_verify`: axioms `[propext,
Classical.choice, Quot.sound]`, no `sorryAx`.

**Note on the FLO reconstruction**: `primeLemma` is assembled from `primeC_exists_maximal` (the
plain `zorn_le₀` Zorn maximalisation), NOT `primeC'_exists_maximal` (the FLO-carrying
reconstruction) -- it does not need FLO at all. The "old label" obstacle both `deriv_reflect` and
`dwitness_mem_of_maximal` hit turned out to be resolvable at the `NIK`/`Graph` level alone
(`NIK.oldLabelTransport`/`NIK.diaWitnessTransportOld`, built from `NIK.relabelFresh`), independent
of *how* the maximal `H` was constructed. The FLO apparatus (`Stage`/`FloSeq`/`FLO`/`flo_succ`/
`flo_limit`/`primeC'_exists_maximal`/`flo_oldlabel_transport`) remains landed (preserved verbatim)
but is not on `primeLemma`'s critical path; `primeC'_exists_maximal`'s own remaining
`Maximal`-conjunct sorry and `flo_succ`'s superseded `redundantEdge` sorry are consequently
non-blocking for this theorem. **Hypothesis `hx₀ : x₀ ∈ G₀.G.X`**: Simpson's own statement of the
judgement `Γ ⊬_G x:A` presupposes `x` is a label of `G` (the standing convention every other
`Deriv`/`NIK` judgement in this development already carries for `Γ`'s own labels via
`Context.ctxSubset`); it is threaded explicitly here because `dwitness_mem_of_maximal` needs it
to separate the excluded label `x₀` from the freshly adjoined diamond witness (see that
theorem's docstring for the exact argument). -/
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

end Cslib.Logic.Modal.Labelled
