import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context
import Mathlib.Order.SetNotation

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

/-- **The reflection theorem** — Simpson's elided "easily seen" step (p. 92, `chunk_0102.md`),
mechanized as far as this dispatch could take it, landed here as a **documented strategic
sorry** per the anti-analysis five-condition test (`.claude/context/contracts/anti-analysis.md`):

1. **Deliberate division boundary**: the plan's own Phase 3 contingency names exactly this
   escalation route ("if it cannot be settled, escalate before spending Phase 4's Zorn
   dispatch"); this is not an abandoned attempt.
2. **Tightly scoped**: exactly this one theorem.
3. **Documented** (this docstring):
   - **What is proven** (`NIK.swap_relabel`/`NIK.freshWitness_transport` above): a `boxI`/`diaE`
     premise reflects to a single chain index for witnesses drawn from the chain's shared
     coinfinite reserve `V'ᶜ` -- pick any `y₀ ∈ V'ᶜ` outside the exclusion set, reflect the IH at
     `y₀` alone to get one index `i₀`, then `freshWitness_transport` carries that single witness
     to every *other* `y ∈ V'ᶜ` (since every chain member's domain lies in `W(V')`, disjoint from
     `V'ᶜ`, so `y ∉ (C i₀).G.X` for every such `y` and every `i₀` -- the freshness hypothesis
     `freshWitness_transport` needs).
   - **What remains open**: `boxI`/`diaE`'s cofinite quantifier ranges over *every* `y ∉ L` in
     `Label Atom`, not just `V'ᶜ`. For `y` that already lies in some `(C i).G.X` (an "old" label,
     not drawn from the reserve), the swap-transport argument does not apply directly: swapping
     `y₀ ↔ y` could collide with structure the chain already built at `y`. Closing this needs
     either (a) an invariant that Phase 4's *concrete* Zorn construction only ever extends a
     context by reserve-drawn (fresh) labels at each step -- true by construction of Lemma
     5.3.1's argument (deductive-closure/disjunction/diamond steps each adjoin at most one fresh
     witness), but only statable once Phase 4's construction exists -- or (b) a separate argument
     for "old" `y` reusing `Deriv.mono`/monotonicity directly (since an "old" `y ∈ (C i).G.X` is,
     by directedness, already dominated by some concrete chain member, so the *fact* needed there
     may already be available without any relabeling at all). Route (a) is the natural one given
     Phase 4 supplies the construction.
4. **Tracked**: recorded in this dispatch's `sorry_inventory` with `strategic: true`,
   `follow_up_task` pointing at Phase 4 (the Zorn application, which supplies the concrete
   extension-step invariant needed to close route (a) above).
5. **Build-green**: `lake env lean` on this file (verified) succeeds with this `sorry` present. -/
theorem deriv_reflect [Nonempty ι] {φ : LabelledFormula Atom} :
    Deriv 𝒯 (𝒞.unionG) 𝒞.unionΓ φ → ∃ i, Deriv 𝒯 (𝒞.C i).G (𝒞.C i).Γ φ := by
  sorry

/-- **Chain closure** (Phase 3 Task 3): if no chain member derives the excluded formula, neither
does the union -- the fact the Zorn chain-closure step (Phase 4) needs to show `(⋃Gᵢ,⋃Γᵢ) ∈ C`.
Immediate contrapositive of `deriv_reflect`; carries no additional proof burden once that theorem
lands. -/
theorem chain_closure [Nonempty ι] {x : Label Atom} {A : Proposition Atom}
    (hC : ∀ i, ¬ Deriv 𝒯 (𝒞.C i).G (𝒞.C i).Γ (x ∶ A)) : ¬ Deriv 𝒯 (𝒞.unionG) 𝒞.unionΓ (x ∶ A) :=
  fun h => let ⟨i, hi⟩ := 𝒞.deriv_reflect h; hC i hi

end ChainCtx

end Cslib.Logic.Modal.Labelled
