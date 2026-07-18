import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context
import Mathlib.Order.SetNotation
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Ordinal.Arithmetic

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

/-- **The reflection theorem** — Simpson's elided "easily seen" step (p. 92, `chunk_0102.md`),
mechanized as far as this dispatch could take it, landed here as a **documented strategic
sorry** per the anti-analysis five-condition test (`.claude/context/contracts/anti-analysis.md`):

1. **Deliberate division boundary**: the plan's own Phase 3 contingency names exactly this
   escalation route ("if it cannot be settled, escalate before spending Phase 4's Zorn
   dispatch"); this is not an abandoned attempt. A dedicated joint follow-up dispatch
   (task 517) re-investigated three further shortcuts and ruled all three out formally — see the
   "Joint follow-up dispatch" section immediately above this docstring.
2. **Tightly scoped**: exactly this one theorem.
3. **Documented** (this docstring; full analysis in the module section above):
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
     `y₀ ↔ y` could collide with structure the chain already built at `y`. **Closing this needs
     route (a)**: an invariant that the construction only ever extends a context by reserve-drawn
     (fresh) labels at each step, carried via a step-indexed/well-founded reconstruction of the
     whole Zorn argument (Mathlib's `zorn_le₀` is non-constructive and cannot supply this).
     Route (b) (a monotonicity argument reusing the IH directly for old labels, no relabelling)
     was tested this dispatch and does not close the gap either: see "Shortcut 2" above — the
     obstruction is the *unbounded family of distinct chain indices*, which no single application
     of `Deriv.mono`/directedness resolves.
4. **Tracked**: recorded in this dispatch's `sorry_inventory` with `strategic: true`,
   `follow_up_task` pointing at a **new, dedicated "Phase 4.5" planning effort** (transfinite
   Lindenbaum construction with a fresh-labels-only invariant) — not a further quick dispatch;
   see the module section above for why the fix is scoped larger than one lemma.
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

/-- **The maximality argument for the diamond witness.** If `y:◇B ∈ H.Γ`, the diamond-witness
label `dwitness y B` must already be in `H.G.X` — else adjoining it, together with the fresh edge
`y R dwitness y B` and the formula `dwitness y B : B`, keeps the extension in `C`:
`NIK.diaWitness_transport` turns the one witnessing `NIK`-derivation into a cofinite one, letting
`NIK.diaE` (fed by `y:◇B`, itself already `Γ`-assumable) rebuild a derivation of the excluded
`x₀:A₀` back over `H` alone, contradicting `hnd`. This forces the extension to equal `H`, i.e.
the witness was already present. Simpson `chunk_0103.md`: *"We show that `v_{y.B}` is in `H`."* -/
theorem dwitness_mem_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) {y : Label Atom}
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
      -- **STRATEGIC SORRY** (documented per the anti-analysis five-condition test):
      --
      -- 1. Deliberate division boundary: this is the SAME cofinite-quantification obstacle
      --    `deriv_reflect` hits (see the "Joint follow-up dispatch" module section preceding
      --    `ChainCtx.deriv_reflect`, ~line 295, for the full sharpened root-cause diagnosis
      --    established by a dedicated joint dispatch, task 517) -- `NIK.diaE`'s eigenvariable
      --    premise `∀y'∉L, ...` ranges over EVERY label outside a FINITE `L`, including labels
      --    already in `H.G.X` ("old" labels), for which `NIK.diaWitness_transport` (built above,
      --    mirroring `NIK.freshWitness_transport`) does not apply -- its own hypothesis needs the
      --    TARGET label fresh w.r.t. `H.G.X`, which cannot be guaranteed merely by choosing the
      --    label outside a *finite* exclusion set when `H.G.X` may be infinite (and, for a
      --    Zorn-maximal `H`, generically IS infinite -- maximality forces `H.G.X` to be "as large
      --    as possible" subject to `V'`-confinement).
      -- 2. Tightly scoped: exactly the "build the cofinite `diaE` premise from the single
      --    witness `v = dwitness y B`" step -- everything else in this clause (the extension's
      --    `Context` validity, the maximality wiring, the fresh-label sub-case via
      --    `NIK.diaWitness_transport`) is proven above, sorry-free.
      -- 3. Documented: what is proven -- `hNIKv` gives the ONE witnessing instance at `v` itself
      --    (always usable, `v` fresh by `hfresh`); `NIK.diaWitness_transport` transports this to
      --    any OTHER label `y'` that is *also* fresh w.r.t. `H.G.X` (not just outside a finite
      --    set). What remains open, and WHY (joint dispatch, task 517, three additional
      --    shortcuts tested and ruled out beyond the plan's own two candidates):
      --      - A naive swap `swapFn v y'` for an "old" `y' ∈ H.G.X` is not merely unproven but
      --        actively INVALID whenever `H.G` has any edge incident to `y'` other than possibly
      --        `(y,y')` itself: such an edge `(p,y')` swaps to `(p,v)`, which is not an edge of
      --        the target graph `H.G.addEdge y y'` (the target graph does not know about `v` at
      --        all) -- the swap corrupts pre-existing structure at `y'`, not just failing to
      --        prove the desired fact.
      --      - Reusing an already-established fact at `y'` directly (skipping the swap) does not
      --        help either in this single-maximal-element setting (no chain/index family is even
      --        available here to reuse from) and, in the analogous chain setting
      --        (`deriv_reflect`), reduces to a distinct-index-per-label problem directedness
      --        cannot bound (see "Shortcut 2" in the module section near `deriv_reflect`).
      --      - Choosing a cleverer finite exclusion set `L` does not help: `L` must stay finite,
      --        but `H.G.X` is (generically) infinite, so infinitely many "old" labels remain
      --        outside any finite `L` regardless of how `L` is chosen.
      --    Closing this needs route (a): an invariant that the *construction* of `H` (not just
      --    its final maximality property) only ever adjoins fresh (reserve-drawn or
      --    dwitness-of-already-known) labels at each step -- unavailable from Mathlib's
      --    non-constructive `zorn_le₀`, and requiring a step-indexed/well-founded reconstruction
      --    of the whole Zorn argument (a "Phase 4.5", scoped larger than a single dispatch; see
      --    the module section above `deriv_reflect` for the full argument, including why
      --    Simpson's own "denumerable ⟹ choice-free iterative" remark, `chunk_0103.md`, does not
      --    directly transfer here since `Atom : Type u` is not assumed countable).
      -- 4. Tracked: recorded in this dispatch's `sorry_inventory` with `strategic: true`,
      --    `follow_up_task: "Phase 4.5 (NEW, dedicated multi-phase effort): step-indexed /
      --    well-founded Lindenbaum construction with a fresh-labels-only invariant, replacing
      --    zorn_le₀ in primeC_exists_maximal -- not a further quick joint dispatch."`
      -- 5. Build-green: `lake env lean` on this file (verified) succeeds with this `sorry`
      --    present.
      sorry
  have hge := hmax.le_of_ge hmem hle
  exact hfresh (hge.1.1 (Or.inr (Or.inr rfl)))

/-- **Clause 4** (`TPrime.diamond`): the diamond property (Simpson `chunk_0103.md`, *"`v_{y.B}`
is the variable required by the diamond property"*). Once `dwitness_mem_of_maximal` supplies
membership of the witness label, `Context.dwitnessMem` (a *field* every `Context` — including
the maximal `H` — already carries, Simpson's "requirement 2 on contexts") directly yields both
conjuncts the diamond property needs; no separate argument is required for this half. -/
theorem diamond_of_maximal {G₀ : Context 𝒯 Atom} {x₀ : Label Atom} {A₀ : Proposition Atom}
    {H : Context 𝒯 Atom} (hmax : Maximal (· ∈ primeC G₀ x₀ A₀) H) :
    ∀ (y : Label Atom) (B : Proposition Atom), (y ∶ Proposition.diamond B) ∈ H.Γ →
      ∃ v, H.G.R y v ∧ (v ∶ B) ∈ H.Γ :=
  fun y B hyB => ⟨Label.dwitness y B, H.dwitnessMem y B (dwitness_mem_of_maximal hmax hyB)⟩

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
The maximal element's `TPrime` structure carries `clModel`/`consistency`/`disjunction`/
`deductiveClosure` sorry-free — `deductiveClosure`'s one dependency, `NIK.subst` (cut
admissibility), was closed by a follow-up dispatch via `NIK.subst_aux` (structural induction,
generalizing over the accumulating prefix `Δ'`, mirroring `NIK.weaken`'s case shape). `diamond`
still routes through `dwitness_mem_of_maximal`'s one remaining documented strategic sorry (the
"old label" cofinite-range sub-case, same root cause as `ChainCtx.deriv_reflect`'s Phase 3
sorry) — see that theorem's docstring. -/
theorem primeLemma (G₀ : Context 𝒯 Atom) (x₀ : Label Atom) (A₀ : Proposition Atom)
    (h0 : ¬ Deriv 𝒯 G₀.G G₀.Γ (x₀ ∶ A₀)) :
    ∃ P : TPrime 𝒯 Atom, G₀ ≤ P.toContext ∧ ¬ Deriv 𝒯 P.G P.Γ (x₀ ∶ A₀) := by
  obtain ⟨H, hmax⟩ := primeC_exists_maximal G₀ x₀ A₀ (primeC_mem_base G₀ x₀ A₀ h0)
  obtain ⟨hG₀H, _, hnd⟩ := hmax.prop
  exact ⟨{ H with
      clModel := clModel_of_maximal hmax
      deductiveClosure := deductiveClosure_of_maximal hmax
      consistency := consistency_of_maximal hmax
      disjunction := disjunction_of_maximal hmax
      diamond := diamond_of_maximal hmax },
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
  sorry

/-- **Phase 4's target**: running the staged construction to a sufficiently large stage yields a
maximal, `FLO`-carrying context, **replacing** `primeC_exists_maximal`'s non-constructive
`zorn_le₀` (above) with the explicit staged construction. `hfair` is the schedule-fairness
hypothesis (every task is eventually attempted) Phase 4 needs to argue the resulting `H` is
genuinely maximal, not merely FLO-coherent. Not attempted here; sorried scaffolding for Phase 4. -/
theorem primeC'_exists_maximal (x₀ : Label Atom) (A₀ : Proposition Atom)
    (h0 : G₀ ∈ primeC G₀ x₀ A₀) (𝒮 : FloSeq 𝒯 Atom G₀)
    (hfair : ∀ t : FloTask 𝒯 Atom, ∃ σ : Stage, 𝒮.task σ = t) :
    ∃ σ : Stage, Maximal (· ∈ primeC G₀ x₀ A₀) (𝒮.H σ) ∧ FLO 𝒮 σ := by
  sorry

/-- **Phase 5's target (the mathematical crux)**: given `FLO`-coherence at stage `σ`, a
`NIK`-derivation witnessed at one label `y₀` fresh w.r.t. the ambient graph transports to ANY
other label `y'` in `(𝒮.H σ).G.X` -- including "old" labels already present, not just fresh ones
-- generalising `NIK.freshWitness_transport` (above) beyond the shared coinfinite reserve. This is
exactly the fact `ChainCtx.deriv_reflect` (~line 395) and `dwitness_mem_of_maximal`'s diamond
sub-case (~line 1030) could not close without it (see the module analysis preceding
`ChainCtx.deriv_reflect`, ~line 295): FLO-2's `rankOf`-indexed edge locality is what makes a
rank-indexed (well-founded) induction transport the witnessing derivation across old labels
legitimate, where a bare `swapFn` transposition is not (Postmortem Constraints: "do not
naive-swap `swapFn v y'` for an 'old' label"). Not attempted here; sorried scaffolding for
Phase 5. -/
theorem flo_oldlabel_transport {𝒮 : FloSeq 𝒯 Atom G₀} {σ : Stage} (hflo : FLO 𝒮 σ)
    {x y₀ : Label Atom} {A : Proposition Atom} {Γ : List (LabelledFormula Atom)}
    (h : NIK 𝒯 ((𝒮.H σ).G.addEdge x y₀) Γ (y₀ ∶ A)) (hy₀ : y₀ ∉ (𝒮.H σ).G.X) (hxy₀ : x ≠ y₀)
    (hΓ : ∀ ψ ∈ Γ, ψ.lbl ≠ y₀) :
    ∀ y' ∈ (𝒮.H σ).G.X, x ≠ y' → (∀ ψ ∈ Γ, ψ.lbl ≠ y') →
      NIK 𝒯 ((𝒮.H σ).G.addEdge x y') Γ (y' ∶ A) := by
  sorry

end Cslib.Logic.Modal.Labelled
