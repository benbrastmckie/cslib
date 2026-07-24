/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.PrimeLemma
public import Cslib.Logics.Modal.Metalogic.Constructive.Forcing

/-! # The Canonical Model and Truth Lemma (Simpson 5.3.2): the labelled/bounded-context route

This module lands A. K. Simpson's **canonical model** `𝒦^𝒯` and the **canonical model lemma**
[Simpson1994], Lemma 5.3.2 (`chunk_0103.md`-`chunk_0105.md`, pp. 94-95): for every `𝒯`-prime
context `(H,Δ)` and every label `y` in `H`, the semantic satisfaction relation `(H,Δ),y ⊩ B`
coincides with syntactic membership `y:B ∈ Δ`.

## The Canonical Relation is the Raw, Uncompleted `xRy`

`chunk_0103.md` (pp. 93-94) states the canonical model construction verbatim: *"We now construct
the canonical `𝒯`-model, `𝒦^𝒯 = ⟨W^𝒯, ≤^𝒯, D_(H,Δ), R_(H,Δ), a_(H,Δ)⟩`. Define: `W^𝒯` = the set of
`𝒯`-prime contexts, `(H,Δ) ≤^𝒯 (H',Δ')` iff `(H,Δ) ⊆ (H',Δ')`, `D_(H,Δ)` = the underlying set of
`H`, `R_(H,Δ)(x,y)` iff `xRy in H`, `a_(H,Δ)(x)` iff `x:a ∈ Δ`."* -- **the canonical relation is
the RAW `xRy` in `H`**, per the primary source. `chunk_0104.md`/`chunk_0105.md` then prove
Lemma 5.3.2 case-by-case; the `□`/`◇` cases are transcribed essentially verbatim into
`canon_truth_lemma` below (see that theorem's docstring for the case-by-case citation).

This module consumes the raw relation `H.G.R` from `primeLemma`'s output **directly**
(`CanonWorld.r` below is defined from `ctx.G.R`, with no `TClosure`/graph-completion step).
Lemma 8.2.6 (`chunk_0166.md`, Chapter 8) is the **bounded** canonical model lemma -- a
depth-indexed statement about *bounded* `𝒯`-prime contexts, a different route from the one
mechanized here (the landed `TPrime` requires the *unbounded* Ch 5 route, raw `clModel`). Since
Lemma 5.3.2's unbounded construction is what is mechanized here and it needs no
`TClosure`/`T-Comp(H)` completion step at any point (every case below closes using either the
raw relation directly, or a *fresh* re-application of `primeLemma`, never a
symmetrized/completed relation), the `T-Comp` graph-completion material (Simpson Lemma 8.2.5,
symmetry) is **unneeded** for this route and is not built.

## Main Definitions

- `CanonWorld`: a **pointed** `𝒯`-prime context `⟨ctx, lbl, mem⟩` -- Simpson's `(H,Δ), y` pair,
  packaged as a single type so it instantiates `CKForces`'s single-sorted `World` parameter.
  `CanonWorld.le` is context extension at a fixed label (`≤^𝒯`, persisting the same domain
  element); `CanonWorld.r` is the **raw**, same-context accessibility relation (`R_(H,Δ)`).
- `canonVal`/`canonBotForces`: the valuation `a_(H,Δ)` and the (trivial, always-`False`)
  `botForces` -- `TPrime`'s Consistency clause bans exploding worlds, so no world of this model is
  fallible; this collapses `CKForces` to ordinary bivalent forcing on this particular model
  (`∀`/`∃`-successor quantification over the trivial-`≤` slice degenerates to a single witness,
  matching Simpson's plain `∃`-diamond and `∀`-box).
- `canon_truth_lemma`: **Lemma 5.3.2** -- `CKForces CanonWorld.r canonVal canonBotForces w φ ↔
  (w.lbl ∶ φ) ∈ w.ctx.Γ`, by induction on `φ`.

## Provenance

Literature: `chunk_0103.md`-`chunk_0105.md` (Lemma 5.3.2, §5.3), `chunk_0166.md` (Lemma 8.2.6,
§8.2, cited only to confirm it is NOT needed here). PDF offset +9.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

open Cslib.Logic.Modal

universe u
variable {Atom : Type u} {𝒯 : Set GeomAxiom}

open Classical

/-! ## A small `Deriv`-level toolkit -/

/-- Any member of `Γ` is trivially `Deriv`-derivable from it (via the singleton witness list). -/
theorem Deriv.of_mem {G : Graph Atom} {Γ : Set (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    (h : φ ∈ Γ) : Deriv 𝒯 G Γ φ :=
  ⟨[φ], fun _ hψ => (List.mem_singleton.mp hψ) ▸ h,
    NIK.assumption G [φ] φ (List.mem_singleton_self _)⟩

/-- **`Deriv`-level `(⊃I)`.** If `φ` is `Deriv`-derivable from `Γ` extended by `x:A`, then
`x:A⊃φ.prop`-shaped conclusion... concretely: `x:B` derivable from `Γ ∪ {x:A}` gives `x:A⊃B`
derivable from `Γ` alone. Mirrors `Deriv.orE`/`Deriv.subst`'s filter-and-reweaken pattern. -/
theorem Deriv.impI {G : Graph Atom} {Γ : Set (LabelledFormula Atom)} {x : Label Atom}
    {A B : Proposition Atom} (h : Deriv 𝒯 G (insert (x ∶ A) Γ) (x ∶ B)) :
    Deriv 𝒯 G Γ (x ∶ Proposition.imp A B) := by
  classical
  obtain ⟨Γ₀, hΓ₀, hNIK⟩ := h
  set Γ₀' := Γ₀.filter (fun ψ => decide (ψ ≠ (x ∶ A))) with hdef
  have hmem' : ∀ ψ ∈ Γ₀', ψ ∈ Γ := by
    intro ψ hψ
    have hne : ψ ≠ (x ∶ A) := by simpa [hdef] using (List.of_mem_filter hψ)
    rcases hΓ₀ ψ (List.mem_of_mem_filter hψ) with rfl | h
    · exact absurd rfl hne
    · exact h
  have hsub : ∀ ψ ∈ Γ₀, ψ ∈ (x ∶ A) :: Γ₀' := by
    intro ψ hψ
    by_cases hcase : ψ = (x ∶ A)
    · exact hcase ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hψ, by simpa using hcase⟩)
  exact ⟨Γ₀', hmem', NIK.impI G Γ₀' x A B (hNIK.weaken (Graph.le_refl G) hsub)⟩

/-! ## `Label.InW` monotonicity -/

/-- `Label.InW` is monotone in the reserve `V'`: widening the reserve preserves membership in
`W(V')`. Structural recursion on the label, mirroring `Label.ne_dwitness_self`'s style. Needed to
patch a context's witnessing reserve after adjoining one fresh raw variable
(`Context.addFreshVar` below). -/
theorem Label.InW.mono {V' V'' : Set PrefixVar} (hsub : V' ⊆ V'') :
    ∀ (x : Label Atom), Label.InW V' x → Label.InW V'' x
  | .var _, h => hsub h
  | .dwitness x _, h => Label.InW.mono hsub x h

/-! ## `Context.addFreshVar`: adjoining one fresh raw-variable node and edge

Simpson's box-backward construction (`chunk_0104.md`, the `□B` case): given a `𝒯`-prime `(H,Δ)`
and `y ∈ H`, pick a coinfinite `V'` witnessing `H`'s clause 1, take `z ∈ V \ V'` fresh, and form
`H₀ := H ∪ {yRz}` (graph extended by one edge to a brand-new raw-variable node, `Δ` unchanged).
`z ∉ V'` forces `Label.var z ∉ H.G.X` (since `H.G.X ⊆ W(V')` and `Label.InW V' (Label.var z)`
unfolds to `z ∈ V'`), so `X` genuinely grows by one node; the witnessing reserve is patched to
`insert z V'` (still coinfinite -- removing one point from an infinite complement keeps it
infinite) to keep clause 1 satisfied. -/

/-- `H` extended by one edge `y R (Label.var z)` to a brand-new raw-variable node, `Γ` unchanged
(`chunk_0104.md`'s `H₀ := H ∪ {yRz}`). See the section docstring above for the full construction
and freshness argument. -/
@[nolint unusedArguments]
def Context.addFreshVar (H : Context 𝒯 Atom) (y : Label Atom) (hy : y ∈ H.G.X)
    (V' : Set PrefixVar) (hV' : Coinfinite V') (hHV' : ∀ x ∈ H.G.X, Label.InW V' x)
    (z : PrefixVar) (_hz : z ∉ V') : Context 𝒯 Atom where
  G := H.G.addEdge y (Label.var z)
  Γ := H.Γ
  ctxSubset := fun φ hφ => Or.inl (H.ctxSubset φ hφ)
  coinfinite := by
    refine ⟨insert z V', ?_, ?_⟩
    · have hcompl : (insert z V' : Set PrefixVar)ᶜ = V'ᶜ \ {z} := by
        ext w
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
        tauto
      change (insert z V' : Set PrefixVar)ᶜ.Infinite
      rw [hcompl]
      exact hV'.sdiff (Set.finite_singleton z)
    · intro x hx
      simp only [Graph.addEdge, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | heq | heq
      · exact Label.InW.mono (Set.subset_insert z V') x (hHV' x hx)
      · rw [heq]; exact Label.InW.mono (Set.subset_insert z V') y (hHV' y hy)
      · rw [heq]; exact Set.mem_insert z V'
  dwitnessMem := by
    intro x A hx
    simp only [Graph.addEdge, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨hR, hmem⟩ := H.dwitnessMem x A hx
      exact ⟨Or.inl hR, hmem⟩
    · have hmemX : Label.dwitness x A ∈ H.G.X := by rw [hx]; exact hy
      obtain ⟨hR, hmem⟩ := H.dwitnessMem x A hmemX
      exact ⟨Or.inl hR, hmem⟩
    · exfalso; injection hx

theorem Context.addFreshVar_le (H : Context 𝒯 Atom) (y : Label Atom) (hy : y ∈ H.G.X)
    (V' : Set PrefixVar) (hV' : Coinfinite V') (hHV' : ∀ x ∈ H.G.X, Label.InW V' x)
    (z : PrefixVar) (hz : z ∉ V') :
    H ≤ H.addFreshVar y hy V' hV' hHV' z hz :=
  ⟨⟨Set.subset_union_left, fun _ _ h => Or.inl h⟩, Set.Subset.refl _⟩

/-- The freshly-adjoined node is a member of the extended graph's domain. -/
theorem Context.mem_addFreshVar (H : Context 𝒯 Atom) (y : Label Atom) (hy : y ∈ H.G.X)
    (V' : Set PrefixVar) (hV' : Coinfinite V') (hHV' : ∀ x ∈ H.G.X, Label.InW V' x)
    (z : PrefixVar) (hz : z ∉ V') :
    Label.var z ∈ (H.addFreshVar y hy V' hV' hHV' z hz).G.X := by
  simp [Context.addFreshVar, Graph.addEdge]

/-! ## The canonical model -/

/-- A **pointed** `𝒯`-prime context: Simpson's `(H,Δ), y` pair (`chunk_0103.md`), packaged as a
single type so it instantiates `CKForces`'s single-sorted `World` parameter. `ctx` is the
`𝒯`-prime context, `lbl` the distinguished domain element, `mem` witnessing `lbl ∈ ctx.G.X`. -/
structure CanonWorld (𝒯 : Set GeomAxiom) (Atom : Type u) : Type u where
  /-- The `𝒯`-prime context. -/
  ctx : TPrime 𝒯 Atom
  /-- The distinguished domain element. -/
  lbl : Label Atom
  /-- `lbl` lies in `ctx`'s domain. -/
  mem : lbl ∈ ctx.G.X

/-- `(H,Δ),y ≤^𝒯 (H',Δ'),y'` (Simpson `chunk_0103.md`): `(H,Δ) ⊆ (H',Δ')` **and the same domain
element persists** (`y = y'`). This is the growing-domain order the `□`/`⊃` clauses of `CKForces`
quantify over. -/
def CanonWorld.le (w w' : CanonWorld 𝒯 Atom) : Prop :=
  w.ctx.toContext ≤ w'.ctx.toContext ∧ w.lbl = w'.lbl

instance : LE (CanonWorld 𝒯 Atom) := ⟨CanonWorld.le⟩

@[refl] theorem CanonWorld.le_refl (w : CanonWorld 𝒯 Atom) : w ≤ w :=
  ⟨Context.le_refl _, rfl⟩

theorem CanonWorld.le_trans {w w' w'' : CanonWorld 𝒯 Atom} (h1 : w ≤ w') (h2 : w' ≤ w'') :
    w ≤ w'' :=
  ⟨Context.le_trans h1.1 h2.1, h1.2.trans h2.2⟩

instance : Preorder (CanonWorld 𝒯 Atom) where
  le := CanonWorld.le
  le_refl := CanonWorld.le_refl
  le_trans := fun _ _ _ => CanonWorld.le_trans

/-- `R_(H,Δ)(x,y)` iff `xRy in H` (Simpson `chunk_0103.md`): the **raw**, same-context
accessibility relation -- confirmed against the source (module docstring, "`--lit` confirmation")
to be the raw graph relation `H.G.R`, not any `TClosure`/`T-Comp` completion. -/
def CanonWorld.r (w u : CanonWorld 𝒯 Atom) : Prop :=
  w.ctx = u.ctx ∧ w.ctx.G.R w.lbl u.lbl

/-- `a_(H,Δ)(x)` iff `x:a ∈ Δ` (Simpson `chunk_0103.md`): the canonical valuation. -/
def canonVal (w : CanonWorld 𝒯 Atom) (p : Atom) : Prop :=
  (w.lbl ∶ Proposition.atom p) ∈ w.ctx.Γ

/-- The trivial (always-false) `botForces`: `TPrime`'s Consistency clause bans exploding worlds,
so no world of this model is fallible. This is what collapses `CKForces` to ordinary bivalent
forcing on this model (see the module docstring). -/
@[nolint unusedArguments]
def canonBotForces (_ : CanonWorld 𝒯 Atom) : Prop := False

theorem canonVal_mono {w w' : CanonWorld 𝒯 Atom} (p : Atom) (h : w ≤ w') (hv : canonVal w p) :
    canonVal w' p := by
  have := h.1.2 hv
  rwa [h.2] at this

theorem canonBotForces_mono {w w' : CanonWorld 𝒯 Atom} (_ : w ≤ w') (hb : canonBotForces w) :
    canonBotForces w' :=
  hb.elim

theorem canonBotForces_val (p : Atom) {w : CanonWorld 𝒯 Atom} (hb : canonBotForces w) :
    canonVal w p :=
  hb.elim

theorem canonBotForces_r {w u : CanonWorld 𝒯 Atom} (hb : canonBotForces w) (_ : CanonWorld.r w u) :
    canonBotForces u :=
  hb.elim

theorem canonBotForces_r_wit {w : CanonWorld 𝒯 Atom} (hb : canonBotForces w) :
    ∃ u, CanonWorld.r w u ∧ canonBotForces u :=
  hb.elim

/-! ## The canonical model lemma (Simpson 5.3.2) -/

/-- **Simpson's Canonical Model Lemma 5.3.2** (`chunk_0103.md`-`chunk_0105.md`, pp. 94-95): for
every `𝒯`-prime context `(H,Δ)` and every label `y` in `H`, `(H,Δ),y ⊩ B` iff `y:B ∈ Δ`. Proved by
induction on `B`, transcribing `chunk_0104.md`/`chunk_0105.md`'s case-by-case argument:

- `atom`/`⊥`: immediate from `canonVal`'s definition / `TPrime.consistency`.
- `∧`/`∨`: immediate from the introduction/elimination `NIK` rules plus `TPrime.disjunction`
  (`∨`) or direct construction (`∧`), no context-growing needed.
- `B ⊃ C` (`chunk_0104.md`): forward is direct (`⊃E` + monotonicity + deductive closure);
  backward is Simpson's reductio -- assume `Δ,y:B ⊬ y:C`, apply `primeLemma` to
  `(H.addFormula (y:B), y, C)` to get a witnessing extension contradicting the semantic
  hypothesis, so `Δ,y:B ⊢ y:C`, hence by `(⊃I)` and deductive closure `y:B⊃C ∈ Δ`.
- `□B` (`chunk_0104.md`): forward is `(□E)` + monotonicity + deductive closure; backward is
  Simpson's reductio -- pick a fresh raw variable `z` outside `H`'s witnessing reserve
  (`Context.addFreshVar`), assume `Δ ⊬_{H∪{yRz}} z:B`, apply `primeLemma` to get a witnessing
  extension contradicting the semantic hypothesis at the fresh edge `yRz`, so
  `Δ ⊢_{H∪{yRz}} z:B`; since `z ∉ H`, `NIK.oldLabelTransport` upgrades the single witness to the
  cofinite family `(□I)` needs, giving `Δ ⊢_H y:□B`, hence by deductive closure `y:□B ∈ Δ`.
- `◇B` (`chunk_0105.md`): forward is immediate from `TPrime.diamond`; backward specializes the
  `∀∃`-clause at the reflexive instance `w' := w` to recover Simpson's plain `∃`-witness, then
  `(◇I)` + deductive closure. -/
theorem canon_truth_lemma {w : CanonWorld 𝒯 Atom} (φ : Proposition Atom) :
    CKForces CanonWorld.r canonVal canonBotForces w φ ↔ (w.lbl ∶ φ) ∈ w.ctx.Γ := by
  induction φ generalizing w with
  | atom p => exact Iff.rfl
  | bot =>
      rw [CKForces_bot]
      constructor
      · intro h; exact h.elim
      · intro hmem
        exact (w.ctx.consistency w.lbl w.mem (Deriv.of_mem hmem)).elim
  | and φ ψ ihφ ihψ =>
      rw [CKForces_and]
      constructor
      · rintro ⟨h1, h2⟩
        have hm1 := (ihφ (w := w)).mp h1
        have hm2 := (ihψ (w := w)).mp h2
        have hNIK1 : NIK 𝒯 w.ctx.G [w.lbl ∶ φ] (w.lbl ∶ φ) :=
          NIK.assumption _ _ _ (List.mem_singleton_self _)
        have hderiv : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ Proposition.and φ ψ) := by
          refine ⟨[w.lbl ∶ φ, w.lbl ∶ ψ], ?_, ?_⟩
          · intro ψ' hψ'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ'
            rcases hψ' with hψ' | hψ'
            · rw [hψ']; exact hm1
            · rw [hψ']; exact hm2
          · exact NIK.andI w.ctx.G [w.lbl ∶ φ, w.lbl ∶ ψ] w.lbl φ ψ
              (NIK.assumption _ _ _ (by simp)) (NIK.assumption _ _ _ (by simp))
        exact w.ctx.deductiveClosure w.lbl w.mem _ hderiv
      · intro hmem
        have hderiv : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ Proposition.and φ ψ) := Deriv.of_mem hmem
        obtain ⟨Γ₀, hΓ₀, hNIK⟩ := hderiv
        have h1 : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ φ) :=
          ⟨Γ₀, hΓ₀, NIK.andE1 w.ctx.G Γ₀ w.lbl φ ψ hNIK⟩
        have h2 : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ ψ) :=
          ⟨Γ₀, hΓ₀, NIK.andE2 w.ctx.G Γ₀ w.lbl φ ψ hNIK⟩
        exact ⟨(ihφ (w := w)).mpr (w.ctx.deductiveClosure w.lbl w.mem _ h1),
          (ihψ (w := w)).mpr (w.ctx.deductiveClosure w.lbl w.mem _ h2)⟩
  | or φ ψ ihφ ihψ =>
      rw [CKForces_or]
      constructor
      · rintro (h | h)
        · have hmem := (ihφ (w := w)).mp h
          have hderiv : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ Proposition.or φ ψ) :=
            ⟨[w.lbl ∶ φ], fun ψ' hψ' => (List.mem_singleton.mp hψ') ▸ hmem,
              NIK.orI1 w.ctx.G [w.lbl ∶ φ] w.lbl φ ψ
                (NIK.assumption _ _ _ (List.mem_singleton_self _))⟩
          exact w.ctx.deductiveClosure w.lbl w.mem _ hderiv
        · have hmem := (ihψ (w := w)).mp h
          have hderiv : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ Proposition.or φ ψ) :=
            ⟨[w.lbl ∶ ψ], fun ψ' hψ' => (List.mem_singleton.mp hψ') ▸ hmem,
              NIK.orI2 w.ctx.G [w.lbl ∶ ψ] w.lbl φ ψ
                (NIK.assumption _ _ _ (List.mem_singleton_self _))⟩
          exact w.ctx.deductiveClosure w.lbl w.mem _ hderiv
      · intro hmem
        rcases w.ctx.disjunction w.lbl φ ψ hmem with h | h
        · exact Or.inl ((ihφ (w := w)).mpr h)
        · exact Or.inr ((ihψ (w := w)).mpr h)
  | imp φ ψ ihφ ihψ =>
      rw [CKForces_imp]
      constructor
      · intro hyp
        have hD : Deriv 𝒯 w.ctx.G (insert (w.lbl ∶ φ) w.ctx.Γ) (w.lbl ∶ ψ) := by
          by_contra hcon
          obtain ⟨H', hle, hnd'⟩ :=
            primeLemma (w.ctx.toContext.addFormula (w.lbl ∶ φ) w.mem) w.lbl ψ w.mem hcon
          have hyX' : w.lbl ∈ H'.G.X := hle.1.1 w.mem
          have hw' : w ≤ (⟨H', w.lbl, hyX'⟩ : CanonWorld 𝒯 Atom) :=
            ⟨Context.le_trans (Context.addFormula_le w.ctx.toContext (w.lbl ∶ φ) w.mem) hle, rfl⟩
          have hmemφ : (w.lbl ∶ φ) ∈ H'.Γ := hle.2 (Set.mem_insert _ _)
          have hφ' : CKForces CanonWorld.r canonVal canonBotForces
              (⟨H', w.lbl, hyX'⟩ : CanonWorld 𝒯 Atom) φ :=
            (ihφ (w := ⟨H', w.lbl, hyX'⟩)).mpr hmemφ
          have hψ' := hyp _ hw' hφ'
          have hmemψ : (w.lbl ∶ ψ) ∈ H'.Γ := (ihψ (w := ⟨H', w.lbl, hyX'⟩)).mp hψ'
          exact hnd' (Deriv.of_mem hmemψ)
        exact w.ctx.deductiveClosure w.lbl w.mem _ (Deriv.impI hD)
      · intro hmem w' hw' hφ'
        have hmem' : (w'.lbl ∶ Proposition.imp φ ψ) ∈ w'.ctx.Γ := by
          rw [← hw'.2]; exact hw'.1.2 hmem
        have hφmem : (w'.lbl ∶ φ) ∈ w'.ctx.Γ := (ihφ (w := w')).mp hφ'
        have hderiv : Deriv 𝒯 w'.ctx.G w'.ctx.Γ (w'.lbl ∶ ψ) := by
          refine ⟨[w'.lbl ∶ Proposition.imp φ ψ, w'.lbl ∶ φ], ?_, ?_⟩
          · intro χ hχ
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
            rcases hχ with hχ | hχ
            · rw [hχ]; exact hmem'
            · rw [hχ]; exact hφmem
          · exact NIK.impE w'.ctx.G _ w'.lbl φ ψ
              (NIK.assumption _ _ _ (by simp)) (NIK.assumption _ _ _ (by simp))
        exact (ihψ (w := w')).mpr (w'.ctx.deductiveClosure w'.lbl w'.mem _ hderiv)
  | box φ ihφ =>
      rw [CKForces_box]
      constructor
      · intro hyp
        obtain ⟨V', hV', hHV'⟩ := w.ctx.coinfinite
        obtain ⟨z, hz⟩ := hV'.nonempty
        have hzX : Label.var z ∉ w.ctx.G.X := fun hmem => hz (hHV' _ hmem)
        set H₀ := w.ctx.toContext.addFreshVar w.lbl w.mem V' hV' hHV' z hz with hH₀def
        have hzX0 : Label.var z ∈ H₀.G.X :=
          Context.mem_addFreshVar w.ctx.toContext w.lbl w.mem V' hV' hHV' z hz
        have hxy₀ : w.lbl ≠ Label.var z := fun heq => hzX (heq ▸ w.mem)
        have hyH₀ : w.lbl ∈ H₀.G.X := (Context.addFreshVar_le w.ctx.toContext w.lbl w.mem
          V' hV' hHV' z hz).1.1 w.mem
        have hD : Deriv 𝒯 H₀.G H₀.Γ (Label.var z ∶ φ) := by
          by_contra hcon
          obtain ⟨H', hle, hnd'⟩ := primeLemma H₀ (Label.var z) φ hzX0 hcon
          have hyX' : w.lbl ∈ H'.G.X := hle.1.1 hyH₀
          have hzX' : Label.var z ∈ H'.G.X := hle.1.1 hzX0
          have hRaw : H'.G.R w.lbl (Label.var z) :=
            hle.1.2 w.lbl (Label.var z) (Or.inr ⟨rfl, rfl⟩)
          have hw' : w ≤ (⟨H', w.lbl, hyX'⟩ : CanonWorld 𝒯 Atom) :=
            ⟨Context.le_trans
              (Context.addFreshVar_le w.ctx.toContext w.lbl w.mem V' hV' hHV' z hz) hle, rfl⟩
          have hru : CanonWorld.r (⟨H', w.lbl, hyX'⟩ : CanonWorld 𝒯 Atom)
              (⟨H', Label.var z, hzX'⟩ : CanonWorld 𝒯 Atom) := ⟨rfl, hRaw⟩
          have := hyp _ hw' _ hru
          have hmem : (Label.var z ∶ φ) ∈ H'.Γ := (ihφ (w := ⟨H', Label.var z, hzX'⟩)).mp this
          exact hnd' (Deriv.of_mem hmem)
        obtain ⟨Γ₀, hΓ₀, hNIK⟩ := hD
        have hΓ₀lbl : ∀ ψ ∈ Γ₀, ψ.lbl ≠ Label.var z := fun ψ hψ heq =>
          hzX (heq ▸ w.ctx.ctxSubset ψ (hΓ₀ ψ hψ))
        have hall : ∀ y' : Label Atom, NIK 𝒯 (w.ctx.G.addEdge w.lbl y') Γ₀ (y' ∶ φ) :=
          fun y' => NIK.oldLabelTransport hNIK hzX hxy₀ hΓ₀lbl y'
        have hbox : NIK 𝒯 w.ctx.G Γ₀ (w.lbl ∶ Proposition.box φ) :=
          NIK.boxI ∅ Set.finite_empty w.ctx.G Γ₀ w.lbl φ (fun y' _ => hall y')
        have hderiv : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ Proposition.box φ) := ⟨Γ₀, hΓ₀, hbox⟩
        exact w.ctx.deductiveClosure w.lbl w.mem _ hderiv
      · intro hmem w' hw' u hru
        have hmem' : (w'.lbl ∶ Proposition.box φ) ∈ w'.ctx.Γ := by
          rw [← hw'.2]; exact hw'.1.2 hmem
        have hedge : TClosure 𝒯 u.ctx.G.R w'.lbl u.lbl := by
          rw [← hru.1]; exact .base hru.2
        have hderiv : Deriv 𝒯 u.ctx.G u.ctx.Γ (u.lbl ∶ φ) := by
          refine ⟨[w'.lbl ∶ Proposition.box φ], ?_, ?_⟩
          · intro χ hχ; rw [List.mem_singleton.mp hχ, ← hru.1]; exact hmem'
          · exact NIK.boxE u.ctx.G _ w'.lbl u.lbl φ hedge
              (NIK.assumption _ _ _ (List.mem_singleton_self _))
        exact (ihφ (w := u)).mpr (u.ctx.deductiveClosure u.lbl u.mem _ hderiv)
  | diamond φ ihφ =>
      rw [CKForces_diamond]
      constructor
      · intro hyp
        obtain ⟨u, hru, hu⟩ := hyp w (CanonWorld.le_refl w)
        have humem : (u.lbl ∶ φ) ∈ u.ctx.Γ := (ihφ (w := u)).mp hu
        have humem' : (u.lbl ∶ φ) ∈ w.ctx.Γ := by rw [hru.1]; exact humem
        have hdia : NIK 𝒯 w.ctx.G [u.lbl ∶ φ] (w.lbl ∶ Proposition.diamond φ) :=
          NIK.diaI w.ctx.G [u.lbl ∶ φ] w.lbl u.lbl φ (.base hru.2)
            (NIK.assumption _ _ _ (List.mem_singleton_self _))
        have hderiv : Deriv 𝒯 w.ctx.G w.ctx.Γ (w.lbl ∶ Proposition.diamond φ) :=
          ⟨[u.lbl ∶ φ], fun ψ hψ => (List.mem_singleton.mp hψ) ▸ humem', hdia⟩
        exact w.ctx.deductiveClosure w.lbl w.mem _ hderiv
      · intro hmem w' hw'
        have hmem' : (w'.lbl ∶ Proposition.diamond φ) ∈ w'.ctx.Γ := by
          rw [← hw'.2]; exact hw'.1.2 hmem
        obtain ⟨v, hRv, hvmem⟩ := w'.ctx.diamond w'.lbl φ hmem'
        have hvX : v ∈ w'.ctx.G.X := w'.ctx.ctxSubset _ hvmem
        exact ⟨⟨w'.ctx, v, hvX⟩, ⟨rfl, hRv⟩, (ihφ (w := ⟨w'.ctx, v, hvX⟩)).mpr hvmem⟩

end Cslib.Logic.Modal.Labelled
