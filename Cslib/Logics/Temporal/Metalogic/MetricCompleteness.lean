/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.MetricSoundness
public import Cslib.Logics.Temporal.Metalogic.DenseCompleteness
public import Mathlib.Order.CountableDenseLinearOrder

/-! # BX⁺ Completeness over the Uniform Class + Dense→ℚ Bridge

This module proves completeness of the metric (BX⁺) temporal proof system over the uniform
serial-linear class `U` (frames validating the four metric-uniformity axioms), and delivers a
general order-isomorphism transport lemma together with a dense→ℚ refutation corollary.

## Strategy

Mirrors `DenseCompleteness.lean`: build the chronicle countermodel from a Metric-MCS. Since the
four uniformity axioms (`discrete_symm_fwd/bwd`, `discrete_propagate_fwd/bwd`) are *theorems* of
the Metric derivation system (not merely consequences of a further hypothesis), they are members
of every limit-MCS's seed `A`, and `G`/`H`-necessitation propagates them to every chronicle point
directly via the truth lemma — no C4 trichotomy is needed (contrast the dense case, which
propagates a *negative* fact `¬U(⊥,⊤)` and needs C4 for the `x > 0` case).

## Main Results

- `Satisfies_orderIso`: satisfaction transports along an order isomorphism `e : D ≃o E`.
- `validMetricUniform`: validity over the uniform class `U` (`Semantics/Validity.lean`).
- `axiom_sound_uniform`, `soundness_uniform`, `soundness_thderivable_uniform`: soundness over `U`.
- `metric_theorem_in_all_limit_points`: every Metric theorem holds at every chronicle point.
- `chronicleUniformMetric`: the chronicle built from a Metric-MCS satisfies the `U`-membership
  hypotheses at every point.
- `completeness_metric`: `validMetricUniform φ → BXPlusDerivable φ`.
- `denseCountermodel_transport_rat`: a dense serial countermodel transports to the oag ℚ.

## Escalation (open, not attempted here)

Literal BX⁺-completeness over the full ordered-abelian-group class (the discrete sub-case) is
**not** proved. It reduces to the open, expected-**false** lemma: every discrete BX⁺-consistent
formula has a homogeneous (`ℤ` / `ℤ ×ₗ ℚ`) oag countermodel. BX⁺ lacks a discreteness/archimedean
axiom, so a non-homogeneous `ℤ ×ₗ A` block-index frame validates BX⁺ but is not an ordered
abelian group; no Mathlib order-embedding bridges this gap (order-embeddings destroy
`U(⊥,⊤)`-truth). Resolution, if wanted, requires a NEW frame class strictly between `Metric` and
the discrete class, strengthened with a discreteness/archimedean axiom — a separate development,
not attempted here.

## References

* Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean — structural template (chronicle
  completeness skeleton)
* Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean — the four metric-uniformity axioms
* [J. Burgess, *Basic Tense Logic*][Burgess1984] §6.1 — metric tense = ordered abelian group time
* [Xu Ming, *Fragments of Temporal Logics*][Xu1988] Thm 2.9 — successor not `U`,`S`-definable
  (evidence for the discrete-completeness gap: `U(⊥,⊤)` cannot force a homogeneous block
  structure without an extra discreteness axiom)
-/

set_option linter.style.setOption false

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic
open Cslib.Logic.Temporal.Metalogic
open Cslib.Logic.Temporal.Metalogic.Chronicle

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Order-Isomorphism Transport -/

/-- **Satisfaction transports along an order isomorphism.** If `e : D ≃o E` is an order
isomorphism, then `φ` is satisfied at `t` in `M` iff `φ` is satisfied at `e t` in the model
pulled forward along `e` (valuation `q ↦ M.valuation (e.symm q) p`).

This is the general reusable transport lemma: it does not depend on any frame-class hypothesis,
only on `e` being an order isomorphism. -/
theorem Satisfies_orderIso {D E : Type*} [LinearOrder D] [LinearOrder E] (e : D ≃o E)
    (M : TemporalModel D Atom) (t : D) (φ : Formula Atom) :
    Satisfies M t φ ↔
      Satisfies (D := E) { valuation := fun q p => M.valuation (e.symm q) p } (e t) φ := by
  induction φ generalizing t with
  | atom p => simp [Satisfies]
  | bot => simp [Satisfies]
  | imp φ ψ ihφ ihψ => simp only [Satisfies]; rw [ihφ, ihψ]
  | untl ψ φ ihψ ihφ =>
    simp only [Satisfies]
    constructor
    · rintro ⟨s, hts, hφs, hguard⟩
      refine ⟨e s, e.lt_iff_lt.mpr hts, (ihφ s).mp hφs, fun r hr1 hr2 => ?_⟩
      have hr1' : t < e.symm r := e.lt_iff_lt.mp (by rwa [e.apply_symm_apply])
      have hr2' : e.symm r < s := e.lt_iff_lt.mp (by rwa [e.apply_symm_apply])
      have h := (ihψ (e.symm r)).mp (hguard (e.symm r) hr1' hr2')
      rwa [e.apply_symm_apply] at h
    · rintro ⟨s, hts, hφs, hguard⟩
      refine ⟨e.symm s, e.lt_iff_lt.mp (by rwa [e.apply_symm_apply]),
        (ihφ (e.symm s)).mpr (by rwa [e.apply_symm_apply]), fun r hr1 hr2 => ?_⟩
      have h1 : e t < e r := e.lt_iff_lt.mpr hr1
      have h2 : e r < s := by rw [show s = e (e.symm s) from (e.apply_symm_apply s).symm]
                              exact e.lt_iff_lt.mpr hr2
      exact (ihψ r).mpr (hguard (e r) h1 h2)
  | snce ψ φ ihψ ihφ =>
    simp only [Satisfies]
    constructor
    · rintro ⟨s, hst, hφs, hguard⟩
      refine ⟨e s, e.lt_iff_lt.mpr hst, (ihφ s).mp hφs, fun r hr1 hr2 => ?_⟩
      have hr1' : s < e.symm r := e.lt_iff_lt.mp (by rwa [e.apply_symm_apply])
      have hr2' : e.symm r < t := e.lt_iff_lt.mp (by rwa [e.apply_symm_apply])
      have h := (ihψ (e.symm r)).mp (hguard (e.symm r) hr1' hr2')
      rwa [e.apply_symm_apply] at h
    · rintro ⟨s, hst, hφs, hguard⟩
      refine ⟨e.symm s, e.lt_iff_lt.mp (by rwa [e.apply_symm_apply]),
        (ihφ (e.symm s)).mpr (by rwa [e.apply_symm_apply]), fun r hr1 hr2 => ?_⟩
      have h1 : e r < e t := e.lt_iff_lt.mpr hr2
      have h2 : s < e r := by rw [show s = e (e.symm s) from (e.apply_symm_apply s).symm]
                              exact e.lt_iff_lt.mpr hr1
      exact (ihψ r).mpr (hguard (e r) h2 h1)
  | allFuture φ ihφ =>
    simp only [Satisfies]
    constructor
    · intro h s hs
      have hs' : t < e.symm s := e.lt_iff_lt.mp (by rwa [e.apply_symm_apply])
      have := (ihφ (e.symm s)).mp (h (e.symm s) hs')
      rwa [e.apply_symm_apply] at this
    · intro h s hs
      exact (ihφ s).mpr (h (e s) (e.lt_iff_lt.mpr hs))
  | allPast φ ihφ =>
    simp only [Satisfies]
    constructor
    · intro h s hs
      have hs' : e.symm s < t := e.lt_iff_lt.mp (by rwa [e.apply_symm_apply])
      have := (ihφ (e.symm s)).mp (h (e.symm s) hs')
      rwa [e.apply_symm_apply] at this
    · intro h s hs
      exact (ihφ s).mpr (h (e s) (e.lt_iff_lt.mpr hs))

/-! ## Soundness over the Uniform Class `U` -/

/-- Every axiom in the BX+Metric system is valid over serial linear orders satisfying
`uniformFrameCondition`. The 4 metric axioms are read directly off the hypothesis; the 26 Base
axioms delegate to `axiom_sound` (`Base ≤ Metric`); the 2 Dense axioms are discharged by
`absurd` (`.Dense ≰ .Metric`). -/
theorem axiom_sound_uniform {D : Type*} [LinearOrder D] [NoMaxOrder D] [NoMinOrder D]
    {φ : Formula Atom} (h_ax : Axiom φ)
    (_h_fc : h_ax.minFrameClass ≤ FrameClass.Metric)
    (h_uniform : uniformFrameCondition (Atom := Atom) D)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  cases h_ax with
  | discrete_symm_fwd => exact (h_uniform M t).1
  | discrete_symm_bwd => exact (h_uniform M t).2.1
  | discrete_propagate_fwd => exact (h_uniform M t).2.2.1
  | discrete_propagate_bwd => exact (h_uniform M t).2.2.2
  | density _ => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | imp_k => exact axiom_sound (.imp_k _ _ _) (FrameClass.base_le _) M t
  | imp_s => exact axiom_sound (.imp_s _ _) (FrameClass.base_le _) M t
  | efq => exact axiom_sound (.efq _) (FrameClass.base_le _) M t
  | peirce => exact axiom_sound (.peirce _ _) (FrameClass.base_le _) M t
  | serial_future => exact axiom_sound .serial_future (FrameClass.base_le _) M t
  | serial_past => exact axiom_sound .serial_past (FrameClass.base_le _) M t
  | left_mono_until_G => exact axiom_sound (.left_mono_until_G _ _ _) (FrameClass.base_le _) M t
  | left_mono_since_H => exact axiom_sound (.left_mono_since_H _ _ _) (FrameClass.base_le _) M t
  | right_mono_until => exact axiom_sound (.right_mono_until _ _ _) (FrameClass.base_le _) M t
  | right_mono_since => exact axiom_sound (.right_mono_since _ _ _) (FrameClass.base_le _) M t
  | connect_future => exact axiom_sound (.connect_future _) (FrameClass.base_le _) M t
  | connect_past => exact axiom_sound (.connect_past _) (FrameClass.base_le _) M t
  | enrichment_until => exact axiom_sound (.enrichment_until _ _ _) (FrameClass.base_le _) M t
  | enrichment_since => exact axiom_sound (.enrichment_since _ _ _) (FrameClass.base_le _) M t
  | self_accum_until => exact axiom_sound (.self_accum_until _ _) (FrameClass.base_le _) M t
  | self_accum_since => exact axiom_sound (.self_accum_since _ _) (FrameClass.base_le _) M t
  | absorb_until => exact axiom_sound (.absorb_until _ _) (FrameClass.base_le _) M t
  | absorb_since => exact axiom_sound (.absorb_since _ _) (FrameClass.base_le _) M t
  | linear_until => exact axiom_sound (.linear_until _ _ _ _) (FrameClass.base_le _) M t
  | linear_since => exact axiom_sound (.linear_since _ _ _ _) (FrameClass.base_le _) M t
  | until_F => exact axiom_sound (.until_F _ _) (FrameClass.base_le _) M t
  | since_P => exact axiom_sound (.since_P _ _) (FrameClass.base_le _) M t
  | temp_linearity => exact axiom_sound (.temp_linearity _ _) (FrameClass.base_le _) M t
  | temp_linearity_past => exact axiom_sound (.temp_linearity_past _ _) (FrameClass.base_le _) M t
  | F_until_equiv => exact axiom_sound (.F_until_equiv _) (FrameClass.base_le _) M t
  | P_since_equiv => exact axiom_sound (.P_since_equiv _) (FrameClass.base_le _) M t
  | allFuture_to_classic =>
      exact axiom_sound (.allFuture_to_classic _) (FrameClass.base_le _) M t
  | classic_to_allFuture =>
      exact axiom_sound (.classic_to_allFuture _) (FrameClass.base_le _) M t
  | allPast_to_classic =>
      exact axiom_sound (.allPast_to_classic _) (FrameClass.base_le _) M t
  | classic_to_allPast =>
      exact axiom_sound (.classic_to_allPast _) (FrameClass.base_le _) M t

/-- The uniform-frame condition transfers to `OrderDual D`: needed for the `temporal_duality`
derivation case of `soundness_uniform`. The symmetry facts (`.1`/`.2.1`) dualize to each other
directly via `swapTemporal_dual` (since `swapTemporal` exchanges `discrete_symm_fwd`/`bwd`'s
underlying formula `U(⊥,⊤) ↔ S(⊥,⊤)`); the propagation facts (`.2.2.1`/`.2.2.2`) dualize to a
`S(⊥,⊤)`-headed statement that is derived directly from the D-side hypothesis (symmetry then
propagation then symmetry again), since `swapTemporal` of a propagation axiom is not literally
one of the four schemata. -/
theorem uniformFrameCondition_dual {D : Type*} [LinearOrder D]
    (h_uniform : uniformFrameCondition (Atom := Atom) D) :
    uniformFrameCondition (Atom := Atom) (OrderDual D) := by
  intro M' t'
  set M : TemporalModel D Atom := ⟨M'.valuation⟩ with hM
  have hMM' : dualModel M = M' := rfl
  have hdual : ∀ (ψ : Formula Atom), Satisfies M' t' ψ ↔
      Satisfies M (OrderDual.ofDual t') (Formula.swapTemporal ψ) := by
    intro ψ
    have h := swapTemporal_dual (D := D) M (OrderDual.ofDual t') ψ
    rw [OrderDual.toDual_ofDual, hMM'] at h
    exact h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- discrete_symm_fwd at t' in M': swap of discrete_symm_bwd's formula
    rw [hdual]
    simp only [Formula.swapTemporal, Formula.top, PropositionalConnectives.top]
    exact (h_uniform M (OrderDual.ofDual t')).2.1
  · rw [hdual]
    simp only [Formula.swapTemporal, Formula.top, PropositionalConnectives.top]
    exact (h_uniform M (OrderDual.ofDual t')).1
  · -- discrete_propagate_fwd at t': swap = S(⊥,⊤) → H(S(⊥,⊤)); derive via symm + propagate_bwd
    rw [hdual]
    simp only [Formula.swapTemporal, Formula.top, PropositionalConnectives.top]
    intro hS
    have hU : Satisfies M (OrderDual.ofDual t') (Formula.untl Formula.bot Formula.top) :=
      (h_uniform M (OrderDual.ofDual t')).2.1 hS
    have hHU := (h_uniform M (OrderDual.ofDual t')).2.2.2 hU
    intro s hs
    exact (h_uniform M s).1 (hHU s hs)
  · -- discrete_propagate_bwd at t': swap = S(⊥,⊤) → G(S(⊥,⊤)); derive via symm + propagate_fwd
    rw [hdual]
    simp only [Formula.swapTemporal, Formula.top, PropositionalConnectives.top]
    intro hS
    have hU : Satisfies M (OrderDual.ofDual t') (Formula.untl Formula.bot Formula.top) :=
      (h_uniform M (OrderDual.ofDual t')).2.1 hS
    have hGU := (h_uniform M (OrderDual.ofDual t')).2.2.1 hU
    intro s hs
    exact (h_uniform M s).1 (hGU s hs)

universe u_dom_uniform

/-- Uniform-class version of `swap_valid_of_valid_metric`: if `φ` is satisfied everywhere in all
`uniformFrameCondition` models, then `swapTemporal φ` is also satisfied. -/
theorem swap_valid_of_valid_uniform
    {φ : Formula Atom}
    (h_valid : ∀ (D : Type u_dom_uniform) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D] (_h_uniform : uniformFrameCondition (Atom := Atom) D)
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ)
    (D : Type u_dom_uniform) [LinearOrder D] [Nontrivial D]
    [NoMaxOrder D] [NoMinOrder D] (h_uniform : uniformFrameCondition (Atom := Atom) D)
    (M : TemporalModel D Atom) (t : D) :
    Satisfies M t (Formula.swapTemporal φ) := by
  rw [swapTemporal_dual]
  exact h_valid (OrderDual D) (uniformFrameCondition_dual h_uniform) (dualModel M)
    (OrderDual.toDual t)

/-- **Soundness at the uniform class `U`**: If `Γ ⊢[Metric] φ`, then for any `D` satisfying
`uniformFrameCondition` and any time where all of `Γ` is satisfied, `φ` is also satisfied. -/
theorem soundness_uniform {D : Type*} [LinearOrder D] [Nontrivial D]
    [NoMaxOrder D] [NoMinOrder D]
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Metric Γ φ)
    (h_uniform : uniformFrameCondition (Atom := Atom) D)
    (M : TemporalModel D Atom) (t : D)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies M t ψ) : Satisfies M t φ := by
  match d with
  | .axiom _ ψ h_ax h_fc =>
    exact axiom_sound_uniform h_ax h_fc h_uniform M t
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact soundness_uniform d₁ h_uniform M t h_ctx (soundness_uniform d₂ h_uniform M t h_ctx)
  | .temporal_necessitation ψ d' =>
    simp only [Satisfies.allFuture_iff]
    intro s hlt
    exact soundness_uniform d' h_uniform M s (fun _ h => nomatch h)
  | .temporal_duality ψ d' =>
    exact swap_valid_of_valid_uniform
      (fun D' _ _ _ _ h_uniform' M' t' =>
        soundness_uniform d' h_uniform' M' t' (fun _ h => nomatch h))
      D h_uniform M t
  | .weakening Γ' Δ ψ d' h_sub =>
    exact soundness_uniform d' h_uniform M t (fun x hx => h_ctx x (h_sub hx))

/-- **Soundness for Metric-derivable formulas over `U`**: If `BXPlusDerivable φ`, then `φ` is
valid over the uniform class `U`. -/
theorem soundness_thderivable_uniform {φ : Formula Atom} (h : Temporal.BXPlusDerivable φ) :
    validMetricUniform φ := by
  intro D _ _ _ _ h_uniform M t
  obtain ⟨d⟩ := h
  exact soundness_uniform d h_uniform M t (fun _ h => nomatch h)

/-- **oag ⊆ U corollary**: every ordered-abelian-group frame validates the four
metric-uniformity axioms (via the `*_sound` theorems of `MetricSoundness.lean`), so `U`-validity
implies oag-validity — recovering the semantic content of `soundness_thderivable_metric`. -/
theorem validMetricUniform_imp_oag {φ : Formula Atom} (h : validMetricUniform φ)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ :=
  h D (fun M t => ⟨discrete_symm_fwd_sound M t, discrete_symm_bwd_sound M t,
    discrete_propagate_fwd_sound M t, discrete_propagate_bwd_sound M t⟩) M t

end Cslib.Logic.Temporal
