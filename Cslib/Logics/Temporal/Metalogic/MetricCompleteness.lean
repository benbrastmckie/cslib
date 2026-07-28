/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.MetricSoundness
public import Cslib.Logics.Temporal.Metalogic.DenseCompleteness
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Algebra.Order.Field.Basic

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

/-! ## Uniformity Axioms Satisfied at Every Chronicle Point -/

/-- A Metric-MCS is also a Base-MCS. Mirrors `dense_mcs_implies_base_mcs`. -/
theorem metric_mcs_implies_base_mcs
    {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Metric M) :
    Temporal.SetMaximalConsistent M := by
  constructor
  · intro L hL hd
    apply h_mcs.1 L hL
    unfold temporalDerivationSystemFc Temporal.DerivFc
    unfold temporalDerivationSystem Temporal.Deriv at hd
    obtain ⟨d⟩ := hd
    exact ⟨d.lift (FrameClass.base_le .Metric)⟩
  · intro φ h_not_mem
    have h_neg := mcs_neg_of_not_mem_fc h_mcs h_not_mem
    intro h_cons
    apply h_cons [φ, Formula.neg φ]
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact Set.mem_insert _ M
      · exact Set.mem_insert_of_mem _ h_neg
    · unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.modus_ponens _ φ Formula.bot
        (.assumption _ (Formula.neg φ) (by simp))
        (.assumption _ φ (by simp))⟩

variable [Denumerable (Formula Atom)]

/-- **Every Metric theorem holds at every chronicle point.** Since `φ` is derivable at the
empty context (`⊢[Metric] φ`), both `G(φ)` and `H(φ)` are also derivable, hence members of the
Metric-MCS seed `A = limitF(0)`; propagate forward/backward to every limit point via the
chronicle truth lemma. Much more direct than the dense case's `dense_indicator_in_all_limit_points`
(no C4 trichotomy needed): the four uniformity axioms are theorems, not merely negative facts to
be defended by contradiction. -/
theorem metric_theorem_in_all_limit_points
    {A : Set (Formula Atom)}
    (h_metric_mcs : Temporal.SetMaximalConsistentFc FrameClass.Metric A)
    (h_base_mcs : Temporal.SetMaximalConsistent A)
    {φ : Formula Atom} (h_thm : DerivationTree FrameClass.Metric ([] : Context Atom) φ)
    (x : Rat) (hx : x ∈ limitDom A h_base_mcs) :
    φ ∈ limitF A h_base_mcs x := by
  have h_phi_in_A : φ ∈ A := theoremInMcsFc h_metric_mcs h_thm
  have h_g_thm : DerivationTree FrameClass.Metric [] φ.allFuture :=
    DerivationTree.temporal_necessitation _ h_thm
  have h_g_in_A : φ.allFuture ∈ A := theoremInMcsFc h_metric_mcs h_g_thm
  have h_h_thm : DerivationTree FrameClass.Metric [] φ.allPast := by
    have d_swap := DerivationTree.temporal_duality _ h_thm
    have d_g := DerivationTree.temporal_necessitation _ d_swap
    have d_h := DerivationTree.temporal_duality _ d_g
    have h_eq_form : φ.swapTemporal.allFuture.swapTemporal = φ.allPast := by
      rw [Formula.swapTemporal_allFuture, Formula.swapTemporal_involution]
    exact h_eq_form ▸ d_h
  have h_h_in_A : φ.allPast ∈ A := theoremInMcsFc h_metric_mcs h_h_thm
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: H(φ) ∈ A = limitF(0); truth lemma gives Sat at all past points.
    let t₀ : ChronicleSubtype A h_base_mcs := chronicleZero A h_base_mcs
    have h_zero_mem : φ.allPast ∈ limitF A h_base_mcs 0 := by rw [limit_f_zero]; exact h_h_in_A
    have h_sat := (chronicle_truth_lemma A h_base_mcs t₀ φ.allPast).mpr h_zero_mem
    rw [Satisfies.allPast_iff] at h_sat
    have h_sat_x := h_sat ⟨x, hx⟩ hx_neg
    exact (chronicle_truth_lemma A h_base_mcs ⟨x, hx⟩ φ).mp h_sat_x
  · subst hx_zero
    rw [limit_f_zero]
    exact h_phi_in_A
  · -- x > 0: G(φ) ∈ A = limitF(0); truth lemma gives Sat at all future points.
    let t₀ : ChronicleSubtype A h_base_mcs := chronicleZero A h_base_mcs
    have h_zero_mem : φ.allFuture ∈ limitF A h_base_mcs 0 := by rw [limit_f_zero]; exact h_g_in_A
    have h_sat := (chronicle_truth_lemma A h_base_mcs t₀ φ.allFuture).mpr h_zero_mem
    rw [Satisfies.allFuture_iff] at h_sat
    have h_sat_x := h_sat ⟨x, hx⟩ hx_pos
    exact (chronicle_truth_lemma A h_base_mcs ⟨x, hx⟩ φ).mp h_sat_x

omit [Denumerable (Formula Atom)] in
/-- The four metric-uniformity axiom formulas, being built purely from `⊥`/`⊤`, are satisfied
(or not) independently of the model's valuation — only the order structure of the domain
matters. This lets `chronicleUniformMetric` transport membership facts (model-independent) to
satisfaction facts about an *arbitrary* model on the chronicle domain, not just
`chronicleModel A h_base_mcs`. -/
theorem satisfies_bot_top_indep {D : Type*} [LinearOrder D]
    (M M' : TemporalModel D Atom) (t : D) (ψ : Formula Atom)
    (h_indep : ψ = (Formula.untl Formula.bot Formula.top).imp
        (Formula.snce Formula.bot Formula.top) ∨
      ψ = (Formula.snce Formula.bot Formula.top).imp
        (Formula.untl Formula.bot Formula.top) ∨
      ψ = (Formula.untl Formula.bot Formula.top).imp
        (Formula.allFuture (Formula.untl Formula.bot Formula.top)) ∨
      ψ = (Formula.untl Formula.bot Formula.top).imp
        (Formula.allPast (Formula.untl Formula.bot Formula.top))) :
    Satisfies M t ψ ↔ Satisfies M' t ψ := by
  rcases h_indep with rfl | rfl | rfl | rfl <;>
    simp only [Satisfies, Formula.top, PropositionalConnectives.top]

/-- **The chronicle built from a Metric-MCS satisfies `uniformFrameCondition`** at every point:
the chronicle domain is in the uniform class `U`. This is the chronicle-membership-in-`U`
witness consumed by `completeness_metric`. -/
theorem chronicleUniformMetric
    {A : Set (Formula Atom)}
    (h_metric_mcs : Temporal.SetMaximalConsistentFc FrameClass.Metric A)
    (h_base_mcs : Temporal.SetMaximalConsistent A) :
    uniformFrameCondition (Atom := Atom) (ChronicleSubtype A h_base_mcs) := by
  intro M t
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_thm : DerivationTree FrameClass.Metric ([] : Context Atom)
        ((Formula.untl Formula.bot Formula.top).imp (Formula.snce Formula.bot Formula.top)) :=
      .axiom [] _ .discrete_symm_fwd (le_refl _)
    have h_mem := metric_theorem_in_all_limit_points h_metric_mcs h_base_mcs h_thm t.val t.property
    have h_chron := (chronicle_truth_lemma A h_base_mcs t _).mpr h_mem
    exact (satisfies_bot_top_indep (chronicleModel A h_base_mcs) M t _ (Or.inl rfl)).mp h_chron
  · have h_thm : DerivationTree FrameClass.Metric ([] : Context Atom)
        ((Formula.snce Formula.bot Formula.top).imp (Formula.untl Formula.bot Formula.top)) :=
      .axiom [] _ .discrete_symm_bwd (le_refl _)
    have h_mem := metric_theorem_in_all_limit_points h_metric_mcs h_base_mcs h_thm t.val t.property
    have h_chron := (chronicle_truth_lemma A h_base_mcs t _).mpr h_mem
    exact (satisfies_bot_top_indep (chronicleModel A h_base_mcs) M t _
      (Or.inr (Or.inl rfl))).mp h_chron
  · have h_thm : DerivationTree FrameClass.Metric ([] : Context Atom)
        ((Formula.untl Formula.bot Formula.top).imp
          (Formula.allFuture (Formula.untl Formula.bot Formula.top))) :=
      .axiom [] _ .discrete_propagate_fwd (le_refl _)
    have h_mem := metric_theorem_in_all_limit_points h_metric_mcs h_base_mcs h_thm t.val t.property
    have h_chron := (chronicle_truth_lemma A h_base_mcs t _).mpr h_mem
    exact (satisfies_bot_top_indep (chronicleModel A h_base_mcs) M t _
      (Or.inr (Or.inr (Or.inl rfl)))).mp h_chron
  · have h_thm : DerivationTree FrameClass.Metric ([] : Context Atom)
        ((Formula.untl Formula.bot Formula.top).imp
          (Formula.allPast (Formula.untl Formula.bot Formula.top))) :=
      .axiom [] _ .discrete_propagate_bwd (le_refl _)
    have h_mem := metric_theorem_in_all_limit_points h_metric_mcs h_base_mcs h_thm t.val t.property
    have h_chron := (chronicle_truth_lemma A h_base_mcs t _).mpr h_mem
    exact (satisfies_bot_top_indep (chronicleModel A h_base_mcs) M t _
      (Or.inr (Or.inr (Or.inr rfl)))).mp h_chron

/-! ## Metric Completeness over `U` -/

set_option linter.unusedSimpArgs false in
omit [Denumerable (Formula Atom)] in
/-- If `φ` is not `BX⁺`-derivable, then `{¬φ}` is Metric-consistent. Mirrors
`neg_consistent_of_not_derivable_dense` with `FrameClass.Dense` replaced by `FrameClass.Metric`. -/
theorem neg_consistent_of_not_derivable_metric
    {φ : Formula Atom} (h_not : ¬ Temporal.ThDerivableFc FrameClass.Metric φ) :
    Temporal.SetConsistentFc FrameClass.Metric ({Formula.neg φ} : Set (Formula Atom)) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d⟩
  have d_weak : DerivationTree FrameClass.Metric [Formula.neg φ] Formula.bot :=
    .weakening L [Formula.neg φ] .bot d (fun x hx => by
      have := hL x hx; simp only [Set.mem_singleton_iff] at this
      exact List.mem_cons.mpr (Or.inl this))
  have d_dne := deductionTheoremFc [] (Formula.neg φ) .bot d_weak
  let neg_phi := Formula.neg φ
  have efq : DerivationTree (Atom := Atom) FrameClass.Metric []
      (Formula.bot.imp φ) := .axiom [] _ (.efq φ) (FrameClass.base_le _)
  have ik : DerivationTree (Atom := Atom) FrameClass.Metric []
      ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
    .axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) (FrameClass.base_le _)
  have step_k := DerivationTree.modus_ponens [] _ _ ik efq
  have is_ax : DerivationTree (Atom := Atom) FrameClass.Metric []
      ((neg_phi.imp (Formula.bot.imp φ)).imp
       ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
    .axiom [] _ (.imp_k neg_phi Formula.bot φ) (FrameClass.base_le _)
  have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
  have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
  have peirce_ax : DerivationTree (Atom := Atom) FrameClass.Metric []
      (((φ.imp Formula.bot).imp φ).imp φ) :=
    .axiom [] _ (.peirce φ Formula.bot) (FrameClass.base_le _)
  exact h_not ⟨DerivationTree.modus_ponens [] _ _ peirce_ax step3⟩

/-- **BX⁺ Completeness Theorem over the Uniform Class `U`**: if `φ` is valid over the uniform
class `U`, then `φ` is `BX⁺`-derivable. Mirrors `completeness_dense`: build the chronicle
countermodel from a Metric-MCS, discharge `validMetricUniform`'s hypothesis with
`chronicleUniformMetric`, and derive a contradiction from `φ ∉ M`. -/
theorem completeness_metric {φ : Formula Atom}
    (h_valid : validMetricUniform φ) :
    Temporal.BXPlusDerivable φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable_metric h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum_fc h_cons
  have h_neg_in_M : (¬φ) ∈ M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg_fc hM_mcs h_neg_in_M
  have h_base_mcs := metric_mcs_implies_base_mcs hM_mcs
  let D := ChronicleSubtype M h_base_mcs
  let model := chronicleModel M h_base_mcs
  let t₀ : D := chronicleZero M h_base_mcs
  have h_uniform : uniformFrameCondition (Atom := Atom) D :=
    chronicleUniformMetric hM_mcs h_base_mcs
  have h_sat := h_valid D h_uniform model t₀
  have h_mem := (chronicle_truth_lemma M h_base_mcs t₀ φ).mp h_sat
  have h_zero : t₀.val = 0 := rfl
  rw [h_zero, limit_f_zero] at h_mem
  exact h_phi_not_M h_mem

/-! ## Dense→ℚ (oag) Bridge -/

omit [Denumerable (Formula Atom)] in
/-- **Dense→ℚ transport corollary**: a countable, dense, serial (no min/max) countermodel for
`φ` transports to a countermodel for `φ` on the ordered-abelian-group ℚ, via Cantor's
isomorphism theorem (`Order.iso_of_countable_dense`) and `Satisfies_orderIso`. This is the
concrete artifact unlocking a semantic route for dense BX⁺-fragment reasoning over oag time. -/
theorem denseCountermodel_transport_rat {D : Type*} [LinearOrder D]
    [Countable D] [DenselyOrdered D] [NoMinOrder D] [NoMaxOrder D] [Nonempty D]
    {φ : Formula Atom} (M : TemporalModel D Atom) (t : D) (h_not_sat : ¬ Satisfies M t φ) :
    ∃ (M' : TemporalModel ℚ Atom) (t' : ℚ), ¬ Satisfies M' t' φ := by
  obtain ⟨e⟩ := Order.iso_of_countable_dense D ℚ
  exact ⟨{ valuation := fun q p => M.valuation (e.symm q) p }, e t,
    (Satisfies_orderIso e M t φ).not.mp h_not_sat⟩

/-- **Dense-fragment BX⁺ completeness over the oag ℚ**: if `φ` is not derivable in the Dense
proof system, then `φ` has a countermodel on the ordered-abelian-group ℚ. Mirrors
`completeness_dense`'s chronicle construction, then transports the resulting dense chronicle
countermodel to ℚ via `denseCountermodel_transport_rat` (the chronicle carries `Countable`
via its `Rat`-subtype structure, `DenselyOrdered` via `chronicleDenselyOrderedDense`, and
`NoMinOrder`/`NoMaxOrder`/`Nonempty` as existing chronicle instances). This is the headline
bridge corollary consumed by dense semantic-route reasoning over oag time. -/
theorem denseFragment_countermodel_rat {φ : Formula Atom}
    (h_not_deriv : ¬ Temporal.ThDerivableFc FrameClass.Dense φ) :
    ∃ (M : TemporalModel ℚ Atom) (t : ℚ), ¬ Satisfies M t φ := by
  have h_cons := neg_consistent_of_not_derivable_dense h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum_fc h_cons
  have h_neg_in_M : (¬φ) ∈ M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg_fc hM_mcs h_neg_in_M
  have h_base_mcs := dense_mcs_implies_base_mcs hM_mcs
  let D := ChronicleSubtype M h_base_mcs
  let model := chronicleModel M h_base_mcs
  let t₀ : D := chronicleZero M h_base_mcs
  haveI : DenselyOrdered D := chronicleDenselyOrderedDense hM_mcs h_base_mcs
  have h_not_sat : ¬ Satisfies model t₀ φ := fun h_sat => by
    have h_mem := (chronicle_truth_lemma M h_base_mcs t₀ φ).mp h_sat
    have h_zero : t₀.val = 0 := rfl
    rw [h_zero, limit_f_zero] at h_mem
    exact h_phi_not_M h_mem
  exact denseCountermodel_transport_rat model t₀ h_not_sat

end Cslib.Logic.Temporal
