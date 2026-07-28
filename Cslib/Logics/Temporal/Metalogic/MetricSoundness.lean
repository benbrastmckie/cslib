/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Soundness
public import Cslib.Logics.Temporal.Metalogic.DenseMCS
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.OrderDual

/-! # Metric Soundness for Temporal Logic (BX⁺)

This module proves that the four metric uniformity axioms (`discrete_symm_fwd`,
`discrete_symm_bwd`, `discrete_propagate_fwd`, `discrete_propagate_bwd`) are semantically
valid over ordered-abelian-group time, and extends the base soundness theorem to
`FrameClass.Metric`. The resulting derivability notion is `BX⁺`, the metric tense logic.

The metric frame class is expressed entirely via the domain typeclasses
`[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]` — no change to
`TemporalModel` is needed. A nontrivial ordered abelian group auto-synthesizes `NoMaxOrder`
and `NoMinOrder`, so Base-axiom delegation to `axiom_sound` requires no extra hypotheses.

## Main Results

- `discrete_symm_fwd_sound`, `discrete_symm_bwd_sound`: metric symmetry axioms are valid.
- `discrete_propagate_fwd_sound`, `discrete_propagate_bwd_sound`: metric propagation axioms
  are valid.
- `axiom_sound_metric`: all axioms are valid over ordered-abelian-group serial linear orders.
- `swap_valid_of_valid_metric`: metric validity transfers to `swapTemporal` via `OrderDual`.
- `soundness_metric`, `soundness_thderivable_metric`: derivation soundness at `FrameClass.Metric`.
- `BXPlusDerivable`: `BX⁺` derivability abbreviation.

## References

* Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean — structural template (Dense layering)
* Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean:451–511 — uniformity-axiom arithmetic
  (`discrete_symm_fwd_valid` … `discrete_propagate_bwd_valid`), ported here to the Temporal
  `Satisfies` semantics
* [J. Burgess, *Basic Tense Logic*][Burgess1984] §6.1 — metric tense = ordered abelian group time
-/

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Metric Axiom Soundness -/

/-- Metric symmetry (fwd): `U(⊥,⊤) → S(⊥,⊤)` is valid over ordered-abelian-group time.

Proof: an immediate successor `s` of `t` (empty guard interval `(t,s)`) yields an immediate
predecessor of `t`, namely `t - (s - t)`, by translating the empty interval backwards. -/
theorem discrete_symm_fwd_sound {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] (M : TemporalModel D Atom) (t : D) :
    Satisfies M t ((Formula.untl Formula.bot Formula.top).imp
      (Formula.snce Formula.bot Formula.top)) := by
  intro ⟨s, hts, _htop, h_guard⟩
  refine ⟨t - (s - t), sub_lt_self t (sub_pos.mpr hts), Satisfies.top_true M _,
    fun c hrc hct => ?_⟩
  have h1 : t < c + (s - t) :=
    calc t = t - (s - t) + (s - t) := (sub_add_cancel t (s - t)).symm
      _ < c + (s - t) := add_lt_add_left hrc (s - t)
  have h2 : c + (s - t) < s :=
    calc c + (s - t) < t + (s - t) := add_lt_add_left hct (s - t)
      _ = s := by rw [add_comm, sub_add_cancel]
  exact h_guard (c + (s - t)) h1 h2

/-- Metric symmetry (bwd): `S(⊥,⊤) → U(⊥,⊤)` is valid over ordered-abelian-group time.

Proof: past mirror of `discrete_symm_fwd_sound`. An immediate predecessor `r` of `t` yields
an immediate successor of `t`, namely `t + (t - r)`. -/
theorem discrete_symm_bwd_sound {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] (M : TemporalModel D Atom) (t : D) :
    Satisfies M t ((Formula.snce Formula.bot Formula.top).imp
      (Formula.untl Formula.bot Formula.top)) := by
  intro ⟨r, hrt, _htop, h_guard⟩
  refine ⟨t + (t - r), lt_add_of_pos_right t (sub_pos.mpr hrt), Satisfies.top_true M _,
    fun c htc hcs => ?_⟩
  have h1 : r < c - (t - r) := by
    calc r = t - (t - r) := by rw [sub_sub_cancel]
      _ < c - (t - r) := sub_lt_sub_right htc _
  have h2 : c - (t - r) < t := by
    calc c - (t - r) < t + (t - r) - (t - r) := sub_lt_sub_right hcs _
      _ = t := by rw [add_sub_cancel_right]
  exact h_guard (c - (t - r)) h1 h2

/-- Metric propagation (fwd): `U(⊥,⊤) → G(U(⊥,⊤))` is valid over ordered-abelian-group time.

Proof: translation-invariance forwards. If `t` has an immediate successor `s`, then every
future point `u` also has an immediate successor, namely `u + (s - t)`. -/
theorem discrete_propagate_fwd_sound {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] (M : TemporalModel D Atom) (t : D) :
    Satisfies M t ((Formula.untl Formula.bot Formula.top).imp
      (Formula.allFuture (Formula.untl Formula.bot Formula.top))) := by
  intro ⟨s, hts, _htop, h_guard⟩ u _htu
  refine ⟨u + (s - t), lt_add_of_pos_right u (sub_pos.mpr hts), Satisfies.top_true M _,
    fun c huc hcs => ?_⟩
  have h1 : t < c - (u - t) := by
    calc t = u - (u - t) := by rw [sub_sub_cancel]
      _ < c - (u - t) := sub_lt_sub_right huc _
  have h2 : c - (u - t) < s := by
    conv_rhs => rw [show s = u + (s - t) - (u - t) from by rw [add_sub_sub_cancel, sub_add_cancel]]
    exact sub_lt_sub_right hcs _
  exact h_guard (c - (u - t)) h1 h2

/-- Metric propagation (bwd): `U(⊥,⊤) → H(U(⊥,⊤))` is valid over ordered-abelian-group time.

Proof: translation-invariance backwards. The witness construction is identical to
`discrete_propagate_fwd_sound` — the immediate-successor witness `u + (s - t)` at a point `u`
does not depend on whether `u` lies before or after `t`. -/
theorem discrete_propagate_bwd_sound {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] (M : TemporalModel D Atom) (t : D) :
    Satisfies M t ((Formula.untl Formula.bot Formula.top).imp
      (Formula.allPast (Formula.untl Formula.bot Formula.top))) := by
  intro ⟨s, hts, _htop, h_guard⟩ u _hut
  refine ⟨u + (s - t), lt_add_of_pos_right u (sub_pos.mpr hts), Satisfies.top_true M _,
    fun c huc hcs => ?_⟩
  have h1 : t < c - (u - t) := by
    calc t = u - (u - t) := by rw [sub_sub_cancel]
      _ < c - (u - t) := sub_lt_sub_right huc _
  have h2 : c - (u - t) < s := by
    conv_rhs => rw [show s = u + (s - t) - (u - t) from by rw [add_sub_sub_cancel, sub_add_cancel]]
    exact sub_lt_sub_right hcs _
  exact h_guard (c - (u - t)) h1 h2

/-! ## Extended Axiom Soundness at Metric -/

/-- Every axiom in the BX+Metric system is valid over ordered-abelian-group serial linear
orders.

The 26 Base axioms delegate to `axiom_sound` (Base ≤ Metric, and `NoMaxOrder`/`NoMinOrder`
are auto-synthesized from `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
[Nontrivial D]`). The 2 Dense axioms are discharged by `absurd` (`.Dense ≰ .Metric`). The
4 Metric axioms use the `*_sound` theorems above. -/
theorem axiom_sound_metric {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D]
    {φ : Formula Atom} (h_ax : Axiom φ)
    (_h_fc : h_ax.minFrameClass ≤ FrameClass.Metric)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  cases h_ax with
  | discrete_symm_fwd => exact discrete_symm_fwd_sound M t
  | discrete_symm_bwd => exact discrete_symm_bwd_sound M t
  | discrete_propagate_fwd => exact discrete_propagate_fwd_sound M t
  | discrete_propagate_bwd => exact discrete_propagate_bwd_sound M t
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

end Cslib.Logic.Temporal

universe u_dom_metric

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Metric Swap Valid -/

/-- Metric version of `swap_valid_of_valid`: if `φ` is satisfied everywhere in all
ordered-abelian-group serial linear order models, then `swapTemporal φ` is also satisfied.
Proved by transferring to the dual model (`OrderDual D` preserves `AddCommGroup`,
`LinearOrder`, `IsOrderedAddMonoid`, and `Nontrivial`). -/
theorem swap_valid_of_valid_metric
    {φ : Formula Atom}
    (h_valid : ∀ (D : Type u_dom_metric) [AddCommGroup D] [LinearOrder D]
      [IsOrderedAddMonoid D] [Nontrivial D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ)
    (D : Type u_dom_metric) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D]
    (M : TemporalModel D Atom) (t : D) :
    Satisfies M t (Formula.swapTemporal φ) := by
  rw [swapTemporal_dual]
  exact h_valid (OrderDual D) (dualModel M) (OrderDual.toDual t)

/-! ## Metric Soundness Theorem -/

/-- **Soundness at Metric**: If `Γ ⊢[Metric] φ`, then for any ordered-abelian-group serial
linear order model and any time where all of `Γ` is satisfied, `φ` is also satisfied. -/
theorem soundness_metric {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D]
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Metric Γ φ)
    (M : TemporalModel D Atom) (t : D)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies M t ψ) : Satisfies M t φ := by
  match d with
  | .axiom _ ψ h_ax h_fc =>
    exact axiom_sound_metric h_ax h_fc M t
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact soundness_metric d₁ M t h_ctx (soundness_metric d₂ M t h_ctx)
  | .temporal_necessitation ψ d' =>
    simp only [Satisfies.allFuture_iff]
    intro s hlt
    exact soundness_metric d' M s (fun _ h => nomatch h)
  | .temporal_duality ψ d' =>
    exact swap_valid_of_valid_metric
      (fun D' _ _ _ _ M' t' => soundness_metric d' M' t' (fun _ h => nomatch h)) D M t
  | .weakening Γ' Δ ψ d' h_sub =>
    exact soundness_metric d' M t (fun x hx => h_ctx x (h_sub hx))

/-- **Soundness for Metric-derivable formulas**: If `ThDerivableFc .Metric φ`, then `φ` is
valid over all ordered-abelian-group serial linear orders. -/
theorem soundness_thderivable_metric {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D]
    {φ : Formula Atom} (h : Temporal.ThDerivableFc FrameClass.Metric φ)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  obtain ⟨d⟩ := h
  exact soundness_metric d M t (fun _ h => nomatch h)

/-! ## BX⁺ Derivability -/

/-- `BX⁺` derivability: derivability at the metric frame class `FrameClass.Metric`.
`BX⁺` is the metric tense logic, sound over ordered-abelian-group time. -/
def BXPlusDerivable (φ : Formula Atom) : Prop :=
  Temporal.ThDerivableFc FrameClass.Metric φ

end Cslib.Logic.Temporal
