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

end Cslib.Logic.Temporal
