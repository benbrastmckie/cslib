/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.DerivationTree
public import Mathlib.Order.Max
public import Cslib.Logics.Temporal.Semantics.Satisfies

/-! # Soundness Theorem for Temporal Logic BX

This module proves that every formula derivable in the BX proof system is valid
over all serial linear orders (linear orders with `NoMaxOrder` and `NoMinOrder`).

## Main Results

- `axiom_sound`: Each of the 26 BX axiom schemata is valid over serial linear orders.
- `swapTemporal_dual`: swapTemporal φ satisfaction equals φ satisfaction in dual model.
- `soundness`: If `Γ ⊢ φ`, then `φ` is satisfied wherever all of `Γ` is satisfied.
- `soundness_thderivable`: If `⊢ φ`, then `φ` is valid over all serial linear orders.

## References

* Cslib/Logics/Modal/Metalogic/Soundness.lean — structural template
* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom system
-/


@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Semantic helpers -/

theorem sat_and_iff {D : Type*} [LinearOrder D] (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (φ ∧ ψ) ↔ (Satisfies M t φ ∧ Satisfies M t ψ) := by
  simp only [Satisfies]
  constructor
  · intro h
    constructor
    · by_contra hφ; exact h (fun hφ' => absurd hφ' hφ)
    · by_contra hψ; exact h (fun _ hψ' => absurd hψ' hψ)
  · intro ⟨hφ, hψ⟩ h; exact h hφ hψ

theorem sat_or_iff {D : Type*} [LinearOrder D] (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (φ ∨ ψ) ↔ (Satisfies M t φ ∨ Satisfies M t ψ) := by
  simp only [Satisfies]
  constructor
  · intro h
    by_contra h_neg
    push Not at h_neg
    exact h_neg.2 (h (fun hφ => absurd hφ h_neg.1))
  · intro h hnφ
    rcases h with hφ | hψ
    · exact absurd hφ hnφ
    · exact hψ

/-! ## Axiom Soundness -/

/-- Every BX axiom is valid over serial linear orders.

The proof handles all 26 axiom constructors by case analysis. For each axiom,
we verify its semantic validity over linear orders with no maximum or minimum. -/
theorem axiom_sound {D : Type*} [LinearOrder D] [NoMaxOrder D] [NoMinOrder D]
    {φ : Formula Atom} (h_ax : Axiom φ)
    (_h_fc : h_ax.minFrameClass ≤ FrameClass.Base)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  cases h_ax with
  | imp_k φ ψ χ => intro h₁ h₂ h₃; exact h₁ h₃ (h₂ h₃)
  | imp_s φ ψ => intro hφ _; exact hφ
  | efq φ => intro h; exact absurd h id
  | peirce φ ψ => intro h; by_contra hn; exact hn (h (fun hφ => absurd hφ hn))
  | serial_future =>
    intro _
    have : Satisfies M t (𝐅⊤) := by
      simp only [Satisfies.someFuture_iff]
      obtain ⟨s, hs⟩ := exists_gt t; exact ⟨s, hs, Satisfies.top_true M s⟩
    exact this
  | serial_past =>
    intro _
    have : Satisfies M t (𝐏⊤) := by
      simp only [Satisfies.somePast_iff]
      obtain ⟨s, hs⟩ := exists_lt t; exact ⟨s, hs, Satisfies.top_true M s⟩
    exact this
  | left_mono_until_G φ ψ χ =>
    -- G(φ→ψ) → (χ U φ → χ U ψ). Guard monotonicity.
    -- G(φ→ψ) unfolds definitionally (allFuture_iff, imp_iff) to
    -- ∀ s > t, Satisfies M s φ → Satisfies M s ψ.
    intro hGimp huntl
    have hG : ∀ s, t < s → Satisfies M s φ → Satisfies M s ψ := hGimp
    obtain ⟨s, hlt, hev, hg⟩ := huntl
    exact ⟨s, hlt, hev, fun r hr1 hr2 => hG r hr1 (hg r hr1 hr2)⟩
  | left_mono_since_H φ ψ χ =>
    intro hHimp hsnce
    have hH : ∀ s, s < t → Satisfies M s φ → Satisfies M s ψ := hHimp
    obtain ⟨s, hlt, hev, hg⟩ := hsnce
    exact ⟨s, hlt, hev, fun r hr1 hr2 => hH r hr2 (hg r hr1 hr2)⟩
  | right_mono_until φ ψ χ =>
    -- G(φ→ψ) → (φ U χ → ψ U χ). Event changes from φ to ψ, guard χ stays.
    intro hGimp huntl
    have hG : ∀ s, t < s → Satisfies M s φ → Satisfies M s ψ := hGimp
    obtain ⟨s, hlt, hev, hg⟩ := huntl
    exact ⟨s, hlt, hG s hlt hev, hg⟩
  | right_mono_since φ ψ χ =>
    intro hHimp hsnce
    have hH : ∀ s, s < t → Satisfies M s φ → Satisfies M s ψ := hHimp
    obtain ⟨s, hlt, hev, hg⟩ := hsnce
    exact ⟨s, hlt, hH s hlt hev, hg⟩
  | connect_future φ =>
    -- φ → G(P(φ)). G(X) unfolds definitionally to ∀ s > t, Satisfies M s X.
    intro hφ s hts
    exact (Satisfies.somePast_iff M s φ).mpr ⟨t, hts, hφ⟩
  | connect_past φ =>
    -- φ → H(F(φ)). H(X) unfolds definitionally to ∀ s < t, Satisfies M s X.
    intro hφ s hts
    exact (Satisfies.someFuture_iff M s φ).mpr ⟨t, hts, hφ⟩
  | enrichment_until φ ψ p =>
    -- p ∧ (φ U ψ) → (φ U (ψ ∧ (φ S p)))
    -- GUARD=φ stays, EVENT enriched: ψ → ψ ∧ (φ S p)
    intro hconj
    have ⟨hp, huntl⟩ := (sat_and_iff M t p (φ U ψ)).mp hconj
    obtain ⟨s, hts, hψs, hguard⟩ := huntl
    -- EVENT at s: need ψ(s) ∧ (φ S p)(s). ψ(s) = hψs.
    -- (φ S p)(s) = ∃ s' < s, p(s') ∧ ∀ r, s' < r → r < s → φ(r). Witness: t.
    exact ⟨s, hts,
      (sat_and_iff M s ψ (φ S p)).mpr
        ⟨hψs, t, hts, hp, fun r' hr1' hr2' => hguard r' hr1' hr2'⟩,
      hguard⟩
  | enrichment_since φ ψ p =>
    -- p ∧ (φ S ψ) → (φ S (ψ ∧ (φ U p)))
    intro hconj
    have ⟨hp, hsnce⟩ := (sat_and_iff M t p (φ S ψ)).mp hconj
    obtain ⟨s, hst, hψs, hguard⟩ := hsnce
    exact ⟨s, hst,
      (sat_and_iff M s ψ (φ U p)).mpr
        ⟨hψs, t, hst, hp, fun r' hr1' hr2' => hguard r' hr1' hr2'⟩,
      hguard⟩
  | self_accum_until φ ψ =>
    -- (φ U ψ) → ((φ ∧ (φ U ψ)) U ψ)
    intro huntl
    obtain ⟨s, hts, hψs, hguard⟩ := huntl
    exact ⟨s, hts, hψs, fun r hr1 hr2 =>
      (sat_and_iff M r φ (φ U ψ)).mpr
        ⟨hguard r hr1 hr2,
         s, hr2, hψs, fun r' hr1' hr2' => hguard r' (lt_trans hr1 hr1') hr2'⟩⟩
  | self_accum_since φ ψ =>
    -- (φ S ψ) → ((φ ∧ (φ S ψ)) S ψ)
    intro hsnce
    obtain ⟨s, hst, hψs, hguard⟩ := hsnce
    exact ⟨s, hst, hψs, fun r hr1 hr2 =>
      (sat_and_iff M r φ (φ S ψ)).mpr
        ⟨hguard r hr1 hr2,
         s, hr1, hψs, fun r' hr1' hr2' => hguard r' hr1' (lt_trans hr2' hr2)⟩⟩
  | absorb_until φ ψ =>
    -- (φ U (φ ∧ (φ U ψ))) → (φ U ψ)
    intro huntl
    obtain ⟨s, hts, hevent, hguard⟩ := huntl
    have ⟨hφs, s', hss', hψs', hguard'⟩ :=
      (sat_and_iff M s φ (φ U ψ)).mp hevent
    -- hψs' is the event at s', hguard' gives φ between s and s'
    exact ⟨s', lt_trans hts hss', hψs', fun r hr1 hr2 => by
      rcases lt_or_ge r s with h | h
      · exact hguard r hr1 h
      · rcases eq_or_lt_of_le h with rfl | h'
        · exact hφs
        · exact hguard' r h' hr2⟩
  | absorb_since φ ψ =>
    -- (φ S (φ ∧ (φ S ψ))) → (φ S ψ)
    intro hsnce
    obtain ⟨s, hst, hevent, hguard⟩ := hsnce
    have ⟨hφs, s', hs's, hψs', hguard'⟩ :=
      (sat_and_iff M s φ (φ S ψ)).mp hevent
    exact ⟨s', lt_trans hs's hst, hψs', fun r hr1 hr2 => by
      rcases le_or_gt s r with h | h
      · rcases eq_or_lt_of_le h with rfl | h'
        · exact hφs
        · exact hguard r h' hr2
      · exact hguard' r hr1 h⟩
  | linear_until φ ψ χ θ =>
    -- (φ U ψ) ∧ (χ U θ) → ((φ∧χ) U (ψ∧θ)) ∨ ((φ∧χ) U (ψ∧χ)) ∨ ((φ∧χ) U (φ∧θ))
    intro hconj
    have ⟨h1, h2⟩ := (sat_and_iff M t (φ U ψ) (χ U θ)).mp hconj
    obtain ⟨s₁, ht1, hψ1, hg1⟩ := h1
    obtain ⟨s₂, ht2, hθ2, hg2⟩ := h2
    rcases lt_trichotomy s₁ s₂ with h | h | h
    · -- s₁ < s₂: second disjunct (φ∧χ) U (ψ∧χ) with witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inl
        ((sat_or_iff M t _ _).mpr (Or.inr
          ⟨s₁, ht1,
           (sat_and_iff M s₁ ψ χ).mpr ⟨hψ1, hg2 s₁ ht1 h⟩,
           fun r hr1 hr2 =>
             (sat_and_iff M r φ χ).mpr ⟨hg1 r hr1 hr2, hg2 r hr1 (lt_trans hr2 h)⟩⟩)))
    · subst h
      -- s₁ = s₂: first disjunct (φ∧χ) U (ψ∧θ) with witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inl
        ((sat_or_iff M t _ _).mpr (Or.inl
          ⟨s₁, ht1,
           (sat_and_iff M s₁ ψ θ).mpr ⟨hψ1, hθ2⟩,
           fun r hr1 hr2 =>
             (sat_and_iff M r φ χ).mpr ⟨hg1 r hr1 hr2, hg2 r hr1 hr2⟩⟩)))
    · -- s₂ < s₁: third disjunct (φ∧χ) U (φ∧θ) with witness s₂
      exact (sat_or_iff M t _ _).mpr (Or.inr
        ⟨s₂, ht2,
         (sat_and_iff M s₂ φ θ).mpr ⟨hg1 s₂ ht2 h, hθ2⟩,
         fun r hr1 hr2 =>
           (sat_and_iff M r φ χ).mpr ⟨hg1 r hr1 (lt_trans hr2 h), hg2 r hr1 hr2⟩⟩)
  | linear_since φ ψ χ θ =>
    -- (φ S ψ) ∧ (χ S θ) → ((φ∧χ) S (ψ∧θ)) ∨ ((φ∧χ) S (ψ∧χ)) ∨ ((φ∧χ) S (φ∧θ))
    intro hconj
    have ⟨h1, h2⟩ := (sat_and_iff M t (φ S ψ) (χ S θ)).mp hconj
    obtain ⟨s₁, h1t, hψ1, hg1⟩ := h1
    obtain ⟨s₂, h2t, hθ2, hg2⟩ := h2
    rcases lt_trichotomy s₁ s₂ with h | h | h
    · -- s₁ < s₂: third disjunct (φ∧χ) S (φ∧θ), witness s₂
      exact (sat_or_iff M t _ _).mpr (Or.inr
        ⟨s₂, h2t,
         (sat_and_iff M s₂ φ θ).mpr ⟨hg1 s₂ h h2t, hθ2⟩,
         fun r hr1 hr2 =>
           (sat_and_iff M r φ χ).mpr ⟨hg1 r (lt_trans h hr1) hr2, hg2 r hr1 hr2⟩⟩)
    · subst h
      -- s₁ = s₂: first disjunct (φ∧χ) S (ψ∧θ), witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inl
        ((sat_or_iff M t _ _).mpr (Or.inl
          ⟨s₁, h1t,
           (sat_and_iff M s₁ ψ θ).mpr ⟨hψ1, hθ2⟩,
           fun r hr1 hr2 =>
             (sat_and_iff M r φ χ).mpr ⟨hg1 r hr1 hr2, hg2 r hr1 hr2⟩⟩)))
    · -- s₂ < s₁: second disjunct (φ∧χ) S (ψ∧χ), witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inl
        ((sat_or_iff M t _ _).mpr (Or.inr
          ⟨s₁, h1t,
           (sat_and_iff M s₁ ψ χ).mpr ⟨hψ1, hg2 s₁ h h1t⟩,
           fun r hr1 hr2 =>
             (sat_and_iff M r φ χ).mpr ⟨hg1 r hr1 hr2, hg2 r (lt_trans h hr1) hr2⟩⟩)))
  | until_F φ ψ =>
    -- (φ U ψ) → F(ψ)
    intro huntl
    obtain ⟨s, hlt, hψ, _⟩ := huntl
    exact (Satisfies.someFuture_iff M t ψ).mpr ⟨s, hlt, hψ⟩
  | since_P φ ψ =>
    -- S(ψ,φ) → P(ψ)
    intro hsnce
    obtain ⟨s, hlt, hψ, _⟩ := hsnce
    exact (Satisfies.somePast_iff M t ψ).mpr ⟨s, hlt, hψ⟩
  | temp_linearity φ ψ =>
    -- F(φ) ∧ F(ψ) → F(φ∧ψ) ∨ F(φ∧F(ψ)) ∨ F(F(φ)∧ψ)
    intro hconj
    have ⟨h1, h2⟩ := (sat_and_iff M t (𝐅φ) (𝐅ψ)).mp hconj
    obtain ⟨s₁, ht1, hφ1⟩ := (Satisfies.someFuture_iff M t φ).mp h1
    obtain ⟨s₂, ht2, hψ2⟩ := (Satisfies.someFuture_iff M t ψ).mp h2
    rcases lt_trichotomy s₁ s₂ with h | h | h
    · -- s₁ < s₂: second disjunct F(φ∧F(ψ)), witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inr
        ((sat_or_iff M t _ _).mpr (Or.inl
          ((Satisfies.someFuture_iff M t _).mpr
            ⟨s₁, ht1, (sat_and_iff M s₁ φ (𝐅ψ)).mpr
              ⟨hφ1, (Satisfies.someFuture_iff M s₁ ψ).mpr ⟨s₂, h, hψ2⟩⟩⟩))))
    · subst h
      -- s₁ = s₂: first disjunct F(φ∧ψ), witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inl
        ((Satisfies.someFuture_iff M t _).mpr
          ⟨s₁, ht1, (sat_and_iff M s₁ φ ψ).mpr ⟨hφ1, hψ2⟩⟩))
    · -- s₂ < s₁: third disjunct F(F(φ)∧ψ), witness s₂
      exact (sat_or_iff M t _ _).mpr (Or.inr
        ((sat_or_iff M t _ _).mpr (Or.inr
          ((Satisfies.someFuture_iff M t _).mpr
            ⟨s₂, ht2, (sat_and_iff M s₂ (𝐅φ) ψ).mpr
              ⟨(Satisfies.someFuture_iff M s₂ φ).mpr ⟨s₁, h, hφ1⟩, hψ2⟩⟩))))
  | temp_linearity_past φ ψ =>
    -- P(φ) ∧ P(ψ) → P(φ∧ψ) ∨ P(φ∧P(ψ)) ∨ P(P(φ)∧ψ)
    intro hconj
    have ⟨h1, h2⟩ := (sat_and_iff M t (𝐏φ) (𝐏ψ)).mp hconj
    obtain ⟨s₁, h1t, hφ1⟩ := (Satisfies.somePast_iff M t φ).mp h1
    obtain ⟨s₂, h2t, hψ2⟩ := (Satisfies.somePast_iff M t ψ).mp h2
    rcases lt_trichotomy s₁ s₂ with h | h | h
    · -- s₁ < s₂: third disjunct P(P(φ)∧ψ), witness s₂
      exact (sat_or_iff M t _ _).mpr (Or.inr
        ((sat_or_iff M t _ _).mpr (Or.inr
          ((Satisfies.somePast_iff M t _).mpr
            ⟨s₂, h2t, (sat_and_iff M s₂ (𝐏φ) ψ).mpr
              ⟨(Satisfies.somePast_iff M s₂ φ).mpr ⟨s₁, h, hφ1⟩, hψ2⟩⟩))))
    · subst h
      -- s₁ = s₂: first disjunct P(φ∧ψ), witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inl
        ((Satisfies.somePast_iff M t _).mpr
          ⟨s₁, h1t, (sat_and_iff M s₁ φ ψ).mpr ⟨hφ1, hψ2⟩⟩))
    · -- s₂ < s₁: second disjunct P(φ∧P(ψ)), witness s₁
      exact (sat_or_iff M t _ _).mpr (Or.inr
        ((sat_or_iff M t _ _).mpr (Or.inl
          ((Satisfies.somePast_iff M t _).mpr
            ⟨s₁, h1t, (sat_and_iff M s₁ φ (𝐏ψ)).mpr
              ⟨hφ1, (Satisfies.somePast_iff M s₁ ψ).mpr ⟨s₂, h, hψ2⟩⟩⟩))))
  | F_until_equiv φ =>
    -- F(φ) → U(φ, ⊤)
    intro hF
    obtain ⟨s, hlt, hφ⟩ := (Satisfies.someFuture_iff M t φ).mp hF
    exact ⟨s, hlt, hφ, fun _ _ _ => Satisfies.top_true M _⟩
  | P_since_equiv φ =>
    -- P(φ) → S(φ, ⊤)
    intro hP
    obtain ⟨s, hlt, hφ⟩ := (Satisfies.somePast_iff M t φ).mp hP
    exact ⟨s, hlt, hφ, fun _ _ _ => Satisfies.top_true M _⟩
  | allFuture_to_classic φ =>
    -- 𝐆φ → ¬𝐅¬φ, via the P2 semantic bridge (allFuture_iff/someFuture_iff/neg_iff).
    exact (Satisfies.sat_allFuture_iff_neg_someFuture_neg M t φ).mp
  | classic_to_allFuture φ =>
    -- ¬𝐅¬φ → 𝐆φ (classical direction), via the same bridge.
    exact (Satisfies.sat_allFuture_iff_neg_someFuture_neg M t φ).mpr
  | allPast_to_classic φ =>
    -- 𝐇φ → ¬𝐏¬φ, via the P2 semantic bridge.
    exact (Satisfies.sat_allPast_iff_neg_somePast_neg M t φ).mp
  | classic_to_allPast φ =>
    -- ¬𝐏¬φ → 𝐇φ (classical direction), via the same bridge.
    exact (Satisfies.sat_allPast_iff_neg_somePast_neg M t φ).mpr
  | density _ => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | discrete_symm_fwd => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | discrete_symm_bwd => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | discrete_propagate_fwd => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | discrete_propagate_bwd => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])

/-! ## Swap Temporal Duality -/

/-- The dual model: given a model on `D`, produce a model on `OrderDual D`
with the same valuation. -/
def dualModel {D : Type*} [LinearOrder D] (M : TemporalModel D Atom) :
    TemporalModel (OrderDual D) Atom where
  valuation := fun t p => M.valuation (OrderDual.ofDual t) p

/-- `swapTemporal φ` in model `M` at time `t` is equivalent to `φ` in the dual model. -/
theorem swapTemporal_dual {D : Type*} [LinearOrder D]
    (M : TemporalModel D Atom) (t : D) (φ : Formula Atom) :
    Satisfies M t (Formula.swapTemporal φ) ↔
      Satisfies (dualModel M) (OrderDual.toDual t) φ := by
  induction φ generalizing t with
  | atom p => simp [Formula.swapTemporal, Satisfies, dualModel]
  | bot => simp [Formula.swapTemporal, Satisfies]
  | imp α β ihα ihβ =>
    simp only [Formula.swapTemporal, Satisfies]
    exact ⟨fun h hα => (ihβ t).mp (h ((ihα t).mpr hα)),
           fun h hα => (ihβ t).mpr (h ((ihα t).mp hα))⟩
  | untl β α ihβ ihα =>
    simp only [Formula.swapTemporal, Satisfies]
    constructor
    · rintro ⟨s, hst, hα, hguard⟩
      exact ⟨OrderDual.toDual s, hst, (ihα s).mp hα,
        fun r hr1 hr2 => (ihβ (OrderDual.ofDual r)).mp (hguard (OrderDual.ofDual r) hr2 hr1)⟩
    · rintro ⟨s, hst, hα, hguard⟩
      exact ⟨OrderDual.ofDual s, hst, (ihα (OrderDual.ofDual s)).mpr hα,
        fun r hr1 hr2 => (ihβ r).mpr (hguard (OrderDual.toDual r) hr2 hr1)⟩
  | snce β α ihβ ihα =>
    simp only [Formula.swapTemporal, Satisfies]
    constructor
    · rintro ⟨s, hts, hα, hguard⟩
      exact ⟨OrderDual.toDual s, hts, (ihα s).mp hα,
        fun r hr1 hr2 => (ihβ (OrderDual.ofDual r)).mp (hguard (OrderDual.ofDual r) hr2 hr1)⟩
    · rintro ⟨s, hts, hα, hguard⟩
      exact ⟨OrderDual.ofDual s, hts, (ihα (OrderDual.ofDual s)).mpr hα,
        fun r hr1 hr2 => (ihβ r).mpr (hguard (OrderDual.toDual r) hr2 hr1)⟩
  | allFuture φ ihφ =>
    -- swap(𝐆φ) = 𝐇(swap φ). Both sides unfold definitionally (allFuture/allPast
    -- structural clauses); the OrderDual `<` is definitionally reversed, so the
    -- witnesses transfer via `OrderDual.toDual`/`OrderDual.ofDual` without a
    -- named order lemma (matches the `untl`/`snce` cases above).
    simp only [Formula.swapTemporal, Satisfies]
    constructor
    · intro h s' hs'
      exact (ihφ (OrderDual.ofDual s')).mp (h (OrderDual.ofDual s') hs')
    · intro h s hs
      exact (ihφ s).mpr (h (OrderDual.toDual s) hs)
  | allPast φ ihφ =>
    -- swap(𝐇φ) = 𝐆(swap φ). Past dual of the `allFuture` case above.
    simp only [Formula.swapTemporal, Satisfies]
    constructor
    · intro h s' hs'
      exact (ihφ (OrderDual.ofDual s')).mp (h (OrderDual.ofDual s') hs')
    · intro h s hs
      exact (ihφ s).mpr (h (OrderDual.toDual s) hs)

end Cslib.Logic.Temporal

universe u_dom

namespace Cslib.Logic.Temporal

/-- If `φ` is satisfied everywhere in all serial linear order models, then
`swapTemporal φ` is also satisfied. Proved by transferring to the dual model. -/
theorem swap_valid_of_valid
    {φ : Formula Atom}
    (h_valid : ∀ (D : Type u_dom) [LinearOrder D] [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ)
    (D : Type u_dom) [LinearOrder D] [NoMaxOrder D] [NoMinOrder D]
    (M : TemporalModel D Atom) (t : D) :
    Satisfies M t (Formula.swapTemporal φ) := by
  rw [swapTemporal_dual]
  exact h_valid (OrderDual D) (dualModel M) (OrderDual.toDual t)

/-! ## Main Soundness Theorem -/

/-- **Soundness Theorem**: If `Γ ⊢ φ`, then for any serial linear order model and
any time where all of `Γ` is satisfied, `φ` is also satisfied. -/
theorem soundness {D : Type*} [LinearOrder D] [NoMaxOrder D] [NoMinOrder D]
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base Γ φ)
    (M : TemporalModel D Atom) (t : D)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies M t ψ) : Satisfies M t φ := by
  match d with
  | .axiom _ ψ h_ax h_fc =>
    exact axiom_sound h_ax h_fc M t
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact soundness d₁ M t h_ctx (soundness d₂ M t h_ctx)
  | .temporal_necessitation ψ d' =>
    simp only [Satisfies.allFuture_iff]
    intro s hlt
    exact soundness d' M s (fun _ h => nomatch h)
  | .temporal_duality ψ d' =>
    exact swap_valid_of_valid
      (fun D' _ _ _ M' t' => soundness d' M' t' (fun _ h => nomatch h)) D M t
  | .weakening Γ' Δ ψ d' h_sub =>
    exact soundness d' M t (fun x hx => h_ctx x (h_sub hx))

/-- **Soundness for derivable formulas**. -/
theorem soundness_thderivable {D : Type*} [LinearOrder D] [NoMaxOrder D] [NoMinOrder D]
    {φ : Formula Atom} (h : Temporal.ThDerivable φ)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  obtain ⟨d⟩ := h
  exact soundness d M t (fun _ h => nomatch h)

end Cslib.Logic.Temporal
