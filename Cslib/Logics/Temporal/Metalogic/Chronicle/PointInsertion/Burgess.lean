/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Seeds

/-! # Burgess — gContent ⊆ B, Xu Lemmas, and Splitting Helpers

gContent ⊆ B from BurgessR3Maximal, Xu Lemma 2.3, derivation monotonicity, BX13/BX13',
F/P monotonicity, Xu Lemma 3.2.1, duality, Lemma 2.6 interval insertion, and
propositional/list/guard helpers used in the Splitting module.

## Main Results

- `g_content_sub`: BurgessR3Maximal implies gContent(A) ⊆ B
- `xu_lemma_3_2_1_until` / `xu_lemma_3_2_1_since`: Full guard strengthening
- `h_content_sub_imp_g_content_sub'`: Duality between gContent and hContent
- `lemma_2_6_splitting`: Burgess Lemma 2.6 interval insertion
- `EnrichedEvent`, `EnrichedEventSince`: Iterated enrichment result structures
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 3200000

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

/-! ## gContent(A) ⊆ B from BurgessR3Maximal -/

/-- Helper: ⊢ φ → (β → (β ∧ φ)). Conjunction introduction curried. -/
private noncomputable def conjIntroCurried (β φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (β.imp (Formula.and β φ))) := by
  have h1 : DerivationTree FrameClass.Base [β, φ] (Formula.and β φ) :=
    DerivationTree.modus_ponens [β, φ] _ _
      (DerivationTree.modus_ponens [β, φ] β _
        (DerivationTree.weakening [] [β, φ] _
          (pairing β φ) (List.nil_subset _))
        (DerivationTree.assumption _ β (by simp)))
      (DerivationTree.assumption _ φ (by simp))
  exact deductionTheorem [] φ _ (deductionTheorem [φ] β _ h1)

/-- Helper: ⊢ φ → (φ.neg → ψ) for any ψ. -/
private noncomputable def exFalsoFromAssumption (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.neg.imp ψ)) := by
  have h1 : DerivationTree FrameClass.Base [φ.neg, φ] Formula.bot :=
    DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
      (DerivationTree.assumption _ φ.neg (by simp))
      (DerivationTree.assumption _ φ (by simp))
  have h2 : DerivationTree FrameClass.Base [φ.neg, φ] ψ :=
    DerivationTree.modus_ponens [φ.neg, φ] Formula.bot ψ
      (DerivationTree.weakening [] [φ.neg, φ] (Formula.bot.imp ψ)
        (efqAxiom ψ) (List.nil_subset _))
      h1
  exact deductionTheorem [] φ _ (deductionTheorem [φ] φ.neg ψ h2)

/-- When {φ} ∪ B is inconsistent with CUD B, then (¬φ) ∈ B. -/
private theorem neg_mem_of_inconsistent_union {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    {φ : Formula Atom} (h_not_cons : ¬Temporal.SetConsistent ({φ} ∪ B)) :
    (¬φ) ∈ B := by
  by_contra h_neg_not_B
  apply h_not_cons
  intro L hL ⟨d⟩
  set M := L.filter (fun x => !decide (x = φ)) with hM_def
  have hM_sub_B : ∀ ψ ∈ M, ψ ∈ B := by
    intro ψ hψ; rw [hM_def] at hψ
    have h_mem := List.mem_filter.mp hψ
    have h1 : ψ ∈ L := h_mem.1
    have h2 : ψ ≠ φ := by simp at h_mem; exact h_mem.2
    rcases hL ψ h1 with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) h2
    · exact h
  have hL_sub_φM : L ⊆ φ :: M := by
    intro x hx
    by_cases heq : x = φ
    · subst heq; exact .head M
    · exact .tail _ (List.mem_filter.mpr ⟨hx, by simp; exact heq⟩)
  have d_w : DerivationTree FrameClass.Base (φ :: M) Formula.bot :=
    DerivationTree.weakening L (φ :: M) Formula.bot d hL_sub_φM
  have d_neg : DerivationTree FrameClass.Base M φ.neg := deductionTheorem M φ Formula.bot d_w
  exact h_neg_not_B (h_cud M φ.neg hM_sub_B d_neg)

/-- G(φ.neg → ψ) ∈ A from G(φ) ∈ A, using exFalsoFromAssumption + temporal necessitation + K. -/
private theorem G_ex_falso_strengthen {A : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_Gφ : (𝐆φ) ∈ A) :
    (φ.neg.imp ψ).allFuture ∈ A := by
  have d_ef := exFalsoFromAssumption φ ψ
  exact temporal_implication_property h_mcs_A
    (temporal_implication_property h_mcs_A
      (theoremInMcs h_mcs_A (tempKDistDerived φ (φ.neg.imp ψ)))
      (theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ d_ef)))
    h_Gφ

/-- When {φ} ∪ B is inconsistent, burgessR3(A, Set.univ, C). -/
private theorem burgessR3_univ_of_inconsistent_ext {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3 : burgessR3 A B C)
    {φ : Formula Atom} (h_Gφ : (𝐆φ) ∈ A)
    (h_neg_in_B : (¬φ) ∈ B) :
    burgessR3 A Set.univ C := by
  constructor
  · intro ψ _ γ hγ
    have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
    have h_G_impl := G_ex_falso_strengthen h_mcs_A φ ψ h_Gφ
    exact untl_left_mono_G h_mcs_A h_G_impl h_untl_neg
  · intro ψ _ α hα
    have h_burgessR : burgessR A ψ C := fun γ hγ => by
      have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
      have h_G_impl := G_ex_falso_strengthen h_mcs_A φ ψ h_Gφ
      exact untl_left_mono_G h_mcs_A h_G_impl h_untl_neg
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR α hα

/-- Set.univ is ClosedUnderDerivation. -/
private theorem set_univ_closed_under_derivation : ClosedUnderDerivation (Set.univ : Set (Formula Atom)) :=
  fun _ _ _ _ => Set.mem_univ _

/-- Inconsistent CUD set equals Set.univ. -/
private theorem closed_under_derivation_inconsistent_eq_univ
    {D : Set (Formula Atom)} (h_cud : ClosedUnderDerivation D) (h_not_cons : ¬Temporal.SetConsistent D) :
    D = Set.univ := by
  have h_exists : ∃ L : List (Formula Atom), (∀ φ ∈ L, φ ∈ D) ∧ Nonempty (DerivationTree FrameClass.Base L (Formula.bot : Formula Atom)) := by
    by_contra h_all
    apply h_not_cons
    intro L hL hd
    exact h_all ⟨L, hL, hd⟩
  obtain ⟨L, hL, ⟨d⟩⟩ := h_exists
  have h_bot : (Formula.bot : Formula Atom) ∈ D := h_cud L Formula.bot hL d
  ext φ; simp only [Set.mem_univ, iff_true]
  have d_efq : DerivationTree FrameClass.Base [(Formula.bot : Formula Atom)] φ :=
    DerivationTree.modus_ponens [(Formula.bot : Formula Atom)] Formula.bot φ
      (DerivationTree.weakening [] [(Formula.bot : Formula Atom)] ((Formula.bot : Formula Atom).imp φ)
        (efqAxiom φ) (List.nil_subset _))
      (DerivationTree.assumption [(Formula.bot : Formula Atom)] Formula.bot (by simp))
  exact h_cud [(Formula.bot : Formula Atom)] φ (fun ψ hψ => by simp at hψ; rw [hψ]; exact h_bot) d_efq

/-- gContent(A) ⊆ B from BurgessR3Maximal: every G(φ) ∈ A has φ ∈ B. -/
theorem g_content_sub {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_R3M : BurgessR3Maximal A B C) :
    gContent A ⊆ B := by
  intro φ hφ
  by_contra h_not
  have h_dcs : ClosedUnderDerivation B := h_R3M.1
  have h_r3 : burgessR3 A B C := h_R3M.2.1
  -- Case split: is {φ} ∪ B consistent?
  by_cases h_cons : Temporal.SetConsistent ({φ} ∪ B)
  · -- Consistent case: show DC({φ}∪B) satisfies burgessR3, contradicting maximality
    have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
        Formula.untl (Formula.and beta φ) gamma ∈ A := by
      intro beta h_beta gamma h_gamma
      have hUntl := h_r3.1 beta h_beta gamma h_gamma
      -- G(φ) ∈ A, so G(β → β ∧ φ) ∈ A
      have h_flip := conjIntroCurried beta φ
      have h_G_flip := theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
      have h_kd := tempKDistDerived φ (beta.imp (Formula.and beta φ))
      have h_G_guard_str : (beta.imp (Formula.and beta φ)).allFuture ∈ A :=
        temporal_implication_property h_mcs_A
          (temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_kd) h_G_flip) hφ
      exact untl_left_mono_G h_mcs_A h_G_guard_str hUntl
    have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
        Formula.snce (Formula.and beta φ) alpha ∈ C := by
      intro beta h_beta alpha h_alpha
      have h_burgessR : burgessR A (Formula.and beta φ) C :=
        fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
      exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha h_alpha
    have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
    exact absurd h_r3_ext (BurgessR3Maximal_extension_fails h_R3M h_not)
  · -- Inconsistent case: (¬φ) ∈ B, derive burgessR3(A, Set.univ, C)
    have h_neg_in := neg_mem_of_inconsistent_union h_dcs h_cons
    have h_r3_univ := burgessR3_univ_of_inconsistent_ext h_mcs_A h_mcs_C h_r3 hφ h_neg_in
    -- Set.univ is CUD, B ⊂ Set.univ (B is consistent since BurgessR3Maximal has a DCS part)
    -- Actually B is CUD. B ≠ Set.univ since ⊥ ∉ B (B is consistent? Not necessarily for BurgessR3Maximal).
    -- BurgessR3Maximal only requires CUD, not SDC. But if B were inconsistent, B = Set.univ.
    -- In that case, φ ∈ B = Set.univ, contradicting h_not. So B must be consistent.
    have h_B_ne_univ : B ≠ Set.univ := by
      intro h_eq
      exact h_not (h_eq ▸ Set.mem_univ φ)
    have h_B_cons : Temporal.SetConsistent B := by
      by_contra h_not_cons
      exact h_B_ne_univ (closed_under_derivation_inconsistent_eq_univ h_dcs h_not_cons)
    -- B ⊂ Set.univ (B is a consistent proper subset)
    have h_proper : B ⊂ Set.univ := by
      constructor
      · exact fun _ _ => Set.mem_univ _
      · intro h_eq; exact h_B_ne_univ (Set.eq_univ_iff_forall.mpr (fun x => h_eq (Set.mem_univ x)))
    exact h_R3M.2.2 Set.univ set_univ_closed_under_derivation h_proper h_r3_univ

/-! ## Xu Lemma 2.3: Guard Strengthening via left_mono_until_G -/

/-- Xu Lemma 2.3 (i): If R(A, B, C) then snce(alpha, top) ∈ B for all alpha ∈ A. -/
private theorem xu_lemma_2_3_since_top {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce (Formula.bot.imp Formula.bot) alpha ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- G(snce(alpha, top)) ∈ A: from alpha ∈ A via BX4 + BX12'
  have h_bx4 : DerivationTree FrameClass.Base [] (alpha.imp (alpha.somePast.allFuture)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future alpha) trivial
  have h_G_P_alpha : alpha.somePast.allFuture ∈ A :=
    temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_bx4) h_alpha
  have h_bx12' : DerivationTree FrameClass.Base [] (alpha.somePast.imp (Formula.snce top alpha)) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv alpha) trivial
  have h_G_impl : (alpha.somePast.imp (Formula.snce top alpha)).allFuture ∈ A :=
    theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_bx12')
  have h_temp_k := tempKDistDerived alpha.somePast (Formula.snce top alpha)
  have h_G_snce : (Formula.snce top alpha).allFuture ∈ A :=
    temporal_implication_property h_mcs_A
      (temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_temp_k) h_G_impl)
      h_G_P_alpha
  -- Until condition: ∀ beta ∈ B, ∀ gamma ∈ C, untl(gamma, beta ∧ snce(alpha, top)) ∈ A
  have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
      Formula.untl (Formula.and beta (Formula.snce top alpha)) gamma ∈ A := by
    intro beta h_beta gamma h_gamma
    have hUntl := h_r3.1 beta h_beta gamma h_gamma
    have h_flip := conjIntroCurried beta (Formula.snce top alpha)
    have h_G_flip := theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
    have h_temp_k2 := tempKDistDerived (Formula.snce top alpha) (beta.imp (Formula.and beta (Formula.snce top alpha)))
    have h_G_guard_str : (beta.imp (Formula.and beta (Formula.snce top alpha))).allFuture ∈ A :=
      temporal_implication_property h_mcs_A
        (temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_temp_k2) h_G_flip)
        h_G_snce
    exact untl_left_mono_G h_mcs_A h_G_guard_str hUntl
  -- Since condition: from burgessR_implies_burgessRSince
  have h_since_all : ∀ beta ∈ B, ∀ alpha' ∈ A,
      Formula.snce (Formula.and beta (Formula.snce top alpha)) alpha' ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_burgessR : burgessR A (Formula.and beta (Formula.snce top alpha)) C :=
      fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha' h_alpha'
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 2.3 (ii): If R(A, B, C) then untl(gamma, top) ∈ B for all gamma ∈ C. -/
private theorem xu_lemma_2_3_until_top {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl (Formula.bot.imp Formula.bot) gamma ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- H(untl(gamma, top)) ∈ C: from gamma ∈ C via BX4' + BX12
  have h_bx4' : DerivationTree FrameClass.Base [] (gamma.imp (gamma.someFuture.allPast)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past gamma) trivial
  have h_H_F_gamma : gamma.someFuture.allPast ∈ C :=
    temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_bx4') h_gamma
  have h_bx12 : DerivationTree FrameClass.Base [] (gamma.someFuture.imp (Formula.untl top gamma)) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv gamma) trivial
  have h_H_impl : (gamma.someFuture.imp (Formula.untl top gamma)).allPast ∈ C :=
    theoremInMcs h_mcs_C (pastNecessitation _ h_bx12)
  have h_past_k := pastKDist gamma.someFuture (Formula.untl top gamma)
  have h_H_untl : (Formula.untl top gamma).allPast ∈ C :=
    temporal_implication_property h_mcs_C
      (temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_past_k) h_H_impl)
      h_H_F_gamma
  -- Since condition
  have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
      Formula.snce (Formula.and beta (Formula.untl top gamma)) alpha ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have hSnce := h_r3.2 beta h_beta alpha' h_alpha'
    have h_flip := conjIntroCurried beta (Formula.untl top gamma)
    have h_H_flip := theoremInMcs h_mcs_C (pastNecessitation _ h_flip)
    have h_past_k2 := pastKDist (Formula.untl top gamma) (beta.imp (Formula.and beta (Formula.untl top gamma)))
    have h_H_guard_str : (beta.imp (Formula.and beta (Formula.untl top gamma))).allPast ∈ C :=
      temporal_implication_property h_mcs_C
        (temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_past_k2) h_H_flip)
        h_H_untl
    exact snce_left_mono_H h_mcs_C h_H_guard_str hSnce
  -- Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta ∈ B, ∀ gamma' ∈ C,
      Formula.untl (Formula.and beta (Formula.untl top gamma)) gamma' ∈ A := by
    intro beta h_beta gamma' h_gamma'
    have h_burgessRSince : burgessRSince C (Formula.and beta (Formula.untl top gamma)) A :=
      fun alpha h_alpha => h_since_all beta h_beta alpha h_alpha
    exact burgessRSince_implies_burgessR h_mcs_A h_mcs_C h_burgessRSince gamma' h_gamma'
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Derivation-Level Monotonicity -/

/-- Derivation-level left_mono for Until. -/
noncomputable def untlLeftMonoDeriv (φ ψ χ : Formula Atom)
    (hImpl : DerivationTree FrameClass.Base [] (φ.imp χ)) :
    DerivationTree FrameClass.Base [] ((Formula.untl φ ψ).imp (Formula.untl χ ψ)) := by
  have h_G := DerivationTree.temporal_necessitation _ hImpl
  have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.left_mono_until_G φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_G

/-- Derivation-level left_mono for Since. -/
noncomputable def snceLeftMonoDeriv (φ ψ χ : Formula Atom)
    (hImpl : DerivationTree FrameClass.Base [] (φ.imp χ)) :
    DerivationTree FrameClass.Base [] ((Formula.snce φ ψ).imp (Formula.snce χ ψ)) := by
  have h_H := pastNecessitation _ hImpl
  have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.left_mono_since_H φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_H

/-- Right monotonicity for Until at MCS level. -/
private theorem right_mono_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {φ ψ χ : Formula Atom}
    (hImpl : DerivationTree FrameClass.Base [] (ψ.imp χ))
    (hUntl : (φ U ψ) ∈ A) :
    (φ U χ) ∈ A := by
  have h_G_impl : Formula.allFuture (ψ.imp χ) ∈ A :=
    theoremInMcs h_mcs (DerivationTree.temporal_necessitation _ hImpl)
  have h_bx3 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until ψ χ φ) trivial
  exact temporal_implication_property h_mcs
    (temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx3) h_G_impl) hUntl

/-- Right monotonicity for Since at MCS level. -/
private theorem right_mono_since_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {φ ψ χ : Formula Atom}
    (hImpl : DerivationTree FrameClass.Base [] (ψ.imp χ))
    (hSnce : (φ S ψ) ∈ C) :
    (φ S χ) ∈ C := by
  have h_H_impl : Formula.allPast (ψ.imp χ) ∈ C :=
    theoremInMcs h_mcs (pastNecessitation _ hImpl)
  have h_bx3' := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since ψ χ φ) trivial
  exact temporal_implication_property h_mcs
    (temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx3') h_H_impl) hSnce

/-! ## BX13/BX13' at MCS Level -/

/-- BX13 (enrichment_until) at MCS level. -/
theorem enrichment_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {phi psi p : Formula Atom}
    (h_p : p ∈ A)
    (hUntl : (phi U psi) ∈ A) :
    Formula.untl phi (Formula.and psi (Formula.snce phi p)) ∈ A := by
  have h_conj := conj_mcs h_mcs p (Formula.untl phi psi) h_p hUntl
  have h_bx13 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_until phi psi p) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx13) h_conj

/-- BX13' (enrichment_since) at MCS level. -/
theorem enrichment_since_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {phi psi p : Formula Atom}
    (h_p : p ∈ C)
    (hSnce : (phi S psi) ∈ C) :
    Formula.snce phi (Formula.and psi (Formula.untl phi p)) ∈ C := by
  have h_conj := conj_mcs h_mcs p (Formula.snce phi psi) h_p hSnce
  have h_bx13 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_since phi psi p) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx13) h_conj

/-! ## F/P Monotonicity -/

/-- F-monotonicity at MCS level. -/
private theorem F_mono_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {phi psi : Formula Atom}
    (hImpl : DerivationTree FrameClass.Base [] (phi.imp psi))
    (h_F : (𝐅phi) ∈ A) :
    (𝐅psi) ∈ A := by
  -- F(phi) = untl phi top. G(phi → psi) → F(phi) → F(psi) via right_mono_until.
  exact right_mono_until_mcs h_mcs hImpl h_F

/-- P-monotonicity at MCS level. -/
private theorem P_mono_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {phi psi : Formula Atom}
    (hImpl : DerivationTree FrameClass.Base [] (phi.imp psi))
    (h_P : (𝐏phi) ∈ C) :
    (𝐏psi) ∈ C := by
  exact right_mono_since_mcs h_mcs hImpl h_P

/-! ## Xu Lemma 3.2.1: Full Guard Strengthening -/

/-- Xu Lemma 3.2.1 (i): If R(A, B, C) then untl(gamma, beta) ∈ B for all beta ∈ B, gamma ∈ C. -/
theorem xu_lemma_3_2_1_until {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    (beta U gamma) ∈ B := by
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  have h_until_all : ∀ beta' ∈ B, ∀ gamma' ∈ C,
      Formula.untl (Formula.and beta' (Formula.untl beta gamma)) gamma' ∈ A := by
    intro beta' h_beta' gamma' h_gamma'
    -- From burgessR3: untl(gamma'', beta'') ∈ A where gamma'' = gamma ∧ gamma', beta'' = beta ∧ beta'
    have h_beta'' : Formula.and beta beta' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
    have h_gamma'' : Formula.and gamma gamma' ∈ C := conj_mcs h_mcs_C gamma gamma' h_gamma h_gamma'
    have hUntl := h_r3.1 (Formula.and beta beta') h_beta'' (Formula.and gamma gamma') h_gamma''
    -- hUntl : untl(γ∧γ', β∧β') ∈ A, i.e., (β∧β') guards until (γ∧γ') happens
    -- BX5: self_accum takes (guard, event): untl(event, guard) → untl(event, guard ∧ untl(event, guard))
    have h_sa := self_accum_until_mcs h_mcs_A (Formula.and beta beta') (Formula.and gamma gamma') hUntl
    have h_guard_r : DerivationTree FrameClass.Base [] (((Formula.and beta beta').and (Formula.untl (Formula.and beta beta') (Formula.and gamma gamma'))).imp
        (Formula.and beta' (Formula.untl beta gamma))) := by
      have h_event_proj := lceImp gamma gamma'  -- ⊢ γ∧γ' → γ
      have h_guard_proj := lceImp beta beta'    -- ⊢ β∧β' → β
      -- ⊢ untl(γ∧γ', β∧β') → untl(γ, β∧β') via right_mono (event)
      have h1 : DerivationTree FrameClass.Base [] ((Formula.untl (Formula.and beta beta') (Formula.and gamma gamma')).imp
          (Formula.untl (Formula.and beta beta') gamma)) := by
        have h_G := DerivationTree.temporal_necessitation _ h_event_proj
        have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until (Formula.and gamma gamma') gamma (Formula.and beta beta')) trivial
        exact DerivationTree.modus_ponens [] _ _ h_ax h_G
      -- ⊢ untl(γ, β∧β') → untl(γ, β) via left_mono (guard)
      have h2 : DerivationTree FrameClass.Base [] ((Formula.untl (Formula.and beta beta') gamma).imp
          (Formula.untl beta gamma)) :=
        untlLeftMonoDeriv (Formula.and beta beta') gamma beta h_guard_proj
      -- ⊢ untl(γ∧γ', β∧β') → untl(γ, β)
      have h_untl_proj := impTrans h1 h2
      -- Now build the pairing: ⊢ x∧y → β' ∧ untl(γ, β)
      -- ⊢ x∧y → β' from ⊢ x → β' via x = β∧β' → β' and ⊢ x∧y → x
      have h_left := impTrans (lceImp (Formula.and beta beta') (Formula.untl (Formula.and beta beta') (Formula.and gamma gamma')))
        (rceImp beta beta')
      -- ⊢ x∧y → untl(γ,β) from ⊢ y → untl(γ,β) and ⊢ x∧y → y
      have h_right := impTrans (rceImp (Formula.and beta beta') (Formula.untl (Formula.and beta beta') (Formula.and gamma gamma')))
        h_untl_proj
      -- Combine: ⊢ x∧y → β' ∧ untl(γ, β) using pairing
      -- Need: from ⊢ A → B and ⊢ A → C, derive ⊢ A → B ∧ C
      -- Build in context [A]: B and C, then apply pairing
      have := DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.untl (Formula.and beta beta') (Formula.and gamma gamma')))] _ _
        (DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.untl (Formula.and beta beta') (Formula.and gamma gamma')))] _ _
          (DerivationTree.weakening [] [_] _ (pairing beta' (Formula.untl beta gamma)) (List.nil_subset _))
          (DerivationTree.modus_ponens [_] _ _
            (DerivationTree.weakening [] [_] _ h_left (List.nil_subset _))
            (DerivationTree.assumption _ _ (by simp))))
        (DerivationTree.modus_ponens [_] _ _
          (DerivationTree.weakening [] [_] _ h_right (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp)))
      exact deductionTheorem [] _ _ this
    -- Apply left_mono: G(guard_str) → untl(γ∧γ', (β∧β') ∧ untl(γ∧γ', β∧β')) → untl(γ∧γ', β' ∧ untl(γ, β))
    have h_step1 := untl_left_mono_thm h_mcs_A h_guard_r h_sa
    -- Now ⊢ γ∧γ' → γ' to go from untl(γ∧γ', ...) to untl(γ', ...)
    have h_event_proj_r := rceImp gamma gamma'
    exact right_mono_until_mcs h_mcs_A h_event_proj_r h_step1
  -- Since condition from burgessR_implies_burgessRSince
  have h_since_all : ∀ beta' ∈ B, ∀ alpha ∈ A,
      Formula.snce (Formula.and beta' (Formula.untl beta gamma)) alpha ∈ C := by
    intro beta' h_beta' alpha h_alpha
    have h_burgessR : burgessR A (Formula.and beta' (Formula.untl beta gamma)) C :=
      fun gamma' h_gamma' => h_until_all beta' h_beta' gamma' h_gamma'
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha h_alpha
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 3.2.1 (ii): If R(A, B, C) then snce(alpha, beta) ∈ B for all beta ∈ B, alpha ∈ A. -/
theorem xu_lemma_3_2_1_since {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    (beta S alpha) ∈ B := by
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- Since condition (dual of xu_lemma_3_2_1_until)
  have h_since_all : ∀ beta' ∈ B, ∀ alpha' ∈ A,
      Formula.snce (Formula.and beta' (Formula.snce beta alpha)) alpha' ∈ C := by
    intro beta' h_beta' alpha' h_alpha'
    have h_beta'' : Formula.and beta beta' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
    have h_alpha'' : Formula.and alpha alpha' ∈ A := conj_mcs h_mcs_A alpha alpha' h_alpha h_alpha'
    have hSnce := h_r3.2 (Formula.and beta beta') h_beta'' (Formula.and alpha alpha') h_alpha''
    -- hSnce : snce(α∧α', β∧β') ∈ C. self_accum_since takes (guard, event)
    have h_sa := self_accum_since_mcs h_mcs_C (Formula.and beta beta') (Formula.and alpha alpha') hSnce
    -- Monotonicity to get snce(α', β' ∧ snce(α, β)) from snce(α∧α', (β∧β') ∧ snce(α∧α', β∧β'))
    have h_guard_r : DerivationTree FrameClass.Base [] (((Formula.and beta beta').and (Formula.snce (Formula.and beta beta') (Formula.and alpha alpha'))).imp
        (Formula.and beta' (Formula.snce beta alpha))) := by
      have h_event_proj := lceImp alpha alpha'
      have h_guard_proj := lceImp beta beta'
      have h1 : DerivationTree FrameClass.Base [] ((Formula.snce (Formula.and beta beta') (Formula.and alpha alpha')).imp
          (Formula.snce (Formula.and beta beta') alpha)) := by
        have h_H := pastNecessitation _ h_event_proj
        have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since (Formula.and alpha alpha') alpha (Formula.and beta beta')) trivial
        exact DerivationTree.modus_ponens [] _ _ h_ax h_H
      have h2 : DerivationTree FrameClass.Base [] ((Formula.snce (Formula.and beta beta') alpha).imp
          (Formula.snce beta alpha)) :=
        snceLeftMonoDeriv (Formula.and beta beta') alpha beta h_guard_proj
      have h_snce_proj := impTrans h1 h2
      have h_left := impTrans (lceImp (Formula.and beta beta') (Formula.snce (Formula.and beta beta') (Formula.and alpha alpha')))
        (rceImp beta beta')
      have h_right := impTrans (rceImp (Formula.and beta beta') (Formula.snce (Formula.and beta beta') (Formula.and alpha alpha')))
        h_snce_proj
      have := DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.snce (Formula.and beta beta') (Formula.and alpha alpha')))] _ _
        (DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.snce (Formula.and beta beta') (Formula.and alpha alpha')))] _ _
          (DerivationTree.weakening [] [_] _ (pairing beta' (Formula.snce beta alpha)) (List.nil_subset _))
          (DerivationTree.modus_ponens [_] _ _
            (DerivationTree.weakening [] [_] _ h_left (List.nil_subset _))
            (DerivationTree.assumption _ _ (by simp))))
        (DerivationTree.modus_ponens [_] _ _
          (DerivationTree.weakening [] [_] _ h_right (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp)))
      exact deductionTheorem [] _ _ this
    have h_step1 := snce_left_mono_thm h_mcs_C h_guard_r h_sa
    have h_event_proj_r := rceImp alpha alpha'
    exact right_mono_since_mcs h_mcs_C h_event_proj_r h_step1
  -- Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta' ∈ B, ∀ gamma ∈ C,
      Formula.untl (Formula.and beta' (Formula.snce beta alpha)) gamma ∈ A := by
    intro beta' h_beta' gamma h_gamma
    have h_burgessRSince : burgessRSince C (Formula.and beta' (Formula.snce beta alpha)) A :=
      fun alpha' h_alpha' => h_since_all beta' h_beta' alpha' h_alpha'
    exact burgessRSince_implies_burgessR h_mcs_A h_mcs_C h_burgessRSince gamma h_gamma
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Duality: hContent ↔ gContent -/

/-- hContent(B) ⊆ A implies gContent(A) ⊆ B for MCS A, B. -/
theorem h_content_sub_imp_g_content_sub' {A B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_B : Temporal.SetMaximalConsistent B)
    (h_hBA : hContent B ⊆ A) :
    gContent A ⊆ B := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : (¬ψ) ∈ B := mcs_neg_of_not_mem h_mcs_B h_not
  have h_ax : DerivationTree FrameClass.Base [] (ψ.neg.imp (ψ.neg.someFuture.allPast)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past ψ.neg) trivial
  have h_HF : Formula.allPast (Formula.someFuture ψ.neg) ∈ B :=
    temporal_implication_property h_mcs_B (theoremInMcs h_mcs_B h_ax) h_neg_ψ
  have h_F_neg_ψ_A : (𝐅(¬ψ)) ∈ A := h_hBA h_HF
  have h_G_nn : Formula.allFuture ψ.neg.neg ∈ A := by
    have h_dni_ax := dni ψ
    have h_G_dni := theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_dni_ax)
    have h_kd := tempKDistDerived ψ ψ.neg.neg
    have h1 := temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_kd) h_G_dni
    exact temporal_implication_property h_mcs_A h1 hψ
  exact someFuture_allFuture_neg_absurd h_mcs_A ψ.neg h_F_neg_ψ_A h_G_nn

/-- gContent(A) ⊆ B implies hContent(B) ⊆ A for MCS A, B. -/
theorem g_content_sub_imp_h_content_sub' {A B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_B : Temporal.SetMaximalConsistent B)
    (h_gAB : gContent A ⊆ B) :
    hContent B ⊆ A := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : (¬ψ) ∈ A := mcs_neg_of_not_mem h_mcs_A h_not
  have h_GP : Formula.allFuture (Formula.somePast ψ.neg) ∈ A :=
    connect_future_mcs' h_mcs_A ψ.neg h_neg_ψ
  have h_P_neg_ψ_B : (𝐏(¬ψ)) ∈ B := h_gAB h_GP
  have h_H_nn : Formula.allPast ψ.neg.neg ∈ B := by
    have h_dni_ax := dni ψ
    have h_H_dni := theoremInMcs h_mcs_B (pastNecessitation _ h_dni_ax)
    have h_kd := pastKDist ψ ψ.neg.neg
    have h1 := temporal_implication_property h_mcs_B (theoremInMcs h_mcs_B h_kd) h_H_dni
    exact temporal_implication_property h_mcs_B h1 hψ
  exact somePast_allPast_neg_absurd h_mcs_B ψ.neg h_P_neg_ψ_B h_H_nn

/-! ## Lemma 2.6 Splitting: BurgessR3Maximal Interval Insertion -/

/-- **Lemma 2.6 Splitting**: Given BurgessR3Maximal(A, B, C) with β ∉ B,
construct MCS D with (¬β) ∈ D and decomposed BurgessR3Maximal relations. -/
theorem lemma_2_6_splitting {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (β : Formula Atom)
    (h_β_not_B : β ∉ B) :
    ∃ B' D B'', BurgessR3Maximal A B' D ∧ BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧ (¬β) ∈ D ∧ B ⊆ D ∧ B ⊆ B' ∧ B ⊆ B'' := by
  have h_B_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Step 1: Trivial seed {β.neg} ∪ B is consistent
  have h_sdc : SetDeductivelyClosed B := cud_not_mem_is_sdc h_B_dcs h_β_not_B
  have h_seed_cons : Temporal.SetConsistent ({β.neg} ∪ B) := dcs_neg_insert_consistent h_B_dcs h_β_not_B
  -- Step 2: Lindenbaum-extend to MCS D
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  -- Step 3: Extract seed memberships
  have h_β_neg_D : (¬β) ∈ D := h_sup (Set.mem_union_left _ (Set.mem_singleton β.neg))
  have h_B_sub_D : B ⊆ D := fun φ hφ => h_sup (Set.mem_union_right _ hφ)
  -- Step 4: Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β' ∈ B, ∀ γ ∈ C, Formula.untl β' γ ∈ D := by
    intro β' hβ' γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until h_mcs_A h_mcs_C h_r3m hβ' hγ)
  have h_snce_D : ∀ β' ∈ B, ∀ α ∈ A, Formula.snce β' α ∈ D := by
    intro β' hβ' α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since h_mcs_A h_mcs_C h_r3m hβ' hα)
  -- Step 5: Establish burgessR3(D, B, C)
  have h_rSet_D : burgessRSet D B C := fun β' hβ' γ hγ => h_untl_D β' hβ' γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β' hβ'
    exact burgessR_implies_burgessRSince h_D_mcs h_mcs_C (h_rSet_D β' hβ')
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 6: Establish burgessR3(A, B, D)
  have h_rSetSince_A : burgessRSetSince D B A := fun β' hβ' α hα => h_snce_D β' hβ' α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β' hβ'
    exact burgessRSince_implies_burgessR h_mcs_A h_D_mcs (h_rSetSince_A β' hβ')
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 7: BurgessR3Maximal via Zorn
  obtain ⟨B', h_B_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_B_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_β_neg_D, h_B_sub_D, h_B_sub_B', h_B_sub_B''⟩

/-! ## Propositional Helpers for Burgess Compression -/

/-- Identity derivation: ⊢ φ → φ. -/
noncomputable def identity' (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp φ) := by
  have h1 : DerivationTree FrameClass.Base [φ] φ := DerivationTree.assumption [φ] φ (by simp)
  exact deductionTheorem [] φ φ h1

/-- From ⊢ R → A and ⊢ R → B, derive ⊢ R → A ∧ B. -/
noncomputable def combineImpConj {R A B : Formula Atom}
    (h1 : DerivationTree FrameClass.Base [] (R.imp A))
    (h2 : DerivationTree FrameClass.Base [] (R.imp B)) :
    DerivationTree FrameClass.Base [] (R.imp (Formula.and A B)) := by
  have d1 : DerivationTree FrameClass.Base [R] A :=
    DerivationTree.modus_ponens [R] R A
      (DerivationTree.weakening [] [R] _ h1 (List.nil_subset _))
      (DerivationTree.assumption _ R (by simp))
  have d2 : DerivationTree FrameClass.Base [R] B :=
    DerivationTree.modus_ponens [R] R B
      (DerivationTree.weakening [] [R] _ h2 (List.nil_subset _))
      (DerivationTree.assumption _ R (by simp))
  have d3 : DerivationTree FrameClass.Base [R] (Formula.and A B) :=
    DerivationTree.modus_ponens [R] B (Formula.and A B)
      (DerivationTree.modus_ponens [R] A (B.imp (Formula.and A B))
        (DerivationTree.weakening [] [R] _ (pairing A B) (List.nil_subset _)) d1) d2
  exact deductionTheorem [] R (Formula.and A B) d3

/-- De Morgan for disjunction negation: ⊢ ¬(A ∨ B) → ¬A ∧ ¬B.
    Recall A.or B = A.neg.imp B. -/
noncomputable def demorganDisjNegForward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).neg.imp (Formula.and A.neg B.neg)) := by
  set neg_disj := (A.or B).neg -- = (A.neg.imp B).neg = (A.neg.imp B) → ⊥
  -- Step 1: derive ¬A from neg_disj
  -- ⊢ A → (¬A → B): this is exFalsoFromAssumption A B
  have h_A_to_disj : DerivationTree FrameClass.Base [] (A.imp (A.neg.imp B)) :=
    exFalsoFromAssumption A B
  -- In context [neg_disj, A]: derive ⊥
  have d_negA : DerivationTree FrameClass.Base [neg_disj] A.neg := by
    have d1 : DerivationTree FrameClass.Base [A, neg_disj] (A.neg.imp B) :=
      DerivationTree.modus_ponens [A, neg_disj] A (A.neg.imp B)
        (DerivationTree.weakening [] [A, neg_disj] _ h_A_to_disj (List.nil_subset _))
        (DerivationTree.assumption _ A (by simp))
    have d2 : DerivationTree FrameClass.Base [A, neg_disj] Formula.bot :=
      DerivationTree.modus_ponens [A, neg_disj] (A.neg.imp B) Formula.bot
        (DerivationTree.assumption _ neg_disj (by simp)) d1
    exact deductionTheorem [neg_disj] A Formula.bot d2
  -- Step 2: derive ¬B from neg_disj
  -- ⊢ B → (¬A → B) via weakening: ⊢ B → ¬A → B is Axiom.imp_s
  have h_B_to_disj : DerivationTree FrameClass.Base [] (B.imp (A.neg.imp B)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s B A.neg) trivial
  have d_negB : DerivationTree FrameClass.Base [neg_disj] B.neg := by
    have d1 : DerivationTree FrameClass.Base [B, neg_disj] (A.neg.imp B) :=
      DerivationTree.modus_ponens [B, neg_disj] B (A.neg.imp B)
        (DerivationTree.weakening [] [B, neg_disj] _ h_B_to_disj (List.nil_subset _))
        (DerivationTree.assumption _ B (by simp))
    have d2 : DerivationTree FrameClass.Base [B, neg_disj] Formula.bot :=
      DerivationTree.modus_ponens [B, neg_disj] (A.neg.imp B) Formula.bot
        (DerivationTree.assumption _ neg_disj (by simp)) d1
    exact deductionTheorem [neg_disj] B Formula.bot d2
  -- Step 3: pair ¬A and ¬B
  have d_conj : DerivationTree FrameClass.Base [neg_disj] (Formula.and A.neg B.neg) :=
    DerivationTree.modus_ponens [neg_disj] B.neg (Formula.and A.neg B.neg)
      (DerivationTree.modus_ponens [neg_disj] A.neg (B.neg.imp (Formula.and A.neg B.neg))
        (DerivationTree.weakening [] [neg_disj] _ (pairing A.neg B.neg) (List.nil_subset _))
        d_negA)
      d_negB
  exact deductionTheorem [] neg_disj (Formula.and A.neg B.neg) d_conj

/-! ## List-Level Cut and Conjunction Helpers -/

/-- List-level cut (derivation from implied context):
If Γ ⊢ φ for each φ ∈ L, and L ⊢ ψ, then Γ ⊢ ψ. -/
noncomputable def derivationFromImplied (Γ : Context Atom) :
    (L : Context Atom) → (ψ : Formula Atom) →
    (∀ φ ∈ L, DerivationTree FrameClass.Base Γ φ) →
    DerivationTree FrameClass.Base L ψ →
    DerivationTree FrameClass.Base Γ ψ
  | [], ψ, _, d => DerivationTree.weakening [] Γ ψ d (List.nil_subset Γ)
  | l :: L', ψ, h_derives, d => by
    have d_impl : DerivationTree FrameClass.Base L' (l.imp ψ) := deductionTheorem L' l ψ d
    have h_derives' : ∀ φ ∈ L', DerivationTree FrameClass.Base Γ φ := fun φ hφ =>
      h_derives φ (List.mem_cons.mpr (Or.inr hφ))
    have d_impl_Γ : DerivationTree FrameClass.Base Γ (l.imp ψ) :=
      derivationFromImplied Γ L' (l.imp ψ) h_derives' d_impl
    have d_l : DerivationTree FrameClass.Base Γ l := h_derives l (List.mem_cons.mpr (Or.inl rfl))
    exact DerivationTree.modus_ponens Γ l ψ d_impl_Γ d_l

/-- Conjunction of a list of formulas. Empty list gives ⊤ (= ⊥→⊥). -/
noncomputable def listConj : List (Formula Atom) → Formula Atom
  | [] => Formula.bot.imp Formula.bot  -- top
  | [φ] => φ
  | (φ :: rest) => Formula.and φ (listConj rest)

/-- ⊢ listConj L → φ for each φ ∈ L. -/
noncomputable def listConjImpliesElem :
    (L : List (Formula Atom)) → (φ : Formula Atom) → (h : φ ∈ L) →
    DerivationTree FrameClass.Base [] ((listConj L).imp φ)
  | [ψ], φ, h => by
    simp [List.mem_singleton] at h
    subst h; simp [listConj]; exact identity' φ
  | (ψ₁ :: ψ₂ :: rest), φ, h => by
    simp [listConj]
    by_cases h_eq : φ = ψ₁
    · subst h_eq; exact lceImp φ (listConj (ψ₂ :: rest))
    · have h' : φ ∈ ψ₂ :: rest := by
        rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl h_eq
        · exact h'
      have h_right : DerivationTree FrameClass.Base [] _ := rceImp ψ₁ (listConj (ψ₂ :: rest))
      have h_rec := listConjImpliesElem (ψ₂ :: rest) φ h'
      exact impTrans h_right h_rec

/-- If B is CUD and all elements of L are in B, then listConj L ∈ B. -/
theorem list_conj_mem_dcs {B : Set (Formula Atom)} (h_dcs : ClosedUnderDerivation B) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ B) → listConj L ∈ B
  | [], _ => cud_contains_theorems h_dcs (identity' (Formula.bot : Formula Atom))
  | [φ], h => by simp [listConj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [listConj]
    have h1 : φ₁ ∈ B := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : listConj (φ₂ :: rest) ∈ B :=
      list_conj_mem_dcs h_dcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact cud_conj_closed h_dcs h1 h2

/-- If A is MCS and all elements of L are in A, then listConj L ∈ A. -/
theorem list_conj_mem_mcs {A : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent A) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ A) → listConj L ∈ A
  | [], _ => theoremInMcs h_mcs (identity' (Formula.bot : Formula Atom))
  | [φ], h => by simp [listConj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [listConj]
    have h1 : φ₁ ∈ A := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : listConj (φ₂ :: rest) ∈ A :=
      list_conj_mem_mcs h_mcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact conj_mcs h_mcs φ₁ (listConj (φ₂ :: rest)) h1 h2

/-- If F(φ) ∈ A (MCS), then {φ} is consistent. -/
theorem consistent_of_F_mem {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    (φ : Formula Atom) (h_F : (𝐅φ) ∈ A) :
    Temporal.SetConsistent ({φ} : Set (Formula Atom)) := by
  have h_seed := forward_temporal_witness_seed_consistent A h_mcs φ h_F
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

/-- If P(φ) ∈ C (MCS), then {φ} is consistent. -/
theorem consistent_of_P_mem {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C)
    (φ : Formula Atom) (h_P : (𝐏φ) ∈ C) :
    Temporal.SetConsistent ({φ} : Set (Formula Atom)) := by
  have h_seed := past_temporal_witness_seed_consistent C h_mcs φ h_P
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

/-- If {φ} is consistent and [φ] ⊢ ⊥, then False. -/
theorem inconsistent_singleton_false {φ : Formula Atom}
    (h_cons : Temporal.SetConsistent ({φ} : Set (Formula Atom)))
    (d : DerivationTree FrameClass.Base [φ] Formula.bot) : False :=
  h_cons [φ] (fun ψ hψ => by simp [List.mem_singleton] at hψ; subst hψ; exact Set.mem_singleton _) ⟨d⟩

/-! ## Guard Conjunction Helpers -/

/-- Guard conjunction for Until: If untl(β₁, γ) ∈ A and untl(β₂, γ) ∈ A (MCS A),
then untl(β₁∧β₂, γ) ∈ A. Uses BX7 + BX3. -/
private theorem untl_conj_guard {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : (β₁ U γ) ∈ A)
    (h2 : (β₂ U γ) ∈ A) :
    Formula.untl (Formula.and β₁ β₂) γ ∈ A := by
  have h_conj : Formula.and (Formula.untl β₁ γ) (Formula.untl β₂ γ) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7 := theoremInMcs h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_until β₁ γ β₂ γ) trivial)
  have h_disj := temporal_implication_property h_mcs h_bx7 h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.untl guard (Formula.and γ γ)
  set D2 := Formula.untl guard (Formula.and γ β₂)
  set D3 := Formula.untl guard (Formula.and β₁ γ)
  set target := Formula.untl guard γ
  have mk_thm : ∀ e : Formula Atom, DerivationTree FrameClass.Base [] (e.imp γ) →
      DerivationTree FrameClass.Base [] ((Formula.untl guard e).imp target) := by
    intro e h_e_imp
    have h_G := DerivationTree.temporal_necessitation _ h_e_imp
    have h_bx3 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3 h_G
  have h_D1_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ γ))
  have h_D2_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ β₂))
  have h_D3_impl := theoremInMcs h_mcs (mk_thm _ (rceImp β₁ γ))
  rcases temporal_negation_complete h_mcs D3 with h | h
  · exact temporal_implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases temporal_negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := temporal_implication_property h_mcs h_disj h'
        exact absurd this (mcs_not_mem_of_neg h_mcs h)
    rcases temporal_negation_complete h_mcs D1 with h' | h'
    · exact temporal_implication_property h_mcs h_D1_impl h'
    · have h_D2 := temporal_implication_property h_mcs h_D1_or_D2 h'
      exact temporal_implication_property h_mcs h_D2_impl h_D2

/-- Guard conjunction for Since: If snce(β₁, γ) ∈ A and snce(β₂, γ) ∈ A (MCS A),
then snce(β₁∧β₂, γ) ∈ A. Uses BX7' + BX3'. -/
private theorem snce_conj_guard {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : (β₁ S γ) ∈ A)
    (h2 : (β₂ S γ) ∈ A) :
    Formula.snce (Formula.and β₁ β₂) γ ∈ A := by
  have h_conj : Formula.and (Formula.snce β₁ γ) (Formula.snce β₂ γ) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7' := theoremInMcs h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_since β₁ γ β₂ γ) trivial)
  have h_disj := temporal_implication_property h_mcs h_bx7' h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.snce guard (Formula.and γ γ)
  set D2 := Formula.snce guard (Formula.and γ β₂)
  set D3 := Formula.snce guard (Formula.and β₁ γ)
  set target := Formula.snce guard γ
  have mk_thm : ∀ e : Formula Atom, DerivationTree FrameClass.Base [] (e.imp γ) →
      DerivationTree FrameClass.Base [] ((Formula.snce guard e).imp target) := by
    intro e h_e_imp
    have h_H := pastNecessitation _ h_e_imp
    have h_bx3' := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3' h_H
  have h_D1_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ γ))
  have h_D2_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ β₂))
  have h_D3_impl := theoremInMcs h_mcs (mk_thm _ (rceImp β₁ γ))
  rcases temporal_negation_complete h_mcs D3 with h | h
  · exact temporal_implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases temporal_negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := temporal_implication_property h_mcs h_disj h'
        exact absurd this (mcs_not_mem_of_neg h_mcs h)
    rcases temporal_negation_complete h_mcs D1 with h' | h'
    · exact temporal_implication_property h_mcs h_D1_impl h'
    · have h_D2 := temporal_implication_property h_mcs h_D1_or_D2 h'
      exact temporal_implication_property h_mcs h_D2_impl h_D2

/-- Set-level guard conjunction for burgessR. -/
theorem burgessR_conj {A C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {α β : Formula Atom}
    (hα : burgessR A α C) (hβ : burgessR A β C) :
    burgessR A (Formula.and α β) C := by
  intro γ hγ
  exact untl_conj_guard h_mcs (hα γ hγ) (hβ γ hγ)

/-- Set-level guard conjunction for burgessRSince. -/
theorem burgessRSince_conj {A C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C)
    {α β : Formula Atom}
    (hα : burgessRSince C α A) (hβ : burgessRSince C β A) :
    burgessRSince C (Formula.and α β) A := by
  intro γ hγ
  exact snce_conj_guard h_mcs (hα γ hγ) (hβ γ hγ)


end Cslib.Logic.Temporal.Metalogic.Chronicle
