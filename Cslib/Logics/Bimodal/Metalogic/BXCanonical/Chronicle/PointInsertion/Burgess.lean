/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion.Seeds

/-! # Burgess — Lemma 2.6, Xu Lemma 2.3, and Splitting Helpers

Burgess Lemma 2.6 content-based approach, Xu Lemma 2.3 (top-guard versions),
gContent/hContent subset relationships, duality, Lemma 2.6 interval insertion,
Lemma 2.7 helpers (list-conjunction utilities, iterated enrichment structures), and
associated seed-consistency results.

## Main Results

- `lemma_2_6_splitting`: Burgess Lemma 2.6 interval insertion
- `EnrichedEvent`, `EnrichedEventSince`: Iterated enrichment result structures
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.TemporalDerived

/-! ## Burgess Lemma 2.6 for BurgessR3Maximal (Content-Based)

The content-based BurgessR3Maximal is ANTI-monotone in B (adding elements to B
adds more requirements on A and C), so B is a genuinely non-MCS DCS in general.
The maximality witness lemma proves that if delta not in B, then some extension
of B by delta violates burgessR3, which is the key to the splitting construction.
-/

/--
Helper: If L is a subset of {delta} union B with B a DCS, and L derives phi, then either
phi is in B, or there exists beta in B with a theorem (beta AND delta) implies phi.
-/
theorem dc_delta_B_controlled (fc : FrameClass) {B : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B)
    {delta phi : Formula Atom} {L : List (Formula Atom)}
    (hL_sub : ∀ psi ∈ L, psi ∈ ({delta} : Set (Formula Atom)) ∪ B)
    (hL_deriv : DerivationTree fc L phi) :
    (phi ∈ B) ∨
      (∃ beta ∈ B, Nonempty (DerivationTree fc [] ((Formula.and beta delta).imp phi))) := by
  haveI : ∀ x : Formula Atom, Decidable (x ∈ B) := fun x => Classical.propDecidable _
  by_cases h_delta_L : delta ∈ L
  · let L_B := L.filter (· ∈ B)
    have hL_sub_dB : L ⊆ delta :: L_B := by
      intro psi hpsi
      by_cases h_B : psi ∈ B
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpsi, decide_eq_true_eq.mpr h_B⟩)
      · rcases hL_sub psi hpsi with h | h
        · rw [Set.mem_singleton_iff.mp h]; exact .head _
        · exact absurd h h_B
    have d_w : DerivationTree fc (delta :: L_B) phi :=
      DerivationTree.weakening L (delta :: L_B) phi hL_deriv hL_sub_dB
    have d_imp := deductionTheorem L_B delta phi d_w
    have hLB_sub : ∀ psi ∈ L_B, psi ∈ B := by
      intro psi hpsi; exact decide_eq_true_eq.mp (List.mem_filter.mp hpsi).2
    by_cases hLB_empty : L_B = []
    · rw [hLB_empty] at d_imp
      have h_top_B : (Formula.bot.imp Formula.bot) ∈ B :=
        cud_contains_theorems h_dcs
          (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
      exact Or.inr ⟨Formula.bot.imp Formula.bot, h_top_B,
        ⟨Cslib.Logic.Bimodal.Theorems.Combinators.impTrans
          (Cslib.Logic.Bimodal.Theorems.Propositional.rceImp (Formula.bot.imp Formula.bot) delta)
          d_imp⟩⟩
    · have h_imp_B : delta.imp phi ∈ B := h_dcs L_B _ hLB_sub d_imp
      right
      refine ⟨delta.imp phi, h_imp_B, ⟨?_⟩⟩
      have h_l : DerivationTree fc [(Formula.and (delta.imp phi) delta)] (delta.imp phi) :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) (delta.imp phi)
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (Cslib.Logic.Bimodal.Theorems.Propositional.lceImp (delta.imp phi) delta)
            (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_r : DerivationTree fc [(Formula.and (delta.imp phi) delta)] delta :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) delta
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (Cslib.Logic.Bimodal.Theorems.Propositional.rceImp (delta.imp phi) delta)
            (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_mp : DerivationTree fc [(Formula.and (delta.imp phi) delta)] phi :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)] delta phi h_l h_r
      exact deductionTheorem [] (Formula.and (delta.imp phi) delta) phi h_mp
  · left
    have hL_B : ∀ psi ∈ L, psi ∈ B := by
      intro psi hpsi
      rcases hL_sub psi hpsi with h | h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hpsi) h_delta_L
      · exact h
    exact h_dcs L phi hL_B hL_deriv

/-- If BurgessR3Maximal(A, B, C) and delta ∉ B, the deductive closure of
{delta} ∪ B does NOT satisfy burgessR3(A, -, C).

No consistency requirement: the maximality clause in BurgessR3Maximal
quantifies over `ClosedUnderDerivation` sets, which includes
`deductiveClosure ({delta} ∪ B)` regardless of consistency. -/
theorem BurgessR3Maximal_extension_fails (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3M : BurgessR3Maximal fc A B C)
    {delta : Formula Atom} (h_delta_not : delta ∉ B) :
    ¬burgessR3 A (deductiveClosure fc ({delta} ∪ B)) C := by
  intro h_r3
  have h_cud : ClosedUnderDerivation fc (deductiveClosure fc ({delta} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  have h_sub : B ⊆ deductiveClosure fc ({delta} ∪ B) :=
    fun phi hphi => subset_deductiveClosure fc ({delta} ∪ B) (Set.mem_union_right _ hphi)
  have h_delta_in : delta ∈ deductiveClosure fc ({delta} ∪ B) :=
    subset_deductiveClosure fc ({delta} ∪ B) (Set.mem_union_left _ (Set.mem_singleton delta))
  have h_proper : B ⊂ deductiveClosure fc ({delta} ∪ B) :=
    ⟨h_sub, fun h_eq => h_delta_not (h_eq h_delta_in)⟩
  exact h_R3M.2.2 _ h_cud h_proper h_r3

/-- If both until and since conditions hold for delta extension of B,
then DC({delta} union B) satisfies burgessR3(A, -, C). -/
theorem dc_delta_B_burgessR3 (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_dcs : ClosedUnderDerivation fc B)
    (h_r3 : burgessR3 A B C)
    {delta : Formula Atom}
    (h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C, Formula.untl (Formula.and beta delta) gamma ∈ A)
    (h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A, Formula.snce (Formula.and beta delta) alpha ∈ C) :
    burgessR3 A (deductiveClosure fc ({delta} ∪ B)) C := by
  constructor
  · intro phi hphi gamma hgamma
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨hImpl⟩⟩
    · exact h_r3.1 phi h_B gamma hgamma
    · exact untl_left_mono_thm fc h_mcs_A hImpl (h_until_all beta hbeta gamma hgamma)
  · intro phi hphi alpha halpha
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨hImpl⟩⟩
    · exact h_r3.2 phi h_B alpha halpha
    · exact snce_left_mono_thm fc h_mcs_C hImpl (h_since_all beta hbeta alpha halpha)

/-! ## Xu Lemma 2.3: Guard Strengthening via left_mono_until_G

Xu 1988 Lemma 2.3: If R(A, B, C), then
  (i)  snce(alpha, top) ∈ B for every alpha ∈ A  (P(alpha) ∈ B)
  (ii) untl(gamma, top) ∈ B for every gamma ∈ C  (F(gamma) ∈ B)

This replaces the need for separation_until (BX14/A4a) in the chronicle
splitting construction by enabling a simpler DCS extension argument (Xu Lemma 2.4).

The proof uses left_mono_until_G (BX2G) for guard strengthening:
from G(snce(alpha, top)) ∈ A (derived via BX4 + BX12'), strengthen the guard
of untl(gamma, beta) ∈ A to untl(gamma, beta ∧ snce(alpha, top)) ∈ A,
then apply burgessR_implies_burgessRSince fc for the Since direction.
-/

/-- Xu Lemma 2.3 (i): If R(A, B, C) then snce(alpha, top) ∈ B for all alpha ∈ A.

Proof by contradiction: if snce(alpha, top) ∉ B, then
BurgessR3Maximal_extension_fails gives ¬burgessR3(A, DC({snce(alpha,top)}∪B), C).
But dc_delta_B_burgessR3 fc shows both Until and Since conditions hold, using
left_mono_until_G with G(snce(alpha, top)) ∈ A (derived from alpha ∈ A via BX4 + BX12'). -/
theorem xu_lemma_2_3_since_top (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce (Formula.bot.imp Formula.bot) alpha ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose snce(alpha, top) ∉ B, derive contradiction
  by_contra h_not_in_B
  -- Step 1: BurgessR3Maximal_extension_fails gives ¬burgessR3 for extension
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Derive G(snce(alpha, top)) ∈ A from alpha ∈ A
  -- BX4: alpha → G(P(alpha))
  have h_bx4 : DerivationTree fc [] (alpha.imp (alpha.somePast.allFuture)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future alpha) trivial
  have h_G_P_alpha : alpha.somePast.allFuture ∈ A :=
    SetMaximalConsistent.implication_property h_mcs_A (theoremInMcsFc h_mcs_A h_bx4) h_alpha
  -- BX12': P(alpha) → snce(alpha, top) (theorem)
  have h_bx12' : DerivationTree fc [] (alpha.somePast.imp (Formula.snce top alpha)) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv alpha) trivial
  -- G(P(alpha) → snce(alpha, top)) via temporal necessitation
  have h_G_impl : (alpha.somePast.imp (Formula.snce top alpha)).allFuture ∈ A :=
    theoremInMcsFc h_mcs_A (DerivationTree.temporal_necessitation _ h_bx12')
  -- G(P(alpha)) → G(snce(alpha, top)) via temporal K distribution
  have h_temp_k :=
    liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived alpha.somePast
      (Formula.snce top alpha))
  have h_G_snce : (Formula.snce top alpha).allFuture ∈ A :=
    SetMaximalConsistent.implication_property h_mcs_A
      (SetMaximalConsistent.implication_property h_mcs_A
        (theoremInMcsFc h_mcs_A h_temp_k) h_G_impl)
      h_G_P_alpha
  -- Step 3: Show both conditions for dc_delta_B_burgessR3
  -- Until condition: ∀ beta ∈ B, ∀ gamma ∈ C, untl(gamma, beta ∧ snce(alpha, top)) ∈ A
  have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
      Formula.untl (Formula.and beta (Formula.snce top alpha)) gamma ∈ A := by
    intro beta h_beta gamma h_gamma
    -- untl(gamma, beta) ∈ A from R3
    have hUntl := h_r3.1 beta h_beta gamma h_gamma
    -- ⊢ snce(alpha,top) → (beta → beta ∧ snce(alpha,top))
    -- From pairing + flip: flip(pairing) gives snce → beta → beta ∧ snce
    have h_flip : DerivationTree fc []
        ((Formula.snce top alpha).imp (beta.imp (Formula.and beta (Formula.snce top alpha)))) :=
      mp (pairing beta (Formula.snce top alpha)) flip
    -- G(snce → (beta → beta ∧ snce)) via temporal necessitation
    have h_G_flip := theoremInMcsFc h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
    -- G(snce) → G(beta → beta ∧ snce) via temporal K distribution
    have h_temp_k2 :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived
        (Formula.snce top alpha) (beta.imp (Formula.and beta (Formula.snce top alpha))))
    have h_G_guard_str : (beta.imp (Formula.and beta (Formula.snce top alpha))).allFuture ∈ A :=
      SetMaximalConsistent.implication_property h_mcs_A
        (SetMaximalConsistent.implication_property h_mcs_A
          (theoremInMcsFc h_mcs_A h_temp_k2) h_G_flip)
        h_G_snce
    -- left_mono_until_G: G(beta → beta ∧ snce) → untl(gamma, beta) → untl(gamma, beta ∧ snce)
    exact untl_left_mono_G fc h_mcs_A h_G_guard_str hUntl
  -- Since condition: ∀ beta ∈ B, ∀ alpha' ∈ A, snce(alpha', beta ∧ snce(alpha, top)) ∈ C
  -- From burgessR_implies_burgessRSince applied to the Until condition
  have h_since_all : ∀ beta ∈ B, ∀ alpha' ∈ A,
      Formula.snce (Formula.and beta (Formula.snce top alpha)) alpha' ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_burgessR : burgessR A (Formula.and beta (Formula.snce top alpha)) C :=
      fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
    exact burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR alpha' h_alpha'
  -- Step 4: Apply dc_delta_B_burgessR3 to get burgessR3 for extension
  have h_r3_ext := dc_delta_B_burgessR3 fc h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  -- Step 5: Contradiction with BurgessR3Maximal_extension_fails
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 2.3 (ii): If R(A, B, C) then untl(gamma, top) ∈ B for all gamma ∈ C.
Dual of xu_lemma_2_3_since_top: uses BX4' + BX12 + left_mono_since_H
for the Since guard strengthening, and burgessRSince_implies_burgessR fc for the Until direction. -/
theorem xu_lemma_2_3_until_top (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl (Formula.bot.imp Formula.bot) gamma ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose untl(gamma, top) ∉ B, derive contradiction
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Derive H(untl(gamma, top)) ∈ C from gamma ∈ C
  -- BX4': gamma → H(F(gamma))
  have h_bx4' : DerivationTree fc [] (gamma.imp (gamma.someFuture.allPast)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past gamma) trivial
  have h_H_F_gamma : gamma.someFuture.allPast ∈ C :=
    SetMaximalConsistent.implication_property h_mcs_C (theoremInMcsFc h_mcs_C h_bx4') h_gamma
  -- BX12: F(gamma) → untl(gamma, top) (theorem)
  have h_bx12 : DerivationTree fc [] (gamma.someFuture.imp (Formula.untl top gamma)) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv gamma) trivial
  -- H(F(gamma) → untl(gamma, top)) via past necessitation
  have h_H_impl : (gamma.someFuture.imp (Formula.untl top gamma)).allPast ∈ C :=
    theoremInMcsFc h_mcs_C (Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_bx12)
  -- H(F(gamma)) → H(untl(gamma, top)) via past K distribution
  have h_past_k : DerivationTree fc [] _ :=
    Cslib.Logic.Bimodal.Theorems.pastKDist gamma.someFuture (Formula.untl top gamma)
  have h_H_untl : (Formula.untl top gamma).allPast ∈ C :=
    SetMaximalConsistent.implication_property h_mcs_C
      (SetMaximalConsistent.implication_property h_mcs_C
        (theoremInMcsFc h_mcs_C h_past_k) h_H_impl)
      h_H_F_gamma
  -- Step 3: Since condition: ∀ beta ∈ B, ∀ alpha ∈ A, snce(alpha, beta ∧ untl(gamma, top)) ∈ C
  have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
      Formula.snce (Formula.and beta (Formula.untl top gamma)) alpha ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have hSnce := h_r3.2 beta h_beta alpha' h_alpha'
    -- ⊢ untl(gamma,top) → (beta → beta ∧ untl(gamma,top))
    have h_flip : DerivationTree fc []
        ((Formula.untl top gamma).imp (beta.imp (Formula.and beta (Formula.untl top gamma)))) :=
      mp (pairing beta (Formula.untl top gamma)) flip
    -- H(untl(gamma,top) → (beta → beta ∧ untl(gamma,top))) via past necessitation
    have h_H_flip :=
      theoremInMcsFc h_mcs_C (Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_flip)
    -- H(untl(gamma,top)) → H(beta → beta ∧ untl(gamma,top)) via past K
    have h_past_k2 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.pastKDist
      (Formula.untl top gamma) (beta.imp (Formula.and beta (Formula.untl top gamma)))
    have h_H_guard_str : (beta.imp (Formula.and beta (Formula.untl top gamma))).allPast ∈ C :=
      SetMaximalConsistent.implication_property h_mcs_C
        (SetMaximalConsistent.implication_property h_mcs_C
          (theoremInMcsFc h_mcs_C h_past_k2) h_H_flip)
        h_H_untl
    -- left_mono_since_H: H(beta → beta ∧ untl) → snce(alpha, beta) → snce(alpha, beta ∧ untl)
    exact snce_left_mono_H fc h_mcs_C h_H_guard_str hSnce
  -- Step 4: Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta ∈ B, ∀ gamma' ∈ C,
      Formula.untl (Formula.and beta (Formula.untl top gamma)) gamma' ∈ A := by
    intro beta h_beta gamma' h_gamma'
    have h_burgessRSince : burgessRSince C (Formula.and beta (Formula.untl top gamma)) A :=
      fun alpha h_alpha => h_since_all beta h_beta alpha h_alpha
    exact burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C h_burgessRSince gamma' h_gamma'
  -- Step 5: Apply dc_delta_B_burgessR3 and contradiction
  have h_r3_ext := dc_delta_B_burgessR3 fc h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Set.univ is ClosedUnderDerivation -/

/-- `Set.univ` is `ClosedUnderDerivation` -- every formula is in `Set.univ`. -/
theorem set_univ_closed_under_derivation (fc : FrameClass) :
    ClosedUnderDerivation fc (Set.univ : Set (Formula Atom)) :=
  fun _ _ _ _ => Set.mem_univ _

/-! ## Inconsistent case helpers for gContent/hContent ⊆ B

When `{φ} ∪ B` is inconsistent and `G(φ) ∈ A` with `burgessR3(A, B, C)`,
we show `burgessR3(A, Set.univ, C)` using ex-falso propagation through
`left_mono_until_G`. The maximality clause of `BurgessR3Maximal` (now over
`ClosedUnderDerivation`) then gives a contradiction via `Set.univ`.
-/

/-- Helper: `⊢ φ → (φ.neg → ψ)` for any ψ (ex falso from assumption). -/
noncomputable def exFalsoFromAssumption (fc : FrameClass) (φ ψ : Formula Atom) :
    DerivationTree fc [] (φ.imp (φ.neg.imp ψ)) := by
  -- [φ.neg, φ] ⊢ ⊥ via modus ponens (φ.neg = φ → ⊥)
  have h1 : DerivationTree fc [φ.neg, φ] Formula.bot :=
    DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
      (DerivationTree.assumption _ φ.neg (by simp))
      (DerivationTree.assumption _ φ (by simp))
  -- [φ.neg, φ] ⊢ ψ via ex falso
  have h2 : DerivationTree fc [φ.neg, φ] ψ :=
    DerivationTree.modus_ponens [φ.neg, φ] Formula.bot ψ
      (DerivationTree.weakening [] [φ.neg, φ] (Formula.bot.imp ψ)
        (Cslib.Logic.Bimodal.Theorems.Propositional.efqAxiom ψ) (List.nil_subset _))
      h1
  -- Discharge φ.neg then φ: [φ] ⊢ φ.neg → ψ, then [] ⊢ φ → (φ.neg → ψ)
  exact deductionTheorem [] φ _ (deductionTheorem [φ] φ.neg ψ h2)

/-- Helper: G(φ.neg → ψ) ∈ A from G(φ) ∈ A, using exFalsoFromAssumption + TG + temp_k_dist. -/
theorem G_ex_falso_strengthen (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_Gφ : Formula.allFuture φ ∈ A) :
    (φ.neg.imp ψ).allFuture ∈ A := by
  have d_ef := exFalsoFromAssumption fc φ ψ
  exact SetMaximalConsistent.implication_property h_mcs_A
    (SetMaximalConsistent.implication_property h_mcs_A
      (theoremInMcsFc h_mcs_A
        (liftBase fc
          (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived φ (φ.neg.imp ψ))))
      (theoremInMcsFc h_mcs_A (DerivationTree.temporal_necessitation _ d_ef)))
    h_Gφ

/-- Helper: H(ψ.neg → χ) ∈ C from H(ψ) ∈ C, using exFalsoFromAssumption + pastNecessitation +
pastKDist. -/
theorem H_ex_falso_strengthen (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs_C : SetMaximalConsistent fc C) (ψ χ : Formula Atom)
    (h_Hψ : Formula.allPast ψ ∈ C) :
    (ψ.neg.imp χ).allPast ∈ C := by
  have d_ef := exFalsoFromAssumption fc ψ χ
  exact SetMaximalConsistent.implication_property h_mcs_C
    (SetMaximalConsistent.implication_property h_mcs_C
      (theoremInMcsFc h_mcs_C (Cslib.Logic.Bimodal.Theorems.pastKDist ψ (ψ.neg.imp χ)))
      (theoremInMcsFc h_mcs_C (Cslib.Logic.Bimodal.Theorems.pastNecessitation _ d_ef)))
    h_Hψ

set_option linter.flexible false in
/-- When {φ} ∪ B is inconsistent with DCS B, we have φ.neg ∈ B.
Proof: ¬SetConsistent means ∃ derivation of ⊥ from {φ} ∪ B.
By deduction theorem: derivation of φ.neg from B. By closure: φ.neg ∈ B. -/
theorem neg_mem_of_inconsistent_union (fc : FrameClass) {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation fc B)
    {φ : Formula Atom} (h_not_cons : ¬SetConsistent fc ({φ} ∪ B)) :
    φ.neg ∈ B := by
  -- ¬SetConsistent means ∃ L ⊆ {φ} ∪ B with Nonempty (DerivationTree fc L ⊥)
  -- SetConsistent S = ∀ L, (∀ ψ ∈ L, ψ ∈ S) → ¬Nonempty (DerivationTree fc L ⊥)
  -- Use classical logic to extract witness
  by_contra h_neg_not_B
  apply h_not_cons
  -- If φ.neg ∉ B, then {φ.neg.neg} ∪ B would extend B... Actually, use dcs_neg_union_consistent
  -- The contrapositive: if {φ} ∪ B is inconsistent, then φ ∉ B (already known) and φ.neg ∈ B.
  -- We prove: if φ.neg ∉ B, then {φ} ∪ B IS consistent.
  -- Since B is DCS and φ.neg ∉ B, by dcs_neg_union_consistent: {φ.neg.neg} ∪ B is consistent.
  -- And φ.neg.neg → φ (double negation elimination), so {φ} ∪ B ⊆ DC({φ.neg.neg} ∪ B).
  -- Any subset of a consistent set is consistent.
  -- Actually, we can be more direct: if φ.neg ∉ B and B is DCS, then for any L ⊆ {φ} ∪ B,
  -- if we had DerivationTree fc L ⊥, we could derive φ.neg from B (contradiction).
  intro L hL ⟨d⟩
  -- L ⊆ {φ} ∪ B and DerivationTree fc L ⊥.
  -- Partition L: separate φ occurrences from B elements.
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
  have d_w : DerivationTree fc (φ :: M) Formula.bot :=
    DerivationTree.weakening L (φ :: M) Formula.bot d hL_sub_φM
  -- By deduction theorem: M ⊢ φ → ⊥ = φ.neg
  have d_neg : DerivationTree fc M φ.neg := deductionTheorem M φ Formula.bot d_w
  -- By DCS closure: φ.neg ∈ B — contradiction
  exact h_neg_not_B (h_cud M φ.neg hM_sub_B d_neg)

/-- **Unified interface**: Given BurgessR3Maximal(A, B, C) and delta ∉ B,
EITHER delta.neg ∈ B (when {delta}∪B is inconsistent)
OR ¬burgessR3(A, DC({delta}∪B), C).

The second disjunct always holds (BurgessR3Maximal_extension_fails). The first
disjunct holds additionally when {delta}∪B is inconsistent. -/
theorem BurgessR3Maximal_neg_or_ext_fails (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3M : BurgessR3Maximal fc A B C)
    {delta : Formula Atom} (h_delta_not : delta ∉ B) :
    delta.neg ∈ B ∨ ¬burgessR3 A (deductiveClosure fc ({delta} ∪ B)) C := by
  by_cases h_cons : SetConsistent fc ({delta} ∪ B)
  · exact Or.inr (BurgessR3Maximal_extension_fails fc h_R3M h_delta_not)
  · exact Or.inl (neg_mem_of_inconsistent_union fc h_R3M.1 h_cons)


/-- When {φ} ∪ B is inconsistent, φ.neg ∈ B, G(φ) ∈ A, and burgessR3(A, B, C),
then burgessR3(A, Set.univ, C). The argument: from φ.neg ∈ B and G(φ) ∈ A,
for any ψ: G(φ.neg → ψ) ∈ A (ex falso), then untl_left_mono_G fc gives
untl(ψ, γ) ∈ A from untl(φ.neg, γ) ∈ A. This gives burgessRSet for Set.univ.
burgessR_implies_burgessRSince fc gives the Since direction. -/
theorem burgessR3_univ_of_inconsistent_ext (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3 : burgessR3 A B C)
    {φ : Formula Atom} (h_Gφ : Formula.allFuture φ ∈ A)
    (h_neg_in_B : φ.neg ∈ B) :
    burgessR3 A Set.univ C := by
  constructor
  · -- burgessRSet(A, Set.univ, C): for any ψ ∈ Set.univ, for any γ ∈ C, untl(ψ, γ) ∈ A
    intro ψ _ γ hγ
    -- untl(φ.neg, γ) ∈ A from burgessR3(A, B, C) and φ.neg ∈ B
    have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
    -- G(φ.neg → ψ) ∈ A from G(φ) ∈ A
    have h_G_impl := G_ex_falso_strengthen fc h_mcs_A φ ψ h_Gφ
    -- untl_left_mono_G: G(φ.neg → ψ) and untl(φ.neg, γ) give untl(ψ, γ)
    exact untl_left_mono_G fc h_mcs_A h_G_impl h_untl_neg
  · -- burgessRSetSince(C, Set.univ, A): for any ψ ∈ Set.univ, for any α ∈ A, snce(ψ, α) ∈ C
    intro ψ _ α hα
    -- burgessR(A, ψ, C) from the Until direction above
    have h_burgessR : burgessR A ψ C := fun γ hγ => by
      have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
      have h_G_impl := G_ex_falso_strengthen fc h_mcs_A φ ψ h_Gφ
      exact untl_left_mono_G fc h_mcs_A h_G_impl h_untl_neg
    -- burgessR_implies_burgessRSince gives snce(ψ, α) ∈ C
    exact burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR α hα

/-! ## gContent(A) ⊆ B from BurgessR3Maximal

Given `BurgessR3Maximal(A, B, C)` with A, C MCS and gContent(A) ⊆ C,
every φ ∈ gContent(A) (i.e., G(φ) ∈ A) must also be in B.

**Proof**:
- **Consistent case** ({φ}∪B consistent): `dc_delta_B_burgessR3` shows
  burgessR3(A, DC({φ}∪B), C) using left_mono_until_G/since_H. But
  `BurgessR3Maximal_extension_fails` gives ¬burgessR3. Contradiction.
- **Inconsistent case** ({φ}∪B inconsistent): φ.neg ∈ B (by DCS closure).
  `burgessR3_univ_of_inconsistent_ext` gives burgessR3(A, Set.univ, C).
  Set.univ is ClosedUnderDerivation. B ⊂ Set.univ (B is consistent).
  BurgessR3Maximal maximality (over ClosedUnderDerivation) gives contradiction.
-/

/-- Helper: ⊢ φ → (β → (β ∧ φ)). Conjunction introduction curried. -/
noncomputable def conjIntroCurried (fc : FrameClass) (β φ : Formula Atom) :
    DerivationTree fc [] (φ.imp (β.imp (Formula.and β φ))) := by
  have h1 : DerivationTree fc [β, φ] (Formula.and β φ) :=
    DerivationTree.modus_ponens [β, φ] _ _
      (DerivationTree.modus_ponens [β, φ] β _
        (DerivationTree.weakening [] [β, φ] _
          (pairing β φ) (List.nil_subset _))
        (DerivationTree.assumption _ β (by simp)))
      (DerivationTree.assumption _ φ (by simp))
  exact deductionTheorem [] φ _ (deductionTheorem [φ] β _ h1)

/-! ## Duality: hContent(C) ⊆ D implies gContent(D) ⊆ C

Local proof of the duality theorem needed for Lemma 2.6 splitting.
(The canonical version lives in ChronicleConstruction.lean which imports
this file, so we reproduce it here to avoid circular imports.)
-/

/-- hContent(B) ⊆ A implies gContent(A) ⊆ B for MCS A, B.
Proof: Suppose G(ψ) ∈ A and ψ ∉ B. Then ¬ψ ∈ B (MCS). By BX4' (connect_past):
¬ψ → H(F(¬ψ)), so H(F(¬ψ)) ∈ B, hence F(¬ψ) ∈ hContent(B) ⊆ A.
But F(¬ψ) = ¬G(ψ^{nn}), so G(ψ^{nn}) ∉ A. Yet G(ψ) → G(ψ^{nn}) by DNI
+ temporal necessitation + K distribution, contradiction. -/
theorem h_content_sub_imp_g_content_sub' (fc : FrameClass) {A B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_B : SetMaximalConsistent fc B)
    (h_hBA : hContent B ⊆ A) :
    gContent A ⊆ B := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : ψ.neg ∈ B := by
    rcases SetMaximalConsistent.negation_complete h_mcs_B ψ with h | h
    · exact absurd h h_not
    · exact h
  have h_ax : DerivationTree fc [] (ψ.neg.imp (ψ.neg.someFuture.allPast)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past ψ.neg) trivial
  have h_HF : Formula.allPast (Formula.someFuture ψ.neg) ∈ B :=
    SetMaximalConsistent.implication_property h_mcs_B
      (theoremInMcsFc h_mcs_B h_ax) h_neg_ψ
  have h_F_neg_ψ_A : Formula.someFuture ψ.neg ∈ A := h_hBA h_HF
  -- G(¬¬ψ) ∈ A from G(ψ) via DNI under G
  have h_dni : DerivationTree fc [] (ψ.imp ψ.neg.neg) :=
    Cslib.Logic.Bimodal.Theorems.Combinators.dni ψ
  have h_G_dni : DerivationTree fc [] (Formula.allFuture (ψ.imp ψ.neg.neg)) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_G_dist : DerivationTree fc [] ((Formula.allFuture (ψ.imp ψ.neg.neg)).imp
      (Formula.allFuture ψ |>.imp (Formula.allFuture ψ.neg.neg))) :=
    liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived ψ ψ.neg.neg)
  have h_G_nn : Formula.allFuture ψ.neg.neg ∈ A := by
    have h1 := theoremInMcsFc h_mcs_A h_G_dni
    have h2 := theoremInMcsFc h_mcs_A h_G_dist
    have h3 := SetMaximalConsistent.implication_property h_mcs_A h2 h1
    exact SetMaximalConsistent.implication_property h_mcs_A h3 hψ
  -- F(¬ψ) and G(¬¬ψ) = G(neg(ψ.neg)) are contradictory
  exact someFuture_allFuture_neg_absurd h_mcs_A ψ.neg h_F_neg_ψ_A h_G_nn

/-- gContent(A) ⊆ B implies hContent(B) ⊆ A for MCS A, B. Dual of above. -/
theorem g_content_sub_imp_h_content_sub' (fc : FrameClass) {A B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_B : SetMaximalConsistent fc B)
    (h_gAB : gContent A ⊆ B) :
    hContent B ⊆ A := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : ψ.neg ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A ψ with h | h
    · exact absurd h h_not
    · exact h
  have h_GP : Formula.allFuture (Formula.somePast ψ.neg) ∈ A :=
    connect_future_mcs fc h_mcs_A ψ.neg h_neg_ψ
  have h_P_neg_ψ_B : Formula.somePast ψ.neg ∈ B := h_gAB h_GP
  -- H(¬¬ψ) ∈ B from H(ψ) via DNI under H
  have h_dni : DerivationTree fc [] (ψ.imp ψ.neg.neg) :=
    Cslib.Logic.Bimodal.Theorems.Combinators.dni ψ
  have h_H_dni : DerivationTree fc [] (Formula.allPast (ψ.imp ψ.neg.neg)) :=
    Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_dni
  have h_H_dist : DerivationTree fc [] ((Formula.allPast (ψ.imp ψ.neg.neg)).imp
      (Formula.allPast ψ |>.imp (Formula.allPast ψ.neg.neg))) :=
    Cslib.Logic.Bimodal.Theorems.pastKDist ψ ψ.neg.neg
  have h_H_nn : Formula.allPast ψ.neg.neg ∈ B := by
    have h1 := theoremInMcsFc h_mcs_B h_H_dni
    have h2 := theoremInMcsFc h_mcs_B h_H_dist
    have h3 := SetMaximalConsistent.implication_property h_mcs_B h2 h1
    exact SetMaximalConsistent.implication_property h_mcs_B h3 hψ
  exact somePast_allPast_neg_absurd h_mcs_B ψ.neg h_P_neg_ψ_B h_H_nn

/-! ## Lemma 2.6 Splitting: BurgessR3Maximal Interval Insertion

Given `BurgessR3Maximal(A, B, C)` with `β ∉ B` and `gContent(A) ⊆ C`,
produce MCS D with `¬β ∈ D` and `BurgessR3Maximal(A, B', D)` and
`BurgessR3Maximal(D, B'', C)`.

## Burgess D₀ Seed Construction (Burgess 1982, p.370)

The original Burgess (1982) approach used a rich D₀ seed with explicit Until/Since
formulas, requiring BX14 (separation_until) for consistency. This module instead uses
the Xu 1988 Lemma 3.2.2 approach: the seed is simply B* ∪ {β.neg}, with
consistency following trivially from `dcs_neg_union_consistent`. The Until/Since
formulas needed for r(A, B*, D) are already in B* via Xu 3.2.1. -/

/-! ## Lemma 2.7: Until-Formula Splitting (Burgess 1982)

Lemma 2.7 (Until-formula splitting): given `BurgessR3Maximal(A, B, C)` with
`U(xi, eta) ∈ A` and `eta ∉ B`, produce `B', D, B''` with:
- `BurgessR3Maximal(A, B', D)`
- `BurgessR3Maximal(D, B'', C)`
- `xi ∈ D` and `eta ∈ B'`

## Proof Strategy (Burgess 1982, direct seed)

From `eta ∉ B` and maximality of B: `BurgessR3Maximal_extension_fails` gives
`¬burgessR3(A, DC({eta}∪B), C)` (when {eta}∪B consistent). This means some
formula `phi ∈ DC({eta}∪B)` with some `gamma ∈ C` has `¬U(phi, gamma) ∈ A`.
By `dc_delta_B_controlled`, either `phi ∈ B` (impossible since burgessR3(A,B,C)
holds) or there exists `beta₀ ∈ B` with `⊢ (beta₀∧eta) → phi`.

So we obtain `beta₀ ∈ B`, `gamma₀ ∈ C` with `¬U(beta₀∧eta, gamma₀) ∈ A`.

**Core BX5+BX7+BX13 chain** (adapted from Burgess 1982 p. 371):

1. BX5 on `U(xi, eta)`: get `U(xi∧U(xi,eta), eta) ∈ A`
2. BX5 on `U(beta₀, gamma₀)` (from burgessR3): get `U(beta₀∧U(beta₀,gamma₀), gamma₀) ∈ A`
3. BX7 on these two enriched Until formulas → three-way disjunction D1∨D2∨D3
4. Eliminate D1 and D2 using `¬U(beta₀∧eta, gamma₀) ∈ A` + left_mono_until_G
5. D3 survives: `U(phi₁∧phi₂, phi₁∧gamma₀) ∈ A` where phi₁ = xi∧U(xi,eta)
6. BX10 gives F(phi₁∧gamma₀) ∈ A, so `{phi₁∧gamma₀} ∪ gContent(A) ∪ hContent(C)` consistent
7. Lindenbaum → MCS D with `xi ∈ D`, `gContent(A) ⊆ D`, `gContent(D) ⊆ C`
8. `BurgessR3Maximal(A, B', D)` and `BurgessR3Maximal(D, B'', C)` from gContent
9. `eta ∈ B'` from `U(xi, beta∧eta) ∈ A` for all beta ∈ B, plus maximality
-/

/-- Helper: BX3 (right_mono_until) at MCS level. If ⊢ ψ → χ and
U(φ, ψ) ∈ A, then U(φ, χ) ∈ A. -/
theorem right_mono_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {φ ψ χ : Formula Atom}
    (hImpl : DerivationTree fc [] (ψ.imp χ))
    (hUntl : Formula.untl φ ψ ∈ A) :
    Formula.untl φ χ ∈ A := by
  -- G(ψ → χ) ∈ A from temporal necessitation
  have h_G_impl : Formula.allFuture (ψ.imp χ) ∈ A :=
    theoremInMcsFc h_mcs (DerivationTree.temporal_necessitation _ hImpl)
  -- BX3: G(ψ → χ) → U(φ, ψ) → U(φ, χ)
  have h_bx3 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until ψ χ φ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs h_bx3) h_G_impl) hUntl

/-- Right monotonicity for Since at MCS level: if ⊢ ψ→χ and S(φ,ψ) ∈ C, then S(φ,χ) ∈ C. -/
theorem right_mono_since_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {φ ψ χ : Formula Atom}
    (hImpl : DerivationTree fc [] (ψ.imp χ))
    (hSnce : Formula.snce φ ψ ∈ C) :
    Formula.snce φ χ ∈ C := by
  have h_H_impl : Formula.allPast (ψ.imp χ) ∈ C :=
    theoremInMcsFc h_mcs (Cslib.Logic.Bimodal.Theorems.pastNecessitation _ hImpl)
  have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since ψ χ φ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs h_bx3') h_H_impl) hSnce

/-! ## Lemma 2.7 Helpers and Implementation -/

/-- BX13 (enrichment_until) at MCS level: If p ∈ A and untl(phi, psi) ∈ A,
then untl(phi, psi ∧ snce(phi, p)) ∈ A. -/
theorem enrichment_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {phi psi p : Formula Atom}
    (h_p : p ∈ A)
    (hUntl : Formula.untl phi psi ∈ A) :
    Formula.untl phi (Formula.and psi (Formula.snce phi p)) ∈ A := by
  have h_conj := conj_mcs fc h_mcs p (Formula.untl phi psi) h_p hUntl
  have h_bx13 := DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_until phi psi p) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_bx13) h_conj

/-- BX10 (until_F) at MCS level: If untl(phi, psi) ∈ A, then F(psi) ∈ A.
Alias for `until_F_mcs` for local use. -/
theorem until_implies_F_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {phi psi : Formula Atom}
    (hUntl : Formula.untl phi psi ∈ A) :
    Formula.someFuture psi ∈ A :=
  until_F_mcs fc h_mcs phi psi hUntl

/-- F-monotonicity at MCS level: If ⊢ phi → psi and F(phi) ∈ A, then F(psi) ∈ A.
F(phi) = ¬G(¬phi). From ⊢ phi → psi we get ⊢ ¬psi → ¬phi, then G(¬psi) → G(¬phi),
so ¬G(¬phi) → ¬G(¬psi), i.e., F(phi) → F(psi). -/
theorem F_mono_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {phi psi : Formula Atom}
    (hImpl : DerivationTree fc [] (phi.imp psi))
    (h_F : Formula.someFuture phi ∈ A) :
    Formula.someFuture psi ∈ A := by
  -- F(phi) = ¬G(¬phi). Suppose G(¬psi) ∈ A for contradiction.
  by_contra h_not_F
  -- ¬F(psi) ∈ A, derive G(¬psi) ∈ A via duality bridge
  have h_neg_F : (Formula.someFuture psi).neg ∈ A :=
    (SetMaximalConsistent.negation_complete h_mcs _).resolve_left h_not_F
  have h_G_neg_psi : Formula.allFuture psi.neg ∈ A :=
    neg_someFuture_to_allFuture_neg h_mcs psi h_neg_F
  -- From ⊢ phi → psi: ⊢ ¬psi → ¬phi (contrapositive)
  -- G(¬psi → ¬phi) is a theorem
  -- G(¬psi) → G(¬phi) by K-distribution
  have h_contra : DerivationTree fc [] (psi.neg.imp phi.neg) := by
    have h1 : DerivationTree fc [phi, psi.neg] psi :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.weakening [] _ _ hImpl (List.nil_subset _))
        (DerivationTree.assumption _ phi (by simp))
    have h2 : DerivationTree fc [phi, psi.neg] Formula.bot :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.assumption _ psi.neg (by simp)) h1
    have h3 := deductionTheorem [psi.neg] phi Formula.bot h2
    exact deductionTheorem [] psi.neg phi.neg h3
  have h_G_contra := theoremInMcsFc h_mcs
    (DerivationTree.temporal_necessitation _ h_contra)
  have h_kd := theoremInMcsFc h_mcs
    (liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived psi.neg phi.neg))
  have h_G_neg_phi : Formula.allFuture phi.neg ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_kd h_G_contra) h_G_neg_psi
  -- F(phi) and G(¬phi) are contradictory in MCS A
  exact someFuture_allFuture_neg_absurd h_mcs phi h_F h_G_neg_phi

/-- Helper: ⊢ (a ∧ b) → a (left conjunction elimination). -/
noncomputable def andLeftImpl (fc : FrameClass) (a b : Formula Atom) :
    DerivationTree fc [] ((Formula.and a b).imp a) :=
  lceImp a b

/-- Helper: ⊢ (a ∧ b) → b (right conjunction elimination). -/
noncomputable def andRightImpl (fc : FrameClass) (a b : Formula Atom) :
    DerivationTree fc [] ((Formula.and a b).imp b) :=
  rceImp a b

/-- **List-level cut** (derivation from implied context):
If Γ ⊢ φ for each φ ∈ L, and L ⊢ ψ, then Γ ⊢ ψ.

This is the substitution principle: we can replace assumptions in L
with their derivations from Γ. Proved by induction on L. -/
noncomputable def derivationFromImplied (fc : FrameClass) (Γ : Context Atom) :
    (L : Context Atom) → (ψ : Formula Atom) →
    (∀ φ ∈ L, DerivationTree fc Γ φ) →
    DerivationTree fc L ψ →
    DerivationTree fc Γ ψ
  | [], ψ, _, d => DerivationTree.weakening [] Γ ψ d (List.nil_subset Γ)
  | l :: L', ψ, h_derives, d => by
    -- Apply deduction theorem to remove l from the head
    have d_impl : DerivationTree fc L' (l.imp ψ) := deductionTheorem L' l ψ d
    -- Recursively derive l.imp ψ from Γ
    have h_derives' : ∀ φ ∈ L', DerivationTree fc Γ φ := fun φ hφ =>
      h_derives φ (List.mem_cons.mpr (Or.inr hφ))
    have d_impl_Γ : DerivationTree fc Γ (l.imp ψ) :=
      derivationFromImplied fc Γ L' (l.imp ψ) h_derives' d_impl
    -- Derive l from Γ
    have d_l : DerivationTree fc Γ l := h_derives l (List.mem_cons.mpr (Or.inl rfl))
    -- Apply modus ponens: Γ ⊢ l.imp ψ and Γ ⊢ l gives Γ ⊢ ψ
    exact DerivationTree.modus_ponens Γ l ψ d_impl_Γ d_l

/-- Corollary: If a set S implies each element of L (i.e., for each φ∈L
there exist premises in S deriving φ), and L ⊢ ⊥, then S is inconsistent.
Contrapositive: if S is consistent, then no L derived from S can derive ⊥,
hence the set of formulas implied by S is consistent. -/
theorem inconsistent_from_implied (fc : FrameClass) {Sig : Set (Formula Atom)}
    (h_cons : SetConsistent fc Sig)
    (L : List (Formula Atom)) (hL : ∀ φ ∈ L, φ ∈ Sig)
    (d : Nonempty (DerivationTree fc L Formula.bot)) : False :=
  h_cons L hL d

/-! ### List Conjunction and Helpers for Burgess Compression

These helpers support the Burgess compression argument: given a finite
subset L of a seed D₀, we compress it into a single conjunction and
show that conjunction is consistent via the BX chain. -/

/-- Conjunction of a list of formulas. Empty list gives ⊤ (= ⊥→⊥). -/
noncomputable def listConj (fc : FrameClass) : List (Formula Atom) → Formula Atom
  | [] => Formula.bot.imp Formula.bot  -- top
  | [φ] => φ
  | (φ :: rest) => Formula.and φ (listConj fc rest)

set_option linter.flexible false in
/-- ⊢ listConj L → φ for each φ ∈ L. -/
noncomputable def listConjImpliesElem (fc : FrameClass) :
    (L : List (Formula Atom)) → (φ : Formula Atom) → (h : φ ∈ L) →
    DerivationTree fc [] ((listConj fc L).imp φ)
  | [ψ], φ, h => by
    simp at h
    subst h; simp [listConj]; exact identity φ
  | (ψ₁ :: ψ₂ :: rest), φ, h => by
    simp [listConj]
    -- Cannot use rcases on Or into Type; use decidable equality instead
    by_cases h_eq : φ = ψ₁
    · -- φ = ψ₁: extract left component of ψ₁ ∧ listConj(ψ₂::rest)
      subst h_eq; exact lceImp φ (listConj fc (ψ₂ :: rest))
    · -- φ ∈ ψ₂ :: rest: extract right component, then recurse
      have h' : φ ∈ ψ₂ :: rest := by
        rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl h_eq
        · exact h'
      have h_right : DerivationTree fc [] _ := rceImp ψ₁ (listConj fc (ψ₂ :: rest))
      have h_rec := listConjImpliesElem fc (ψ₂ :: rest) φ h'
      exact impTrans h_right h_rec

set_option linter.flexible false in
/-- If B is DCS and all elements of L are in B, then listConj L ∈ B. -/
theorem list_conj_mem_dcs (fc : FrameClass) {B : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ B) → listConj fc L ∈ B
  | [], _ => cud_contains_theorems h_dcs (identity (Formula.bot : Formula Atom))
  | [φ], h => by simp [listConj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [listConj]
    have h1 : φ₁ ∈ B := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : listConj fc (φ₂ :: rest) ∈ B :=
      list_conj_mem_dcs fc h_dcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact cud_conj_closed h_dcs h1 h2

set_option linter.flexible false in
/-- If A is MCS and all elements of L are in A, then listConj L ∈ A. -/
theorem list_conj_mem_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ A) → listConj fc L ∈ A
  | [], _ => theoremInMcsFc h_mcs (identity (Formula.bot : Formula Atom))
  | [φ], h => by simp [listConj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [listConj]
    have h1 : φ₁ ∈ A := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : listConj fc (φ₂ :: rest) ∈ A :=
      list_conj_mem_mcs fc h_mcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact conj_mcs fc h_mcs φ₁ (listConj fc (φ₂ :: rest)) h1 h2

/-- If F(φ)∈A (MCS), then {φ} is consistent. -/
theorem consistent_of_F_mem (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    (φ : Formula Atom) (h_F : Formula.someFuture φ ∈ A) :
    SetConsistent fc ({φ} : Set (Formula Atom)) := by
  -- {φ} ⊆ {φ} ∪ gContent(A), and the latter is consistent
  have h_seed := forward_temporal_witness_seed_consistent A h_mcs φ h_F
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

set_option linter.flexible false in
/-- If {φ} is consistent and [φ] ⊢ ⊥, then False. -/
theorem inconsistent_singleton_false (fc : FrameClass) {φ : Formula Atom}
    (h_cons : SetConsistent fc ({φ} : Set (Formula Atom)))
    (d : DerivationTree fc [φ] Formula.bot) : False :=
  h_cons [φ] (fun ψ hψ => by simp at hψ; subst hψ; exact Set.mem_singleton _) ⟨d⟩


/-- Derivation-level left_mono for Until: if ⊢ φ→χ then ⊢ untl(φ,ψ) → untl(χ,ψ).
Uses BX2G (left_mono_until_G): G(φ→χ) → untl(φ,ψ) → untl(χ,ψ). -/
noncomputable def untlLeftMonoDeriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (hImpl : DerivationTree fc [] (φ.imp χ)) :
    DerivationTree fc [] ((Formula.untl φ ψ).imp (Formula.untl χ ψ)) := by
  have h_G := DerivationTree.temporal_necessitation _ hImpl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.left_mono_until_G φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_G

/-- Derivation-level left_mono for Since: if ⊢ φ→χ then ⊢ snce(φ,ψ) → snce(χ,ψ).
Uses BX2H (left_mono_since_H): H(φ→χ) → snce(φ,ψ) → snce(χ,ψ). -/
noncomputable def snceLeftMonoDeriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (hImpl : DerivationTree fc [] (φ.imp χ)) :
    DerivationTree fc [] ((Formula.snce φ ψ).imp (Formula.snce χ ψ)) := by
  have h_H := Cslib.Logic.Bimodal.Theorems.pastNecessitation _ hImpl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.left_mono_since_H φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_H

/-- Derivation-level right_mono for Until: if ⊢ φ→ψ then ⊢ untl(χ,φ) → untl(χ,ψ).
Uses BX3 (right_mono_until): G(φ→ψ) → untl(χ,φ) → untl(χ,ψ). -/
noncomputable def untlRightMonoDeriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (hImpl : DerivationTree fc [] (φ.imp ψ)) :
    DerivationTree fc [] ((Formula.untl χ φ).imp (Formula.untl χ ψ)) := by
  have h_G := DerivationTree.temporal_necessitation _ hImpl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until φ ψ χ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_G

/-- Derivation-level right_mono for Since: if ⊢ φ→ψ then ⊢ snce(χ,φ) → snce(χ,ψ).
Uses BX3' (right_mono_since): H(φ→ψ) → snce(χ,φ) → snce(χ,ψ). -/
noncomputable def snceRightMonoDeriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (hImpl : DerivationTree fc [] (φ.imp ψ)) :
    DerivationTree fc [] ((Formula.snce χ φ).imp (Formula.snce χ ψ)) := by
  have h_H := Cslib.Logic.Bimodal.Theorems.pastNecessitation _ hImpl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since φ ψ χ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_H

/-- BX13' (enrichment_since) at MCS level: If p ∈ C and snce(phi, psi) ∈ C,
then snce(phi, psi ∧ untl(phi, p)) ∈ C. -/
theorem enrichment_since_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {phi psi p : Formula Atom}
    (h_p : p ∈ C)
    (hSnce : Formula.snce phi psi ∈ C) :
    Formula.snce phi (Formula.and psi (Formula.untl phi p)) ∈ C := by
  have h_conj := conj_mcs fc h_mcs p (Formula.snce phi psi) h_p hSnce
  have h_bx13 := DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_since phi psi p) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_bx13) h_conj

/-- BX10' (since_P) at MCS level: If snce(phi, psi) ∈ C, then P(psi) ∈ C. -/
theorem since_implies_P_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {phi psi : Formula Atom}
    (hSnce : Formula.snce phi psi ∈ C) :
    Formula.somePast psi ∈ C :=
  since_implies_P_in_mcs fc h_mcs hSnce

/-- If P(φ)∈C (MCS), then {φ} is consistent. -/
theorem consistent_of_P_mem (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C)
    (φ : Formula Atom) (h_P : Formula.somePast φ ∈ C) :
    SetConsistent fc ({φ} : Set (Formula Atom)) := by
  have h_seed := past_temporal_witness_seed_consistent C h_mcs φ h_P
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

/-- P-monotonicity at MCS level: If ⊢ phi → psi and P(phi) ∈ C, then P(psi) ∈ C.
Mirror of F_mono_mcs fc using H instead of G. -/
theorem P_mono_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {phi psi : Formula Atom}
    (hImpl : DerivationTree fc [] (phi.imp psi))
    (h_P : Formula.somePast phi ∈ C) :
    Formula.somePast psi ∈ C := by
  by_contra h_not_P
  have h_neg_P : (Formula.somePast psi).neg ∈ C :=
    (SetMaximalConsistent.negation_complete h_mcs _).resolve_left h_not_P
  have h_H_neg_psi : Formula.allPast psi.neg ∈ C :=
    neg_somePast_to_allPast_neg h_mcs psi h_neg_P
  have h_contra : DerivationTree fc [] (psi.neg.imp phi.neg) := by
    have h1 : DerivationTree fc [phi, psi.neg] psi :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.weakening [] _ _ hImpl (List.nil_subset _))
        (DerivationTree.assumption _ phi (by simp))
    have h2 : DerivationTree fc [phi, psi.neg] Formula.bot :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.assumption _ psi.neg (by simp)) h1
    have h3 := deductionTheorem [psi.neg] phi Formula.bot h2
    exact deductionTheorem [] psi.neg phi.neg h3
  have h_H_contra := theoremInMcsFc h_mcs
    (Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_contra)
  have h_kd := theoremInMcsFc h_mcs
    (Cslib.Logic.Bimodal.Theorems.pastKDist psi.neg phi.neg)
  have h_H_neg_phi : Formula.allPast phi.neg ∈ C :=
    SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_kd h_H_contra) h_H_neg_psi
  exact somePast_allPast_neg_absurd h_mcs phi h_P h_H_neg_phi

/-- Structure to hold the result of iterated BX13 enrichment. -/
structure EnrichedEvent (fc : FrameClass) (A : Set (Formula Atom)) (guard event : Formula Atom)
    (alphas : List (Formula Atom)) where
  /-- The enriched event formula produced by BX13 enrichment. -/
  event' : Formula Atom
  /-- Proof that `untl(event', guard)` belongs to the MCS `A`. -/
  hUntl : Formula.untl guard event' ∈ A
  /-- Derivation that the enriched event implies the original event. -/
  hImpl : DerivationTree fc [] (event'.imp event)
  /-- For each α in alphas, derivation that the enriched event implies snce(α, guard). -/
  hSnce : ∀ α ∈ alphas, DerivationTree fc [] (event'.imp (Formula.snce guard α))

/-- Iterated BX13 enrichment: given untl(guard, event) ∈ A and a list of
formulas each in A, enrich the event with snce(guard, αⱼ) for each αⱼ.

Result: EnrichedEvent fc containing the new event and proofs. -/
noncomputable def iteratedEnrichment (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    (guard : Formula Atom) :
    (alphas : List (Formula Atom)) →
    (h_alphas : ∀ α ∈ alphas, α ∈ A) →
    (event : Formula Atom) →
    Formula.untl guard event ∈ A →
    EnrichedEvent fc A guard event alphas
  | [], _, event, hUntl => EnrichedEvent.mk event hUntl (identity event) (fun _ h => by simp at h)
  | α :: rest, h_alphas, event, hUntl => by
    have h_α : α ∈ A := h_alphas α (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_until_mcs fc h_mcs h_α hUntl
    have h_rest : ∀ α' ∈ rest, α' ∈ A := fun α' hα' =>
      h_alphas α' (List.mem_cons.mpr (Or.inr hα'))
    let evt := iteratedEnrichment fc h_mcs guard rest h_rest
      (Formula.and event (Formula.snce guard α)) h_enriched
    exact EnrichedEvent.mk evt.event' evt.hUntl
      (impTrans evt.hImpl (lceImp event (Formula.snce guard α)))
      (fun α' hα' => by
        by_cases h_eq : α' = α
        · subst h_eq; exact impTrans evt.hImpl (rceImp event (Formula.snce guard α'))
        · have h : α' ∈ rest := by
            rcases List.mem_cons.mp hα' with rfl | h
            · exact absurd rfl h_eq
            · exact h
          exact evt.hSnce α' h)

/-- Structure for iterated BX13' (Since-direction) enrichment. -/
structure EnrichedEventSince (fc : FrameClass) (C : Set (Formula Atom)) (guard event : Formula Atom)
    (gammas : List (Formula Atom)) where
  /-- The enriched event formula produced by BX13' enrichment. -/
  event' : Formula Atom
  /-- Proof that `snce(event', guard)` belongs to the MCS `C`. -/
  hSnce : Formula.snce guard event' ∈ C
  /-- Derivation that the enriched event implies the original event. -/
  hImpl : DerivationTree fc [] (event'.imp event)
  /-- For each γ in gammas, derivation that the enriched event implies untl(γ, guard). -/
  hUntl : ∀ γ ∈ gammas, DerivationTree fc [] (event'.imp (Formula.untl guard γ))

/-- Iterated BX13' enrichment (Since direction): given snce(guard, event) ∈ C and
a list of formulas each in C, enrich the event with untl(guard, γⱼ) for each γⱼ. -/
noncomputable def iteratedEnrichmentSince (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C)
    (guard : Formula Atom) :
    (gammas : List (Formula Atom)) →
    (h_gammas : ∀ γ ∈ gammas, γ ∈ C) →
    (event : Formula Atom) →
    Formula.snce guard event ∈ C →
    EnrichedEventSince fc C guard event gammas
  | [], _, event, hSnce =>
    EnrichedEventSince.mk event hSnce (identity event) (fun _ h => by simp at h)
  | γ :: rest, h_gammas, event, hSnce => by
    have h_γ : γ ∈ C := h_gammas γ (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_since_mcs fc h_mcs h_γ hSnce
    have h_rest : ∀ γ' ∈ rest, γ' ∈ C := fun γ' hγ' =>
      h_gammas γ' (List.mem_cons.mpr (Or.inr hγ'))
    let evt := iteratedEnrichmentSince fc h_mcs guard rest h_rest
      (Formula.and event (Formula.untl guard γ)) h_enriched
    exact EnrichedEventSince.mk evt.event' evt.hSnce
      (impTrans evt.hImpl (lceImp event (Formula.untl guard γ)))
      (fun γ' hγ' => by
        by_cases h_eq : γ' = γ
        · subst h_eq; exact impTrans evt.hImpl (rceImp event (Formula.untl guard γ'))
        · have h : γ' ∈ rest := by
            rcases List.mem_cons.mp hγ' with rfl | h
            · exact absurd rfl h_eq
            · exact h
          exact evt.hUntl γ' h)


end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

end
