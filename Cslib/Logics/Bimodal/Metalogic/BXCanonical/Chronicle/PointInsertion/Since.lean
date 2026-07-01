/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion.XuGuard
public import Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency

/-! # Since — Lemma 2.7' and Lemma 2.4 Enriched Seed (Since Direction)

Lemma 2.7' (Since direction): Given `BurgessR3Maximal(A, B, C)` with `snce(xi, eta) ∈ C`
and `xi ∉ B`, produces `B', D, B''` such that the required R3-maximality conditions hold.

Also includes Lemma 2.8' and the enriched Lemma 2.4 variants (with/without guard, Since direction).

## Main Results

- `lemma_2_7_since`: Since-direction Burgess Lemma 2.7
- `lemma_2_8_since`: Since-direction Burgess Lemma 2.8
- `lemma24WithGuard`: Lemma 2.4 with guard (enriched Until version)
- `lemma24SinceWithGuard`: Lemma 2.4 with guard (Since direction)
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false

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

/-! ## Lemma 2.7' (Since direction): Since-Formula Splitting

Mirror of Lemma 2.7 for the Since direction. Given `BurgessR3Maximal(A, B, C)` with
`snce(xi, eta) ∈ C` and `xi ∉ B`, produce `B', D, B''` with:
- `BurgessR3Maximal(A, B', D)`
- `BurgessR3Maximal(D, B'', C)`
- `eta ∈ D`

Uses BX5'+BX7'+BX13' (Since-direction chain) instead of BX5+BX7+BX13. -/

/-- The `SinceSeedInterface` instance family for Bimodal (task 454), indexed by `fc`:
populates every field of the shared Foundations interface with Bimodal's own
`fc`-threaded apparatus. Used to delegate to the generic `lemma27SinceSeed`/`l27s*`
helpers (`Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`) instead of
duplicating them locally (task-454 Phase 1). -/
private noncomputable def bimodalSinceInterface (fc : FrameClass) :
    Cslib.Logic.Metalogic.Chronicle.SinceSeedInterface (Formula Atom) where
  bot := Formula.bot
  imp := Formula.imp
  and := Formula.and
  untl := Formula.untl
  snce := Formula.snce
  somePast := Formula.somePast
  allPast := Formula.allPast
  allFuture := Formula.allFuture
  Deriv := DerivationTree fc
  untlInjective := fun h => Formula.untl.inj h
  andInjective := by
    intro a b c d h
    simp only [Formula.and] at h
    have h1 := Formula.imp.inj h
    have h2 := Formula.imp.inj h1.1
    exact ⟨h2.1, (Formula.imp.inj h2.2).1⟩
  assumption := fun h => DerivationTree.assumption _ _ h
  modusPonens := fun h1 h2 => DerivationTree.modus_ponens _ _ _ h1 h2
  weakening := fun Γ Δ φ d hsub => DerivationTree.weakening Γ Δ φ d hsub
  deductionTheorem := fun Γ φ ψ d => deductionTheorem Γ φ ψ d
  identity' := fun φ => identity φ
  impTrans := fun h1 h2 => impTrans h1 h2
  lceImp := fun φ ψ => lceImp φ ψ
  rceImp := fun φ ψ => rceImp φ ψ
  combineImpConj := fun h1 h2 => combineImpConj h1 h2
  untlLeftMonoDeriv := fun g1 e g2 h => untlLeftMonoDeriv fc g1 e g2 h
  pastNecessitation := fun φ d => Cslib.Logic.Bimodal.Theorems.pastNecessitation φ d
  theoremInMcs := by intro _ hmcs _ hd; exact theoremInMcsFc hmcs hd
  negationComplete := fun hmcs φ => SetMaximalConsistent.negation_complete hmcs φ
  negExcludes := by
    intro _ hmcs _ hneg hmem; exact SetMaximalConsistent.neg_excludes hmcs _ hneg hmem
  cudContainsTheorems := by intro _ hcud _ hd; exact cud_contains_theorems hcud hd
  selfAccumSinceMcs := fun hmcs γ β h => self_accum_since_mcs fc hmcs γ β h
  linearSinceMcs := fun hmcs φ ψ χ θ h1 h2 => linear_since_mcs fc hmcs φ ψ χ θ h1 h2
  rightMonoSinceMcs := by intro _ hmcs _ _ _ hi hs; exact right_mono_since_mcs fc hmcs hi hs
  sinceImpliesP := by intro _ hmcs _ _ h; exact since_implies_P_mcs fc hmcs h
  consistentOfPMem := fun hmcs φ h => consistent_of_P_mem fc hmcs φ h
  inconsistentSingletonFalse := by intro _ hcons d; exact inconsistent_singleton_false fc hcons d
  derivationFromImplied := fun Γ L ψ h d => derivationFromImplied fc Γ L ψ h d
  dcDeltaBControlled := by
    intro _ hcud _ _ _ hLsub hd; exact dc_delta_B_controlled fc hcud hLsub hd
  iteratedEnrichmentSince := fun hmcs guard gammas hgammas event hsnce => by
    have evt := iteratedEnrichmentSince fc hmcs guard gammas hgammas event hsnce
    exact ⟨evt.event', evt.hSnce, evt.hImpl, evt.hUntl⟩
  xuLemma321Until := by
    intro _ _ _ hA hC hR3M beta hbeta gamma hgamma
    exact xu_lemma_3_2_1_until fc hA hC hR3M hbeta hgamma
  xuLemma321Since := by
    intro _ _ _ hA hC hR3M beta hbeta alpha halpha
    exact xu_lemma_3_2_1_since fc hA hC hR3M hbeta halpha
  burgessRImpliesBurgessRSince := by
    intro _ _ hA hC beta hR; exact burgessR_implies_burgessRSince fc hA hC hR
  burgessRSinceImpliesBurgessR := by
    intro _ _ hA hC beta hR; exact burgessRSince_implies_burgessR fc hA hC hR
  burgessRConj := by intro _ _ hA α β ha hb; exact burgessR_conj fc hA ha hb
  burgessRSinceConj := by intro _ _ hC α β ha hb; exact burgessRSince_conj fc hC ha hb
  burgessR3MaximalExtensionFails := by
    intro _ _ _ hR3M delta hnotmem; exact BurgessR3Maximal_extension_fails fc hR3M hnotmem
  dcDeltaBBurgessR3 := by
    intro _ _ _ hA hC hcud hr3 delta huntl hsince
    exact dc_delta_B_burgessR3 fc hA hC hcud hr3 huntl hsince
  burgessR3MaximalExtensionExists := by
    intro _ _ _ hA hC hcud hr3
    obtain ⟨B, hsub, _, hmax⟩ := burgessR3Maximal_extension_exists fc hA hC hcud hr3
    exact ⟨B, hsub, hmax⟩
  listConj := listConj fc
  listConjMemDcs := fun hcud L hL => list_conj_mem_dcs fc hcud L hL
  listConjMemMcs := fun hmcs L hL => list_conj_mem_mcs fc hmcs L hL
  listConjImpliesElem := fun L φ h => listConjImpliesElem fc L φ h
  untlLeftMonoThm := by intro _ hmcs _ _ _ hi hu; exact untl_left_mono_thm fc hmcs hi hu
  snceLeftMonoThm := by intro _ hmcs _ _ _ hi hs; exact snce_left_mono_thm fc hmcs hi hs
  lindenbaum := by intro _ hcons; exact set_lindenbaum_fc hcons

/-- Since-direction seed, simplified via Xu 3.2.1:
B ∪ {eta} ∪ {untl(γ, β∧xi) | β∈B, γ∈C}.

The original 5-component seed included {untl(γ,β)} and {snce(α,β)} but these are
redundant: Xu 3.2.1 proves they are already in B. The 3rd component untl(γ, β∧xi)
cannot be dropped because xi ∉ B prevents Xu 3.2.1 from applying. Relocated (task-454
Phase 1) to the shared `Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`
module; this is a thin alias. These formula-operator-only helpers do not depend on `fc`
(only `untl`/`and` and their injectivity), so the arbitrary `FrameClass.Base` index of
`bimodalSinceInterface` is used internally and the original no-`fc` signatures are
preserved verbatim. -/
@[nolint unusedArguments]
private def lemma27SinceSeed (_A B C : Set (Formula Atom)) (xi eta : Formula Atom) :
    Set (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed
    (bimodalSinceInterface FrameClass.Base) _A B C xi eta

/-- Extract γ' events from component 3 elements (untl(γ, β∧xi)) of a list. Relocated
(task-454 Phase 1). -/
private noncomputable def l27sC5EventList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sC5EventList (bimodalSinceInterface FrameClass.Base) B C xi L

/-- Elements of l27sC5EventList are in C. Relocated (task-454 Phase 1). -/
private theorem l27s_c5_event_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {γ : Formula Atom} (hγ : γ ∈ l27sC5EventList B C xi L) : γ ∈ C :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_event_list_mem (bimodalSinceInterface FrameClass.Base) hγ

/-- Extract β' guards from component 3 elements (untl(γ, β∧xi)) of a list. Relocated
(task-454 Phase 1). -/
private noncomputable def l27sB5GuardList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sB5GuardList (bimodalSinceInterface FrameClass.Base) B C xi L

/-- Elements of l27sB5GuardList are in B. Relocated (task-454 Phase 1). -/
private theorem l27s_b5_guard_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β : Formula Atom} (hβ : β ∈ l27sB5GuardList B C xi L) : β ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_guard_list_mem
    (bimodalSinceInterface FrameClass.Base) hβ

/-- For a component 3 element untl(γ', β'∧xi) in L, the extracted γ' is in c5_event_list.
Relocated (task-454 Phase 1). -/
private theorem l27s_c5_γ_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    γ' ∈ l27sC5EventList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_γ_mem (bimodalSinceInterface FrameClass.Base) hφ hβ' hγ'

/-- For a component 3 element untl(γ', β'∧xi) in L, the extracted β' is in b5_guard_list.
Relocated (task-454 Phase 1). -/
private theorem l27s_b5_β_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    β' ∈ l27sB5GuardList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_β_mem (bimodalSinceInterface FrameClass.Base) hφ hβ' hγ'

/-- Since-direction seed consistency (simplified via Xu 3.2.1):
Given BurgessR3Maximal(A, B, C) with snce(xi, eta) ∈ C and xi ∉ B,
the 3-component seed B ∪ {eta} ∪ {untl(γ, β∧xi)} is consistent.

Uses BX5'+BX7'+BX13' chain operating on C. -/
private theorem lemma_2_7_since_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce xi eta ∈ C)
    (h_xi_not_B : xi ∉ B) :
    SetConsistent fc (lemma27SinceSeed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  have h_not_r3_xi := BurgessR3Maximal_extension_fails fc h_r3m h_xi_not_B
  have h_neg_since_exists : ∃ beta0 ∈ B, ∃ alpha0 ∈ A,
      Formula.snce (Formula.and beta0 xi) alpha0 ∉ C := by
    by_contra h_all_since
    push Not at h_all_since
    have h_rset : burgessRSet A (deductiveClosure fc ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · have h_burgessRSince_ext : burgessRSince C (Formula.and beta_w xi) A :=
          fun alpha halpha => h_all_since beta_w hbeta_w alpha halpha
        have h_burgessR_ext := burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C h_burgessRSince_ext
        exact untl_left_mono_thm fc h_mcs_A hImpl (h_burgessR_ext gamma hgamma)
    have h_rsince : burgessRSetSince C (deductiveClosure fc ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · exact snce_left_mono_thm fc h_mcs_C hImpl (h_all_since beta_w hbeta_w alpha halpha)
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, alpha0, h_alpha0, h_not_in_C⟩ := h_neg_since_exists
  have h_neg_since_in_C : (Formula.snce (Formula.and beta0 xi) alpha0).neg ∈ C := by
    rcases SetMaximalConsistent.negation_complete h_mcs_C
      (Formula.snce (Formula.and beta0 xi) alpha0) with h | h
    · exfalso; exact h_not_in_C h
    · exact h
  intro L hL ⟨d⟩
  have h_bx5_xe := self_accum_since_mcs fc h_mcs_C xi eta h_since
  -- h_key: BX5'+BX7'+BX13' chain for the since direction
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B) (h_b_beta0 : DerivationTree fc [] (b.imp beta0))
      (α_hat : Formula Atom) (hα : α_hat ∈ A) (h_α_alpha0 : DerivationTree fc [] (α_hat.imp alpha0))
      (gamma_list : List (Formula Atom)) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : Formula Atom),
        Formula.somePast event ∈ C ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.snce b α_hat)) ×'
        (∀ γ ∈ gamma_list, DerivationTree fc [] (event.imp (Formula.untl (Formula.and b (Formula.and xi (Formula.snce xi eta))) γ))) by
    -- Extract B-guards, C-events from L
    let b_list_5 := l27sB5GuardList B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem hg
    let c_list := l27sC5EventList B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem hγ
    -- Also need B-guards for elements of L that are in B directly
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := beta0 :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List (Formula Atom) := [alpha0]
    have ha_list : ∀ α ∈ a_list, α ∈ A := by
      intro α hα; simp [a_list] at hα; subst hα; exact h_alpha0
    let b := listConj fc b_list
    let α_hat := listConj fc a_list
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := list_conj_mem_mcs fc h_mcs_A a_list ha_list
    have h_b_to_beta0 : DerivationTree fc [] (b.imp beta0) :=
      listConjImpliesElem fc b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_α_to_alpha0 : DerivationTree fc [] (α_hat.imp alpha0) :=
      listConjImpliesElem fc a_list alpha0 (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B h_b_to_beta0 α_hat hα_A h_α_to_alpha0 c_list hc_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.snce xi eta)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      -- Case 1: φ ∈ B
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := listConjImpliesElem fc b_list φ h_φ_in_b
        have h_ev_to_φ := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · -- Case 2: φ = eta
        by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · -- Case 3: φ = untl(γ', β'∧xi) with β'∈B, γ'∈C
          by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl (Formula.and β' xi) γ'
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = Formula.untl (Formula.and β' xi) γ' :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : Formula.untl (Formula.and β' xi) γ' ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := listConjImpliesElem fc b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : DerivationTree fc [] ((Formula.and b χ_gen).imp
                (Formula.and β' xi)) := by
              have h1 := impTrans (lceImp b χ_gen) h_b_to_β'
              have h2 : DerivationTree fc [] ((Formula.and b χ_gen).imp xi) :=
                impTrans (rceImp b χ_gen) (lceImp xi (Formula.snce xi eta))
              exact combineImpConj h1 h2
            have h_left := untlLeftMonoDeriv fc (Formula.and b χ_gen) γ'
              (Formula.and β' xi) h_bχ_to_β'xi
            have h_chain := impTrans h_ev_untl_γ' h_left
            exact DerivationTree.modus_ponens _ _ _
              (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
              (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, Set.mem_union, Set.mem_setOf_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta h2
            · exact h_comp5 h5
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivationFromImplied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_P_mem fc h_mcs_C event h_P_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain.
  intro b hb h_b_beta0 α_hat hα h_α_alpha0 gamma_list h_gammas
  have h_snce_ba : Formula.snce b α_hat ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := self_accum_since_mcs fc h_mcs_C b α_hat h_snce_ba
  let φ_gen := Formula.and b (Formula.snce b α_hat)
  let χ_gen := Formula.and xi (Formula.snce xi eta)
  have h_bx7_gen := linear_since_mcs fc h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_guard_to_b0xi : DerivationTree fc [] ((Formula.and φ_gen χ_gen).imp (Formula.and beta0 xi)) := by
    have h1 : DerivationTree fc [] _ := impTrans (impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.snce b α_hat))) h_b_beta0
    have h2 : DerivationTree fc [] _ := impTrans (rceImp φ_gen χ_gen) (lceImp xi (Formula.snce xi eta))
    exact combineImpConj h1 h2
  have h_guard_to_alpha0 : DerivationTree fc [] ((Formula.and α_hat eta).imp alpha0) :=
    impTrans (lceImp α_hat eta) h_α_alpha0
  have h_D3_gen : Formula.snce (Formula.and φ_gen χ_gen) (Formula.and φ_gen eta) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and α_hat eta).imp alpha0) := h_guard_to_alpha0
      have h_contra := right_mono_since_mcs fc h_mcs_C h_rm
        (snce_left_mono_thm fc h_mcs_C h_guard_to_b0xi h_D1)
      exact SetMaximalConsistent.neg_excludes h_mcs_C _ h_neg_since_in_C h_contra
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and α_hat χ_gen).imp alpha0) :=
        impTrans (lceImp α_hat χ_gen) h_α_alpha0
      have h_contra := right_mono_since_mcs fc h_mcs_C h_rm
        (snce_left_mono_thm fc h_mcs_C h_guard_to_b0xi h_D2)
      exact SetMaximalConsistent.neg_excludes h_mcs_C _ h_neg_since_in_C h_contra
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichmentSince fc h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.event'
  have h_P_event : Formula.somePast event ∈ C := since_implies_P_mcs fc h_mcs_C evt.hSnce
  have h_ev_base := evt.hImpl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.snce b α_hat)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_snce_ba : DerivationTree fc [] (event.imp (Formula.snce b α_hat)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.snce b α_hat)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      DerivationTree fc [] (event.imp (Formula.untl (Formula.and b χ_gen) γ)) := by
    intro γ hγ
    have h_untl_guard := evt.hUntl γ hγ
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.snce b α_hat))
      have h2 : DerivationTree fc [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_untl_guard (untlLeftMonoDeriv fc guard γ (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.7'** (Since direction, Burgess 1982): Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and xi ∉ B, construct MCS D with eta ∈ D splitting the R3 pair.

Mirror of lemma_2_7 fc using BX5'+BX7'+BX13' instead of BX5+BX7+BX13. -/
theorem lemma_2_7_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce xi eta ∈ C)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_7_since_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_xi_not_B
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27SinceSeed A B C xi eta
    simp [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27SinceSeed A B C xi eta; simp [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl β γ ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce β α ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Extract untl(γ, β∧xi) ∈ D from the 3rd seed component
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl (Formula.and β xi) γ ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show Formula.untl (Formula.and β xi) γ ∈ lemma27SinceSeed A B C xi eta
    simp only [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, Set.mem_union, Set.mem_setOf_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  -- Derive untl(γ, xi) ∈ D via left_mono
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, Formula.untl xi γ ∈ D := by
    intro γ hγ
    have hImpl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rceImp β₀ xi
    exact untl_left_mono_thm fc h_D_mcs hImpl (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince C xi D :=
    burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C h_burgessR_xi
  -- Guard conjunction + DC(B ∪ {xi}) Zorn seed for B'' with xi ∈ B''
  have h_burgessR_conj : ∀ β ∈ B, burgessR D (Formula.and β xi) C := by
    intro β hβ
    exact burgessR_conj fc h_D_mcs (h_rSet_D β hβ) h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, Formula.snce (Formula.and β xi) δ ∈ C := by
    intro β hβ δ hδ
    have h_rSince := burgessRSince_conj fc h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi
    exact h_rSince δ hδ
  have h_r3_DC_DBC : burgessR3 D (deductiveClosure fc ({xi} ∪ B)) C :=
    dc_delta_B_burgessR3 fc h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  obtain ⟨B', h_B_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B''⟩

/-- **Lemma 2.8' seed consistency** (Since direction): Same seed as lemma_2_7_since,
but consistency proved using ¬(eta ∨ (xi ∧ snce(xi,eta))) ∈ A instead of xi ∉ B. -/
private theorem lemma_2_8_since_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce xi eta ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg ∈ A) :
    SetConsistent fc (lemma27SinceSeed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set α' := (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg with α'_def
  have h_α'_to_neg_eta : DerivationTree fc [] (α'.imp eta.neg) :=
    impTrans (liftBase fc (demorganDisjNegForward eta (Formula.and xi (Formula.snce xi eta))))
      (lceImp eta.neg (Formula.and xi (Formula.snce xi eta)).neg)
  have h_α'_to_neg_chi : DerivationTree fc [] (α'.imp (Formula.and xi (Formula.snce xi eta)).neg) :=
    impTrans (liftBase fc (demorganDisjNegForward eta (Formula.and xi (Formula.snce xi eta))))
      (rceImp eta.neg (Formula.and xi (Formula.snce xi eta)).neg)
  have h_bx5_xe := self_accum_since_mcs fc h_mcs_C xi eta h_since
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (α_hat : Formula Atom) (hα : α_hat ∈ A) (h_α_to_α' : DerivationTree fc [] (α_hat.imp α'))
      (gamma_list : List (Formula Atom)) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : Formula Atom),
        Formula.somePast event ∈ C ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.snce b α_hat)) ×'
        (∀ γ ∈ gamma_list, DerivationTree fc [] (event.imp (Formula.untl (Formula.and b (Formula.and xi (Formula.snce xi eta))) γ))) by
    intro L hL ⟨d⟩
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    -- Extract B-guards and C-events from L
    let b_list_5 := l27sB5GuardList B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem hg
    let c_list := l27sC5EventList B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem hγ
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := (Formula.bot.imp Formula.bot) :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact cud_contains_theorems h_B_dcs (identity (Formula.bot : Formula Atom))
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List (Formula Atom) := [α']
    have ha_list : ∀ α_elem ∈ a_list, α_elem ∈ A := by
      intro α_elem hα_elem; simp [a_list] at hα_elem; subst hα_elem; exact h_neg_disj
    let b := listConj fc b_list
    let α_hat := listConj fc a_list
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := list_conj_mem_mcs fc h_mcs_A a_list ha_list
    have h_αhat_to_α' : DerivationTree fc [] (α_hat.imp α') :=
      listConjImpliesElem fc a_list α' (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B α_hat hα_A h_αhat_to_α' c_list hc_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.snce xi eta)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := listConjImpliesElem fc b_list φ h_φ_in_b
        have h_ev_to_φ := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta_case : φ = eta
        · subst h_eta_case
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl (Formula.and β' xi) γ'
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = Formula.untl (Formula.and β' xi) γ' :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : Formula.untl (Formula.and β' xi) γ' ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := listConjImpliesElem fc b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : DerivationTree fc [] ((Formula.and b χ_gen).imp
                (Formula.and β' xi)) := by
              have h1 := impTrans (lceImp b χ_gen) h_b_to_β'
              have h2 : DerivationTree fc [] ((Formula.and b χ_gen).imp xi) :=
                impTrans (rceImp b χ_gen) (lceImp xi (Formula.snce xi eta))
              exact combineImpConj h1 h2
            have h_left := untlLeftMonoDeriv fc (Formula.and b χ_gen) γ'
              (Formula.and β' xi) h_bχ_to_β'xi
            have h_chain := impTrans h_ev_untl_γ' h_left
            exact DerivationTree.modus_ponens _ _ _
              (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
              (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, Set.mem_union, Set.mem_setOf_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta_case h2
            · exact h_comp5 h5
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivationFromImplied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_P_mem fc h_mcs_C event h_P_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain with D1/D2 eliminated via α'
  intro b hb α_hat hα h_α_to_α' gamma_list h_gammas
  have h_snce_ba : Formula.snce b α_hat ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := self_accum_since_mcs fc h_mcs_C b α_hat h_snce_ba
  let φ_gen := Formula.and b (Formula.snce b α_hat)
  let χ_gen := Formula.and xi (Formula.snce xi eta)
  have h_bx7_gen := linear_since_mcs fc h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_D3_gen : Formula.snce (Formula.and φ_gen χ_gen) (Formula.and φ_gen eta) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and α_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and α_hat eta).imp eta.neg) :=
          impTrans (lceImp α_hat eta) (impTrans h_α_to_α' h_α'_to_neg_eta)
        have h2 : DerivationTree fc [] _ := rceImp α_hat eta
        let PConj := Formula.and α_hat eta
        have d1 : DerivationTree fc [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs fc h_mcs_C h_event_to_bot
        (since_implies_P_mcs fc h_mcs_C h_D1)
      have h_H_top : Formula.allPast (Formula.bot.imp Formula.bot) ∈ C :=
        theoremInMcsFc h_mcs_C (Cslib.Logic.Bimodal.Theorems.pastNecessitation _
          (identity (Formula.bot : Formula Atom)))
      exact somePast_allPast_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and α_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and α_hat χ_gen).imp χ_gen.neg) :=
          impTrans (lceImp α_hat χ_gen) (impTrans h_α_to_α' h_α'_to_neg_chi)
        have h2 : DerivationTree fc [] _ := rceImp α_hat χ_gen
        let PConj := Formula.and α_hat χ_gen
        have d1 : DerivationTree fc [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs fc h_mcs_C h_event_to_bot
        (since_implies_P_mcs fc h_mcs_C h_D2)
      have h_H_top : Formula.allPast (Formula.bot.imp Formula.bot) ∈ C :=
        theoremInMcsFc h_mcs_C (Cslib.Logic.Bimodal.Theorems.pastNecessitation _
          (identity (Formula.bot : Formula Atom)))
      exact somePast_allPast_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichmentSince fc h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.event'
  have h_P_event : Formula.somePast event ∈ C := since_implies_P_mcs fc h_mcs_C evt.hSnce
  have h_ev_base := evt.hImpl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.snce b α_hat)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_snce_ba : DerivationTree fc [] (event.imp (Formula.snce b α_hat)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.snce b α_hat)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      DerivationTree fc [] (event.imp (Formula.untl (Formula.and b χ_gen) γ)) := by
    intro γ hγ
    have h_untl_guard := evt.hUntl γ hγ
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.snce b α_hat))
      have h2 : DerivationTree fc [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_untl_guard (untlLeftMonoDeriv fc guard γ (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.8'** (Since direction, Burgess 1982): Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A, construct MCS D
with eta ∈ D splitting the R3 pair. Returns xi ∈ B'' via DC(B∪{xi}) Zorn seed. -/
theorem lemma_2_8_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce xi eta ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg ∈ A) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_8_since_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_neg_disj
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27SinceSeed A B C xi eta
    simp [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27SinceSeed A B C xi eta; simp [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl β γ ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce β α ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Extract untl(γ, β∧xi) ∈ D from the 3rd seed component
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl (Formula.and β xi) γ ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show Formula.untl (Formula.and β xi) γ ∈ lemma27SinceSeed A B C xi eta
    simp only [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, Set.mem_union, Set.mem_setOf_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, Formula.untl xi γ ∈ D := by
    intro γ hγ
    have hImpl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rceImp β₀ xi
    exact untl_left_mono_thm fc h_D_mcs hImpl (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince C xi D :=
    burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, Formula.snce (Formula.and β xi) δ ∈ C := by
    intro β hβ δ hδ
    exact (burgessRSince_conj fc h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi) δ hδ
  have h_r3_DC_DBC : burgessR3 D (deductiveClosure fc ({xi} ∪ B)) C :=
    dc_delta_B_burgessR3 fc h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  obtain ⟨B', h_B_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B''⟩

/-! ## Lemma 2.4 with Guard: Enriched Seed Version (Burgess 2.4)

Strengthens `lemma24` to additionally return `γ ∈ B` (guard membership in the
interval DCS). This matches Burgess 1982, Lemma 2.4 exactly: "there exist B, C
such that β ∈ B, γ ∈ C, and R(A,B,C)". In our convention, γ is the guard
(first arg of untl) and β is the event (second arg).

The enriched seed `{β} ∪ gContent(A) ∪ {snce(γ, α) : α ∈ A}` ensures the
Lindenbaum extension C satisfies burgessRSince(C, γ, A), enabling
`burgessR3Maximal_with_guard` to produce B with γ ∈ B. -/

/-- **Enriched Until witness seed consistency**: {β} ∪ gContent(A) ∪ {snce(γ, α) : α ∈ A}
is consistent when untl(γ,β) ∈ MCS A.

Proof (Burgess 2.4): For any finite L ⊆ seed with L ⊢ ⊥, extract α-witnesses
from Since-obligations, form α* ∈ A, apply BX13 enrichment to get
F(β ∧ snce(γ, α*)) ∈ A, then derive ⊥ from {β ∧ snce(γ, α*)} ∪ gContent(A),
contradicting forward_temporal_witness_seed_consistent. -/
private theorem until_witness_enriched_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl γ β ∈ A) :
    SetConsistent fc ({β} ∪ gContent A ∪ {φ | ∃ α ∈ A, φ = Formula.snce γ α}) := by
  intro L hL ⟨d⟩
  have h_extract : ∀ φ ∈ L, (φ ∈ {β} ∪ gContent A) ∨ (∃ α ∈ A, φ = Formula.snce γ α) := by
    intro φ hφ
    have := hL φ hφ
    simp only [Set.mem_union] at this
    rcases this with (h | h) | h
    · exact Or.inl (Set.mem_union_left _ h)
    · exact Or.inl (Set.mem_union_right _ h)
    · exact Or.inr h
  haveI : ∀ φ : Formula Atom, Decidable (∃ α ∈ A, φ = Formula.snce γ α) :=
    fun φ => Classical.dec _
  let get_alpha : Formula Atom → Option (Formula Atom) := fun φ =>
    if h : ∃ α ∈ A, φ = Formula.snce γ α then some h.choose else none
  let alpha_list := L.filterMap get_alpha
  have h_get_alpha_some : ∀ (φ α : Formula Atom),
      get_alpha φ = some α → α ∈ A ∧ φ = Formula.snce γ α := by
    intro φ α hga
    simp only [get_alpha] at hga
    split at hga
    · rename_i h_ex; simp at hga; subst hga
      exact ⟨h_ex.choose_spec.1, h_ex.choose_spec.2⟩
    · simp at hga
  have h_alphas_in_A : ∀ α ∈ alpha_list, α ∈ A := by
    intro α hα
    simp only [alpha_list, List.mem_filterMap] at hα
    obtain ⟨φ, _, hga⟩ := hα
    exact (h_get_alpha_some φ α hga).1
  have h_since_extracted : ∀ φ ∈ L, (∃ α ∈ A, φ = Formula.snce γ α) →
      ∃ α ∈ alpha_list, φ = Formula.snce γ α := by
    intro φ hφ h_ex
    have h_ga_ne_none : get_alpha φ ≠ none := by
      simp only [get_alpha, dif_pos h_ex]; exact Option.some_ne_none _
    obtain ⟨α', hα'⟩ := Option.ne_none_iff_exists'.mp h_ga_ne_none
    have ⟨hα'_A, hφ_eq'⟩ := h_get_alpha_some φ α' hα'
    exact ⟨α', List.mem_filterMap.mpr ⟨φ, hφ, hα'⟩, hφ_eq'⟩
  by_cases h_empty : alpha_list = []
  · have hL' : ∀ φ ∈ L, φ ∈ {β} ∪ gContent A := by
      intro φ hφ
      rcases h_extract φ hφ with h_cov | h_since
      · exact h_cov
      · exfalso
        obtain ⟨α, hα_list, _⟩ := h_since_extracted φ hφ h_since
        rw [h_empty] at hα_list; simp at hα_list
    exact until_witness_seed_consistent fc h_mcs γ β h_until L hL' ⟨d⟩
  · set α_star := listConj fc alpha_list
    have hα_star_A : α_star ∈ A := list_conj_mem_mcs fc h_mcs alpha_list h_alphas_in_A
    have h_enriched := enrichment_until_mcs fc h_mcs hα_star_A h_until
    have h_F := until_implies_F_mcs fc h_mcs h_enriched
    set ψ_star := Formula.and β (Formula.snce γ α_star)
    have h_cons := forward_temporal_witness_seed_consistent A h_mcs ψ_star h_F
    suffices h_derives : ∀ φ ∈ L, φ ∈ gContent A ∨
        (Nonempty (DerivationTree fc [] (ψ_star.imp φ))) by
      haveI : DecidablePred (· ∈ gContent A) := fun φ => Classical.dec _
      let Γ := L.map (fun φ => if φ ∈ gContent A then φ else ψ_star)
      have hΓ_sub : ∀ ψ ∈ Γ, ψ ∈ {ψ_star} ∪ gContent A := by
        intro ψ hψ
        simp only [Γ, List.mem_map] at hψ
        obtain ⟨φ, _, hψ_eq⟩ := hψ
        split at hψ_eq
        · subst hψ_eq; exact Set.mem_union_right _ ‹_›
        · subst hψ_eq; exact Set.mem_union_left _ (Set.mem_singleton ψ_star)
      have h_L_from_Γ : ∀ φ ∈ L, DerivationTree fc Γ φ := by
        intro φ hφ
        have h_d := h_derives φ hφ
        by_cases h_gc : φ ∈ gContent A
        · exact DerivationTree.assumption Γ φ
            (List.mem_map.mpr ⟨φ, hφ, by simp [h_gc]⟩)
        · have h_ne : Nonempty (DerivationTree fc [] (ψ_star.imp φ)) := by
            rcases h_d with h | h
            · exact absurd h h_gc
            · exact h
          let hImpl := h_ne.some
          have hψ_in_Γ : ψ_star ∈ Γ := by
            simp only [Γ, List.mem_map]
            exact ⟨φ, hφ, by simp [h_gc]⟩
          exact DerivationTree.modus_ponens Γ _ _
            (DerivationTree.weakening [] Γ _ hImpl (List.nil_subset _))
            (DerivationTree.assumption Γ ψ_star hψ_in_Γ)
      exact h_cons Γ hΓ_sub ⟨derivationFromImplied fc Γ L Formula.bot h_L_from_Γ d⟩
    intro φ hφ
    rcases h_extract φ hφ with h_cov | h_since
    · simp only [Set.mem_union, Set.mem_singleton_iff] at h_cov
      rcases h_cov with h_eq | h_gc
      · rw [h_eq]
        exact Or.inr ⟨lceImp β (Formula.snce γ α_star)⟩
      · exact Or.inl h_gc
    · obtain ⟨α, hα_list, hφ_eq⟩ := h_since_extracted φ hφ h_since
      rw [hφ_eq]
      have h_proj := listConjImpliesElem fc alpha_list α hα_list
      have h_H_proj := Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_proj
      have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since α_star α γ) trivial
      have h_snce_mono : DerivationTree fc [] ((Formula.snce γ α_star).imp (Formula.snce γ α)) :=
        mp h_H_proj h_bx3'
      exact Or.inr ⟨impTrans (rceImp β (Formula.snce γ α_star)) h_snce_mono⟩

/-- **Lemma 2.4 with guard** (Burgess 2.4, full version): Given MCS A with
untl(γ, β) ∈ A, there exist B, C such that β ∈ C, gContent(A) ⊆ C,
γ ∈ B, and BurgessR3Maximal(A, B, C).

This strengthens `lemma24` by additionally returning `γ ∈ B`. The guard
membership follows from enriching the seed with Since-obligations
{snce(γ, α) : α ∈ A}, which gives burgessRSince(C, γ, A), then applying
burgessR3Maximal_with_guard (RRelation.lean). -/
lemma lemma24WithGuard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl γ β ∈ A) :
    ∃ B C : Set (Formula Atom), SetMaximalConsistent fc C ∧
      β ∈ C ∧ gContent A ⊆ C ∧
      Formula.somePast (Formula.untl γ β) ∈ C ∧
      γ ∈ B ∧ BurgessR3Maximal fc A B C := by
  have h_seed_cons := until_witness_enriched_seed_consistent fc h_mcs γ β h_until
  obtain ⟨C, h_sup, h_C_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- β ∈ C from seed
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton β)))
  -- gContent(A) ⊆ C from seed
  have h_g_sub : gContent A ⊆ C := fun χ hχ =>
    h_sup (Set.mem_union_left _ (Set.mem_union_right _ hχ))
  -- P(untl(γ,β)) ∈ C from gContent
  have h_GP : Formula.allFuture (Formula.somePast (Formula.untl γ β)) ∈ A := by
    have h_ax : DerivationTree fc [] ((Formula.untl γ β).imp
        (Formula.allFuture (Formula.somePast (Formula.untl γ β)))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl γ β)) trivial
    exact SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs h_ax) h_until
  have h_P_until_C : Formula.somePast (Formula.untl γ β) ∈ C := h_g_sub h_GP
  -- snce(γ, α) ∈ C for all α ∈ A (from Since-obligation part of enriched seed)
  have h_burgessRSince : burgessRSince C γ A := by
    intro α hα
    exact h_sup (Set.mem_union_right _ ⟨α, hα, rfl⟩)
  -- burgessR(A, γ, C) from burgessRSince via Lemma 2.3 backward
  have h_burgessR := burgessRSince_implies_burgessR fc h_mcs h_C_mcs h_burgessRSince
  -- B with γ ∈ B and BurgessR3Maximal(A, B, C)
  obtain ⟨B, h_γ_B, h_r3m⟩ := burgessR3Maximal_with_guard fc A C γ h_mcs h_C_mcs
    h_burgessR h_burgessRSince
  exact ⟨B, C, h_C_mcs, h_β_C, h_g_sub, h_P_until_C, h_γ_B, h_r3m⟩

/-! ## Lemma 2.4 Since with Guard (Burgess 2.4, backward direction)

Mirror of `lemma24WithGuard` for the Since direction. Given snce(γ,β) ∈ A (MCS),
produces C, B such that β ∈ C, hContent(A) ⊆ C, γ ∈ B, BurgessR3Maximal(C, B, A).

The enriched seed `{β} ∪ hContent(A) ∪ {untl(γ, α) : α ∈ A}` ensures
burgessR(C, γ, A), then `burgessR_implies_burgessRSince` gives
burgessRSince(A, γ, C), enabling `burgessR3Maximal_with_guard C A γ`. -/

/-- **Enriched Since witness seed consistency**: `{β} ∪ hContent(A) ∪ {untl(γ, α) : α ∈ A}`
is consistent when `snce(γ,β) ∈ MCS A`.

Proof (mirror of until_witness_enriched_seed_consistent): For finite L ⊆ seed with L ⊢ ⊥,
extract α-witnesses from Until-obligations, form α*, apply enrichment_since to get
P(β ∧ untl(γ, α*)) ∈ A, then derive ⊥ from `{β ∧ untl(γ, α*)} ∪ hContent(A)`,
contradicting past_temporal_witness_seed_consistent. -/
private theorem since_witness_enriched_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_since : Formula.snce γ β ∈ A) :
    SetConsistent fc ({β} ∪ hContent A ∪ {φ | ∃ α ∈ A, φ = Formula.untl γ α}) := by
  intro L hL ⟨d⟩
  have h_extract : ∀ φ ∈ L, (φ ∈ {β} ∪ hContent A) ∨ (∃ α ∈ A, φ = Formula.untl γ α) := by
    intro φ hφ
    have := hL φ hφ
    simp only [Set.mem_union] at this
    rcases this with (h | h) | h
    · exact Or.inl (Set.mem_union_left _ h)
    · exact Or.inl (Set.mem_union_right _ h)
    · exact Or.inr h
  haveI : ∀ φ : Formula Atom, Decidable (∃ α ∈ A, φ = Formula.untl γ α) :=
    fun φ => Classical.dec _
  let get_alpha : Formula Atom → Option (Formula Atom) := fun φ =>
    if h : ∃ α ∈ A, φ = Formula.untl γ α then some h.choose else none
  let alpha_list := L.filterMap get_alpha
  have h_get_alpha_some : ∀ (φ α : Formula Atom),
      get_alpha φ = some α → α ∈ A ∧ φ = Formula.untl γ α := by
    intro φ α hga
    simp only [get_alpha] at hga
    split at hga
    · rename_i h_ex; simp at hga; subst hga
      exact ⟨h_ex.choose_spec.1, h_ex.choose_spec.2⟩
    · simp at hga
  have h_alphas_in_A : ∀ α ∈ alpha_list, α ∈ A := by
    intro α hα
    simp only [alpha_list, List.mem_filterMap] at hα
    obtain ⟨φ, _, hga⟩ := hα
    exact (h_get_alpha_some φ α hga).1
  have h_untl_extracted : ∀ φ ∈ L, (∃ α ∈ A, φ = Formula.untl γ α) →
      ∃ α ∈ alpha_list, φ = Formula.untl γ α := by
    intro φ hφ h_ex
    have h_ga_ne_none : get_alpha φ ≠ none := by
      simp only [get_alpha, dif_pos h_ex]; exact Option.some_ne_none _
    obtain ⟨α', hα'⟩ := Option.ne_none_iff_exists'.mp h_ga_ne_none
    have ⟨hα'_A, hφ_eq'⟩ := h_get_alpha_some φ α' hα'
    exact ⟨α', List.mem_filterMap.mpr ⟨φ, hφ, hα'⟩, hφ_eq'⟩
  by_cases h_empty : alpha_list = []
  · have hL' : ∀ φ ∈ L, φ ∈ {β} ∪ hContent A := by
      intro φ hφ
      rcases h_extract φ hφ with h_cov | hUntl
      · exact h_cov
      · exfalso
        obtain ⟨α, hα_list, _⟩ := h_untl_extracted φ hφ hUntl
        rw [h_empty] at hα_list; simp at hα_list
    exact past_temporal_witness_seed_consistent A h_mcs β
      (since_implies_P_in_mcs fc h_mcs h_since) L hL' ⟨d⟩
  · set α_star := listConj fc alpha_list
    have hα_star_A : α_star ∈ A := list_conj_mem_mcs fc h_mcs alpha_list h_alphas_in_A
    have h_enriched := enrichment_since_mcs fc h_mcs hα_star_A h_since
    -- enrichment_since gives: snce(γ, β ∧ untl(γ, α_star)) ∈ A
    -- since_implies_P gives: P(β ∧ untl(γ, α_star)) ∈ A
    have h_P := since_implies_P_mcs fc h_mcs h_enriched
    set ψ_star := Formula.and β (Formula.untl γ α_star)
    have h_cons := past_temporal_witness_seed_consistent A h_mcs ψ_star h_P
    suffices h_derives : ∀ φ ∈ L, φ ∈ hContent A ∨
        (Nonempty (DerivationTree fc [] (ψ_star.imp φ))) by
      haveI : DecidablePred (· ∈ hContent A) := fun φ => Classical.dec _
      let Γ := L.map (fun φ => if φ ∈ hContent A then φ else ψ_star)
      have hΓ_sub : ∀ ψ ∈ Γ, ψ ∈ {ψ_star} ∪ hContent A := by
        intro ψ hψ
        simp only [Γ, List.mem_map] at hψ
        obtain ⟨φ, _, hψ_eq⟩ := hψ
        split at hψ_eq
        · subst hψ_eq; exact Set.mem_union_right _ ‹_›
        · subst hψ_eq; exact Set.mem_union_left _ (Set.mem_singleton ψ_star)
      have h_L_from_Γ : ∀ φ ∈ L, DerivationTree fc Γ φ := by
        intro φ hφ
        have h_d := h_derives φ hφ
        by_cases h_hc : φ ∈ hContent A
        · exact DerivationTree.assumption Γ φ
            (List.mem_map.mpr ⟨φ, hφ, by simp [h_hc]⟩)
        · have h_ne : Nonempty (DerivationTree fc [] (ψ_star.imp φ)) := by
            rcases h_d with h | h
            · exact absurd h h_hc
            · exact h
          let hImpl := h_ne.some
          have hψ_in_Γ : ψ_star ∈ Γ := by
            simp only [Γ, List.mem_map]
            exact ⟨φ, hφ, by simp [h_hc]⟩
          exact DerivationTree.modus_ponens Γ _ _
            (DerivationTree.weakening [] Γ _ hImpl (List.nil_subset _))
            (DerivationTree.assumption Γ ψ_star hψ_in_Γ)
      exact h_cons Γ hΓ_sub ⟨derivationFromImplied fc Γ L Formula.bot h_L_from_Γ d⟩
    intro φ hφ
    rcases h_extract φ hφ with h_cov | h_untl_case
    · simp only [Set.mem_union, Set.mem_singleton_iff] at h_cov
      rcases h_cov with h_eq | h_hc
      · rw [h_eq]
        exact Or.inr ⟨lceImp β (Formula.untl γ α_star)⟩
      · exact Or.inl h_hc
    · obtain ⟨α, hα_list, hφ_eq⟩ := h_untl_extracted φ hφ h_untl_case
      rw [hφ_eq]
      have h_proj := listConjImpliesElem fc alpha_list α hα_list
      -- G(α_star → α) gives untl(γ, α_star) → untl(γ, α) via BX3 (right_mono_until)
      have h_G_proj := DerivationTree.temporal_necessitation _ h_proj
      have h_bx2 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until α_star α γ) trivial
      have h_untl_mono : DerivationTree fc [] ((Formula.untl γ α_star).imp (Formula.untl γ α)) :=
        mp h_G_proj h_bx2
      exact Or.inr ⟨impTrans (rceImp β (Formula.untl γ α_star)) h_untl_mono⟩

/-- **Lemma 2.4 Since with guard** (Burgess 2.4, backward direction): Given MCS A with
snce(γ, β) ∈ A, there exist B, C such that β ∈ C, hContent(A) ⊆ C,
γ ∈ B, and BurgessR3Maximal(C, B, A).

This is the Since mirror of `lemma24WithGuard`. The guard membership
follows from enriching the seed with Until-obligations
{untl(γ, α) : α ∈ A}, which gives burgessR(C, γ, A), then
burgessR_implies_burgessRSince fc and burgessR3Maximal_with_guard. -/
lemma lemma24SinceWithGuard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_since : Formula.snce γ β ∈ A) :
    ∃ B C : Set (Formula Atom), SetMaximalConsistent fc C ∧
      β ∈ C ∧ hContent A ⊆ C ∧
      γ ∈ B ∧ BurgessR3Maximal fc C B A := by
  have h_seed_cons := since_witness_enriched_seed_consistent fc h_mcs γ β h_since
  obtain ⟨C, h_sup, h_C_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- β ∈ C from seed
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton β)))
  -- hContent(A) ⊆ C from seed
  have h_h_sub : hContent A ⊆ C := fun χ hχ =>
    h_sup (Set.mem_union_left _ (Set.mem_union_right _ hχ))
  -- burgessR(C, γ, A): ∀ α ∈ A, untl(γ, α) ∈ C (from Until-obligations in seed)
  have h_burgessR : burgessR C γ A := by
    intro α hα
    exact h_sup (Set.mem_union_right _ ⟨α, hα, rfl⟩)
  -- burgessRSince(A, γ, C) from burgessR via Lemma 2.3 forward
  have h_burgessRSince := burgessR_implies_burgessRSince fc h_C_mcs h_mcs h_burgessR
  -- B with γ ∈ B and BurgessR3Maximal(C, B, A)
  obtain ⟨B, h_γ_B, h_r3m⟩ := burgessR3Maximal_with_guard fc C A γ h_C_mcs h_mcs
    h_burgessR h_burgessRSince
  exact ⟨B, C, h_C_mcs, h_β_C, h_h_sub, h_γ_B, h_r3m⟩


end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

end
