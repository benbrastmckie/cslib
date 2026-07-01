/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Splitting
public import Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency

/-! # Since — Enriched Lemma 2.4 and Since-Direction Mirrors

Lemma 2.4 with guard (enriched version), Since-direction mirrors of Lemma 2.7/2.8,
and the final Lemma 2.4 Since-direction with guard.

## Main Results

- `lemma24WithGuard`: Strengthened Lemma 2.4 with guard membership in the DCS interval
- `lemma_2_7_since`: Since-direction mirror of Lemma 2.7
- `lemma_2_8_since`: Since-direction mirror of Lemma 2.8
- `lemma24SinceWithGuard`: Strengthened Lemma 2.4 for Since direction with guard
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

/-! ## Lemma 2.4 with Guard (Enriched Version) -/

/-- **Lemma 2.4 with guard**: Strengthened version of lemma24 that additionally
returns γ ∈ B (guard membership in the interval DCS). -/
lemma lemma24WithGuard {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (γ U β) ∈ A) :
    ∃ B C : Set (Formula Atom), Temporal.SetMaximalConsistent C ∧
      β ∈ C ∧ gContent A ⊆ C ∧
      BurgessR3Maximal A B C ∧
      γ ∈ B := by
  obtain ⟨B₀, C, h_C_mcs, h_β_C, h_g_sub, _, h_R3M₀⟩ := lemma24 h_mcs γ β h_until
  -- Check if γ is already in B₀
  by_cases h_γ_B₀ : γ ∈ B₀
  · exact ⟨B₀, C, h_C_mcs, h_β_C, h_g_sub, h_R3M₀, h_γ_B₀⟩
  · -- γ ∉ B₀: use lemma_2_7 to split and get B' with γ ∈ B'.
    obtain ⟨B', D, B'', h_R3M_AB'D, _, h_D_mcs, h_eta_D, h_B₀_sub_B', h_B₀_sub_D, _, h_γ_B'⟩ :=
      lemma_2_7 h_mcs h_C_mcs h_R3M₀ h_R3M₀.1 h_g_sub γ β h_until h_γ_B₀
    have h_g_sub_D : gContent A ⊆ D := by
      have h_gc_B₀ := g_content_sub h_mcs h_C_mcs h_R3M₀
      exact Set.Subset.trans h_gc_B₀ h_B₀_sub_D
    exact ⟨B', D, h_D_mcs, h_eta_D, h_g_sub_D, h_R3M_AB'D, h_γ_B'⟩

/-! ## Phase 4: Since-Direction Mirrors -/

/-- The `SinceSeedInterface` instance for Temporal (task 454): populates every field of the
shared Foundations interface with Temporal's own apparatus at `FrameClass.Base`. Used to
delegate to the generic `lemma27SinceSeed`/`l27s*` helpers
(`Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`) instead of duplicating
them locally (task-454 Phase 1). -/
private noncomputable def temporalSinceInterface : Cslib.Logic.Metalogic.Chronicle.SinceSeedInterface (Formula Atom) where
  bot := Formula.bot
  imp := Formula.imp
  and := Formula.and
  untl := Formula.untl
  snce := Formula.snce
  somePast := Formula.somePast
  allPast := Formula.allPast
  allFuture := Formula.allFuture
  Deriv := DerivationTree FrameClass.Base
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
  identity' := fun φ => identity' φ
  impTrans := fun h1 h2 => impTrans h1 h2
  lceImp := fun φ ψ => lceImp φ ψ
  rceImp := fun φ ψ => rceImp φ ψ
  combineImpConj := fun h1 h2 => combineImpConj h1 h2
  untlLeftMonoDeriv := fun g1 e g2 h => untlLeftMonoDeriv g1 e g2 h
  pastNecessitation := fun φ d => pastNecessitation φ d
  theoremInMcs := by intro _ hmcs _ hd; exact theoremInMcs hmcs hd
  negationComplete := fun hmcs φ => temporal_negation_complete hmcs φ
  negExcludes := by intro _ hmcs _ hneg hmem; exact mcs_not_mem_of_neg hmcs hneg hmem
  cudContainsTheorems := by intro _ hcud _ hd; exact cud_contains_theorems hcud hd
  selfAccumSinceMcs := fun hmcs γ β h => self_accum_since_mcs hmcs γ β h
  linearSinceMcs := fun hmcs φ ψ χ θ h1 h2 => linear_since_mcs hmcs φ ψ χ θ h1 h2
  rightMonoSinceMcs := by intro _ hmcs _ _ _ hi hs; exact right_mono_since_mcs hmcs hi hs
  sinceImpliesP := by intro _ hmcs _ _ h; exact since_implies_P_in_mcs hmcs h
  consistentOfPMem := fun hmcs φ h => consistent_of_P_mem hmcs φ h
  inconsistentSingletonFalse := by intro _ hcons d; exact inconsistent_singleton_false hcons d
  derivationFromImplied := fun Γ L ψ h d => derivationFromImplied Γ L ψ h d
  dcDeltaBControlled := by intro _ hcud _ _ _ hLsub hd; exact dc_delta_B_controlled hcud hLsub hd
  iteratedEnrichmentSince := fun hmcs guard gammas hgammas event hsnce => by
    have evt := iteratedEnrichmentSince hmcs guard gammas hgammas event hsnce
    exact ⟨evt.event', evt.hSnce, evt.hImpl, evt.hUntl⟩
  xuLemma321Until := by
    intro _ _ _ hA hC hR3M beta hbeta gamma hgamma
    exact xu_lemma_3_2_1_until hA hC hR3M hbeta hgamma
  xuLemma321Since := by
    intro _ _ _ hA hC hR3M beta hbeta alpha halpha
    exact xu_lemma_3_2_1_since hA hC hR3M hbeta halpha
  burgessRImpliesBurgessRSince := by
    intro _ _ hA hC beta hR; exact burgessR_implies_burgessRSince hA hC hR
  burgessRSinceImpliesBurgessR := by
    intro _ _ hA hC beta hR; exact burgessRSince_implies_burgessR hA hC hR
  burgessRConj := by intro _ _ hA α β ha hb; exact burgessR_conj hA ha hb
  burgessRSinceConj := by intro _ _ hC α β ha hb; exact burgessRSince_conj hC ha hb
  burgessR3MaximalExtensionFails := by
    intro _ _ _ hR3M delta hnotmem; exact BurgessR3Maximal_extension_fails hR3M hnotmem
  dcDeltaBBurgessR3 := by
    intro _ _ _ hA hC hcud hr3 delta huntl hsince
    exact dc_delta_B_burgessR3 hA hC hcud hr3 huntl hsince
  burgessR3MaximalExtensionExists := by
    intro _ _ _ hA hC hcud hr3
    obtain ⟨B, hsub, hmax⟩ := burgessR3Maximal_extension_exists hA hC hcud hr3
    exact ⟨B, hsub, hmax⟩
  listConj := listConj
  listConjMemDcs := fun hcud L hL => list_conj_mem_dcs hcud L hL
  listConjMemMcs := fun hmcs L hL => list_conj_mem_mcs hmcs L hL
  listConjImpliesElem := fun L φ h => listConjImpliesElem L φ h
  untlLeftMonoThm := by intro _ hmcs _ _ _ hi hu; exact untl_left_mono_thm hmcs hi hu
  snceLeftMonoThm := by intro _ hmcs _ _ _ hi hs; exact snce_left_mono_thm hmcs hi hs
  lindenbaum := by intro _ hcons; exact temporal_lindenbaum hcons

/-- Since-direction seed: B ∪ {eta} ∪ {untl(γ, β∧xi) | β∈B, γ∈C}. Relocated (task-454
Phase 1) to the shared `Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`
module; this is a thin alias fixing Temporal's interface instance. -/
@[nolint unusedArguments]
private def lemma27SinceSeed (_A B C : Set (Formula Atom)) (xi eta : Formula Atom) :
    Set (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed temporalSinceInterface _A B C xi eta

/-- Extract γ' events from component 3 elements of a list. Relocated (task-454 Phase 1). -/
private noncomputable def l27sC5EventList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sC5EventList temporalSinceInterface B C xi L

/-- Elements of l27sC5EventList are in C. Relocated (task-454 Phase 1). -/
private theorem l27s_c5_event_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {γ : Formula Atom} (hγ : γ ∈ l27sC5EventList B C xi L) : γ ∈ C :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_event_list_mem temporalSinceInterface hγ

/-- Extract β' guards from component 3 elements. Relocated (task-454 Phase 1). -/
private noncomputable def l27sB5GuardList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sB5GuardList temporalSinceInterface B C xi L

/-- Elements of l27sB5GuardList are in B. Relocated (task-454 Phase 1). -/
private theorem l27s_b5_guard_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β : Formula Atom} (hβ : β ∈ l27sB5GuardList B C xi L) : β ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_guard_list_mem temporalSinceInterface hβ

/-- For a component 3 element, the extracted γ' is in c5_event_list. Relocated
(task-454 Phase 1). -/
private theorem l27s_c5_γ_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    γ' ∈ l27sC5EventList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_γ_mem temporalSinceInterface hφ hβ' hγ'

/-- For a component 3 element, the extracted β' is in b5_guard_list. Relocated
(task-454 Phase 1). -/
private theorem l27s_b5_β_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    β' ∈ l27sB5GuardList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_β_mem temporalSinceInterface hφ hβ' hγ'

/-- Since-direction seed consistency. Uses BX5'+BX7'+BX13' chain. Delegates (task-454
Phase 2) to the generic `Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since_seed_consistent`. -/
private theorem lemma_2_7_since_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (xi S eta) ∈ C)
    (h_xi_not_B : xi ∉ B) :
    Temporal.SetConsistent (lemma27SinceSeed A B C xi eta) :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since_seed_consistent temporalSinceInterface
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_xi_not_B

/-- **Lemma 2.7 (Since direction)**: Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and xi ∉ B, construct MCS D with eta ∈ D splitting the R3 pair.
Returns xi ∈ B'' via DC(B ∪ {xi}) Zorn seed. Delegates (task-454 Phase 2) to the generic
`Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since`. -/
theorem lemma_2_7_since {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (xi S eta) ∈ C)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B'' :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since temporalSinceInterface
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_xi_not_B

/-- **Lemma 2.8 (Since direction) seed consistency**: Same seed as lemma_2_7_since
but with ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A instead of xi ∉ B. -/
private theorem lemma_2_8_since_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (xi S eta) ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg ∈ A) :
    Temporal.SetConsistent (lemma27SinceSeed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set α' := (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg with α'_def
  have h_α'_to_neg_eta : DerivationTree FrameClass.Base [] (α'.imp eta.neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.snce xi eta)))
      (lceImp eta.neg (Formula.and xi (Formula.snce xi eta)).neg)
  have h_α'_to_neg_chi : DerivationTree FrameClass.Base [] (α'.imp (Formula.and xi (Formula.snce xi eta)).neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.snce xi eta)))
      (rceImp eta.neg (Formula.and xi (Formula.snce xi eta)).neg)
  have h_bx5_xe := self_accum_since_mcs h_mcs_C xi eta h_since
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (α_hat : Formula Atom) (hα : α_hat ∈ A) (h_α_to_α' : DerivationTree FrameClass.Base [] (α_hat.imp α'))
      (gamma_list : List (Formula Atom)) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : Formula Atom),
        (𝐏event) ∈ C ×'
        DerivationTree FrameClass.Base [] (event.imp b) ×'
        DerivationTree FrameClass.Base [] (event.imp eta) ×'
        DerivationTree FrameClass.Base [] (event.imp (Formula.snce b α_hat)) ×'
        (∀ γ ∈ gamma_list, DerivationTree FrameClass.Base [] (event.imp (Formula.untl (Formula.and b (Formula.and xi (Formula.snce xi eta))) γ))) by
    intro L hL ⟨d⟩
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
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
      · exact cud_contains_theorems h_B_dcs (identity' (Formula.bot : Formula Atom))
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List (Formula Atom) := [α']
    have ha_list : ∀ α_elem ∈ a_list, α_elem ∈ A := by
      intro α_elem hα_elem; simp [a_list] at hα_elem; subst hα_elem; exact h_neg_disj
    let b := listConj b_list
    let α_hat := listConj a_list
    have hb_B : b ∈ B := list_conj_mem_dcs h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := list_conj_mem_mcs h_mcs_A a_list ha_list
    have h_αhat_to_α' : DerivationTree FrameClass.Base [] (α_hat.imp α') :=
      listConjImpliesElem a_list α' (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B α_hat hα_A h_αhat_to_α' c_list hc_list
    let χ_gen := Formula.and xi (Formula.snce xi eta)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree FrameClass.Base [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := listConjImpliesElem b_list φ h_φ_in_b
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
            have h_b_to_β' := listConjImpliesElem b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp
                (Formula.and β' xi)) := by
              have h1 := impTrans (lceImp b χ_gen) h_b_to_β'
              have h2 : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp xi) :=
                impTrans (rceImp b χ_gen) (lceImp xi (Formula.snce xi eta))
              exact combineImpConj h1 h2
            have h_left := untlLeftMonoDeriv (Formula.and b χ_gen) γ'
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
    have d_event : DerivationTree FrameClass.Base [event] Formula.bot :=
      derivationFromImplied [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_P_mem h_mcs_C event h_P_event
    exact inconsistent_singleton_false h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain with D1/D2 eliminated via α'
  intro b hb α_hat hα h_α_to_α' gamma_list h_gammas
  have h_snce_ba : (b S α_hat) ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := self_accum_since_mcs h_mcs_C b α_hat h_snce_ba
  let φ_gen := Formula.and b (Formula.snce b α_hat)
  let χ_gen := Formula.and xi (Formula.snce xi eta)
  have h_bx7_gen := linear_since_mcs h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_D3_gen : Formula.snce (Formula.and φ_gen χ_gen) (Formula.and φ_gen eta) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and α_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and α_hat eta).imp eta.neg) :=
          impTrans (lceImp α_hat eta) (impTrans h_α_to_α' h_α'_to_neg_eta)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp α_hat eta
        let PConj := Formula.and α_hat eta
        have d1 : DerivationTree FrameClass.Base [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs h_mcs_C h_event_to_bot (since_implies_P_in_mcs h_mcs_C h_D1)
      have h_H_top : Formula.allPast (Formula.bot.imp Formula.bot) ∈ C :=
        theoremInMcs h_mcs_C (pastNecessitation _ (identity' (Formula.bot : Formula Atom)))
      exact somePast_allPast_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and α_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and α_hat χ_gen).imp χ_gen.neg) :=
          impTrans (lceImp α_hat χ_gen) (impTrans h_α_to_α' h_α'_to_neg_chi)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp α_hat χ_gen
        let PConj := Formula.and α_hat χ_gen
        have d1 : DerivationTree FrameClass.Base [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs h_mcs_C h_event_to_bot (since_implies_P_in_mcs h_mcs_C h_D2)
      have h_H_top : Formula.allPast (Formula.bot.imp Formula.bot) ∈ C :=
        theoremInMcs h_mcs_C (pastNecessitation _ (identity' (Formula.bot : Formula Atom)))
      exact somePast_allPast_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichmentSince h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.event'
  have h_P_event : (𝐏event) ∈ C := since_implies_P_in_mcs h_mcs_C evt.hSnce
  have h_ev_base := evt.hImpl
  have h_ev_b : DerivationTree FrameClass.Base [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.snce b α_hat)))
  have h_ev_eta : DerivationTree FrameClass.Base [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_snce_ba : DerivationTree FrameClass.Base [] (event.imp (Formula.snce b α_hat)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.snce b α_hat)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      DerivationTree FrameClass.Base [] (event.imp (Formula.untl (Formula.and b χ_gen) γ)) := by
    intro γ hγ
    have h_untl_guard := evt.hUntl γ hγ
    have h_guard_to_bχ : DerivationTree FrameClass.Base [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.snce b α_hat))
      have h2 : DerivationTree FrameClass.Base [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_untl_guard (untlLeftMonoDeriv guard γ (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.8 (Since direction)**: Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A. -/
theorem lemma_2_8_since {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (xi S eta) ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg ∈ A) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_8_since_seed_consistent h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_neg_disj
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27SinceSeed A B C xi eta
    simp [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27SinceSeed A B C xi eta; simp [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, hφ]
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, (β U γ) ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, (β S α) ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl (Formula.and β xi) γ ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show Formula.untl (Formula.and β xi) γ ∈ lemma27SinceSeed A B C xi eta
    simp only [lemma27SinceSeed, Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed, Set.mem_union, Set.mem_setOf_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (identity' (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, (xi U γ) ∈ D := by
    intro γ hγ
    exact untl_left_mono_thm h_D_mcs (rceImp β₀ xi) (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince C xi D :=
    burgessR_implies_burgessRSince h_D_mcs h_mcs_C h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, Formula.snce (Formula.and β xi) δ ∈ C := by
    intro β hβ δ hδ
    exact (burgessRSince_conj h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi) δ hδ
  have h_r3_DC_DBC : burgessR3 D (deductiveClosure ({xi} ∪ B)) C :=
    dc_delta_B_burgessR3 h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation (deductiveClosure ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  obtain ⟨B', h_B_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure ({xi} ∪ B) :=
    subset_deductiveClosure _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B''⟩

/-- **Lemma 2.4 (Since direction) with guard**: Strengthened version for Since.
Returns R3M(A, B, C) with γ ∈ B. Note: only guarantees hContent(C) ⊆ A for
the original A from the Lindenbaum extension. -/
lemma lemma24SinceWithGuard {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) (γ β : Formula Atom)
    (h_since : (γ S β) ∈ C) :
    ∃ B A : Set (Formula Atom), Temporal.SetMaximalConsistent A ∧
      β ∈ A ∧
      BurgessR3Maximal A B C ∧
      γ ∈ B := by
  have h_P_β : (𝐏β) ∈ C := since_implies_P_in_mcs h_mcs h_since
  have h_seed_cons := past_temporal_witness_seed_consistent C h_mcs β h_P_β
  obtain ⟨A, h_sup, h_A_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_β_A : β ∈ A := h_sup (Set.mem_union_left _ (Set.mem_singleton β))
  have h_h_sub : hContent C ⊆ A := fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_g_sub : gContent A ⊆ C := h_content_sub_imp_g_content_sub' h_A_mcs h_mcs h_h_sub
  obtain ⟨B₀, h_B₀⟩ := burgessR3Maximal_from_g_content_sub' h_A_mcs h_mcs h_g_sub
  by_cases h_γ_B₀ : γ ∈ B₀
  · exact ⟨B₀, A, h_A_mcs, h_β_A, h_B₀, h_γ_B₀⟩
  · obtain ⟨_, D, B'', _, h_R3M_DB''C, h_D_mcs, h_eta_D, _, _, _, h_γ_B''⟩ :=
      lemma_2_7_since h_A_mcs h_mcs h_B₀ h_B₀.1 h_g_sub γ β h_since h_γ_B₀
    exact ⟨B'', D, h_D_mcs, h_eta_D, h_R3M_DB''C, h_γ_B''⟩


end Cslib.Logic.Temporal.Metalogic.Chronicle
