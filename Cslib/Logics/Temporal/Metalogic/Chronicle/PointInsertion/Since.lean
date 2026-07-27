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

/-! ## Since-Direction Mirrors -/

/-- The `SinceSeedInterface` instance for Temporal: populates every field of the
shared Foundations interface with Temporal's own apparatus at `FrameClass.Base`. Used to
delegate to the generic `lemma27SinceSeed`/`l27s*` helpers
(`Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`) instead of duplicating
them locally. -/
private noncomputable def temporalSinceInterface :
    Cslib.Logic.Metalogic.Chronicle.SinceSeedInterface (Formula Atom) where
  bot := Formula.bot
  imp := Formula.imp
  and := Formula.and
  untl := Formula.untl
  snce := Formula.snce
  somePast := Formula.somePast
  allPast := Formula.allPast
  allFuture := Formula.allFuture
  or := Formula.or
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
  demorganDisjNegForward := fun A B => demorganDisjNegForward A B
  pMonoMcs := by intro _ hmcs _ _ hi hp; exact P_mono_mcs hmcs hi hp
  somePastAllPastNegAbsurd := by
    intro _ hmcs psi hp hh; exact somePast_allPast_neg_absurd hmcs psi hp hh

/-- Since-direction seed: B ∪ {eta} ∪ {untl(γ, β∧xi) | β∈B, γ∈C}. Relocated to the shared
`Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency` module; this is a thin
alias fixing Temporal's interface instance. -/
@[nolint unusedArguments]
private def lemma27SinceSeed (_A B C : Set (Formula Atom)) (xi eta : Formula Atom) :
    Set (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed temporalSinceInterface _A B C xi eta

/-- Extract γ' events from component 3 elements of a list. Relocated to the shared
Foundations module. -/
private noncomputable def l27sC5EventList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sC5EventList temporalSinceInterface B C xi L

/-- Elements of l27sC5EventList are in C. Relocated to the shared Foundations module. -/
private theorem l27s_c5_event_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {γ : Formula Atom} (hγ : γ ∈ l27sC5EventList B C xi L) : γ ∈ C :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_event_list_mem temporalSinceInterface hγ

/-- Extract β' guards from component 3 elements. Relocated to the shared Foundations
module. -/
private noncomputable def l27sB5GuardList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sB5GuardList temporalSinceInterface B C xi L

/-- Elements of l27sB5GuardList are in B. Relocated to the shared Foundations module. -/
private theorem l27s_b5_guard_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β : Formula Atom} (hβ : β ∈ l27sB5GuardList B C xi L) : β ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_guard_list_mem temporalSinceInterface hβ

/-- For a component 3 element, the extracted γ' is in c5_event_list. Relocated to the
shared Foundations module. -/
private theorem l27s_c5_γ_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    γ' ∈ l27sC5EventList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_γ_mem temporalSinceInterface hφ hβ' hγ'

/-- For a component 3 element, the extracted β' is in b5_guard_list. Relocated to the
shared Foundations module. -/
private theorem l27s_b5_β_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    β' ∈ l27sB5GuardList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_β_mem temporalSinceInterface hφ hβ' hγ'

/-- Since-direction seed consistency. Uses BX5'+BX7'+BX13' chain. Delegates to the generic
`Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since_seed_consistent`. -/
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
Returns xi ∈ B'' via DC(B ∪ {xi}) Zorn seed. Delegates to the generic
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
but with ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A instead of xi ∉ B. Delegates to the generic
`Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since_seed_consistent`. -/
private theorem lemma_2_8_since_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (xi S eta) ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg ∈ A) :
    Temporal.SetConsistent (lemma27SinceSeed A B C xi eta) :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since_seed_consistent temporalSinceInterface
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_neg_disj

/-- **Lemma 2.8 (Since direction)**: Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A. Delegates to the generic
`Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since`. -/
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
      xi ∈ B'' :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since temporalSinceInterface
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_neg_disj

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
