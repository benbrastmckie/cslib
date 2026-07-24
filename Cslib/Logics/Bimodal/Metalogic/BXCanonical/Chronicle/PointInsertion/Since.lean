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

/-- The `SinceSeedInterface` instance family for Bimodal, indexed by `fc`:
populates every field of the shared Foundations interface with Bimodal's own
`fc`-threaded apparatus. Used to delegate to the generic `lemma27SinceSeed`/`l27s*`
helpers (`Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`) instead of
duplicating them locally. -/
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
  or := Formula.or
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
  demorganDisjNegForward := fun A B => liftBase fc (demorganDisjNegForward A B)
  pMonoMcs := by intro _ hmcs _ _ hi hp; exact P_mono_mcs fc hmcs hi hp
  somePastAllPastNegAbsurd := by
    intro _ hmcs psi hp hh; exact somePast_allPast_neg_absurd hmcs psi hp hh

/-- Since-direction seed, simplified via Xu 3.2.1:
B ∪ {eta} ∪ {untl(γ, β∧xi) | β∈B, γ∈C}.

The original 5-component seed included {untl(γ,β)} and {snce(α,β)} but these are
redundant: Xu 3.2.1 proves they are already in B. The 3rd component untl(γ, β∧xi)
cannot be dropped because xi ∉ B prevents Xu 3.2.1 from applying. Relocated to the shared
`Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency` module; this is a thin
alias. These formula-operator-only helpers do not depend on `fc`
(only `untl`/`and` and their injectivity), so the arbitrary `FrameClass.Base` index of
`bimodalSinceInterface` is used internally and the original no-`fc` signatures are
preserved verbatim. -/
@[nolint unusedArguments]
private def lemma27SinceSeed (_A B C : Set (Formula Atom)) (xi eta : Formula Atom) :
    Set (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.lemma27SinceSeed
    (bimodalSinceInterface FrameClass.Base) _A B C xi eta

/-- Extract γ' events from component 3 elements (untl(γ, β∧xi)) of a list. Relocated to
the shared Foundations module. -/
private noncomputable def l27sC5EventList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sC5EventList (bimodalSinceInterface FrameClass.Base) B C xi L

/-- Elements of l27sC5EventList are in C. Relocated to the shared Foundations module. -/
private theorem l27s_c5_event_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {γ : Formula Atom} (hγ : γ ∈ l27sC5EventList B C xi L) : γ ∈ C :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_event_list_mem (bimodalSinceInterface FrameClass.Base) hγ

/-- Extract β' guards from component 3 elements (untl(γ, β∧xi)) of a list. Relocated to
the shared Foundations module. -/
private noncomputable def l27sB5GuardList (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.l27sB5GuardList (bimodalSinceInterface FrameClass.Base) B C xi L

/-- Elements of l27sB5GuardList are in B. Relocated to the shared Foundations module. -/
private theorem l27s_b5_guard_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β : Formula Atom} (hβ : β ∈ l27sB5GuardList B C xi L) : β ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_guard_list_mem
    (bimodalSinceInterface FrameClass.Base) hβ

/-- For a component 3 element untl(γ', β'∧xi) in L, the extracted γ' is in c5_event_list.
Relocated to the shared Foundations module. -/
private theorem l27s_c5_γ_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    γ' ∈ l27sC5EventList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_c5_γ_mem (bimodalSinceInterface FrameClass.Base) hφ hβ' hγ'

/-- For a component 3 element untl(γ', β'∧xi) in L, the extracted β' is in b5_guard_list.
Relocated to the shared Foundations module. -/
private theorem l27s_b5_β_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl (Formula.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    β' ∈ l27sB5GuardList B C xi L :=
  Cslib.Logic.Metalogic.Chronicle.l27s_b5_β_mem (bimodalSinceInterface FrameClass.Base) hφ hβ' hγ'

/-- Since-direction seed consistency (simplified via Xu 3.2.1):
Given BurgessR3Maximal(A, B, C) with snce(xi, eta) ∈ C and xi ∉ B,
the 3-component seed B ∪ {eta} ∪ {untl(γ, β∧xi)} is consistent.

Uses BX5'+BX7'+BX13' chain operating on C. Delegates to the generic
`Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since_seed_consistent`. -/
private theorem lemma_2_7_since_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce xi eta ∈ C)
    (h_xi_not_B : xi ∉ B) :
    SetConsistent fc (lemma27SinceSeed A B C xi eta) :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since_seed_consistent (bimodalSinceInterface fc)
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_xi_not_B

/-- **Lemma 2.7'** (Since direction, Burgess 1982): Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and xi ∉ B, construct MCS D with eta ∈ D splitting the R3 pair.

Mirror of lemma_2_7 fc using BX5'+BX7'+BX13' instead of BX5+BX7+BX13. Delegates to the
generic `Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since`. -/
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
      xi ∈ B'' :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since (bimodalSinceInterface fc)
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_xi_not_B

/-- **Lemma 2.8' seed consistency** (Since direction): Same seed as lemma_2_7_since,
but consistency proved using ¬(eta ∨ (xi ∧ snce(xi,eta))) ∈ A instead of xi ∉ B. Delegates
to the generic `Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since_seed_consistent`. -/
private theorem lemma_2_8_since_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce xi eta ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce xi eta))).neg ∈ A) :
    SetConsistent fc (lemma27SinceSeed A B C xi eta) :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since_seed_consistent (bimodalSinceInterface fc)
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_neg_disj

/-- **Lemma 2.8'** (Since direction, Burgess 1982): Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A, construct MCS D
with eta ∈ D splitting the R3 pair. Returns xi ∈ B'' via DC(B∪{xi}) Zorn seed. Delegates
to the generic `Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since`. -/
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
      xi ∈ B'' :=
  Cslib.Logic.Metalogic.Chronicle.lemma_2_8_since (bimodalSinceInterface fc)
    h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_since h_neg_disj

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
