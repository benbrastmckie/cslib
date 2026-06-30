/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Burgess

/-! # Splitting — Iterated BX13 Structures, Lemma 2.7, and Lemma 2.8

Iterated BX13 enrichment structures, the main Lemma 2.7 Until-formula splitting,
and Lemma 2.8 (variant with negated disjunction hypothesis in C).

## Main Results

- `EnrichedEvent`, `EnrichedEventSince`: Iterated BX13 enrichment result structures
- `lemma_2_7`: Until-formula splitting construction (BurgessR3Maximal triple decomposition)
- `lemma_2_8`: Lemma 2.8 variant (with ¬(eta ∨ xi∧U(xi,eta)) ∈ C)
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

/-! ## Iterated BX13 Enrichment Structures -/

/-- Structure to hold the result of iterated BX13 enrichment. -/
structure EnrichedEvent (A : Set (Formula Atom)) (guard event : Formula Atom) (alphas : List (Formula Atom)) where
  /-- The enriched event formula. -/
  event' : Formula Atom
  /-- Membership of the Until formula in `A`. -/
  hUntl : Formula.untl guard event' ∈ A
  /-- Derivation that `event'` implies the original event. -/
  hImpl : DerivationTree FrameClass.Base [] (event'.imp event)
  /-- For each alpha, derivation that `event'` implies the Since formula. -/
  hSnce : ∀ α ∈ alphas, DerivationTree FrameClass.Base [] (event'.imp (Formula.snce guard α))

/-- Iterated BX13 enrichment: given untl(guard, event) ∈ A and a list of
formulas each in A, enrich the event with snce(guard, αⱼ) for each αⱼ. -/
private noncomputable def iteratedEnrichment {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    (guard : Formula Atom) :
    (alphas : List (Formula Atom)) →
    (h_alphas : ∀ α ∈ alphas, α ∈ A) →
    (event : Formula Atom) →
    (guard U event) ∈ A →
    EnrichedEvent A guard event alphas
  | [], _, event, hUntl => EnrichedEvent.mk event hUntl (identity' event) (fun _ h => by simp at h)
  | α :: rest, h_alphas, event, hUntl => by
    have h_α : α ∈ A := h_alphas α (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_until_mcs h_mcs h_α hUntl
    have h_rest : ∀ α' ∈ rest, α' ∈ A := fun α' hα' =>
      h_alphas α' (List.mem_cons.mpr (Or.inr hα'))
    let evt := iteratedEnrichment h_mcs guard rest h_rest
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
structure EnrichedEventSince (C : Set (Formula Atom)) (guard event : Formula Atom) (gammas : List (Formula Atom)) where
  /-- The enriched event formula. -/
  event' : Formula Atom
  /-- Membership of the Since formula in `C`. -/
  hSnce : Formula.snce guard event' ∈ C
  /-- Derivation that `event'` implies the original event. -/
  hImpl : DerivationTree FrameClass.Base [] (event'.imp event)
  /-- For each gamma, derivation that `event'` implies the Until formula. -/
  hUntl : ∀ γ ∈ gammas, DerivationTree FrameClass.Base [] (event'.imp (Formula.untl guard γ))

/-- Iterated BX13' enrichment (Since direction). -/
noncomputable def iteratedEnrichmentSince {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C)
    (guard : Formula Atom) :
    (gammas : List (Formula Atom)) →
    (h_gammas : ∀ γ ∈ gammas, γ ∈ C) →
    (event : Formula Atom) →
    (guard S event) ∈ C →
    EnrichedEventSince C guard event gammas
  | [], _, event, hSnce => EnrichedEventSince.mk event hSnce (identity' event) (fun _ h => by simp at h)
  | γ :: rest, h_gammas, event, hSnce => by
    have h_γ : γ ∈ C := h_gammas γ (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_since_mcs h_mcs h_γ hSnce
    have h_rest : ∀ γ' ∈ rest, γ' ∈ C := fun γ' hγ' =>
      h_gammas γ' (List.mem_cons.mpr (Or.inr hγ'))
    let evt := iteratedEnrichmentSince h_mcs guard rest h_rest
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

/-! ## Lemma 2.7: Until-Formula Splitting -/

/-- The D0 seed for Lemma 2.7: B ∪ {eta} ∪ {snce(α, β∧xi) : β ∈ B, α ∈ A}. -/
@[nolint unusedArguments]
private def lemma27Seed (A B _C : Set (Formula Atom)) (xi eta : Formula Atom) : Set (Formula Atom) :=
  B ∪ {eta} ∪ {φ | ∃ β ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β xi) α}

/-- Extract a B-guard from a single element of the lemma27Seed. -/
@[nolint unusedArguments]
private noncomputable def l27Guard {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B)
    (xi eta : Formula Atom) (φ : Formula Atom) (_h : φ ∈ lemma27Seed A B C xi eta) :
    { g : Formula Atom // g ∈ B } := by
  classical
  by_cases h1 : φ ∈ B
  · exact ⟨φ, h1⟩
  · by_cases h5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α
    · exact ⟨Classical.choose h5, (Classical.choose_spec h5).1⟩
    · exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_dcs (identity' (Formula.bot : Formula Atom))⟩

/-- Recursively extract B-guards from L ⊆ lemma27Seed. -/
private noncomputable def l27CollectGuards {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B)
    (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma27Seed A B C xi eta) →
    { gs : List (Formula Atom) // ∀ g ∈ gs, g ∈ B }
  | [], _ => ⟨[], fun _ h => (by simp at h)⟩
  | φ :: rest, hL =>
    let ⟨g, hg⟩ := l27Guard h_dcs xi eta φ (hL φ (List.mem_cons.mpr (Or.inl rfl)))
    let ⟨gs, hgs⟩ := l27CollectGuards h_dcs xi eta rest
      (fun ψ hψ => hL ψ (List.mem_cons.mpr (Or.inr hψ)))
    ⟨g :: gs, fun g' hg' => by
      rcases List.mem_cons.mp hg' with rfl | h
      · exact hg
      · exact hgs g' h⟩

/-- For each element of L ⊆ lemma27Seed, extract the A-event. -/
@[nolint unusedArguments]
private noncomputable def l27AEventList {A B C : Set (Formula Atom)}
    (xi eta : Formula Atom) (L : List (Formula Atom))
    (_hL : ∀ φ ∈ L, φ ∈ lemma27Seed A B C xi eta) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α then
      some (Classical.choose (Classical.choose_spec h).2)
    else none)

/-- Elements of l27AEventList are in A. -/
private theorem l27_a_event_list_mem {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma27Seed A B C xi eta}
    {α : Formula Atom} (hα : α ∈ l27AEventList xi eta L hL) : α ∈ A := by
  unfold l27AEventList at hα
  rcases List.mem_filterMap.mp hα with ⟨φ, _, h_eq⟩
  split at h_eq
  · next h_snce5 =>
    simp at h_eq
    rw [← h_eq]
    exact (Classical.choose_spec ((Classical.choose_spec h_snce5).2)).1
  · simp at h_eq

/-- If φ ∈ L ∩ B then φ is in l27CollectGuards output. -/
private theorem l27_collect_guards_mem_of_B {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma27Seed A B C xi eta) →
    ∀ φ ∈ L, φ ∈ B → φ ∈ (l27CollectGuards h_dcs xi eta L hL).val
  | [], _, φ, hφ, _ => (by simp at hφ)
  | ψ :: rest, hL, φ, hφ, h_B => by
    simp [l27CollectGuards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      unfold l27Guard; simp [h_B]
    · right; exact l27_collect_guards_mem_of_B h_dcs xi eta rest _ φ h_rest h_B

/-- Formula.and is injective in the first argument. -/
private theorem formula_and_left_cancel {a b c : Formula Atom}
    (h : Formula.and a c = Formula.and b c) : a = b := by
  simp only [Formula.and, Formula.neg] at h
  exact (Formula.imp.injEq _ _ _ _ |>.mp (Formula.imp.injEq _ _ _ _ |>.mp h).1).1

/-- l27Guard for snce(β'∧xi,α') when snce(β'∧xi,α') ∉ B returns β'. -/
private theorem l27_guard_snce_xi_val {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B) (xi eta β' α' : Formula Atom)
    (h_seed : Formula.snce (Formula.and β' xi) α' ∈ lemma27Seed A B C xi eta)
    (h_not_B : Formula.snce (Formula.and β' xi) α' ∉ B)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    (l27Guard h_dcs xi eta (Formula.snce (Formula.and β' xi) α') h_seed).val = β' := by
  unfold l27Guard; simp [h_not_B]
  split
  · next h =>
    have h_exists : ∃ β'' ∈ B, ∃ α'' ∈ A,
        Formula.snce (Formula.and β' xi) α' = Formula.snce (Formula.and β'' xi) α'' :=
      ⟨β', h.1, α', h.2, rfl⟩
    have h_spec := Classical.choose_spec h_exists
    obtain ⟨hβ_B, α'', hα'', h_eq⟩ := h_spec
    rw [Formula.snce.injEq] at h_eq
    have h_β_eq := (formula_and_left_cancel h_eq.1).symm
    convert h_β_eq using 1; simp
  · next h =>
    exfalso; exact h ⟨hβ', hα'⟩

/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, snce(β'∧xi,α') ∉ B,
then β' is in the guard list. -/
private theorem l27_collect_guards_mem_of_snce_xi {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma27Seed A B C xi eta) →
    ∀ β' α', Formula.snce (Formula.and β' xi) α' ∈ L → β' ∈ B → α' ∈ A →
      Formula.snce (Formula.and β' xi) α' ∉ B →
      β' ∈ (l27CollectGuards h_dcs xi eta L hL).val
  | [], _, β', α', hφ, _, _, _ => (by simp at hφ)
  | ψ :: rest, hL, β', α', hφ, hβ', hα', h_not_B => by
    simp [l27CollectGuards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      exact (l27_guard_snce_xi_val h_dcs xi eta β' α'
        (hL (Formula.snce (Formula.and β' xi) α') (List.mem_cons.mpr (Or.inl rfl)))
        h_not_B hβ' hα').symm
    · right
      exact l27_collect_guards_mem_of_snce_xi h_dcs xi eta rest _ β' α' h_rest hβ' hα' h_not_B

/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, then α' ∈ l27AEventList. -/
private theorem l27_a_event_list_α_mem_xi {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma27Seed A B C xi eta}
    {β' α' : Formula Atom} (hφ : Formula.snce (Formula.and β' xi) α' ∈ L)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    α' ∈ l27AEventList xi eta L hL := by
  unfold l27AEventList
  apply List.mem_filterMap.mpr
  refine ⟨Formula.snce (Formula.and β' xi) α', hφ, ?_⟩
  have h_ex : ∃ β'' ∈ B, ∃ α'' ∈ A, Formula.snce (Formula.and β' xi) α' = Formula.snce (Formula.and β'' xi) α'' :=
    ⟨β', hβ', α', hα', rfl⟩
  rw [dif_pos h_ex]
  congr 1
  have h_spec := Classical.choose_spec (Classical.choose_spec h_ex).2
  rw [Formula.snce.injEq] at h_spec
  exact h_spec.2.2.symm

/-- Consistency of the Lemma 2.7 D0 seed. Uses BX5+BX7+BX13 chain. -/
private theorem lemma_2_7_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (xi U eta) ∈ A)
    (h_xi_not_B : xi ∉ B) :
    Temporal.SetConsistent (lemma27Seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  have h_not_r3_xi := BurgessR3Maximal_extension_fails h_r3m h_xi_not_B
  have h_neg_until_exists : ∃ beta0 ∈ B, ∃ gamma0 ∈ C,
      Formula.untl (Formula.and beta0 xi) gamma0 ∉ A := by
    by_contra h_all_until
    push Not at h_all_until
    have h_rset : burgessRSet A (deductiveClosure ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · exact untl_left_mono_thm h_mcs_A hImpl (h_all_until beta_w hbeta_w gamma hgamma)
    have h_rsince : burgessRSetSince C (deductiveClosure ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · have h_burgessR_ext : burgessR A (Formula.and beta_w xi) C :=
          fun gamma hgamma => h_all_until beta_w hbeta_w gamma hgamma
        have h_snce_ext := burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR_ext alpha halpha
        exact snce_left_mono_thm h_mcs_C hImpl h_snce_ext
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, gamma0, h_gamma0, h_not_in_A⟩ := h_neg_until_exists
  have h_neg_until_in_A : (Formula.untl (Formula.and beta0 xi) gamma0).neg ∈ A := by
    rcases temporal_negation_complete h_mcs_A
      (Formula.untl (Formula.and beta0 xi) gamma0) with h | h
    · exfalso; exact h_not_in_A h
    · exact h
  intro L hL ⟨d⟩
  have h_bx5_xe := self_accum_until_mcs h_mcs_A xi eta h_until
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B) (h_b_beta0 : DerivationTree FrameClass.Base [] (b.imp beta0))
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_gamma0 : DerivationTree FrameClass.Base [] (γ_hat.imp gamma0))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        (𝐅event) ∈ A ×'
        DerivationTree FrameClass.Base [] (event.imp b) ×'
        DerivationTree FrameClass.Base [] (event.imp eta) ×'
        DerivationTree FrameClass.Base [] (event.imp (Formula.untl b γ_hat)) ×'
        (∀ α ∈ alpha_list, DerivationTree FrameClass.Base [] (event.imp (Formula.snce (Formula.and b (Formula.and xi (Formula.untl xi eta))) α))) by
    let b_list_raw := (l27CollectGuards h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27CollectGuards h_B_dcs xi eta L hL).property
    let b_list := beta0 :: b_list_raw
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · exact hb_list g h
    let a_list := l27AEventList xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem hα
    let b := listConj b_list
    let γ_hat := gamma0
    have hb_B : b ∈ B := list_conj_mem_dcs h_B_dcs b_list hb_list'
    have hγ_C : γ_hat ∈ C := h_gamma0
    have h_b_to_beta0 : DerivationTree FrameClass.Base [] (b.imp beta0) :=
      listConjImpliesElem b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_γ_to_gamma0 : DerivationTree FrameClass.Base [] (γ_hat.imp gamma0) := identity' gamma0
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B h_b_to_beta0 γ_hat hγ_C h_γ_to_gamma0 a_list ha_list
    let χ_gen := Formula.and xi (Formula.untl xi eta)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree FrameClass.Base [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree FrameClass.Base [] (b.imp φ) := listConjImpliesElem b_list φ h_φ_in_b
        have h_ev_to_φ : DerivationTree FrameClass.Base [] (event.imp φ) := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce (Formula.and β' xi) α' := (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce (Formula.and β' xi) α' ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce (Formula.and β' xi) α' ∈ B
            · have h_in_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL (Formula.snce (Formula.and β' xi) α') h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce (Formula.and β' xi) α' ∈ b_list := List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree FrameClass.Base [] (b.imp (Formula.snce (Formula.and β' xi) α')) :=
                listConjImpliesElem b_list (Formula.snce (Formula.and β' xi) α') h_in_b
              have h_ev_imp := impTrans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · have h_α'_in_a := @l27_a_event_list_α_mem_xi _ A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi h_B_dcs xi eta L hL β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree FrameClass.Base [] (b.imp β') := listConjImpliesElem b_list β' h_β'_in_b
              have h_bχ_to_β'xi : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp b χ_gen) h_b_to_β'
                have h2 : DerivationTree FrameClass.Base [] _ := impTrans (rceImp b χ_gen) (lceImp xi (Formula.untl xi eta))
                exact combineImpConj h1 h2
              have h_mono := snceLeftMonoDeriv (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := impTrans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp [lemma27Seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    have d_event : DerivationTree FrameClass.Base [event] Formula.bot :=
      derivationFromImplied [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem h_mcs_A event h_F_event
    exact inconsistent_singleton_false h_event_cons d_event
  -- Prove h_key: the generalized BX5+BX7+BX13 chain helper.
  intro b hb h_b_beta0 γ_hat hγ h_γ_gamma0 alpha_list h_alphas
  have h_untl_bg : (b U γ_hat) ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl b γ_hat)
  let χ_gen := Formula.and xi (Formula.untl xi eta)
  have h_bx7_gen := linear_until_mcs h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_guard_to_b0xi : DerivationTree FrameClass.Base [] ((Formula.and φ_gen χ_gen).imp (Formula.and beta0 xi)) := by
    have h1 : DerivationTree FrameClass.Base [] _ := impTrans (impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl b γ_hat))) h_b_beta0
    have h2 : DerivationTree FrameClass.Base [] _ := impTrans (rceImp φ_gen χ_gen) (lceImp xi (Formula.untl xi eta))
    exact combineImpConj h1 h2
  have h_D3_gen : Formula.untl (Formula.and φ_gen χ_gen) (Formula.and φ_gen eta) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : DerivationTree FrameClass.Base [] ((Formula.and γ_hat eta).imp gamma0) :=
        impTrans (lceImp γ_hat eta) h_γ_gamma0
      have h_contra := right_mono_until_mcs h_mcs_A h_rm
        (untl_left_mono_thm h_mcs_A h_guard_to_b0xi h_D1)
      exact mcs_not_mem_of_neg h_mcs_A h_neg_until_in_A h_contra
    · exfalso
      have h_rm : DerivationTree FrameClass.Base [] ((Formula.and γ_hat χ_gen).imp gamma0) :=
        impTrans (lceImp γ_hat χ_gen) h_γ_gamma0
      have h_contra := right_mono_until_mcs h_mcs_A h_rm
        (untl_left_mono_thm h_mcs_A h_guard_to_b0xi h_D2)
      exact mcs_not_mem_of_neg h_mcs_A h_neg_until_in_A h_contra
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichment h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : (𝐅event) ∈ A := until_implies_F_in_mcs h_mcs_A evt.hUntl
  have h_ev_base := evt.hImpl
  have h_ev_b : DerivationTree FrameClass.Base [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.untl b γ_hat)))
  have h_ev_eta : DerivationTree FrameClass.Base [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_untl : DerivationTree FrameClass.Base [] (event.imp (Formula.untl b γ_hat)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.untl b γ_hat)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree FrameClass.Base [] (event.imp (Formula.snce (Formula.and b χ_gen) α)) := by
    intro α hα
    have h_snce_guard := evt.hSnce α hα
    have h_guard_to_bχ : DerivationTree FrameClass.Base [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl b γ_hat))
      have h2 : DerivationTree FrameClass.Base [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_snce_guard (snceLeftMonoDeriv guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩

/-- **Lemma 2.7**: Given BurgessR3Maximal(A, B, C) with untl(xi, eta) ∈ A and xi ∉ B,
construct MCS D with eta ∈ D and B' with B ⊆ B' and xi ∈ B'. -/
theorem lemma_2_7 {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (xi U eta) ∈ A)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  have h_seed_cons := lemma_2_7_seed_consistent h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_until h_xi_not_B
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27Seed A B C xi eta; simp [lemma27Seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27Seed A B C xi eta; simp [lemma27Seed, hφ]
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
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce (Formula.and β xi) α ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce (Formula.and β xi) α ∈ lemma27Seed A B C xi eta
    simp only [lemma27Seed, Set.mem_union, Set.mem_setOf_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (identity' (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, (xi S α) ∈ D := by
    intro α hα
    have hImpl : DerivationTree FrameClass.Base [] ((Formula.and β₀ xi).imp xi) := rceImp β₀ xi
    exact snce_left_mono_thm h_D_mcs hImpl (h_snce_conj_xi_D β₀ hβ₀ α hα)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR h_mcs_A h_D_mcs h_burgessRSince_xi
  have h_burgessR_conj' : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl (Formula.and β xi) δ ∈ A := by
    intro β hβ δ hδ
    exact h_burgessR_conj' β hβ δ hδ
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  have h_DC_cud : ClosedUnderDerivation (deductiveClosure ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  obtain ⟨B', h_DC_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  have h_xi_in_DC : xi ∈ deductiveClosure ({xi} ∪ B) :=
    subset_deductiveClosure _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B'⟩

/-! ## Lemma 2.8: Until-Formula Splitting (Variant) -/

/-- **Lemma 2.8 seed consistency**: Same seed as Lemma 2.7 but with
¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C instead of xi ∉ B. -/
private theorem lemma_2_8_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (_h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (xi U eta) ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl xi eta))).neg ∈ C) :
    Temporal.SetConsistent (lemma27Seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set γ' := (Formula.or eta (Formula.and xi (Formula.untl xi eta))).neg with γ'_def
  have h_γ'_to_neg_eta : DerivationTree FrameClass.Base [] (γ'.imp eta.neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.untl xi eta)))
      (lceImp eta.neg (Formula.and xi (Formula.untl xi eta)).neg)
  have h_γ'_to_neg_chi : DerivationTree FrameClass.Base [] (γ'.imp (Formula.and xi (Formula.untl xi eta)).neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.untl xi eta)))
      (rceImp eta.neg (Formula.and xi (Formula.untl xi eta)).neg)
  have h_bx5_xe := self_accum_until_mcs h_mcs_A xi eta h_until
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_to_γ' : DerivationTree FrameClass.Base [] (γ_hat.imp γ'))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        (𝐅event) ∈ A ×'
        DerivationTree FrameClass.Base [] (event.imp b) ×'
        DerivationTree FrameClass.Base [] (event.imp eta) ×'
        DerivationTree FrameClass.Base [] (event.imp (Formula.untl b γ_hat)) ×'
        (∀ α ∈ alpha_list, DerivationTree FrameClass.Base [] (event.imp (Formula.snce (Formula.and b (Formula.and xi (Formula.untl xi eta))) α))) by
    intro L hL ⟨d⟩
    let b_list_raw := (l27CollectGuards h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27CollectGuards h_B_dcs xi eta L hL).property
    let a_list := l27AEventList xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem hα
    let b_list_full := (Formula.bot.imp Formula.bot) :: b_list_raw
    have hb_list_full : ∀ g ∈ b_list_full, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact cud_contains_theorems h_B_dcs (identity' (Formula.bot : Formula Atom))
      · exact hb_list g h
    let b := listConj b_list_full
    let γ_hat := γ'
    have hb_B : b ∈ B := list_conj_mem_dcs h_B_dcs b_list_full hb_list_full
    have hγ_C : γ_hat ∈ C := h_neg_disj
    have h_γhat_to_γ' : DerivationTree FrameClass.Base [] (γ_hat.imp γ') := identity' γ'
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B γ_hat hγ_C h_γhat_to_γ' a_list ha_list
    let χ_gen := Formula.and xi (Formula.untl xi eta)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree FrameClass.Base [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list_full := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree FrameClass.Base [] (b.imp φ) := listConjImpliesElem b_list_full φ h_φ_in_b
        have h_ev_to_φ : DerivationTree FrameClass.Base [] (event.imp φ) := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce (Formula.and β' xi) α' := (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce (Formula.and β' xi) α' ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce (Formula.and β' xi) α' ∈ B
            · have h_in_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL (Formula.snce (Formula.and β' xi) α') h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce (Formula.and β' xi) α' ∈ b_list_full := List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree FrameClass.Base [] (b.imp (Formula.snce (Formula.and β' xi) α')) :=
                listConjImpliesElem b_list_full (Formula.snce (Formula.and β' xi) α') h_in_b
              have h_ev_imp := impTrans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · have h_α'_in_a := @l27_a_event_list_α_mem_xi _ A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi h_B_dcs xi eta L hL β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list_full := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree FrameClass.Base [] (b.imp β') := listConjImpliesElem b_list_full β' h_β'_in_b
              have h_bχ_to_β'xi : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp b χ_gen) h_b_to_β'
                have h2 : DerivationTree FrameClass.Base [] _ := impTrans (rceImp b χ_gen) (lceImp xi (Formula.untl xi eta))
                exact combineImpConj h1 h2
              have h_mono := snceLeftMonoDeriv (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := impTrans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp [lemma27Seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    have d_event : DerivationTree FrameClass.Base [event] Formula.bot :=
      derivationFromImplied [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem h_mcs_A event h_F_event
    exact inconsistent_singleton_false h_event_cons d_event
  -- Prove h_key: BX5+BX7+BX13 chain with D1/D2 eliminated via γ'
  intro b hb γ_hat hγ h_γ_to_γ' alpha_list h_alphas
  have h_untl_bg : (b U γ_hat) ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl b γ_hat)
  let χ_gen := Formula.and xi (Formula.untl xi eta)
  have h_bx7_gen := linear_until_mcs h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_D3_gen : Formula.untl (Formula.and φ_gen χ_gen) (Formula.and φ_gen eta) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and γ_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and γ_hat eta).imp eta.neg) :=
          impTrans (lceImp γ_hat eta) (impTrans h_γ_to_γ' h_γ'_to_neg_eta)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp γ_hat eta
        let PConj := Formula.and γ_hat eta
        have d1 : DerivationTree FrameClass.Base [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs h_mcs_A h_event_to_bot (until_implies_F_in_mcs h_mcs_A h_D1)
      have h_G_top : Formula.allFuture (Formula.bot.imp Formula.bot) ∈ A :=
        theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ (identity' (Formula.bot : Formula Atom)))
      exact someFuture_allFuture_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and γ_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and γ_hat χ_gen).imp χ_gen.neg) :=
          impTrans (lceImp γ_hat χ_gen) (impTrans h_γ_to_γ' h_γ'_to_neg_chi)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp γ_hat χ_gen
        let PConj := Formula.and γ_hat χ_gen
        have d1 : DerivationTree FrameClass.Base [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs h_mcs_A h_event_to_bot (until_implies_F_in_mcs h_mcs_A h_D2)
      have h_G_top : Formula.allFuture (Formula.bot.imp Formula.bot) ∈ A :=
        theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ (identity' (Formula.bot : Formula Atom)))
      exact someFuture_allFuture_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichment h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : (𝐅event) ∈ A := until_implies_F_in_mcs h_mcs_A evt.hUntl
  have h_ev_base := evt.hImpl
  have h_ev_b : DerivationTree FrameClass.Base [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.untl b γ_hat)))
  have h_ev_eta : DerivationTree FrameClass.Base [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_untl : DerivationTree FrameClass.Base [] (event.imp (Formula.untl b γ_hat)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.untl b γ_hat)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree FrameClass.Base [] (event.imp (Formula.snce (Formula.and b χ_gen) α)) := by
    intro α hα
    have h_snce_guard := evt.hSnce α hα
    have h_guard_to_bχ : DerivationTree FrameClass.Base [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl b γ_hat))
      have h2 : DerivationTree FrameClass.Base [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_snce_guard (snceLeftMonoDeriv guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩

/-- **Lemma 2.8**: Given BurgessR3Maximal(A, B, C) with untl(xi, eta) ∈ A and
¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C, construct splitting. -/
theorem lemma_2_8 {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (xi U eta) ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl xi eta))).neg ∈ C) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  have h_seed_cons := lemma_2_8_seed_consistent h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_until h_neg_disj
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27Seed A B C xi eta; simp [lemma27Seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27Seed A B C xi eta; simp [lemma27Seed, hφ]
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
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce (Formula.and β xi) α ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce (Formula.and β xi) α ∈ lemma27Seed A B C xi eta
    simp only [lemma27Seed, Set.mem_union, Set.mem_setOf_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (identity' (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, (xi S α) ∈ D := by
    intro α hα
    exact snce_left_mono_thm h_D_mcs (rceImp β₀ xi) (h_snce_conj_xi_D β₀ hβ₀ α hα)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR h_mcs_A h_D_mcs h_burgessRSince_xi
  have h_burgessR_conj' : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl (Formula.and β xi) δ ∈ A := by
    intro β hβ δ hδ; exact h_burgessR_conj' β hβ δ hδ
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  have h_DC_cud : ClosedUnderDerivation (deductiveClosure ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  obtain ⟨B', h_DC_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  have h_xi_in_DC : xi ∈ deductiveClosure ({xi} ∪ B) :=
    subset_deductiveClosure _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B'⟩


end Cslib.Logic.Temporal.Metalogic.Chronicle
