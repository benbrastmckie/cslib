/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation
public import Cslib.Logics.Temporal.Metalogic.CompletenessHelpers

/-! # Seeds — F/G Helpers, Lemma 2.4/2.5/2.6, and BurgessR3Maximal Properties

F/G helper lemmas, Lemma 2.4/2.5/2.6, MCS-level axiom helpers, seriality consequences,
DCS neg insert, and R3Maximal/BurgessR3Maximal properties.

## Key Results

- `F_neg_of_G_not` / `P_neg_of_H_not`: If G(φ)/H(φ) not in MCS, then F(¬φ)/P(¬φ) is.
- `lemma24`: Until witness endpoint construction
- `lemma_2_5b` / `lemma_2_5b_past`: g/h-content ordering transitivity
- `lemma26`: Counterexample insertion
- `dc_delta_B_burgessR3`: Extension of B by delta preserves burgessR3
- `BurgessR3Maximal_extension_fails`: Maximality prevents consistent proper extensions
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

/-! ## Helper: F(neg phi) from G(phi) not in A -/

/-- If G(φ) ∉ MCS A, then F(¬φ) ∈ A. -/
private theorem F_neg_of_G_not {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_Gφ_not : (𝐆φ) ∉ A) :
    (𝐅(¬φ)) ∈ A := by
  rcases temporal_negation_complete h_mcs (Formula.someFuture φ.neg) with h | h
  · exact h
  · -- Task 180 (F1): h : (someFuture φ.neg).neg ∈ A is no longer definitionally allFuture φ
    -- ∈ A now that G is primitive; convert via mcs_allFuture_iff before the contradiction.
    exact absurd ((mcs_allFuture_iff h_mcs).mpr h) h_Gφ_not

/-- If H(φ) ∉ MCS A, then P(¬φ) ∈ A. Dual of `F_neg_of_G_not`. -/
private theorem P_neg_of_H_not {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_Hφ_not : (𝐇φ) ∉ A) :
    (𝐏(¬φ)) ∈ A := by
  rcases temporal_negation_complete h_mcs (Formula.somePast φ.neg) with h | h
  · exact h
  · -- Task 180 (F1): h : ¬P(¬φ) ∈ A is no longer definitionally H(φ) ∈ A now that H is
    -- primitive; convert via mcs_allPast_iff before the contradiction.
    exact absurd ((mcs_allPast_iff h_mcs).mpr h) h_Hφ_not

/-! ## Lemma 2.4: Until Witness Endpoint Construction -/

/-- The Until witness seed: {β} ∪ gContent(A) is consistent when U(γ,β) ∈ MCS A. -/
private theorem until_witness_seed_consistent {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (γ U β) ∈ A) :
    Temporal.SetConsistent ({β} ∪ gContent A) := by
  have h_F_β : (𝐅β) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl γ β).imp (Formula.someFuture β)) :=
      DerivationTree.axiom [] _ (Axiom.until_F γ β) trivial
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_until
  exact forward_temporal_witness_seed_consistent A h_mcs β h_F_β

/-- F(γ) ∈ A for all γ ∈ C when gContent(A) ⊆ C. -/
private theorem F_mem_of_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_gc : gContent A ⊆ C) (γ : Formula Atom) (h_γ : γ ∈ C) :
    (𝐅γ) ∈ A := by
  by_contra h_not_F
  have h_neg_F : (Formula.someFuture γ).neg ∈ A :=
    mcs_neg_of_not_mem h_mcs_A h_not_F
  -- ¬F(γ) ∈ A → G(¬γ) ∈ A: from ⊢ ¬¬γ → γ (DNE) via BX3 contrapositive: ¬F(γ) → ¬F(¬¬γ) = G(¬γ).
  have h_G_neg : (𝐆(¬γ)) ∈ A := by
    have h_dne := doubleNegation γ
    have h_G_dne : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dne
    have h_bx3 : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).allFuture.imp
        ((Formula.untl Formula.top γ.neg.neg).imp (Formula.untl Formula.top γ))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until γ.neg.neg γ Formula.top) trivial
    -- ⊢ F(¬¬γ) → F(γ)
    have h_F_mono : DerivationTree FrameClass.Base [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
    -- Contrapositive: ⊢ ¬F(γ) → ¬F(¬¬γ)
    have h_contra : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).neg.imp (Formula.someFuture γ.neg.neg).neg) :=
      contraposition h_F_mono
    -- Task 180 (F1): ¬F(¬¬γ) → G(¬γ) is no longer defeq (G is now primitive); bridge via
    -- the classic_to_allFuture axiom, then compose with the contrapositive above.
    have h_bridge : DerivationTree FrameClass.Base [] ((Formula.someFuture γ.neg.neg).neg.imp
        (Formula.allFuture γ.neg)) :=
      DerivationTree.axiom [] _ (Axiom.classic_to_allFuture γ.neg) trivial
    -- ¬F(γ) ∈ A → G(¬γ) ∈ A
    exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A (impTrans h_contra h_bridge)) h_neg_F
  have h_neg_C : (¬γ) ∈ C := h_gc h_G_neg
  exact mcs_not_mem_of_neg h_mcs_C h_neg_C h_γ

/-- P(α) ∈ C for all α ∈ A when gContent(A) ⊆ C. -/
private theorem P_mem_of_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_gc : gContent A ⊆ C) (α : Formula Atom) (h_α : α ∈ A) :
    (𝐏α) ∈ C := by
  have h_GP : Formula.allFuture (Formula.somePast α) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] (α.imp (Formula.allFuture (Formula.somePast α))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future α) trivial
    exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_ax) h_α
  exact h_gc h_GP

/-- BurgessR3Maximal existence from gContent inclusion. -/
theorem burgessR3Maximal_from_g_content_sub' {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_gc : gContent A ⊆ C) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal A B C := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with top_def
  have h_top_A : top ∈ A :=
    theoremInMcs h_mcs_A (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_bR : burgessR A top C := by
    intro γ hγ
    have h_F := F_mem_of_g_content_sub h_mcs_A h_mcs_C h_gc γ hγ
    have h_bx12 : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).imp (Formula.untl top γ)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_bx12) h_F
  have h_bRS : burgessRSince C top A := by
    intro α hα
    have h_P := P_mem_of_g_content_sub h_mcs_A h_gc α hα
    have h_bx12' : DerivationTree FrameClass.Base [] ((Formula.somePast α).imp (Formula.snce top α)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

/-- **Lemma 2.4**: Given MCS A with U(γ, β) ∈ A, there exists MCS C with
β ∈ C, gContent(A) ⊆ C, P(U(γ,β)) ∈ C, and a DCS interval set B with
BurgessR3Maximal(A, B, C). -/
lemma lemma24 {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (γ U β) ∈ A) :
    ∃ B C : Set (Formula Atom), Temporal.SetMaximalConsistent C ∧
      β ∈ C ∧ gContent A ⊆ C ∧
      Formula.somePast (Formula.untl γ β) ∈ C ∧
      BurgessR3Maximal A B C := by
  have h_seed_cons := until_witness_seed_consistent h_mcs γ β h_until
  obtain ⟨C, h_sup, h_C_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton β))
  have h_g_sub : gContent A ⊆ C := fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_GP : Formula.allFuture (Formula.somePast (Formula.untl γ β)) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl γ β).imp
        (Formula.allFuture (Formula.somePast (Formula.untl γ β)))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl γ β)) trivial
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_until
  have h_P_until_C : Formula.somePast (Formula.untl γ β) ∈ C := h_g_sub h_GP
  obtain ⟨B, h_B⟩ := burgessR3Maximal_from_g_content_sub' h_mcs h_C_mcs h_g_sub
  exact ⟨B, C, h_C_mcs, h_β_C, h_g_sub, h_P_until_C, h_B⟩

/-! ## MCS-Level Axiom Helpers -/

/-- BX10 at MCS level: U(γ,β) ∈ A implies F(β) ∈ A. -/
private theorem until_F_mcs' {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (γ U β) ∈ A) :
    (𝐅β) ∈ A :=
  until_implies_F_in_mcs h_mcs h_until

/-- BX5 at MCS level: U(γ,β) ∈ A implies U(γ∧U(γ,β), β) ∈ A. -/
theorem self_accum_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (γ U β) ∈ A) :
    Formula.untl (Formula.and γ (Formula.untl γ β)) β ∈ A :=
  until_self_accum_in_mcs h_mcs h_until

/-- BX5' at MCS level: snce(γ, β) ∈ A implies snce(γ ∧ snce(γ, β), β) ∈ A. -/
theorem self_accum_since_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_since : (γ S β) ∈ A) :
    Formula.snce (Formula.and γ (Formula.snce γ β)) β ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce γ β).imp
      (Formula.snce (Formula.and γ (Formula.snce γ β)) β)) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_since γ β) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_since

/-- BX4 at MCS level: φ ∈ A implies G(P(φ)) ∈ A. -/
theorem connect_future_mcs' {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_φ : φ ∈ A) :
    Formula.allFuture (Formula.somePast φ) ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] (φ.imp (Formula.allFuture (Formula.somePast φ))) :=
    DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_φ

/-- Conjunction introduction at MCS level. -/
theorem conj_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_φ : φ ∈ A) (h_ψ : ψ ∈ A) :
    Formula.and φ ψ ∈ A :=
  dcs_conj_closed (mcs_is_dcs h_mcs) h_φ h_ψ

/-- MCS disjunction elimination: If (φ ∨ ψ) ∈ A then φ ∈ A ∨ ψ ∈ A.
Recall φ.or ψ = φ.neg.imp ψ. -/
private theorem or_elim_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {φ ψ : Formula Atom}
    (h : (φ.or ψ) ∈ A) : φ ∈ A ∨ ψ ∈ A := by
  rcases temporal_negation_complete h_mcs φ with h_φ | h_neg_φ
  · exact Or.inl h_φ
  · exact Or.inr (temporal_implication_property h_mcs h h_neg_φ)

/-- BX7 (linear_until) at MCS level. -/
theorem linear_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ χ θ : Formula Atom)
    (h_u1 : (φ U ψ) ∈ A)
    (h_u2 : (χ U θ) ∈ A) :
    Formula.untl (Formula.and φ χ) (Formula.and ψ θ) ∈ A ∨
    Formula.untl (Formula.and φ χ) (Formula.and ψ χ) ∈ A ∨
    Formula.untl (Formula.and φ χ) (Formula.and φ θ) ∈ A := by
  have h_conj := conj_mcs h_mcs _ _ h_u1 h_u2
  have h_bx7 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.linear_until φ ψ χ θ) trivial
  have h_disj := temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx7) h_conj
  rcases or_elim_mcs h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- BX7' (linear_since) at MCS level. -/
theorem linear_since_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ χ θ : Formula Atom)
    (h_s1 : (φ S ψ) ∈ A)
    (h_s2 : (χ S θ) ∈ A) :
    Formula.snce (Formula.and φ χ) (Formula.and ψ θ) ∈ A ∨
    Formula.snce (Formula.and φ χ) (Formula.and ψ χ) ∈ A ∨
    Formula.snce (Formula.and φ χ) (Formula.and φ θ) ∈ A := by
  have h_conj := conj_mcs h_mcs _ _ h_s1 h_s2
  have h_bx7 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.linear_since φ ψ χ θ) trivial
  have h_disj := temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx7) h_conj
  rcases or_elim_mcs h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-! ## Lemma 2.5: gContent Ordering Composition -/

/-- **Lemma 2.5** (composition): gContent ordering is transitive. -/
private theorem lemma_2_5b {A D C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_AD : gContent A ⊆ D) (h_DC : gContent D ⊆ C) :
    gContent A ⊆ C := by
  intro φ hφ
  have h_GGφ := mcs_g_trans h_mcs_A hφ
  exact h_DC (h_AD h_GGφ)

/-- Dual: hContent ordering is transitive. -/
private theorem lemma_2_5b_past {A D C : Set (Formula Atom)}
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_CD : hContent C ⊆ D) (h_DA : hContent D ⊆ A) :
    hContent C ⊆ A := by
  intro φ hφ
  have h_HHφ : Formula.allPast (Formula.allPast φ) ∈ C := mcs_h_trans h_mcs_C hφ
  exact h_DA (h_CD h_HHφ)

/-! ## Lemma 2.6: Counterexample Insertion -/

/-- **Lemma 2.6**: Given MCS A and C with gContent(A) ⊆ C,
if δ ∉ C, then there exists MCS D with ¬δ ∈ D and gContent(A) ⊆ D. -/
lemma lemma26 {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (_h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_g_AC : gContent A ⊆ C)
    (δ : Formula Atom)
    (h_δ_not_C : δ ∉ C) :
    ∃ D : Set (Formula Atom), Temporal.SetMaximalConsistent D ∧
      (¬δ) ∈ D ∧ gContent A ⊆ D := by
  have h_Gδ_not_A : (𝐆δ) ∉ A := by
    intro h_Gδ; exact h_δ_not_C (h_g_AC h_Gδ)
  have h_F_neg_δ := F_neg_of_G_not h_mcs_A δ h_Gδ_not_A
  have h_seed_cons := forward_temporal_witness_seed_consistent A h_mcs_A δ.neg h_F_neg_δ
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  exact ⟨D, h_D_mcs,
    h_sup (Set.mem_union_left _ (Set.mem_singleton _)),
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)⟩

/-! ## Conjunction Elimination at MCS Level -/

/-- Conjunction left elimination at MCS level. -/
theorem conj_left_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    φ ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp φ) := lceImp φ ψ
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_conj

/-- Conjunction right elimination at MCS level. -/
theorem conj_right_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    ψ ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp ψ) := rceImp φ ψ
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_conj

/-! ## G/H Implies F/P (Seriality) -/

/-- In an MCS, G(α) implies F(α). -/
private theorem G_implies_F_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (α : Formula Atom)
    (h_G : (𝐆α) ∈ A) :
    (𝐅α) ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree FrameClass.Base [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_G_top_α : Formula.allFuture (Formula.imp top α) ∈ A := by
    have h1 := theoremInMcs h_mcs (DerivationTree.temporal_necessitation _ h_weak)
    have h2 := theoremInMcs h_mcs (tempKDistDerived α (Formula.imp top α))
    exact temporal_implication_property h_mcs
      (temporal_implication_property h_mcs h2 h1) h_G
  have h_top_in : top ∈ A :=
    theoremInMcs h_mcs (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_F_top : (𝐅top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_future trivial)) h_top_in
  have h_TUT : (top U top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.F_until_equiv top) trivial)) h_F_top
  have h_TUα : (top U α) ∈ A := by
    have h1 := temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_until top α top) trivial))
      h_G_top_α
    exact temporal_implication_property h_mcs h1 h_TUT
  exact temporal_implication_property h_mcs
    (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.until_F top α) trivial)) h_TUα

/-- In an MCS, H(α) implies P(α). Mirror of G_implies_F_mcs. -/
private theorem H_implies_P_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (α : Formula Atom)
    (h_H : (𝐇α) ∈ A) :
    (𝐏α) ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree FrameClass.Base [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_H_top_α : Formula.allPast (Formula.imp top α) ∈ A := by
    have h1 := theoremInMcs h_mcs (pastNecessitation _ h_weak)
    have h2 := theoremInMcs h_mcs (pastKDist α (Formula.imp top α))
    exact temporal_implication_property h_mcs
      (temporal_implication_property h_mcs h2 h1) h_H
  have h_top_in : top ∈ A :=
    theoremInMcs h_mcs (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_P_top : (𝐏top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_past trivial)) h_top_in
  have h_TST : (top S top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.P_since_equiv top) trivial)) h_P_top
  have h_TSα : (top S α) ∈ A := by
    have h1 := temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_since top α top) trivial))
      h_H_top_α
    exact temporal_implication_property h_mcs h1 h_TST
  exact temporal_implication_property h_mcs
    (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.since_P top α) trivial)) h_TSα

/-! ## DCS Neg Insert Consistent -/

/-- If B is CUD and φ ∉ B, then {¬φ} ∪ B is consistent. -/
private theorem dcs_neg_union_consistent' {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed Sig)
    {φ : Formula Atom} (h_not : φ ∉ Sig) :
    Temporal.SetConsistent ({φ.neg} ∪ Sig) :=
  dcs_neg_insert_consistent h_dcs.2 h_not

/-! ## R3Maximal / BurgessR3Maximal Properties -/

/-- R3Maximal negation completeness: δ ∉ B implies (¬δ) ∈ B. -/
private theorem r3Maximal_neg_of_not_mem {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal A B C) (δ : Formula Atom) (h_not : δ ∉ B) :
    (¬δ) ∈ B := by
  by_contra h_neg_not
  have h_cons := dcs_neg_insert_consistent h_R3.1.2 h_not
  have h_dc_dcs := deductiveClosure_is_dcs h_cons
  have h_B_sub : B ⊆ deductiveClosure ({δ.neg} ∪ B) :=
    fun φ hφ => subset_deductiveClosure ({δ.neg} ∪ B) (Set.mem_union_right _ hφ)
  have h_neg_in : (¬δ) ∈ deductiveClosure ({δ.neg} ∪ B) :=
    subset_deductiveClosure ({δ.neg} ∪ B) (Set.mem_union_left _ (Set.mem_singleton δ.neg))
  have h_proper : B ⊂ deductiveClosure ({δ.neg} ∪ B) :=
    ⟨h_B_sub, fun h_eq => h_neg_not (h_eq h_neg_in)⟩
  have h_r3 : r3Relation A (deductiveClosure ({δ.neg} ∪ B)) C :=
    r3Relation_subset h_R3.2.1 h_B_sub
  exact h_R3.2.2 _ (deductiveClosure_is_dcs h_cons) h_proper h_r3

/-- R3Maximal forces MCS. -/
private theorem R3Maximal_is_mcs {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal A B C) : Temporal.SetMaximalConsistent B := by
  refine ⟨h_R3.1.1, ?_⟩
  intro φ h_not_φ h_cons_insert
  have h_cons : Temporal.SetConsistent ({φ} ∪ B) := by rwa [Set.insert_eq] at h_cons_insert
  have h_dc_dcs := deductiveClosure_is_dcs h_cons
  have h_B_sub : B ⊆ deductiveClosure ({φ} ∪ B) :=
    fun ψ hψ => subset_deductiveClosure ({φ} ∪ B) (Set.mem_union_right _ hψ)
  have h_φ_in : φ ∈ deductiveClosure ({φ} ∪ B) :=
    subset_deductiveClosure ({φ} ∪ B) (Set.mem_union_left _ (Set.mem_singleton φ))
  exact h_R3.2.2 _ h_dc_dcs ⟨h_B_sub, fun h_eq => h_not_φ (h_eq h_φ_in)⟩
    (r3Relation_subset h_R3.2.1 h_B_sub)

/-- An MCS has no proper DCS extension. -/
private theorem mcs_no_proper_dcs_extension {B D : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent B) (h_dcs : SetDeductivelyClosed D)
    (hBD : B ⊂ D) : False := by
  obtain ⟨φ, h_φ_D, h_φ_not_B⟩ := Set.not_subset.mp hBD.2
  have h_incons := h_mcs.2 φ h_φ_not_B
  apply h_incons
  intro L hL ⟨d⟩
  exact h_dcs.1 L (fun ψ hψ => (Set.insert_subset h_φ_D hBD.1) (hL ψ hψ)) ⟨d⟩

/-! ## BurgessR3Maximal Extension Properties -/

/-- If L is a subset of {delta} union B with B a CUD, and L derives phi, then either
phi is in B, or there exists beta in B with ⊢ (beta ∧ delta) → phi. -/
theorem dc_delta_B_controlled {B : Set (Formula Atom)} (h_dcs : ClosedUnderDerivation B)
    {delta phi : Formula Atom} {L : List (Formula Atom)}
    (hL_sub : ∀ psi ∈ L, psi ∈ ({delta} : Set (Formula Atom)) ∪ B)
    (hL_deriv : DerivationTree FrameClass.Base L phi) :
    (phi ∈ B) ∨ (∃ beta ∈ B, Nonempty (DerivationTree FrameClass.Base [] ((Formula.and beta delta).imp phi))) := by
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
    have d_w : DerivationTree FrameClass.Base (delta :: L_B) phi :=
      DerivationTree.weakening L (delta :: L_B) phi hL_deriv hL_sub_dB
    have d_imp := deductionTheorem L_B delta phi d_w
    have hLB_sub : ∀ psi ∈ L_B, psi ∈ B := by
      intro psi hpsi; exact decide_eq_true_eq.mp (List.mem_filter.mp hpsi).2
    by_cases hLB_empty : L_B = []
    · rw [hLB_empty] at d_imp
      -- When L_B is empty, ⊢ delta → phi. Need ⊢ (top ∧ delta) → phi.
      have h_top_B : ((Formula.bot : Formula Atom).imp Formula.bot) ∈ B :=
        cud_contains_theorems h_dcs
          (DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.efq (Formula.bot : Formula Atom)) trivial)
      exact Or.inr ⟨Formula.bot.imp Formula.bot, h_top_B, ⟨impTrans (rceImp (Formula.bot.imp Formula.bot) delta) d_imp⟩⟩
    · have h_imp_B : (delta → phi) ∈ B := h_dcs L_B _ hLB_sub d_imp
      right
      refine ⟨delta.imp phi, h_imp_B, ⟨?_⟩⟩
      have h_l : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] (delta.imp phi) :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) (delta.imp phi)
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (lceImp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_r : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] delta :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) delta
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (rceImp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_mp : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] phi :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)] delta phi h_l h_r
      exact deductionTheorem [] (Formula.and (delta.imp phi) delta) phi h_mp
  · left
    have hL_B : ∀ psi ∈ L, psi ∈ B := by
      intro psi hpsi
      rcases hL_sub psi hpsi with h | h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hpsi) h_delta_L
      · exact h
    exact h_dcs L phi hL_B hL_deriv

/-- BurgessR3Maximal extension fails: if δ ∉ B, then DC({δ} ∪ B) does NOT satisfy burgessR3. -/
theorem BurgessR3Maximal_extension_fails {A B C : Set (Formula Atom)}
    (h_R3M : BurgessR3Maximal A B C)
    {delta : Formula Atom} (h_delta_not : delta ∉ B) :
    ¬burgessR3 A (deductiveClosure ({delta} ∪ B)) C := by
  intro h_r3
  have h_cud : ClosedUnderDerivation (deductiveClosure ({delta} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  have h_sub : B ⊆ deductiveClosure ({delta} ∪ B) :=
    fun phi hphi => subset_deductiveClosure ({delta} ∪ B) (Set.mem_union_right _ hphi)
  have h_delta_in : delta ∈ deductiveClosure ({delta} ∪ B) :=
    subset_deductiveClosure ({delta} ∪ B) (Set.mem_union_left _ (Set.mem_singleton delta))
  have h_proper : B ⊂ deductiveClosure ({delta} ∪ B) :=
    ⟨h_sub, fun h_eq => h_delta_not (h_eq h_delta_in)⟩
  exact h_R3M.2.2 _ h_cud h_proper h_r3

/-- dc_delta_B_burgessR3: Extension of B by delta preserves burgessR3. -/
theorem dc_delta_B_burgessR3 {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_dcs : ClosedUnderDerivation B)
    (h_r3 : burgessR3 A B C)
    {delta : Formula Atom}
    (h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C, Formula.untl (Formula.and beta delta) gamma ∈ A)
    (h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A, Formula.snce (Formula.and beta delta) alpha ∈ C) :
    burgessR3 A (deductiveClosure ({delta} ∪ B)) C := by
  constructor
  · intro phi hphi gamma hgamma
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨hImpl⟩⟩
    · exact h_r3.1 phi h_B gamma hgamma
    · exact untl_left_mono_thm h_mcs_A hImpl (h_until_all beta hbeta gamma hgamma)
  · intro phi hphi alpha halpha
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨hImpl⟩⟩
    · exact h_r3.2 phi h_B alpha halpha
    · exact snce_left_mono_thm h_mcs_C hImpl (h_since_all beta hbeta alpha halpha)


end Cslib.Logic.Temporal.Metalogic.Chronicle
