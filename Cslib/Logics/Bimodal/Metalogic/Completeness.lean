/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers

/-!
# MCS Completeness Properties for Bimodal Logic

This module provides modal and propositional MCS properties needed for the
completeness theorem of TM (Tense and Modality) bimodal logic.

## Main Results

Propositional MCS properties:
- `SetMaximalConsistent.disjunction_intro`: phi or psi in MCS
- `SetMaximalConsistent.disjunction_elim`: MCS disjunction elimination
- `SetMaximalConsistent.disjunction_iff`: Iff wrapper
- `SetMaximalConsistent.conjunction_intro`: phi and psi in MCS
- `SetMaximalConsistent.conjunction_elim`: MCS conjunction elimination
- `SetMaximalConsistent.conjunction_iff`: Iff wrapper

Modal MCS properties:
- `SetMaximalConsistent.box_closure`: Modal T for MCS
- `SetMaximalConsistent.box_box`: Modal 4 for MCS

Diamond-box duality:
- `SetMaximalConsistent.neg_box_implies_diamond_neg`
- `SetMaximalConsistent.diamond_neg_implies_neg_box`
- `SetMaximalConsistent.diamond_box_duality`: Iff wrapper

## References

* Modal Logic, Blackburn et al., Chapter 4 (Canonical Models)
* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Completeness.lean
-/

set_option linter.style.emptyLine false
set_option linter.flexible false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic

open Cslib.Logic.Bimodal
open Cslib.Logic

open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-!
### Propositional MCS Properties

These lemmas establish propositional closure properties for set-based maximal
consistent sets: disjunction intro/elim/iff and conjunction intro/elim/iff.
-/

/--
Set-based MCS: disjunction property (forward direction).

If phi in Omega or psi in Omega, then (phi or psi) in Omega.
Uses orI1 and orI2 axioms.
-/
theorem SetMaximalConsistent.disjunction_intro {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : φ ∈ Omega ∨ ψ ∈ Omega) : (φ.or ψ) ∈ Omega := by
  cases h with
  | inl h_phi =>
    have h_orI1_thm : DerivationTree fc [] (φ.imp (Formula.or φ ψ)) :=
      DerivationTree.axiom [] _ (Axiom.orI1 φ ψ) (FrameClass.base_le fc)
    have h_orI1 : DerivationTree fc [φ] (φ.imp (Formula.or φ ψ)) :=
      DerivationTree.weakening [] _ _ h_orI1_thm (by intro; simp)
    have h_assume : DerivationTree fc [φ] φ :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [φ] (Formula.or φ ψ) :=
      DerivationTree.modus_ponens _ _ _ h_orI1 h_assume
    have h_sub : ∀ χ ∈ [φ], χ ∈ Omega := by simp [h_phi]
    exact SetMaximalConsistent.closed_under_derivation h_mcs [φ] h_sub h_deriv
  | inr h_psi =>
    have h_orI2_thm : DerivationTree fc [] (ψ.imp (Formula.or φ ψ)) :=
      DerivationTree.axiom [] _ (Axiom.orI2 φ ψ) (FrameClass.base_le fc)
    have h_orI2 : DerivationTree fc [ψ] (ψ.imp (Formula.or φ ψ)) :=
      DerivationTree.weakening [] _ _ h_orI2_thm (by intro; simp)
    have h_assume : DerivationTree fc [ψ] ψ :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [ψ] (Formula.or φ ψ) :=
      DerivationTree.modus_ponens _ _ _ h_orI2 h_assume
    have h_sub : ∀ χ ∈ [ψ], χ ∈ Omega := by simp [h_psi]
    exact SetMaximalConsistent.closed_under_derivation h_mcs [ψ] h_sub h_deriv

/--
Set-based MCS: disjunction property (backward direction).

If (phi or psi) in Omega, then phi in Omega or psi in Omega.
-/
theorem SetMaximalConsistent.disjunction_elim {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : (φ.or ψ) ∈ Omega) : φ ∈ Omega ∨ ψ ∈ Omega := by
  cases SetMaximalConsistent.negation_complete h_mcs φ with
  | inl h_phi => exact Or.inl h_phi
  | inr h_neg_phi =>
    right
    -- From [φ.neg, φ.or ψ], derive ψ:
    -- Step 1: from φ.neg, derive φ → ψ (via ex falso on φ ∧ ¬φ → ⊥ → ψ)
    -- Step 2: derive ψ → ψ (identity)
    -- Step 3: use orE axiom: (φ→ψ) → ((ψ→ψ) → ((φ∨ψ) → ψ))
    have h_sub : ∀ χ ∈ [φ.neg, Formula.or φ ψ], χ ∈ Omega := by
      intro χ h_mem
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_mem
      cases h_mem with
      | inl h_eq => exact h_eq ▸ h_neg_phi
      | inr h_eq => exact h_eq ▸ h
    have h_deriv : DerivationTree fc [φ.neg, Formula.or φ ψ] ψ := by
      -- φ → ψ from ¬φ (ex falso)
      have h_neg_assume : DerivationTree fc [φ.neg, Formula.or φ ψ] φ.neg :=
        DerivationTree.assumption _ _ (by simp)
      have h_or_assume : DerivationTree fc [φ.neg, Formula.or φ ψ] (Formula.or φ ψ) :=
        DerivationTree.assumption _ _ (by simp)
      -- φ → ⊥ (i.e., ¬φ), then ⊥ → ψ (efq), so φ → ψ
      have h_efq_thm : DerivationTree fc [] (Formula.bot.imp ψ) :=
        DerivationTree.axiom [] _ (Axiom.efq ψ) (FrameClass.base_le fc)
      have h_efq : DerivationTree fc [φ.neg, Formula.or φ ψ] (Formula.bot.imp ψ) :=
        DerivationTree.weakening [] _ _ h_efq_thm (by intro; simp)
      -- Derive (φ → ψ) by deduction: assume φ, derive ⊥ from φ ∧ ¬φ, then ψ
      have h_phi_imp_psi : DerivationTree fc [φ.neg, Formula.or φ ψ] (φ.imp ψ) := by
        have h_inner : DerivationTree fc (φ :: [φ.neg, Formula.or φ ψ]) ψ := by
          have h1 : DerivationTree fc (φ :: [φ.neg, Formula.or φ ψ]) φ :=
            DerivationTree.assumption _ _ (by simp)
          have h2 : DerivationTree fc (φ :: [φ.neg, Formula.or φ ψ]) φ.neg :=
            DerivationTree.assumption _ _ (by simp)
          have h_bot : DerivationTree fc (φ :: [φ.neg, Formula.or φ ψ]) Formula.bot :=
            derivesBotFromPhiNegPhi h1 h2
          have h_efq2 : DerivationTree fc (φ :: [φ.neg, Formula.or φ ψ]) (Formula.bot.imp ψ) :=
            DerivationTree.weakening [] _ _ h_efq_thm (by intro; simp)
          exact DerivationTree.modus_ponens _ _ _ h_efq2 h_bot
        exact deductionTheorem [φ.neg, Formula.or φ ψ] φ ψ h_inner
      -- ψ → ψ (identity: from ⊢ ψ → ψ via deduction theorem on empty context)
      have h_psi_imp_psi_thm : DerivationTree fc [] (ψ.imp ψ) :=
        deductionTheorem [] ψ ψ (DerivationTree.assumption [ψ] ψ (by simp))
      have h_psi_imp_psi : DerivationTree fc [φ.neg, Formula.or φ ψ] (ψ.imp ψ) :=
        DerivationTree.weakening [] _ _ h_psi_imp_psi_thm (by intro; simp)
      -- orE: (φ→ψ) → ((ψ→ψ) → ((φ∨ψ) → ψ))
      have h_orE_thm : DerivationTree fc [] ((φ.imp ψ).imp ((ψ.imp ψ).imp ((Formula.or φ ψ).imp ψ))) :=
        DerivationTree.axiom [] _ (Axiom.orE φ ψ ψ) (FrameClass.base_le fc)
      have h_orE : DerivationTree fc [φ.neg, Formula.or φ ψ]
          ((φ.imp ψ).imp ((ψ.imp ψ).imp ((Formula.or φ ψ).imp ψ))) :=
        DerivationTree.weakening [] _ _ h_orE_thm (by intro; simp)
      have h1 := DerivationTree.modus_ponens _ _ _ h_orE h_phi_imp_psi
      have h2 := DerivationTree.modus_ponens _ _ _ h1 h_psi_imp_psi
      exact DerivationTree.modus_ponens _ _ _ h2 h_or_assume
    exact SetMaximalConsistent.closed_under_derivation h_mcs [φ.neg, Formula.or φ ψ] h_sub h_deriv

/--
Set-based MCS: disjunction iff property.

(phi or psi) in Omega iff (phi in Omega or psi in Omega).
-/
theorem SetMaximalConsistent.disjunction_iff {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega) :
    (φ.or ψ) ∈ Omega ↔ (φ ∈ Omega ∨ ψ ∈ Omega) :=
  ⟨SetMaximalConsistent.disjunction_elim h_mcs, SetMaximalConsistent.disjunction_intro h_mcs⟩

/--
Set-based MCS: conjunction property (forward direction).

If phi in Omega and psi in Omega, then (phi and psi) in Omega.
Uses andI axiom directly.
-/
theorem SetMaximalConsistent.conjunction_intro {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_phi : φ ∈ Omega) (h_psi : ψ ∈ Omega) : (φ.and ψ) ∈ Omega := by
  -- Use andI axiom: φ → (ψ → (φ ∧ ψ))
  have h_andI_thm : DerivationTree fc [] (φ.imp (ψ.imp (Formula.and φ ψ))) :=
    DerivationTree.axiom [] _ (Axiom.andI φ ψ) (FrameClass.base_le fc)
  have h_sub : ∀ χ ∈ [φ, ψ], χ ∈ Omega := by
    intro χ h_mem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_mem
    cases h_mem with
    | inl h_eq => exact h_eq ▸ h_phi
    | inr h_eq => exact h_eq ▸ h_psi
  have h_andI : DerivationTree fc [φ, ψ] (φ.imp (ψ.imp (Formula.and φ ψ))) :=
    DerivationTree.weakening [] _ _ h_andI_thm (by intro; simp)
  have h_phi_assume : DerivationTree fc [φ, ψ] φ :=
    DerivationTree.assumption _ _ (by simp)
  have h_psi_assume : DerivationTree fc [φ, ψ] ψ :=
    DerivationTree.assumption _ _ (by simp)
  have h_step1 := DerivationTree.modus_ponens _ _ _ h_andI h_phi_assume
  have h_deriv := DerivationTree.modus_ponens _ _ _ h_step1 h_psi_assume
  exact SetMaximalConsistent.closed_under_derivation h_mcs [φ, ψ] h_sub h_deriv

/--
Set-based MCS: conjunction property (backward direction).

If (phi and psi) in Omega, then phi in Omega and psi in Omega.
Uses andE1 and andE2 axioms directly.
-/
theorem SetMaximalConsistent.conjunction_elim {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : (φ.and ψ) ∈ Omega) : φ ∈ Omega ∧ ψ ∈ Omega := by
  constructor
  · -- Show phi in Omega using andE1: (φ ∧ ψ) → φ
    have h_andE1_thm : DerivationTree fc [] ((Formula.and φ ψ).imp φ) :=
      DerivationTree.axiom [] _ (Axiom.andE1 φ ψ) (FrameClass.base_le fc)
    have h_andE1 : DerivationTree fc [Formula.and φ ψ] ((Formula.and φ ψ).imp φ) :=
      DerivationTree.weakening [] _ _ h_andE1_thm (by intro; simp)
    have h_assume : DerivationTree fc [Formula.and φ ψ] (Formula.and φ ψ) :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [Formula.and φ ψ] φ :=
      DerivationTree.modus_ponens _ _ _ h_andE1 h_assume
    have h_sub : ∀ χ ∈ [Formula.and φ ψ], χ ∈ Omega := by simp [h]
    exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.and φ ψ] h_sub h_deriv
  · -- Show psi in Omega using andE2: (φ ∧ ψ) → ψ
    have h_andE2_thm : DerivationTree fc [] ((Formula.and φ ψ).imp ψ) :=
      DerivationTree.axiom [] _ (Axiom.andE2 φ ψ) (FrameClass.base_le fc)
    have h_andE2 : DerivationTree fc [Formula.and φ ψ] ((Formula.and φ ψ).imp ψ) :=
      DerivationTree.weakening [] _ _ h_andE2_thm (by intro; simp)
    have h_assume : DerivationTree fc [Formula.and φ ψ] (Formula.and φ ψ) :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [Formula.and φ ψ] ψ :=
      DerivationTree.modus_ponens _ _ _ h_andE2 h_assume
    have h_sub : ∀ χ ∈ [Formula.and φ ψ], χ ∈ Omega := by simp [h]
    exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.and φ ψ] h_sub h_deriv

/--
Set-based MCS: conjunction iff property.

(phi and psi) in Omega iff (phi in Omega and psi in Omega).
-/
theorem SetMaximalConsistent.conjunction_iff {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega) :
    (φ.and ψ) ∈ Omega ↔ (φ ∈ Omega ∧ ψ ∈ Omega) :=
  ⟨SetMaximalConsistent.conjunction_elim h_mcs,
   fun ⟨h1, h2⟩ => SetMaximalConsistent.conjunction_intro h_mcs h1 h2⟩

/-!
### Modal Closure Properties

These lemmas establish modal closure properties for SetMaximalConsistent sets,
using the Modal T axiom (box phi -> phi) to derive that necessity implies truth.
-/

/--
Set-based MCS: box closure property.

If box phi in Omega for a SetMaximalConsistent Omega, then phi in Omega.

**Proof Strategy**:
1. Modal T axiom: box phi -> phi
2. With box phi in Omega, derive phi via modus ponens
3. By closure: phi in Omega
-/
theorem SetMaximalConsistent.box_closure {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_box : Formula.box φ ∈ Omega) : φ ∈ Omega := by
  have h_modal_t_thm : DerivationTree fc [] ((Formula.box φ).imp φ) :=
    DerivationTree.axiom [] _ (Axiom.modal_t φ) (FrameClass.base_le fc)
  have h_modal_t : DerivationTree fc [Formula.box φ] ((Formula.box φ).imp φ) :=
    DerivationTree.weakening [] _ _ h_modal_t_thm (by intro; simp)
  have h_box_assume : DerivationTree fc [Formula.box φ] (Formula.box φ) :=
    DerivationTree.assumption _ _ (by simp)
  have h_deriv : DerivationTree fc [Formula.box φ] φ :=
    DerivationTree.modus_ponens _ _ _ h_modal_t h_box_assume
  have h_sub : ∀ χ ∈ [Formula.box φ], χ ∈ Omega := by simp [h_box]
  exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.box φ] h_sub h_deriv

/--
Set-based MCS: modal 4 axiom property.

If box phi in Omega for a SetMaximalConsistent Omega, then box(box phi) in Omega.

**Proof Strategy**:
1. Modal 4 axiom: box phi -> box(box phi)
2. With box phi in Omega, derive box(box phi) via modus ponens
3. By closure: box(box phi) in Omega
-/
theorem SetMaximalConsistent.box_box {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_box : Formula.box φ ∈ Omega) : (Formula.box φ).box ∈ Omega := by
  have h_modal_4_thm : DerivationTree fc []
      ((Formula.box φ).imp (Formula.box (Formula.box φ))) :=
    DerivationTree.axiom [] _ (Axiom.modal_4 φ) (FrameClass.base_le fc)
  have h_modal_4 : DerivationTree fc [Formula.box φ]
      ((Formula.box φ).imp (Formula.box (Formula.box φ))) :=
    DerivationTree.weakening [] _ _ h_modal_4_thm (by intro; simp)
  have h_box_assume : DerivationTree fc [Formula.box φ] (Formula.box φ) :=
    DerivationTree.assumption _ _ (by simp)
  have h_deriv : DerivationTree fc [Formula.box φ] (Formula.box φ).box :=
    DerivationTree.modus_ponens _ _ _ h_modal_4 h_box_assume
  have h_sub : ∀ χ ∈ [Formula.box φ], χ ∈ Omega := by simp [h_box]
  exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.box φ] h_sub h_deriv

/-!
### Diamond-Box Duality

These lemmas establish the classical duality between box and diamond modalities
for MCS membership: neg(box phi) iff diamond(neg phi).
-/

noncomputable section

open Cslib.Logic.Bimodal.Theorems.Perpetuity (doubleNegation dni)

/--
Set-based MCS: diamond-box duality (forward direction).

If neg(box phi) in Omega, then diamond(neg phi) in Omega.

Note: diamond psi = neg(box(neg psi)), so diamond(neg phi) = neg(box(neg(neg phi))).
-/
theorem SetMaximalConsistent.neg_box_implies_diamond_neg {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : (Formula.box φ).neg ∈ Omega) : φ.neg.diamond ∈ Omega := by
  unfold Formula.diamond
  cases SetMaximalConsistent.negation_complete h_mcs (φ.neg.neg.box) with
  | inr h_neg => exact h_neg
  | inl h_dne_box =>
    exfalso
    have h_dne : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.neg.neg.imp φ) := doubleNegation φ
    have h_nec_dne : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.neg.neg.imp φ).box :=
      DerivationTree.necessitation _ h_dne
    have h_modal_k : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.neg.neg.imp φ).box.imp ((φ.neg.neg.box).imp (φ.box))) :=
      DerivationTree.axiom [] _ (Axiom.modal_k_dist φ.neg.neg φ) trivial
    have h_impl : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.neg.neg.box).imp (φ.box)) :=
      DerivationTree.modus_ponens [] _ _ h_modal_k h_nec_dne
    -- Lift to generic fc
    have h_impl_fc : DerivationTree fc ([] : List (Formula Atom))
        ((φ.neg.neg.box).imp (φ.box)) :=
      DerivationTree.lift (FrameClass.base_le fc) h_impl
    have h_sub : ∀ χ ∈ [φ.neg.neg.box], χ ∈ Omega := by simp [h_dne_box]
    have h_impl_ctx : DerivationTree fc [φ.neg.neg.box]
        ((φ.neg.neg.box).imp (φ.box)) :=
      DerivationTree.weakening [] _ _ h_impl_fc (by intro; simp)
    have h_assume : DerivationTree fc [φ.neg.neg.box] φ.neg.neg.box :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [φ.neg.neg.box] φ.box :=
      DerivationTree.modus_ponens _ _ _ h_impl_ctx h_assume
    have h_box_in : φ.box ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs [φ.neg.neg.box] h_sub h_deriv
    have h_deriv_bot : DerivationTree fc [φ.box, (φ.box).neg] Formula.bot := by
      have h1 : DerivationTree fc [φ.box, (φ.box).neg] φ.box :=
        DerivationTree.assumption _ _ (by simp)
      have h2 : DerivationTree fc [φ.box, (φ.box).neg] (φ.box).neg :=
        DerivationTree.assumption _ _ (by simp)
      exact derivesBotFromPhiNegPhi h1 h2
    have h_sub2 : ∀ χ ∈ [φ.box, (φ.box).neg], χ ∈ Omega := by
      intro χ hχ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hχ
      cases hχ with
      | inl h_eq => exact h_eq ▸ h_box_in
      | inr h_eq => exact h_eq ▸ h
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs _ h_sub2 h_deriv_bot
    have h_bot_deriv : DerivationTree fc
        [(Formula.bot : Formula Atom)] Formula.bot :=
      DerivationTree.assumption _ _ (by simp)
    exact h_mcs.1 [(Formula.bot : Formula Atom)]
      (by simp [h_bot_in]) ⟨h_bot_deriv⟩

/--
Set-based MCS: diamond-box duality (backward direction).

If diamond(neg phi) in Omega, then neg(box phi) in Omega.
-/
theorem SetMaximalConsistent.diamond_neg_implies_neg_box {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : φ.neg.diamond ∈ Omega) : (Formula.box φ).neg ∈ Omega := by
  unfold Formula.diamond at h
  cases SetMaximalConsistent.negation_complete h_mcs (Formula.box φ) with
  | inr h_neg => exact h_neg
  | inl h_box =>
    exfalso
    have h_dni : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.imp φ.neg.neg) := dni φ
    have h_nec_dni : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.imp φ.neg.neg).box :=
      DerivationTree.necessitation _ h_dni
    have h_modal_k : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.imp φ.neg.neg).box.imp ((φ.box).imp (φ.neg.neg.box))) :=
      DerivationTree.axiom [] _ (Axiom.modal_k_dist φ φ.neg.neg) trivial
    have h_impl : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.box).imp (φ.neg.neg.box)) :=
      DerivationTree.modus_ponens [] _ _ h_modal_k h_nec_dni
    -- Lift to generic fc
    have h_impl_fc : DerivationTree fc ([] : List (Formula Atom))
        ((φ.box).imp (φ.neg.neg.box)) :=
      DerivationTree.lift (FrameClass.base_le fc) h_impl
    have h_sub : ∀ χ ∈ [φ.box], χ ∈ Omega := by simp [h_box]
    have h_impl_ctx : DerivationTree fc [φ.box]
        ((φ.box).imp (φ.neg.neg.box)) :=
      DerivationTree.weakening [] _ _ h_impl_fc (by intro; simp)
    have h_assume : DerivationTree fc [φ.box] φ.box :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [φ.box] φ.neg.neg.box :=
      DerivationTree.modus_ponens _ _ _ h_impl_ctx h_assume
    have h_dne_box_in : φ.neg.neg.box ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs [φ.box] h_sub h_deriv
    have h_deriv_bot : DerivationTree fc
        [φ.neg.neg.box, (φ.neg.neg.box).neg] Formula.bot := by
      have h1 : DerivationTree fc [φ.neg.neg.box, (φ.neg.neg.box).neg]
          φ.neg.neg.box :=
        DerivationTree.assumption _ _ (by simp)
      have h2 : DerivationTree fc [φ.neg.neg.box, (φ.neg.neg.box).neg]
          (φ.neg.neg.box).neg :=
        DerivationTree.assumption _ _ (by simp)
      exact derivesBotFromPhiNegPhi h1 h2
    have h_sub2 : ∀ χ ∈ [φ.neg.neg.box, (φ.neg.neg.box).neg], χ ∈ Omega := by
      intro χ hχ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hχ
      cases hχ with
      | inl h_eq => exact h_eq ▸ h_dne_box_in
      | inr h_eq => exact h_eq ▸ h
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs _ h_sub2 h_deriv_bot
    have h_bot_deriv : DerivationTree fc
        [(Formula.bot : Formula Atom)] Formula.bot :=
      DerivationTree.assumption _ _ (by simp)
    exact h_mcs.1 [(Formula.bot : Formula Atom)]
      (by simp [h_bot_in]) ⟨h_bot_deriv⟩

/--
Set-based MCS: diamond-box duality iff property.

neg(box phi) in Omega iff diamond(neg phi) in Omega.

This establishes the classical duality between box and diamond:
neg(box phi) iff diamond(neg phi) (equivalently, box phi iff neg(diamond(neg phi))).
-/
theorem SetMaximalConsistent.diamond_box_duality {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega) :
    (Formula.box φ).neg ∈ Omega ↔ φ.neg.diamond ∈ Omega :=
  ⟨SetMaximalConsistent.neg_box_implies_diamond_neg h_mcs,
   SetMaximalConsistent.diamond_neg_implies_neg_box h_mcs⟩

end -- noncomputable section

end Cslib.Logic.Bimodal.Metalogic
