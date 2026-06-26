/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Foundations.Logic.Metalogic.MCSProperties
public import Cslib.Logics.Bimodal.ProofSystem.Instances

/-! # GenericMCS Bridge for Bimodal Logic TM

This module proves the bidirectional equivalence between the tree-based
`bimodalDerivationSystem` and the algebraic `algebraicDerivationSystem` instantiated
at `S := Bimodal.HilbertTM`.

## Main Results

- `deriv_tree_to_list`: `DerivationTree .Base Γ φ → (bimodalAlgDS).Deriv Γ φ`
  (forward, structural induction on the tree).
- `unfold_listImp_in_tree`: `Γ ⊢ listImp Ψ φ → Ψ ⊆ Γ → Γ ⊢ φ`
  (backward helper).
- `list_deriv_to_tree`: `(bimodalAlgDS).Deriv Γ φ → DerivationTree .Base Γ φ`
  (backward direction).
- `bimodal_deriv_iff_algebraic`: bidirectional equivalence on derivability.
- `bimodal_setConsistent_iff_algebraic`: consistency equivalence.
- `bimodal_setMaxConsistent_iff_algebraic`: MCS equivalence.

## Architecture

`bimodalDerivationSystem.Deriv Γ φ = Bimodal.Deriv Γ φ`
  `= Nonempty (DerivationTree FrameClass.Base Γ φ)`

`(bimodalAlgDS).Deriv Γ φ`
  `= ListDeriv Γ φ` (with `S` inferred as `Bimodal.HilbertTM`)
  `= InferenceSystem.DerivableIn HilbertTM (listImp Γ φ)`
  `= Nonempty (DerivationTree FrameClass.Base [] (listImp Γ φ))`

**Forward** (tree → algebraic): structural induction on the `DerivationTree`. Each
constructor maps to a corresponding algebraic derivation operation. The three
non-propositional rules (`necessitation`, `temporal_necessitation`, `temporal_duality`)
only fire at empty context and bottom out at `InferenceSystem.DerivableIn HilbertTM`.

**Backward** (algebraic → tree): extract `d₀ : [] ⊢ listImp Γ φ`, weaken to
`Γ ⊢ listImp Γ φ`, then apply `unfold_listImp_in_tree` to eliminate each layer.

## Design Note

This file does NOT import `Core/DeductionTheorem.lean`. The equivalence is derived
directly from the `InferenceSystem` and `MinimalHilbert` instances for `HilbertTM`
(registered in `Bimodal.ProofSystem.Instances`). This ensures `DeductionTheorem.lean`
can import this bridge without creating a cycle.

## References

* Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean — direct template
* Cslib/Foundations/Logic/Metalogic/GenericMCS.lean
* Cslib/Foundations/Logic/Metalogic/MCSProperties.lean
* Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean — gap analysis (documentation only)
-/

set_option linter.dupNamespace false
set_option linter.style.setOption false
set_option maxHeartbeats 400000

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Core

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction
open Cslib.Logic.Metalogic.GenericMCS
open Cslib.Logic.Metalogic.MCSProperties
open Cslib.Logic.Metalogic
open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-- Shorthand for the algebraic derivation system at `Bimodal.HilbertTM`. -/
@[reducible] def bimodalAlgDS : Metalogic.DerivationSystem (Bimodal.Formula Atom) :=
  @algebraicDerivationSystem (Bimodal.Formula Atom) _ _ Bimodal.HilbertTM _ _

/-! ## Forward Direction: DerivationTree → Algebraic Deriv -/

/-- Forward bridge: given `d : DerivationTree FrameClass.Base Γ φ`, produce
`bimodalAlgDS.Deriv Γ φ` by structural induction on the derivation tree.

- **axiom**: the axiom `⊢ ψ` in `HilbertTM` lifts to `Deriv Γ ψ` via K-weakening.
- **assumption**: reflected directly.
- **modus_ponens**: contextual modus ponens.
- **necessitation**: box-necessitation gives `⊢ □ψ` in `HilbertTM`.
- **temporal_necessitation**: G-necessitation gives `⊢ Gψ` in `HilbertTM`.
- **temporal_duality**: construct the dual tree using `temporal_duality`.
- **weakening**: monotone in the context. -/
noncomputable def deriv_tree_to_list
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (d : Bimodal.DerivationTree FrameClass.Base Γ φ) :
    (bimodalAlgDS (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | «axiom» Γ ψ h_ax h_fc =>
    -- ψ is a HilbertTM theorem
    have h_thm : InferenceSystem.DerivableIn Bimodal.HilbertTM ψ :=
      ⟨Bimodal.DerivationTree.axiom [] ψ h_ax h_fc⟩
    -- Lift to the algebraic system via K-weakening: ⊢ ψ → listImp Γ ψ, then MP
    simp only [bimodalAlgDS, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [bimodalAlgDS, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [bimodalAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @necessitation ψ _d ih =>
    -- ih : bimodalAlgDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn HilbertTM ψ
    simp only [bimodalAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn Bimodal.HilbertTM ψ := by
      unfold ListDeriv at ih
      simp only [listImp_nil] at ih
      exact ih
    -- Box-necessitation: ⊢ ψ → ⊢ □ψ in HilbertTM
    unfold ListDeriv
    simp only [listImp_nil]
    -- Construct □ψ derivation directly using the tree constructor
    exact ⟨Bimodal.DerivationTree.necessitation ψ h_thm.toDerivation⟩
  | @temporal_necessitation ψ _d ih =>
    -- ih : bimodalAlgDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn HilbertTM ψ
    simp only [bimodalAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn Bimodal.HilbertTM ψ := by
      unfold ListDeriv at ih
      simp only [listImp_nil] at ih
      exact ih
    -- G-necessitation: ⊢ ψ → ⊢ G(ψ) in HilbertTM
    unfold ListDeriv
    simp only [listImp_nil]
    -- Construct G(ψ) derivation directly using the tree constructor
    exact ⟨Bimodal.DerivationTree.temporal_necessitation ψ h_thm.toDerivation⟩
  | @temporal_duality ψ _d ih =>
    -- ih : bimodalAlgDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn HilbertTM ψ
    simp only [bimodalAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn Bimodal.HilbertTM ψ := by
      unfold ListDeriv at ih
      simp only [listImp_nil] at ih
      exact ih
    -- Construct the temporal-dual derivation
    have h_dual : InferenceSystem.DerivableIn Bimodal.HilbertTM ψ.swapTemporal :=
      ⟨Bimodal.DerivationTree.temporal_duality ψ h_thm.toDerivation⟩
    unfold ListDeriv
    simp only [listImp_nil]
    exact h_dual
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [bimodalAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih

/-! ## Backward Helper: Unfold listImp Using Assumptions -/

/-- Backward helper: given `Γ ⊢ listImp Ψ φ` (tree) and `Ψ ⊆ Γ`,
produce `Γ ⊢ φ` by iterating modus ponens with assumption trees.

Induction on `Ψ`: in the cons case, `a ∈ Γ` gives `Γ ⊢ a` by assumption,
then MP reduces `listImp (a :: Ψ') φ` to `listImp Ψ' φ`. -/
noncomputable def unfold_listImp_in_tree
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (Ψ : Bimodal.Context Atom)
    (d : Bimodal.DerivationTree FrameClass.Base Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    Bimodal.DerivationTree FrameClass.Base Γ φ := by
  induction Ψ generalizing φ with
  | nil =>
    simp only [listImp_nil] at d
    exact d
  | cons a Ψ' ih =>
    simp only [listImp_cons] at d
    -- d : Γ ⊢ a → listImp Ψ' φ
    have ha_mem : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
    have d_a : Bimodal.DerivationTree FrameClass.Base Γ a :=
      Bimodal.DerivationTree.assumption Γ a ha_mem
    have d_tail : Bimodal.DerivationTree FrameClass.Base Γ (listImp Ψ' φ) :=
      Bimodal.DerivationTree.modus_ponens Γ a (listImp Ψ' φ) d d_a
    exact ih d_tail (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-! ## Backward Direction: Algebraic Deriv → DerivationTree -/

/-- Backward bridge: `bimodalAlgDS.Deriv Γ φ → DerivationTree .Base Γ φ`.

Extracts `d₀ : [] ⊢ listImp Γ φ` from the algebraic derivation, weakens to `Γ`,
then applies `unfold_listImp_in_tree` to eliminate the list-implication layers. -/
noncomputable def list_deriv_to_tree
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (h : (bimodalAlgDS (Atom := Atom)).Deriv Γ φ) :
    Bimodal.DerivationTree FrameClass.Base Γ φ := by
  simp only [bimodalAlgDS, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  -- h : InferenceSystem.DerivableIn HilbertTM (listImp Γ φ)
  -- = Nonempty (DerivationTree .Base [] (listImp Γ φ))
  have d₀ : Bimodal.DerivationTree FrameClass.Base [] (listImp Γ φ) := h.toDerivation
  -- Weaken from [] to Γ
  have d_weak : Bimodal.DerivationTree FrameClass.Base Γ (listImp Γ φ) :=
    Bimodal.DerivationTree.weakening [] Γ (listImp Γ φ) d₀ (List.nil_subset Γ)
  -- Eliminate listImp using assumption trees
  exact unfold_listImp_in_tree Γ d_weak (fun _a ha => ha)

/-! ## Full Derivability Equivalence -/

/-- Bidirectional derivability equivalence between `bimodalDerivationSystem` and
the algebraic derivation system at `S := Bimodal.HilbertTM`. -/
theorem bimodal_deriv_iff_algebraic
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom} :
    bimodalDerivationSystem.Deriv Γ φ ↔
    (bimodalAlgDS (Atom := Atom)).Deriv Γ φ := by
  unfold bimodalDerivationSystem Bimodal.Deriv
  constructor
  · intro ⟨d⟩
    exact deriv_tree_to_list d
  · intro h
    exact ⟨list_deriv_to_tree h⟩

/-! ## MCS Equivalences -/

/-- `SetConsistent` under `bimodalDerivationSystem` iff under `bimodalAlgDS`. -/
theorem bimodal_setConsistent_iff_algebraic
    {Ω : Set (Bimodal.Formula Atom)} :
    SetConsistent bimodalDerivationSystem Ω ↔
    SetConsistent (bimodalAlgDS (Atom := Atom)) Ω := by
  unfold SetConsistent Consistent
  constructor
  · intro h L hL hd
    exact h L hL (bimodal_deriv_iff_algebraic.mpr hd)
  · intro h L hL hd
    exact h L hL (bimodal_deriv_iff_algebraic.mp hd)

/-- `SetMaximalConsistent` under `bimodalDerivationSystem` iff under `bimodalAlgDS`. -/
theorem bimodal_setMaxConsistent_iff_algebraic
    {Ω : Set (Bimodal.Formula Atom)} :
    SetMaximalConsistent bimodalDerivationSystem Ω ↔
    SetMaximalConsistent (bimodalAlgDS (Atom := Atom)) Ω := by
  unfold SetMaximalConsistent
  constructor
  · intro ⟨hcons, hmax⟩
    refine ⟨bimodal_setConsistent_iff_algebraic.mp hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (bimodal_setConsistent_iff_algebraic.mpr hinsert)
  · intro ⟨hcons, hmax⟩
    refine ⟨bimodal_setConsistent_iff_algebraic.mpr hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (bimodal_setConsistent_iff_algebraic.mp hinsert)

end Cslib.Logic.Bimodal.Metalogic.Core
