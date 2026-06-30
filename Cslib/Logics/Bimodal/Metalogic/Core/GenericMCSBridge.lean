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

- `derivTreeToList`: `DerivationTree .Base Γ φ → (bimodalAlgDS).Deriv Γ φ`
  (forward, structural induction on the tree).
- `unfoldListImpInTree`: `Γ ⊢ listImp Ψ φ → Ψ ⊆ Γ → Γ ⊢ φ`
  (backward helper).
- `listDerivToTree`: `(bimodalAlgDS).Deriv Γ φ → DerivationTree .Base Γ φ`
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
`Γ ⊢ listImp Γ φ`, then apply `unfoldListImpInTree` to eliminate each layer.

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
lemma derivTreeToList
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
noncomputable def unfoldListImpInTree
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
then applies `unfoldListImpInTree` to eliminate the list-implication layers. -/
noncomputable def listDerivToTree
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
  exact unfoldListImpInTree Γ d_weak (fun _a ha => ha)

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
    exact derivTreeToList d
  · intro h
    exact ⟨listDerivToTree h⟩

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

/-! ## FC-Parameterized Bridge: HilbertTMFc Tag Type

To reroute the fc-polymorphic deduction theorem in `DeductionTheorem.lean` through
the algebraic seam, we need a `MinimalHilbert` instance parameterized by an arbitrary
`fc : FrameClass`. The key observations are:

1. `imp_s` (K) and `imp_k` (S) have `minFrameClass = .Base`, so they are provable
   at any `fc` via `DerivationTree.axiom [] _ h (FrameClass.base_le fc)`.
2. All non-propositional constructors (`necessitation`, `temporal_necessitation`,
   `temporal_duality`) require empty context, so in the forward bridge they are
   handled via `InferenceSystem.DerivableIn (HilbertTMFc fc) (□ψ)` etc., which
   are `Nonempty (DerivationTree fc [] ...)`.
3. The backward bridge uses `unfoldListImpInTreeFc` — the fc-generalization
   of the existing `unfoldListImpInTree`.

This gives `algebraic_has_deduction_theorem` for any `fc`, enabling
`deductionTheorem {fc}` and `deductionWithMem {fc}` in `DeductionTheorem.lean`
to be rerouted without structural recursion.
-/

/-- Empty tag type for the fc-parameterized algebraic derivation system.
`InferenceSystem (HilbertTMFc fc)` maps `(HilbertTMFc fc)⇓φ` to
`Nonempty (DerivationTree fc [] φ)` — provability from empty context at `fc`. -/
inductive HilbertTMFc (fc : FrameClass) : Type

/-- `(HilbertTMFc fc)⇓φ` is a (nonempty) closed derivation tree at frame class `fc`. -/
instance (fc : FrameClass) :
    InferenceSystem (HilbertTMFc fc) (Bimodal.Formula Atom) where
  derivation φ := Bimodal.DerivationTree fc [] φ

section HilbertTMFcInstances
variable (fc : FrameClass)

/-- Modus ponens for `HilbertTMFc fc`: from `⊢[fc] φ → ψ` and `⊢[fc] φ`, derive `⊢[fc] ψ`. -/
instance : @ModusPonens (Formula Atom) (HilbertTMFc fc) _ _ where
  mp := fun h₁ h₂ => by
    obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
    exact ⟨.modus_ponens [] _ _ d₁ d₂⟩

/-- K axiom (weakening) for `HilbertTMFc fc`: `⊢[fc] φ → (ψ → φ)`.
Uses `imp_s` which has `minFrameClass = .Base ≤ fc` for all `fc`.
Note: Bimodal uses swapped axiom names — `imp_s` is K and `imp_k` is S. -/
instance : @HasAxiomImplyK (Formula Atom) (HilbertTMFc fc) _ _ where
  implyK := ⟨.axiom [] _ (.imp_s _ _) (FrameClass.base_le fc)⟩

/-- S axiom (distribution) for `HilbertTMFc fc`:
`⊢[fc] (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`.
Uses `imp_k` which has `minFrameClass = .Base ≤ fc` for all `fc`. -/
instance : @HasAxiomImplyS (Formula Atom) (HilbertTMFc fc) _ _ where
  implyS := ⟨.axiom [] _ (.imp_k _ _ _) (FrameClass.base_le fc)⟩

/-- `HilbertTMFc fc` is a `MinimalHilbert` system for any `fc : FrameClass`.
Synthesised from `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS` instances above. -/
instance : @MinimalHilbert (Formula Atom) (HilbertTMFc fc) _ _ _ where

end HilbertTMFcInstances

/-- The algebraic derivation system at `HilbertTMFc fc`, parameterized by frame class. -/
@[reducible] def bimodalAlgDSFc (fc : FrameClass) :
    Metalogic.DerivationSystem (Bimodal.Formula Atom) :=
  @algebraicDerivationSystem (Bimodal.Formula Atom) _ _ (HilbertTMFc fc) _ _

/-! ## FC-Parameterized Forward Bridge -/

/-- Forward bridge: `DerivationTree fc Γ φ → (bimodalAlgDSFc fc).Deriv Γ φ`.

Structural induction on the tree. Propositional/modal/temporal constructors all
map cleanly; necessitation/duality constructors have empty context and use
`listImp_axiom_k` to produce a result at the same empty context. -/
lemma derivTreeToListFc {fc : FrameClass}
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (d : Bimodal.DerivationTree fc Γ φ) :
    (bimodalAlgDSFc fc (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | «axiom» Γ ψ h_ax h_fc =>
    have h_thm : InferenceSystem.DerivableIn (HilbertTMFc fc) ψ :=
      ⟨Bimodal.DerivationTree.axiom [] ψ h_ax h_fc⟩
    simp only [bimodalAlgDSFc, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [bimodalAlgDSFc, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [bimodalAlgDSFc, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @necessitation ψ _d ih =>
    simp only [bimodalAlgDSFc, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (HilbertTMFc fc) ψ := by
      unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih
    unfold ListDeriv; simp only [listImp_nil]
    exact ⟨Bimodal.DerivationTree.necessitation ψ h_thm.toDerivation⟩
  | @temporal_necessitation ψ _d ih =>
    simp only [bimodalAlgDSFc, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (HilbertTMFc fc) ψ := by
      unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih
    unfold ListDeriv; simp only [listImp_nil]
    exact ⟨Bimodal.DerivationTree.temporal_necessitation ψ h_thm.toDerivation⟩
  | @temporal_duality ψ _d ih =>
    simp only [bimodalAlgDSFc, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (HilbertTMFc fc) ψ := by
      unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih
    have h_dual : InferenceSystem.DerivableIn (HilbertTMFc fc) ψ.swapTemporal :=
      ⟨Bimodal.DerivationTree.temporal_duality ψ h_thm.toDerivation⟩
    unfold ListDeriv; simp only [listImp_nil]
    exact h_dual
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [bimodalAlgDSFc, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih

/-! ## FC-Parameterized Backward Helper -/

/-- Backward helper (fc-generalized): given `Γ ⊢[fc] listImp Ψ φ` and `Ψ ⊆ Γ`,
produce `Γ ⊢[fc] φ` by iterating modus ponens with assumption trees. -/
noncomputable def unfoldListImpInTreeFc {fc : FrameClass}
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (Ψ : Bimodal.Context Atom)
    (d : Bimodal.DerivationTree fc Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    Bimodal.DerivationTree fc Γ φ := by
  induction Ψ generalizing φ with
  | nil =>
    simp only [listImp_nil] at d; exact d
  | cons a Ψ' ih =>
    simp only [listImp_cons] at d
    have ha_mem : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
    have d_a : Bimodal.DerivationTree fc Γ a :=
      Bimodal.DerivationTree.assumption Γ a ha_mem
    have d_tail : Bimodal.DerivationTree fc Γ (listImp Ψ' φ) :=
      Bimodal.DerivationTree.modus_ponens Γ a (listImp Ψ' φ) d d_a
    exact ih d_tail (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-! ## FC-Parameterized Backward Bridge -/

/-- Backward bridge: `(bimodalAlgDSFc fc).Deriv Γ φ → DerivationTree fc Γ φ`.

Extracts `d₀ : [] ⊢[fc] listImp Γ φ` from the algebraic derivation, weakens to `Γ`,
then applies `unfoldListImpInTreeFc`. -/
noncomputable def listDerivToTreeFc {fc : FrameClass}
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (h : (bimodalAlgDSFc fc (Atom := Atom)).Deriv Γ φ) :
    Bimodal.DerivationTree fc Γ φ := by
  simp only [bimodalAlgDSFc, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  have d₀ : Bimodal.DerivationTree fc [] (listImp Γ φ) := h.toDerivation
  have d_weak : Bimodal.DerivationTree fc Γ (listImp Γ φ) :=
    Bimodal.DerivationTree.weakening [] Γ (listImp Γ φ) d₀ (List.nil_subset Γ)
  exact unfoldListImpInTreeFc Γ d_weak (fun _a ha => ha)

/-! ## FC-Parameterized Full Equivalence -/

/-- Bidirectional equivalence between bimodal tree derivability at fc and
the algebraic derivation system `bimodalAlgDSFc fc`, for arbitrary `fc`. -/
theorem bimodal_deriv_iff_algebraic_fc {fc : FrameClass}
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom} :
    Nonempty (Bimodal.DerivationTree fc Γ φ) ↔
    (bimodalAlgDSFc fc (Atom := Atom)).Deriv Γ φ := by
  constructor
  · intro ⟨d⟩; exact derivTreeToListFc d
  · intro h; exact ⟨listDerivToTreeFc h⟩

end Cslib.Logic.Bimodal.Metalogic.Core
