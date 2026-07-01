/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.Metalogic.GenericMCS
public import Cslib.Logics.Temporal.ProofSystem.Instances

/-! # GenericMCS Bridge for Temporal Logic BX

This module proves the bidirectional equivalence between the tree-based
`temporalDerivationSystem` and the algebraic `algebraicDerivationSystem` instantiated
at `S := Temporal.HilbertBX`.

## Main Results

- `derivTreeToList`: `DerivationTree .Base Γ φ → (algDS).Deriv Γ φ`
  (forward, structural induction on the tree).
- `unfoldListImpInTree`: `Γ ⊢ listImp Ψ φ → Ψ ⊆ Γ → Γ ⊢ φ`
  (backward helper).
- `listDerivToTree`: `(algDS).Deriv Γ φ → DerivationTree .Base Γ φ`
  (backward direction).
- `temporal_deriv_iff_algebraic`: bidirectional equivalence on derivability.
- `temporal_setConsistent_iff_algebraic`: consistency equivalence.
- `temporal_setMaxConsistent_iff_algebraic`: MCS equivalence.

## Architecture

`temporalDerivationSystem.Deriv Γ φ = Nonempty (DerivationTree FrameClass.Base Γ φ)`

`(algDS).Deriv Γ φ`
  `= ListDeriv Γ φ` (with `S` inferred as `Temporal.HilbertBX`)
  `= InferenceSystem.DerivableIn HilbertBX (listImp Γ φ)`
  `= Nonempty (DerivationTree FrameClass.Base [] (listImp Γ φ))`

**Forward** (tree → algebraic): structural induction on the `DerivationTree`. Each
constructor maps to a corresponding algebraic derivation operation.

**Backward** (algebraic → tree): extract `d₀ : [] ⊢ listImp Γ φ`, weaken to
`Γ ⊢ listImp Γ φ`, then apply `unfoldListImpInTree` to eliminate each layer.

## References

* Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean
* Cslib/Foundations/Logic/Metalogic/GenericMCS.lean
* Cslib/Foundations/Logic/Metalogic/MCSProperties.lean
* Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean — gap analysis (documentation only)
-/

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction
open Cslib.Logic.Metalogic.GenericMCS
open Cslib.Logic.Metalogic

variable {Atom : Type*}

/-- Shorthand for the algebraic derivation system at `Temporal.HilbertBX`. -/
@[reducible] def temporalAlgDS : Metalogic.DerivationSystem (Formula Atom) :=
  @algebraicDerivationSystem (Formula Atom) _ _ Temporal.HilbertBX _ _

/-! ## Forward Direction: DerivationTree → Algebraic Deriv -/

/-- Forward bridge: given `d : DerivationTree FrameClass.Base Γ φ`, produce
`temporalAlgDS.Deriv Γ φ` by structural induction on the derivation tree.

- **axiom**: the axiom `⊢ ψ` in `HilbertBX` lifts to `Deriv Γ ψ` via K-weakening.
- **assumption**: reflected directly.
- **modus_ponens**: contextual modus ponens.
- **temporal_necessitation**: G-necessitation gives `⊢ G(ψ)` in `HilbertBX`.
- **temporal_duality**: construct the dual tree using `temporal_duality`.
- **weakening**: monotone in the context. -/
lemma derivTreeToList
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base Γ φ) :
    (temporalAlgDS (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | «axiom» Γ ψ h_ax h_fc =>
    -- ψ is a HilbertBX theorem
    have h_thm : InferenceSystem.DerivableIn Temporal.HilbertBX ψ :=
      ⟨DerivationTree.axiom [] ψ h_ax h_fc⟩
    -- Lift to the algebraic system via K-weakening: ⊢ ψ → listImp Γ ψ, then MP
    simp only [temporalAlgDS, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [temporalAlgDS, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [temporalAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @temporal_necessitation ψ _d ih =>
    -- ih : algDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn HilbertBX ψ
    simp only [temporalAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn Temporal.HilbertBX ψ := by
      unfold ListDeriv at ih
      simp only [listImp_nil] at ih
      exact ih
    -- G-necessitation: ⊢ ψ → ⊢ G(ψ) in HilbertBX
    unfold ListDeriv
    simp only [listImp_nil]
    -- Construct G(ψ) derivation directly using the tree constructor
    exact ⟨DerivationTree.temporal_necessitation ψ h_thm.toDerivation⟩
  | @temporal_duality ψ _d ih =>
    -- ih : algDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn HilbertBX ψ
    simp only [temporalAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn Temporal.HilbertBX ψ := by
      unfold ListDeriv at ih
      simp only [listImp_nil] at ih
      exact ih
    -- Construct the dual derivation
    have h_dual : InferenceSystem.DerivableIn Temporal.HilbertBX ψ.swapTemporal :=
      ⟨DerivationTree.temporal_duality ψ h_thm.toDerivation⟩
    unfold ListDeriv
    simp only [listImp_nil]
    exact h_dual
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [temporalAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih

/-! ## Backward Helper: Unfold listImp Using Assumptions -/

/-- Backward helper: given `Γ ⊢ listImp Ψ φ` (tree) and `Ψ ⊆ Γ`,
produce `Γ ⊢ φ` by iterating modus ponens with assumption trees.

Induction on `Ψ`: in the cons case, `a ∈ Γ` gives `Γ ⊢ a` by assumption,
then MP reduces `listImp (a :: Ψ') φ` to `listImp Ψ' φ`. -/
noncomputable def unfoldListImpInTree
    {Γ : Context Atom} {φ : Formula Atom}
    (Ψ : Context Atom)
    (d : DerivationTree FrameClass.Base Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    DerivationTree FrameClass.Base Γ φ := by
  induction Ψ generalizing φ with
  | nil =>
    simp only [listImp_nil] at d
    exact d
  | cons a Ψ' ih =>
    simp only [listImp_cons] at d
    -- d : Γ ⊢ a → listImp Ψ' φ
    have ha_mem : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
    have d_a : DerivationTree FrameClass.Base Γ a :=
      DerivationTree.assumption Γ a ha_mem
    have d_tail : DerivationTree FrameClass.Base Γ (listImp Ψ' φ) :=
      DerivationTree.modus_ponens Γ a (listImp Ψ' φ) d d_a
    exact ih d_tail (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-! ## Backward Direction: Algebraic Deriv → DerivationTree -/

/-- Backward bridge: `temporalAlgDS.Deriv Γ φ → DerivationTree .Base Γ φ`.

Extracts `d₀ : [] ⊢ listImp Γ φ` from the algebraic derivation, weakens to `Γ`,
then applies `unfoldListImpInTree` to eliminate the list-implication layers. -/
noncomputable def listDerivToTree
    {Γ : Context Atom} {φ : Formula Atom}
    (h : (temporalAlgDS (Atom := Atom)).Deriv Γ φ) :
    DerivationTree FrameClass.Base Γ φ := by
  simp only [temporalAlgDS, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  -- h : InferenceSystem.DerivableIn HilbertBX (listImp Γ φ)
  -- = Nonempty (HilbertBX ⇓ listImp Γ φ)
  -- = Nonempty (DerivationTree .Base [] (listImp Γ φ))
  -- Extract the tree using Classical.choice (since DerivationTree is Type-valued)
  have d₀ : DerivationTree FrameClass.Base [] (listImp Γ φ) := h.toDerivation
  -- Weaken from [] to Γ
  have d_weak : DerivationTree FrameClass.Base Γ (listImp Γ φ) :=
    DerivationTree.weakening [] Γ (listImp Γ φ) d₀ (List.nil_subset Γ)
  -- Eliminate listImp using assumption trees
  exact unfoldListImpInTree Γ d_weak (fun _a ha => ha)

/-! ## Full Derivability Equivalence -/

/-- Bidirectional derivability equivalence between `temporalDerivationSystem` and
the algebraic derivation system at `S := Temporal.HilbertBX`. -/
theorem temporal_deriv_iff_algebraic
    {Γ : Context Atom} {φ : Formula Atom} :
    temporalDerivationSystem.Deriv Γ φ ↔
    (temporalAlgDS (Atom := Atom)).Deriv Γ φ := by
  unfold temporalDerivationSystem Temporal.Deriv
  constructor
  · intro ⟨d⟩
    exact derivTreeToList d
  · intro h
    exact ⟨listDerivToTree h⟩

/-! ## MCS Equivalences -/

/-- `SetConsistent` under `temporalDerivationSystem` iff under `temporalAlgDS`. -/
theorem temporal_setConsistent_iff_algebraic
    {Ω : Set (Formula Atom)} :
    SetConsistent temporalDerivationSystem Ω ↔
    SetConsistent (temporalAlgDS (Atom := Atom)) Ω := by
  unfold SetConsistent Consistent
  constructor
  · intro h L hL hd
    exact h L hL (temporal_deriv_iff_algebraic.mpr hd)
  · intro h L hL hd
    exact h L hL (temporal_deriv_iff_algebraic.mp hd)

/-- `SetMaximalConsistent` under `temporalDerivationSystem` iff under `temporalAlgDS`. -/
theorem temporal_setMaxConsistent_iff_algebraic
    {Ω : Set (Formula Atom)} :
    SetMaximalConsistent temporalDerivationSystem Ω ↔
    SetMaximalConsistent (temporalAlgDS (Atom := Atom)) Ω := by
  unfold SetMaximalConsistent
  constructor
  · intro ⟨hcons, hmax⟩
    refine ⟨temporal_setConsistent_iff_algebraic.mp hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (temporal_setConsistent_iff_algebraic.mpr hinsert)
  · intro ⟨hcons, hmax⟩
    refine ⟨temporal_setConsistent_iff_algebraic.mpr hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (temporal_setConsistent_iff_algebraic.mp hinsert)

/-! ## FC-Parameterized Bridge: HilbertBXFc Tag Type

To reroute the fc-polymorphic deduction theorem in `DenseMCS.lean` through the
algebraic seam, we need a `MinimalHilbert` instance parameterized by an arbitrary
`fc : FrameClass`. The key observations are:

1. `imp_s` (K) and `imp_k` (S) have `minFrameClass = .Base`, so they are provable
   at any `fc` via `DerivationTree.axiom [] _ h (FrameClass.base_le fc)`.
2. The `ModusPonens`, `HasAxiomImplyK`, and `HasAxiomImplyS` instances use only
   empty-context trees (`DerivationTree fc [] φ`), which exist for any `fc`.
3. All other axioms (Dense, Discrete) and connectives (temporal_necessitation,
   temporal_duality) also extend cleanly to arbitrary `fc` in the forward bridge.

This gives `algebraic_has_deduction_theorem` for any `fc`, enabling `deductionTheoremFc`
and `deductionWithMemFc` in `DenseMCS.lean` to be rerouted without structural recursion.
-/

/-- Empty tag type for the fc-parameterized algebraic derivation system.
`InferenceSystem (HilbertBXFc fc)` maps `(HilbertBXFc fc)⇓φ` to
`Nonempty (DerivationTree fc [] φ)` — i.e., provability from empty context at `fc`. -/
inductive HilbertBXFc (fc : FrameClass) : Type

/-- `(HilbertBXFc fc)⇓φ` is a (nonempty) closed derivation tree at frame class `fc`. -/
instance (fc : FrameClass) :
    InferenceSystem (HilbertBXFc fc) (Temporal.Formula Atom) where
  derivation φ := DerivationTree fc [] φ

/-- Modus ponens for `HilbertBXFc fc`: from `⊢[fc] φ → ψ` and `⊢[fc] φ`, derive `⊢[fc] ψ`. -/
instance (fc : FrameClass) :
    ModusPonens (HilbertBXFc fc) (F := Temporal.Formula Atom) where
  mp := fun h₁ h₂ => by
    obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
    exact ⟨.modus_ponens [] _ _ d₁ d₂⟩

/-- K axiom (weakening) for `HilbertBXFc fc`: `⊢[fc] φ → (ψ → φ)`.
Uses `imp_s` which has `minFrameClass = .Base ≤ fc` for all `fc`. -/
instance (fc : FrameClass) :
    HasAxiomImplyK (HilbertBXFc fc) (F := Temporal.Formula Atom) where
  implyK := ⟨.axiom [] _ (.imp_s _ _) (FrameClass.base_le fc)⟩

/-- S axiom (distribution) for `HilbertBXFc fc`: `⊢[fc] (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`.
Uses `imp_k` which has `minFrameClass = .Base ≤ fc` for all `fc`. -/
instance (fc : FrameClass) :
    HasAxiomImplyS (HilbertBXFc fc) (F := Temporal.Formula Atom) where
  implyS := ⟨.axiom [] _ (.imp_k _ _ _) (FrameClass.base_le fc)⟩

/-- `HilbertBXFc fc` is a `MinimalHilbert` system for any `fc : FrameClass`.
Synthesised from `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS` instances above. -/
instance (fc : FrameClass) :
    MinimalHilbert (HilbertBXFc fc) (F := Temporal.Formula Atom) where

/-- The algebraic derivation system at `HilbertBXFc fc`, parameterized by frame class. -/
@[reducible] def temporalAlgDSFc (fc : FrameClass) :
    Metalogic.DerivationSystem (Temporal.Formula Atom) :=
  @algebraicDerivationSystem (Temporal.Formula Atom) _ _ (HilbertBXFc fc) _ _

/-! ## FC-Parameterized Forward Bridge -/

/-- Forward bridge: `DerivationTree fc Γ φ → (temporalAlgDSFc fc).Deriv Γ φ`.

Structural induction on the tree. Propositional/temporal constructors all map
cleanly; necessitation and duality constructors have empty context and use
`listImp_axiom_k` to weaken to arbitrary `Γ`. -/
lemma derivTreeToListFc {fc : FrameClass}
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree fc Γ φ) :
    (temporalAlgDSFc fc (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | «axiom» Γ ψ h_ax h_fc =>
    have h_thm : InferenceSystem.DerivableIn (HilbertBXFc fc) ψ :=
      ⟨DerivationTree.axiom [] ψ h_ax h_fc⟩
    simp only [temporalAlgDSFc, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [temporalAlgDSFc, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [temporalAlgDSFc, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @temporal_necessitation ψ _d ih =>
    simp only [temporalAlgDSFc, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (HilbertBXFc fc) ψ := by
      unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih
    unfold ListDeriv; simp only [listImp_nil]
    exact ⟨DerivationTree.temporal_necessitation ψ h_thm.toDerivation⟩
  | @temporal_duality ψ _d ih =>
    simp only [temporalAlgDSFc, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (HilbertBXFc fc) ψ := by
      unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih
    have h_dual : InferenceSystem.DerivableIn (HilbertBXFc fc) ψ.swapTemporal :=
      ⟨DerivationTree.temporal_duality ψ h_thm.toDerivation⟩
    unfold ListDeriv; simp only [listImp_nil]
    exact h_dual
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [temporalAlgDSFc, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih

/-! ## FC-Parameterized Backward Helper -/

/-- Backward helper (fc-generalized): given `Γ ⊢[fc] listImp Ψ φ` and `Ψ ⊆ Γ`,
produce `Γ ⊢[fc] φ` by iterating modus ponens with assumption trees. -/
noncomputable def unfoldListImpInTreeFc {fc : FrameClass}
    {Γ : Context Atom} {φ : Formula Atom}
    (Ψ : Context Atom)
    (d : DerivationTree fc Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    DerivationTree fc Γ φ := by
  induction Ψ generalizing φ with
  | nil =>
    simp only [listImp_nil] at d; exact d
  | cons a Ψ' ih =>
    simp only [listImp_cons] at d
    have ha_mem : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
    have d_a : DerivationTree fc Γ a := .assumption Γ a ha_mem
    have d_tail : DerivationTree fc Γ (listImp Ψ' φ) :=
      .modus_ponens Γ a (listImp Ψ' φ) d d_a
    exact ih d_tail (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-! ## FC-Parameterized Backward Bridge -/

/-- Backward bridge: `(temporalAlgDSFc fc).Deriv Γ φ → DerivationTree fc Γ φ`.

Extracts `d₀ : [] ⊢[fc] listImp Γ φ` from the algebraic derivation, weakens to `Γ`,
then applies `unfoldListImpInTreeFc`. -/
noncomputable def listDerivToTreeFc {fc : FrameClass}
    {Γ : Context Atom} {φ : Formula Atom}
    (h : (temporalAlgDSFc fc (Atom := Atom)).Deriv Γ φ) :
    DerivationTree fc Γ φ := by
  simp only [temporalAlgDSFc, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  have d₀ : DerivationTree fc [] (listImp Γ φ) := h.toDerivation
  have d_weak : DerivationTree fc Γ (listImp Γ φ) :=
    .weakening [] Γ (listImp Γ φ) d₀ (List.nil_subset Γ)
  exact unfoldListImpInTreeFc Γ d_weak (fun _a ha => ha)

/-! ## FC-Parameterized Full Equivalence -/

/-- Bidirectional equivalence between `temporalDerivationSystemFc fc` and
the algebraic derivation system at `HilbertBXFc fc`, for arbitrary `fc`. -/
theorem temporal_deriv_iff_algebraic_fc {fc : FrameClass}
    {Γ : Context Atom} {φ : Formula Atom} :
    Nonempty (DerivationTree fc Γ φ) ↔
    (temporalAlgDSFc fc (Atom := Atom)).Deriv Γ φ := by
  constructor
  · intro ⟨d⟩; exact derivTreeToListFc d
  · intro h; exact ⟨listDerivToTreeFc h⟩

end Cslib.Logic.Temporal
