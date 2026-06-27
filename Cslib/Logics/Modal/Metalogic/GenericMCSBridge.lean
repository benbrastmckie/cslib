/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.Metalogic.MCSProperties

/-! # GenericMCS Bridge for Normal Modal Logics

This module proves the bidirectional equivalence between the tree-based
`modalDerivationSystem Axioms` and the algebraic `algebraicDerivationSystem` instantiated
at `S := HilbertOf Axioms`, for any axiom predicate satisfying `HasMinimalAxioms`.

## Main Results

- `HilbertOf Axioms`: Empty inductive tag type whose `InferenceSystem` maps derivability
  to `Nonempty (DerivationTree Axioms [] φ)`.
- `MinimalHilbert (HilbertOf Axioms)`: Synthesised from `[HasMinimalAxioms Axioms]`.
- `deriv_tree_to_list`: `DerivationTree Axioms Γ φ → (modalAlgDS).Deriv Γ φ`
  (forward, structural induction on the tree; 5 arms including `necessitation`).
- `unfold_listImp_in_tree`: `Γ ⊢ listImp Ψ φ → Ψ ⊆ Γ → Γ ⊢ φ`
  (backward helper).
- `list_deriv_to_tree`: `(modalAlgDS).Deriv Γ φ → DerivationTree Axioms Γ φ`
  (backward direction).
- `modal_deriv_iff_algebraic`: bidirectional equivalence on derivability.
- `modal_setConsistent_iff_algebraic`: consistency equivalence.
- `modal_setMaxConsistent_iff_algebraic`: MCS equivalence.

## Architecture

`modalDerivationSystem.Deriv Γ φ = Modal.Deriv Axioms Γ φ`
  `= Nonempty (DerivationTree Axioms Γ φ)`

`(modalAlgDS Axioms).Deriv Γ φ`
  `= ListDeriv Γ φ` (with `S` inferred as `HilbertOf Axioms`)
  `= InferenceSystem.DerivableIn (HilbertOf Axioms) (listImp Γ φ)`
  `= Nonempty ((HilbertOf Axioms)⇓(listImp Γ φ))`
  `= Nonempty (DerivationTree Axioms [] (listImp Γ φ))`

**Forward** (tree → algebraic): structural induction on `DerivationTree`. The
`necessitation` arm (present in Modal, absent in Propositional) fires only at empty
context and constructs `⊢ □ψ` via the `InferenceSystem` instance for `HilbertOf Axioms`.

**Backward** (algebraic → tree): extract `d₀ : [] ⊢ listImp Γ φ`, weaken to
`Γ ⊢ listImp Γ φ`, then apply `unfold_listImp_in_tree` to eliminate each layer.

## Design Note

This file does NOT import `Modal/Metalogic/DeductionTheorem.lean`. The equivalence is
derived directly from the `InferenceSystem` and `MinimalHilbert` instances for
`HilbertOf Axioms` registered below. This ensures `DeductionTheorem.lean` can import
this bridge without creating a cycle.

## References

* Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean — closest template
* Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean — further template
* Cslib/Foundations/Logic/Metalogic/GenericMCS.lean
* Cslib/Foundations/Logic/Metalogic/MCSProperties.lean
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction
open Cslib.Logic.Metalogic.GenericMCS
open Cslib.Logic.Metalogic.MCSProperties
open Cslib.Logic.Metalogic

variable {Atom : Type*}
variable {Axioms : Proposition Atom → Prop}

/-! ## HilbertOf Tag Type -/

/-- Empty tag type whose `InferenceSystem` maps `HilbertOf Axioms`-derivability to
`Nonempty (DerivationTree Axioms [] φ)`. This is a pure infrastructure type with no
constructors; all proof content lives in the `InferenceSystem` and `MinimalHilbert`
instances below. -/
inductive HilbertOf (Axioms : Proposition Atom → Prop) : Type

/-! ## InferenceSystem Instance -/

/-- `(HilbertOf Axioms)⇓φ` is a `DerivationTree Axioms [] φ` — a closed derivation tree
(from empty context) using axioms satisfying `Axioms`. -/
instance : InferenceSystem (HilbertOf Axioms) (Proposition Atom) where
  derivation φ := DerivationTree Axioms [] φ

/-! ## ModusPonens Instance -/

/-- Modus ponens for `HilbertOf Axioms`: from `⊢ φ → ψ` and `⊢ φ`, derive `⊢ ψ`
using the tree `modus_ponens` constructor at empty context. -/
instance : ModusPonens (HilbertOf Axioms) (F := Proposition Atom) where
  mp := fun h₁ h₂ => by
    obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
    exact ⟨DerivationTree.modus_ponens [] _ _ d₁ d₂⟩

/-! ## Conditional Axiom Instances -/

/-- `HilbertOf Axioms` proves the K axiom whenever `Axioms` satisfies `HasMinimalAxioms`. -/
instance [h : HasMinimalAxioms Axioms] :
    HasAxiomImplyK (HilbertOf Axioms) (F := Proposition Atom) where
  implyK := ⟨DerivationTree.ax [] _ (h.hasImplyK _ _)⟩

/-- `HilbertOf Axioms` proves the S axiom whenever `Axioms` satisfies `HasMinimalAxioms`. -/
instance [h : HasMinimalAxioms Axioms] :
    HasAxiomImplyS (HilbertOf Axioms) (F := Proposition Atom) where
  implyS := ⟨DerivationTree.ax [] _ (h.hasImplyS _ _ _)⟩

/-- `HilbertOf Axioms` is a `MinimalHilbert` system whenever `Axioms` satisfies
`HasMinimalAxioms`. Synthesised automatically from `ModusPonens`, `HasAxiomImplyK`,
`HasAxiomImplyS` instances above. -/
instance [HasMinimalAxioms Axioms] :
    MinimalHilbert (HilbertOf Axioms) (F := Proposition Atom) where

/-! ## Algebraic DS Alias -/

/-- Shorthand for the algebraic derivation system at `HilbertOf Axioms`. -/
@[reducible] def modalAlgDS (Axioms : Proposition Atom → Prop)
    [HasMinimalAxioms Axioms] :
    Metalogic.DerivationSystem (Proposition Atom) :=
  @algebraicDerivationSystem (Proposition Atom) _ _ (HilbertOf Axioms) _ _

/-! ## Forward Direction: DerivationTree → Algebraic Deriv -/

/-- Forward bridge: given `d : DerivationTree Axioms Γ φ` and `[HasMinimalAxioms Axioms]`,
produce `(modalAlgDS Axioms).Deriv Γ φ` by structural induction on the derivation tree.

- **ax**: the axiom `⊢ ψ` in `HilbertOf Axioms` lifts to `Deriv Γ ψ` via K-weakening.
- **assumption**: reflected directly.
- **modus_ponens**: contextual modus ponens.
- **necessitation**: box-necessitation gives `⊢ □ψ` in `HilbertOf Axioms`.
- **weakening**: monotone in the context. -/
noncomputable def deriv_tree_to_list [HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ) :
    (modalAlgDS Axioms (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | ax Γ ψ h_ax =>
    -- ψ is a HilbertOf Axioms theorem (tree at empty context)
    have h_thm : InferenceSystem.DerivableIn (HilbertOf Axioms) ψ :=
      ⟨DerivationTree.ax [] ψ h_ax⟩
    -- Lift to the algebraic system via K-weakening: ⊢ ψ → listImp Γ ψ, then MP
    simp only [modalAlgDS, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [modalAlgDS, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [modalAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @necessitation ψ _d ih =>
    -- ih : modalAlgDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn (HilbertOf Axioms) ψ
    simp only [modalAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (HilbertOf Axioms) ψ := by
      unfold ListDeriv at ih
      simp only [listImp_nil] at ih
      exact ih
    -- Box-necessitation: ⊢ ψ → ⊢ □ψ in HilbertOf Axioms
    unfold ListDeriv
    simp only [listImp_nil]
    -- Construct □ψ derivation directly using the tree necessitation constructor
    exact ⟨DerivationTree.necessitation ψ h_thm.toDerivation⟩
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [modalAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih

/-! ## Backward Helper: Unfold listImp Using Assumptions -/

/-- Backward helper: given `Γ ⊢ listImp Ψ φ` (tree) and `Ψ ⊆ Γ`,
produce `Γ ⊢ φ` by iterating modus ponens with assumption trees.

Induction on `Ψ`: in the cons case, `a ∈ Γ` gives `Γ ⊢ a` by assumption,
then MP reduces `listImp (a :: Ψ') φ` to `listImp Ψ' φ`. -/
noncomputable def unfold_listImp_in_tree
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (Ψ : List (Proposition Atom))
    (d : DerivationTree Axioms Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    DerivationTree Axioms Γ φ := by
  induction Ψ generalizing φ with
  | nil =>
    simp only [listImp_nil] at d
    exact d
  | cons a Ψ' ih =>
    simp only [listImp_cons] at d
    -- d : Γ ⊢ a → listImp Ψ' φ
    have ha_mem : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
    have d_a : DerivationTree Axioms Γ a :=
      DerivationTree.assumption Γ a ha_mem
    have d_tail : DerivationTree Axioms Γ (listImp Ψ' φ) :=
      DerivationTree.modus_ponens Γ a (listImp Ψ' φ) d d_a
    exact ih d_tail (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-! ## Backward Direction: Algebraic Deriv → DerivationTree -/

/-- Backward bridge: `(modalAlgDS Axioms).Deriv Γ φ → DerivationTree Axioms Γ φ`.

Extracts `d₀ : [] ⊢ listImp Γ φ` from the algebraic derivation, weakens to `Γ`,
then applies `unfold_listImp_in_tree` to eliminate the list-implication layers. -/
noncomputable def list_deriv_to_tree [HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : (modalAlgDS Axioms (Atom := Atom)).Deriv Γ φ) :
    DerivationTree Axioms Γ φ := by
  simp only [modalAlgDS, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  -- h : InferenceSystem.DerivableIn (HilbertOf Axioms) (listImp Γ φ)
  -- = Nonempty ((HilbertOf Axioms)⇓(listImp Γ φ))
  -- = Nonempty (DerivationTree Axioms [] (listImp Γ φ))
  have d₀ : DerivationTree Axioms [] (listImp Γ φ) := h.toDerivation
  -- Weaken from [] to Γ
  have d_weak : DerivationTree Axioms Γ (listImp Γ φ) :=
    DerivationTree.weakening [] Γ (listImp Γ φ) d₀ (List.nil_subset Γ)
  -- Eliminate listImp using assumption trees
  exact unfold_listImp_in_tree Γ d_weak (fun _a ha => ha)

/-! ## Full Derivability Equivalence -/

/-- Bidirectional derivability equivalence between `modalDerivationSystem Axioms` and
the algebraic derivation system at `S := HilbertOf Axioms`, for any `Axioms` satisfying
`HasMinimalAxioms`. -/
theorem modal_deriv_iff_algebraic [HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom} :
    (modalDerivationSystem Axioms).Deriv Γ φ ↔
    (modalAlgDS Axioms (Atom := Atom)).Deriv Γ φ := by
  unfold modalDerivationSystem Deriv
  constructor
  · intro ⟨d⟩
    exact deriv_tree_to_list d
  · intro h
    exact ⟨list_deriv_to_tree h⟩

/-! ## MCS Equivalences -/

/-- `SetConsistent` under `modalDerivationSystem Axioms` iff under `modalAlgDS Axioms`. -/
theorem modal_setConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (Proposition Atom)} :
    SetConsistent (modalDerivationSystem Axioms) Ω ↔
    SetConsistent (modalAlgDS Axioms (Atom := Atom)) Ω := by
  unfold SetConsistent Consistent
  constructor
  · intro h L hL hd
    exact h L hL (modal_deriv_iff_algebraic.mpr hd)
  · intro h L hL hd
    exact h L hL (modal_deriv_iff_algebraic.mp hd)

/-- `SetMaximalConsistent` under `modalDerivationSystem Axioms` iff under `modalAlgDS Axioms`. -/
theorem modal_setMaxConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (Proposition Atom)} :
    SetMaximalConsistent (modalDerivationSystem Axioms) Ω ↔
    SetMaximalConsistent (modalAlgDS Axioms (Atom := Atom)) Ω := by
  unfold SetMaximalConsistent
  constructor
  · intro ⟨hcons, hmax⟩
    refine ⟨modal_setConsistent_iff_algebraic.mp hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (modal_setConsistent_iff_algebraic.mpr hinsert)
  · intro ⟨hcons, hmax⟩
    refine ⟨modal_setConsistent_iff_algebraic.mpr hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (modal_setConsistent_iff_algebraic.mp hinsert)

end Cslib.Logic.Modal
