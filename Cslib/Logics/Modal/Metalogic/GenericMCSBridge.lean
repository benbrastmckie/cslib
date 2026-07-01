/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.Metalogic.GenericMCS

/-! # GenericMCS Bridge for Normal Modal Logics

This module proves the bidirectional equivalence between the tree-based
`modalDerivationSystem Axioms` and the algebraic `algebraicDerivationSystem` instantiated
at `S := HilbertOf Axioms`, for any axiom predicate satisfying `HasMinimalAxioms`.

## Main Results

- `HilbertOf Axioms`: Empty inductive tag type whose `InferenceSystem` maps derivability
  to `Nonempty (DerivationTree Axioms [] φ)`.
- `MinimalHilbert (HilbertOf Axioms)`: Synthesised from `[HasMinimalAxioms Axioms]`.
- `derivTreeToList`: `DerivationTree Axioms Γ φ → (modalAlgDS).Deriv Γ φ`
  (forward, structural induction on the tree; 5 arms including `necessitation`).
- `unfoldListImpInTree`: `Γ ⊢ listImp Ψ φ → Ψ ⊆ Γ → Γ ⊢ φ`
  (backward helper).
- `listDerivToTree`: `(modalAlgDS).Deriv Γ φ → DerivationTree Axioms Γ φ`
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
`Γ ⊢ listImp Γ φ`, then apply `unfoldListImpInTree` to eliminate each layer.

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

/-- `DerivationTree Axioms` is a `HilbertTree` whenever `Axioms` satisfies
`HasMinimalAxioms`: closed under assumption, modus ponens, weakening, and the K/S axiom
schemata at the empty context. Feeds the generic backward combinators
(`unfoldListImp`/`listDerivToTree`) below. -/
instance [h : HasMinimalAxioms Axioms] :
    HilbertTree (F := Proposition Atom) (DerivationTree Axioms) where
  assumption {Γ a} hmem := .assumption Γ a hmem
  mp {Γ φ ψ} d₁ d₂ := .modus_ponens Γ φ ψ d₁ d₂
  weakening {Γ Δ φ} hsub d := .weakening Γ Δ φ d hsub
  axiomK φ ψ := .ax [] _ (h.hasImplyK φ ψ)
  axiomS φ ψ χ := .ax [] _ (h.hasImplyS φ ψ χ)

/-! ## Forward Direction: DerivationTree → Algebraic Deriv -/

/-- Forward bridge: given `d : DerivationTree Axioms Γ φ` and `[HasMinimalAxioms Axioms]`,
produce `(modalAlgDS Axioms).Deriv Γ φ` by structural induction on the derivation tree.

- **ax**: the axiom `⊢ ψ` in `HilbertOf Axioms` lifts to `Deriv Γ ψ` via K-weakening.
- **assumption**: reflected directly.
- **modus_ponens**: contextual modus ponens.
- **necessitation**: box-necessitation gives `⊢ □ψ` in `HilbertOf Axioms`.
- **weakening**: monotone in the context. -/
lemma derivTreeToList [HasMinimalAxioms Axioms]
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
produce `Γ ⊢ φ` by iterating modus ponens with assumption trees. Delegates to the
generic `unfoldListImp` (Foundations), instantiated at `D := DerivationTree Axioms`
via the `HilbertTree` instance above. -/
noncomputable def unfoldListImpInTree [HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (Ψ : List (Proposition Atom))
    (d : DerivationTree Axioms Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    DerivationTree Axioms Γ φ :=
  GenericMCS.unfoldListImp Ψ d h_sub

/-! ## Backward Direction: Algebraic Deriv → DerivationTree -/

/-- Backward bridge: `(modalAlgDS Axioms).Deriv Γ φ → DerivationTree Axioms Γ φ`.

Delegates to the generic `listDerivToTree` (Foundations), instantiated at
`D := DerivationTree Axioms`. External callers: PL and Modal `DeductionTheorem.lean`. -/
noncomputable def listDerivToTree [HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : (modalAlgDS Axioms (Atom := Atom)).Deriv Γ φ) :
    DerivationTree Axioms Γ φ :=
  GenericMCS.listDerivToTree (D := DerivationTree Axioms) h

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
    exact derivTreeToList d
  · intro h
    exact ⟨listDerivToTree h⟩

/-! ## MCS Equivalences -/

/-- `SetConsistent` under `modalDerivationSystem Axioms` iff under `modalAlgDS Axioms`.
Delegates to the generic `setConsistent_iff_congr` (Foundations). -/
theorem modal_setConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (Proposition Atom)} :
    SetConsistent (modalDerivationSystem Axioms) Ω ↔
    SetConsistent (modalAlgDS Axioms (Atom := Atom)) Ω :=
  GenericMCS.setConsistent_iff_congr (fun _ _ => modal_deriv_iff_algebraic)

/-- `SetMaximalConsistent` under `modalDerivationSystem Axioms` iff under `modalAlgDS Axioms`.
Delegates to the generic `setMaxConsistent_iff_congr` (Foundations). -/
theorem modal_setMaxConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (Proposition Atom)} :
    SetMaximalConsistent (modalDerivationSystem Axioms) Ω ↔
    SetMaximalConsistent (modalAlgDS Axioms (Atom := Atom)) Ω :=
  GenericMCS.setMaxConsistent_iff_congr (fun _ _ => modal_deriv_iff_algebraic)

end Cslib.Logic.Modal
