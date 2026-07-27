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
at `S := ClosedHilbert (DerivationTree Axioms)`, for any axiom predicate satisfying
`HasMinimalAxioms`.

## Main Results

- `HilbertTree (DerivationTree Axioms)`: instance feeding the generic `ClosedHilbert`
  tag (Foundations) and the generic backward combinators.
- `derivTreeToList`: `DerivationTree Axioms Γ φ → (modalAlgDS).Deriv Γ φ`
  (forward, structural induction on the tree; 5 arms including `necessitation`).
- `listDerivToTree`: `(modalAlgDS).Deriv Γ φ → DerivationTree Axioms Γ φ`
  (backward direction).
- `modal_deriv_iff_algebraic`: bidirectional equivalence on derivability.

## Architecture

`modalDerivationSystem.Deriv Γ φ = Modal.Deriv Axioms Γ φ`
  `= Nonempty (DerivationTree Axioms Γ φ)`

`(modalAlgDS Axioms).Deriv Γ φ`
  `= ListDeriv Γ φ` (with `S` inferred as `ClosedHilbert (DerivationTree Axioms)`)
  `= InferenceSystem.DerivableIn (ClosedHilbert (DerivationTree Axioms)) (listImp Γ φ)`
  `= Nonempty (DerivationTree Axioms [] (listImp Γ φ))`

**Forward** (tree → algebraic): structural induction on `DerivationTree`. The
`necessitation` arm (present in Modal, absent in Propositional) fires only at empty
context and constructs `⊢ □ψ` via the `InferenceSystem` instance for
`ClosedHilbert (DerivationTree Axioms)`.

**Backward** (algebraic → tree): `listDerivToTree` delegates directly to the generic
`GenericMCS.listDerivToTree` (Foundations), which extracts `d₀ : [] ⊢ listImp Γ φ`, weakens to
`Γ ⊢ listImp Γ φ`, then applies the generic `GenericMCS.unfoldListImp` to eliminate each layer.

## Design Note

This file uses the generic `ClosedHilbert (DerivationTree Axioms)` tag (Foundations) rather
than a local `HilbertOf Axioms` bundle, since `HilbertOf Axioms` has no external references
(grep-confirmed); the generic tag's `InferenceSystem`/`ModusPonens`/`HasAxiomImplyK`/
`HasAxiomImplyS`/`MinimalHilbert` instances are supplied automatically from the
`HilbertTree (DerivationTree Axioms)` instance below. This file still does NOT import
`Modal/Metalogic/DeductionTheorem.lean`, preserving the no-cycle property.

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

/-- `DerivationTree Axioms` is a `HilbertTree` whenever `Axioms` satisfies
`HasMinimalAxioms`: closed under assumption, modus ponens, weakening, and the K/S axiom
schemata at the empty context. Feeds the generic `ClosedHilbert` tag and backward
combinators (`unfoldListImp`/`listDerivToTree`) below. Must precede `modalAlgDS` (Lean
scoping: `treeAlgDS` requires this instance in scope). -/
instance [h : HasMinimalAxioms Axioms] :
    HilbertTree (F := Proposition Atom) (DerivationTree Axioms) where
  assumption {Γ a} hmem := .assumption Γ a hmem
  mp {Γ φ ψ} d₁ d₂ := .modus_ponens Γ φ ψ d₁ d₂
  weakening {Γ Δ φ} hsub d := .weakening Γ Δ φ d hsub
  axiomK φ ψ := .ax [] _ (h.hasImplyK φ ψ)
  axiomS φ ψ χ := .ax [] _ (h.hasImplyS φ ψ χ)

/-! ## Algebraic DS Alias -/

/-- Shorthand for the algebraic derivation system at the generic `ClosedHilbert
(DerivationTree Axioms)` tag. A thin re-export: the underlying tag changed from the
retired local `HilbertOf Axioms` to `ClosedHilbert`, but the name and signature are
unchanged. -/
@[reducible] def modalAlgDS (Axioms : Proposition Atom → Prop)
    [HasMinimalAxioms Axioms] :
    Metalogic.DerivationSystem (Proposition Atom) :=
  treeAlgDS (DerivationTree Axioms)

/-! ## Forward Direction: DerivationTree → Algebraic Deriv -/

/-- Forward bridge: given `d : DerivationTree Axioms Γ φ` and `[HasMinimalAxioms Axioms]`,
produce `(modalAlgDS Axioms).Deriv Γ φ` by structural induction on the derivation tree.

- **ax**: the axiom `⊢ ψ` in `ClosedHilbert (DerivationTree Axioms)` lifts to `Deriv Γ ψ`
  via K-weakening.
- **assumption**: reflected directly.
- **modus_ponens**: contextual modus ponens.
- **necessitation**: box-necessitation gives `⊢ □ψ` in `ClosedHilbert (DerivationTree Axioms)`.
- **weakening**: monotone in the context. -/
lemma derivTreeToList [HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ) :
    (modalAlgDS Axioms (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | ax Γ ψ h_ax =>
    -- ψ is a ClosedHilbert (DerivationTree Axioms) theorem (tree at empty context)
    have h_thm : InferenceSystem.DerivableIn (ClosedHilbert (DerivationTree Axioms)) ψ :=
      ⟨DerivationTree.ax [] ψ h_ax⟩
    -- Lift to the algebraic system via K-weakening: ⊢ ψ → listImp Γ ψ, then MP
    simp only [modalAlgDS, treeAlgDS, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [modalAlgDS, treeAlgDS, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [modalAlgDS, treeAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @necessitation ψ _d ih =>
    -- ih : modalAlgDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn (ClosedHilbert ...) ψ
    simp only [modalAlgDS, treeAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (ClosedHilbert (DerivationTree Axioms)) ψ := by
      unfold ListDeriv at ih
      simp only [listImp_nil] at ih
      exact ih
    -- Box-necessitation: ⊢ ψ → ⊢ □ψ in ClosedHilbert (DerivationTree Axioms)
    unfold ListDeriv
    simp only [listImp_nil]
    -- Construct □ψ derivation directly using the tree necessitation constructor
    exact ⟨DerivationTree.necessitation ψ h_thm.toDerivation⟩
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [modalAlgDS, treeAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih

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
the algebraic derivation system at `S := ClosedHilbert (DerivationTree Axioms)`, for any
`Axioms` satisfying `HasMinimalAxioms`. Assembled via the generic
`GenericMCS.deriv_iff_algebraic_of_forward` (Foundations). -/
theorem modal_deriv_iff_algebraic [HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom} :
    (modalDerivationSystem Axioms).Deriv Γ φ ↔
    (modalAlgDS Axioms (Atom := Atom)).Deriv Γ φ :=
  GenericMCS.deriv_iff_algebraic_of_forward Iff.rfl derivTreeToList

end Cslib.Logic.Modal
