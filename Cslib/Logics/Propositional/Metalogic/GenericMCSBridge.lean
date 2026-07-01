/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Foundations.Logic.Metalogic.MCSProperties

/-! # GenericMCS Bridge for Propositional Logic

This module proves the bidirectional equivalence between the tree-based
`propDerivationSystem Axioms` and the algebraic `algebraicDerivationSystem` instantiated
at `S := HilbertOf Axioms`, for any axiom predicate satisfying `HasMinimalAxioms`.

## Main Results

- `HilbertOf Axioms`: Empty inductive tag type whose `InferenceSystem` maps derivability
  to `Nonempty (DerivationTree Axioms [] φ)`.
- `MinimalHilbert (HilbertOf Axioms)`: Synthesised from `[HasMinimalAxioms Axioms]`.
- `derivTreeToList`: `DerivationTree Axioms Γ φ → (propAlgDS Axioms).Deriv Γ φ`
  (forward, structural induction on the tree; 4 arms, no necessitation).
- `unfoldListImpInTree`: `Γ ⊢ listImp Ψ φ → Ψ ⊆ Γ → Γ ⊢ φ`
  (backward helper).
- `listDerivToTree`: `(propAlgDS Axioms).Deriv Γ φ → DerivationTree Axioms Γ φ`
  (backward direction).
- `pl_deriv_iff_algebraic`: bidirectional equivalence on derivability.
- `pl_setConsistent_iff_algebraic`: consistency equivalence.
- `pl_setMaxConsistent_iff_algebraic`: MCS equivalence.

## Architecture

`propDerivationSystem.Deriv Γ φ = PL.Deriv Axioms Γ φ`
  `= Nonempty (DerivationTree Axioms Γ φ)`

`(propAlgDS Axioms).Deriv Γ φ`
  `= ListDeriv Γ φ` (with `S` inferred as `HilbertOf Axioms`)
  `= InferenceSystem.DerivableIn (HilbertOf Axioms) (listImp Γ φ)`
  `= Nonempty ((HilbertOf Axioms)⇓(listImp Γ φ))`
  `= Nonempty (DerivationTree Axioms [] (listImp Γ φ))`

**Forward** (tree → algebraic): structural induction on `DerivationTree`. Propositional
logic has 4 constructors (ax, assumption, modus_ponens, weakening); there is no
`necessitation` arm.

**Backward** (algebraic → tree): extract `d₀ : [] ⊢ listImp Γ φ`, weaken to
`Γ ⊢ listImp Γ φ`, then apply `unfoldListImpInTree` to eliminate each layer.

## Design Note

This file does NOT import `Propositional/Metalogic/DeductionTheorem.lean`. The equivalence
is derived directly from the `InferenceSystem` and `MinimalHilbert` instances for
`HilbertOf Axioms` registered below. This ensures `DeductionTheorem.lean` can import
this bridge without creating a cycle.

## References

* `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — D1 architecture docstring;
  `algebraic_has_deduction_theorem`, `HasMinimalAxioms`, `algebraicDerivationSystem`
* `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` — `SetConsistent`, `SetMaximalConsistent`
* `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — closest template
* `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — fc-parameterized template
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction
open Cslib.Logic.Metalogic.GenericMCS
open Cslib.Logic.Metalogic.MCSProperties
open Cslib.Logic.Metalogic

variable {Atom : Type*}
variable {Axioms : PL.Proposition Atom → Prop}

/-! ## HilbertOf Tag Type -/

/-- Empty tag type whose `InferenceSystem` maps `HilbertOf Axioms`-derivability to
`Nonempty (DerivationTree Axioms [] φ)`. This is a pure infrastructure type with no
constructors; all proof content lives in the `InferenceSystem` and `MinimalHilbert`
instances below. -/
inductive HilbertOf (Axioms : PL.Proposition Atom → Prop) : Type

/-! ## InferenceSystem Instance -/

/-- `(HilbertOf Axioms)⇓φ` is a `DerivationTree Axioms [] φ` — a closed derivation tree
(from empty context) using axioms satisfying `Axioms`. -/
instance : InferenceSystem (HilbertOf Axioms) (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree Axioms [] φ

/-! ## ModusPonens Instance -/

/-- Modus ponens for `HilbertOf Axioms`: from `⊢ φ → ψ` and `⊢ φ`, derive `⊢ ψ`
using the tree `modus_ponens` constructor at empty context. -/
instance : ModusPonens (HilbertOf Axioms) (F := PL.Proposition Atom) where
  mp := fun h₁ h₂ => by
    obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
    exact ⟨PL.DerivationTree.modus_ponens [] _ _ d₁ d₂⟩

/-! ## Conditional Axiom Instances -/

/-- `HilbertOf Axioms` proves the K axiom whenever `Axioms` satisfies `HasMinimalAxioms`. -/
instance [h : HasMinimalAxioms Axioms] :
    HasAxiomImplyK (HilbertOf Axioms) (F := PL.Proposition Atom) where
  implyK := ⟨PL.DerivationTree.ax [] _ (h.hasImplyK _ _)⟩

/-- `HilbertOf Axioms` proves the S axiom whenever `Axioms` satisfies `HasMinimalAxioms`. -/
instance [h : HasMinimalAxioms Axioms] :
    HasAxiomImplyS (HilbertOf Axioms) (F := PL.Proposition Atom) where
  implyS := ⟨PL.DerivationTree.ax [] _ (h.hasImplyS _ _ _)⟩

/-- `HilbertOf Axioms` is a `MinimalHilbert` system whenever `Axioms` satisfies
`HasMinimalAxioms`. Synthesised automatically from `ModusPonens`, `HasAxiomImplyK`,
`HasAxiomImplyS` instances above. -/
instance [HasMinimalAxioms Axioms] :
    MinimalHilbert (HilbertOf Axioms) (F := PL.Proposition Atom) where

/-! ## Algebraic DS Alias -/

/-- Shorthand for the algebraic derivation system at `HilbertOf Axioms`. -/
@[reducible] def propAlgDS (Axioms : PL.Proposition Atom → Prop)
    [HasMinimalAxioms Axioms] :
    Metalogic.DerivationSystem (PL.Proposition Atom) :=
  @algebraicDerivationSystem (PL.Proposition Atom) _ _ (HilbertOf Axioms) _ _

/-- `PL.DerivationTree Axioms` is a `HilbertTree` whenever `Axioms` satisfies
`HasMinimalAxioms`: closed under assumption, modus ponens, weakening, and the K/S axiom
schemata at the empty context. Feeds the generic backward combinators
(`unfoldListImp`/`listDerivToTree`) below. -/
instance [h : HasMinimalAxioms Axioms] :
    HilbertTree (F := PL.Proposition Atom) (PL.DerivationTree Axioms) where
  assumption {Γ a} hmem := .assumption Γ a hmem
  mp {Γ φ ψ} d₁ d₂ := .modus_ponens Γ φ ψ d₁ d₂
  weakening {Γ Δ φ} hsub d := .weakening Γ Δ φ d hsub
  axiomK φ ψ := .ax [] _ (h.hasImplyK φ ψ)
  axiomS φ ψ χ := .ax [] _ (h.hasImplyS φ ψ χ)

/-! ## Forward Direction: DerivationTree → Algebraic Deriv -/

/-- Forward bridge: given `d : DerivationTree Axioms Γ φ` and `[HasMinimalAxioms Axioms]`,
produce `(propAlgDS Axioms).Deriv Γ φ` by structural induction on the derivation tree.

- **ax**: the axiom `⊢ ψ` in `HilbertOf Axioms` lifts to `Deriv Γ ψ` via K-weakening.
- **assumption**: reflected directly.
- **modus_ponens**: contextual modus ponens.
- **weakening**: monotone in the context. -/
lemma derivTreeToList [HasMinimalAxioms Axioms]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : PL.DerivationTree Axioms Γ φ) :
    (propAlgDS Axioms (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | ax Γ ψ h_ax =>
    -- ψ is a HilbertOf Axioms theorem (tree at empty context)
    have h_thm : InferenceSystem.DerivableIn (HilbertOf Axioms) ψ :=
      ⟨PL.DerivationTree.ax [] ψ h_ax⟩
    -- Lift to the algebraic system via K-weakening: ⊢ ψ → listImp Γ ψ, then MP
    simp only [propAlgDS, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [propAlgDS, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [propAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [propAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih

/-! ## Backward Helper: Unfold listImp Using Assumptions -/

/-- Backward helper: given `Γ ⊢ listImp Ψ φ` (tree) and `Ψ ⊆ Γ`,
produce `Γ ⊢ φ` by iterating modus ponens with assumption trees. Delegates to the
generic `unfoldListImp` (Foundations), instantiated at `D := PL.DerivationTree Axioms`
via the `HilbertTree` instance above. -/
noncomputable def unfoldListImpInTree [HasMinimalAxioms Axioms]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (Ψ : List (PL.Proposition Atom))
    (d : PL.DerivationTree Axioms Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    PL.DerivationTree Axioms Γ φ :=
  GenericMCS.unfoldListImp Ψ d h_sub

/-! ## Backward Direction: Algebraic Deriv → DerivationTree -/

/-- Backward bridge: `(propAlgDS Axioms).Deriv Γ φ → DerivationTree Axioms Γ φ`.

Delegates to the generic `listDerivToTree` (Foundations), instantiated at
`D := PL.DerivationTree Axioms`. External callers: PL and Modal
`DeductionTheorem.lean`. -/
noncomputable def listDerivToTree [HasMinimalAxioms Axioms]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : (propAlgDS Axioms (Atom := Atom)).Deriv Γ φ) :
    PL.DerivationTree Axioms Γ φ :=
  GenericMCS.listDerivToTree (D := PL.DerivationTree Axioms) h

/-! ## Full Derivability Equivalence -/

/-- Bidirectional derivability equivalence between `propDerivationSystem Axioms` and
the algebraic derivation system at `S := HilbertOf Axioms`, for any `Axioms` satisfying
`HasMinimalAxioms`. -/
theorem pl_deriv_iff_algebraic [HasMinimalAxioms Axioms]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    (propDerivationSystem Axioms).Deriv Γ φ ↔
    (propAlgDS Axioms (Atom := Atom)).Deriv Γ φ := by
  unfold propDerivationSystem Deriv
  constructor
  · intro ⟨d⟩
    exact derivTreeToList d
  · intro h
    exact ⟨listDerivToTree h⟩

/-! ## MCS Equivalences -/

/-- `SetConsistent` under `propDerivationSystem Axioms` iff under `propAlgDS Axioms`.
Delegates to the generic `setConsistent_iff_congr` (Foundations). -/
theorem pl_setConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (PL.Proposition Atom)} :
    SetConsistent (propDerivationSystem Axioms) Ω ↔
    SetConsistent (propAlgDS Axioms (Atom := Atom)) Ω :=
  GenericMCS.setConsistent_iff_congr (fun _ _ => pl_deriv_iff_algebraic)

/-- `SetMaximalConsistent` under `propDerivationSystem Axioms` iff under `propAlgDS Axioms`.
Delegates to the generic `setMaxConsistent_iff_congr` (Foundations). -/
theorem pl_setMaxConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (PL.Proposition Atom)} :
    SetMaximalConsistent (propDerivationSystem Axioms) Ω ↔
    SetMaximalConsistent (propAlgDS Axioms (Atom := Atom)) Ω :=
  GenericMCS.setMaxConsistent_iff_congr (fun _ _ => pl_deriv_iff_algebraic)

end Cslib.Logic.PL
