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
produce `Γ ⊢ φ` by iterating modus ponens with assumption trees.

Induction on `Ψ`: in the cons case, `a ∈ Γ` gives `Γ ⊢ a` by assumption,
then MP reduces `listImp (a :: Ψ') φ` to `listImp Ψ' φ`. -/
noncomputable def unfoldListImpInTree
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (Ψ : List (PL.Proposition Atom))
    (d : PL.DerivationTree Axioms Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    PL.DerivationTree Axioms Γ φ := by
  induction Ψ generalizing φ with
  | nil =>
    simp only [listImp_nil] at d
    exact d
  | cons a Ψ' ih =>
    simp only [listImp_cons] at d
    -- d : Γ ⊢ a → listImp Ψ' φ
    have ha_mem : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
    have d_a : PL.DerivationTree Axioms Γ a :=
      PL.DerivationTree.assumption Γ a ha_mem
    have d_tail : PL.DerivationTree Axioms Γ (listImp Ψ' φ) :=
      PL.DerivationTree.modus_ponens Γ a (listImp Ψ' φ) d d_a
    exact ih d_tail (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-! ## Backward Direction: Algebraic Deriv → DerivationTree -/

/-- Backward bridge: `(propAlgDS Axioms).Deriv Γ φ → DerivationTree Axioms Γ φ`.

Extracts `d₀ : [] ⊢ listImp Γ φ` from the algebraic derivation, weakens to `Γ`,
then applies `unfoldListImpInTree` to eliminate the list-implication layers. -/
noncomputable def listDerivToTree [HasMinimalAxioms Axioms]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : (propAlgDS Axioms (Atom := Atom)).Deriv Γ φ) :
    PL.DerivationTree Axioms Γ φ := by
  simp only [propAlgDS, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  -- h : InferenceSystem.DerivableIn (HilbertOf Axioms) (listImp Γ φ)
  -- = Nonempty ((HilbertOf Axioms)⇓(listImp Γ φ))
  -- = Nonempty (DerivationTree Axioms [] (listImp Γ φ))
  have d₀ : PL.DerivationTree Axioms [] (listImp Γ φ) := h.toDerivation
  -- Weaken from [] to Γ
  have d_weak : PL.DerivationTree Axioms Γ (listImp Γ φ) :=
    PL.DerivationTree.weakening [] Γ (listImp Γ φ) d₀ (List.nil_subset Γ)
  -- Eliminate listImp using assumption trees
  exact unfoldListImpInTree Γ d_weak (fun _a ha => ha)

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

/-- `SetConsistent` under `propDerivationSystem Axioms` iff under `propAlgDS Axioms`. -/
theorem pl_setConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (PL.Proposition Atom)} :
    SetConsistent (propDerivationSystem Axioms) Ω ↔
    SetConsistent (propAlgDS Axioms (Atom := Atom)) Ω := by
  unfold SetConsistent Consistent
  constructor
  · intro h L hL hd
    exact h L hL (pl_deriv_iff_algebraic.mpr hd)
  · intro h L hL hd
    exact h L hL (pl_deriv_iff_algebraic.mp hd)

/-- `SetMaximalConsistent` under `propDerivationSystem Axioms` iff under `propAlgDS Axioms`. -/
theorem pl_setMaxConsistent_iff_algebraic [HasMinimalAxioms Axioms]
    {Ω : Set (PL.Proposition Atom)} :
    SetMaximalConsistent (propDerivationSystem Axioms) Ω ↔
    SetMaximalConsistent (propAlgDS Axioms (Atom := Atom)) Ω := by
  unfold SetMaximalConsistent
  constructor
  · intro ⟨hcons, hmax⟩
    refine ⟨pl_setConsistent_iff_algebraic.mp hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (pl_setConsistent_iff_algebraic.mpr hinsert)
  · intro ⟨hcons, hmax⟩
    refine ⟨pl_setConsistent_iff_algebraic.mpr hcons, fun φ hφ hinsert => ?_⟩
    exact hmax φ hφ (pl_setConsistent_iff_algebraic.mp hinsert)

end Cslib.Logic.PL
