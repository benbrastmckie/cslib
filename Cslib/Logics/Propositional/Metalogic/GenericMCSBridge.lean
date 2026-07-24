/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Foundations.Logic.Metalogic.GenericMCS

/-! # GenericMCS Bridge for Propositional Logic

This module proves the bidirectional equivalence between the tree-based
`propDerivationSystem Axioms` and the algebraic `algebraicDerivationSystem` instantiated
at `S := ClosedHilbert (PL.DerivationTree Axioms)`, for any axiom predicate satisfying
`HasMinimalAxioms`.

## Main Results

- `HilbertTree (PL.DerivationTree Axioms)`: instance feeding the generic `ClosedHilbert`
  tag (Foundations) and the generic backward combinators.
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
  `= ListDeriv Γ φ` (with `S` inferred as `ClosedHilbert (PL.DerivationTree Axioms)`)
  `= InferenceSystem.DerivableIn (ClosedHilbert (PL.DerivationTree Axioms)) (listImp Γ φ)`
  `= Nonempty (PL.DerivationTree Axioms [] (listImp Γ φ))`

**Forward** (tree → algebraic): structural induction on `DerivationTree`. Propositional
logic has 4 constructors (ax, assumption, modusPonens, weakening); there is no
`necessitation` arm.

**Backward** (algebraic → tree): extract `d₀ : [] ⊢ listImp Γ φ`, weaken to
`Γ ⊢ listImp Γ φ`, then apply `unfoldListImpInTree` to eliminate each layer.

## Design Note

This file uses the generic `ClosedHilbert (PL.DerivationTree Axioms)` tag (Foundations) rather
than a local `HilbertOf Axioms` bundle, since `HilbertOf Axioms` has no external references
(grep-confirmed); the generic tag's `InferenceSystem`/`ModusPonens`/`HasAxiomImplyK`/
`HasAxiomImplyS`/`MinimalHilbert` instances are supplied automatically from the
`HilbertTree (PL.DerivationTree Axioms)` instance below. This file still does NOT import
`Propositional/Metalogic/DeductionTheorem.lean`, preserving the no-cycle property.

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
open Cslib.Logic.Metalogic

variable {Atom : Type*}
variable {Axioms : PL.Proposition Atom → Prop}

/-- `PL.DerivationTree Axioms` is a `HilbertTree` whenever `Axioms` satisfies
`HasMinimalAxioms`: closed under assumption, modus ponens, weakening, and the K/S axiom
schemata at the empty context. Feeds the generic `ClosedHilbert` tag and backward
combinators (`unfoldListImp`/`listDerivToTree`) below. Must precede `propAlgDS` (Lean
scoping: `treeAlgDS` requires this instance in scope). -/
instance [h : HasMinimalAxioms Axioms] :
    HilbertTree (F := PL.Proposition Atom) (PL.DerivationTree Axioms) where
  assumption {Γ a} hmem := .assumption Γ a hmem
  mp {Γ φ ψ} d₁ d₂ := .modusPonens Γ φ ψ d₁ d₂
  weakening {Γ Δ φ} hsub d := .weakening Γ Δ φ d hsub
  axiomK φ ψ := .ax [] _ (h.hasImplyK φ ψ)
  axiomS φ ψ χ := .ax [] _ (h.hasImplyS φ ψ χ)

/-! ## Algebraic DS Alias -/

/-- Shorthand for the algebraic derivation system at the generic `ClosedHilbert
(PL.DerivationTree Axioms)` tag. A thin re-export: the underlying tag changed from the
retired local `HilbertOf Axioms` to `ClosedHilbert`, but the name and signature are
unchanged. -/
@[reducible] def propAlgDS (Axioms : PL.Proposition Atom → Prop)
    [HasMinimalAxioms Axioms] :
    Metalogic.DerivationSystem (PL.Proposition Atom) :=
  treeAlgDS (PL.DerivationTree Axioms)

/-! ## Forward Direction: DerivationTree → Algebraic Deriv -/

/-- Forward bridge: given `d : DerivationTree Axioms Γ φ` and `[HasMinimalAxioms Axioms]`,
produce `(propAlgDS Axioms).Deriv Γ φ` by structural induction on the derivation tree.

- **ax**: the axiom `⊢ ψ` in `ClosedHilbert (PL.DerivationTree Axioms)` lifts to `Deriv Γ ψ`
  via K-weakening.
- **assumption**: reflected directly.
- **modusPonens**: contextual modus ponens.
- **weakening**: monotone in the context. -/
lemma derivTreeToList [HasMinimalAxioms Axioms]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : PL.DerivationTree Axioms Γ φ) :
    (propAlgDS Axioms (Atom := Atom)).Deriv Γ φ := by
  induction d with
  | ax Γ ψ h_ax =>
    -- ψ is a ClosedHilbert (PL.DerivationTree Axioms) theorem (tree at empty context)
    have h_thm : InferenceSystem.DerivableIn (ClosedHilbert (PL.DerivationTree Axioms)) ψ :=
      ⟨PL.DerivationTree.ax [] ψ h_ax⟩
    -- Lift to the algebraic system via K-weakening: ⊢ ψ → listImp Γ ψ, then MP
    simp only [propAlgDS, treeAlgDS, algebraicDerivationSystem]
    unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [propAlgDS, treeAlgDS, algebraicDerivationSystem]
    exact list_deriv_reflection h_mem
  | @modusPonens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [propAlgDS, treeAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_mp ih₁ ih₂
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [propAlgDS, treeAlgDS, algebraicDerivationSystem] at *
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
the algebraic derivation system at `S := ClosedHilbert (PL.DerivationTree Axioms)`, for
any `Axioms` satisfying `HasMinimalAxioms`. -/
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
