/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Foundations.Logic.Metalogic.GenericMCS
public import Cslib.Logics.Bimodal.ProofSystem.Instances

/-! # GenericMCS Bridge for Bimodal Logic TM

This module proves the bidirectional equivalence between the tree-based
`bimodalDerivationSystem` and the algebraic `algebraicDerivationSystem` instantiated
at `S := Bimodal.HilbertTM`.

## Main Results

- `derivTreeToList`: `DerivationTree .Base Γ φ → (bimodalAlgDS).Deriv Γ φ`
  (forward, structural induction on the tree).
- `listDerivToTree`: `(bimodalAlgDS).Deriv Γ φ → DerivationTree .Base Γ φ`
  (backward direction).
- `bimodal_deriv_iff_algebraic`: bidirectional equivalence on derivability.

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

**Backward** (algebraic → tree): `listDerivToTree` delegates directly to the generic
`GenericMCS.listDerivToTree` (Foundations), which extracts `d₀ : [] ⊢ listImp Γ φ`, weakens to
`Γ ⊢ listImp Γ φ`, then applies the generic `GenericMCS.unfoldListImp` to eliminate each layer.

The base (`fc := .Base`) bridge is defined below as a thin delegation to the
`fc`-parameterized bridge (`*Fc` names): `bimodalAlgDS.Deriv Γ φ` and
`bimodalAlgDSFc .Base .Deriv Γ φ` are definitionally equal (both reduce to
`Nonempty (DerivationTree .Base [] (listImp Γ φ))`), so the base helpers below are
one-line delegations to the `_fc` versions at `fc := .Base`. The `_fc` machinery must
therefore be defined first (Lean scoping).

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
open Cslib.Logic.Metalogic
open Cslib.Logic.Bimodal

variable {Atom : Type*}

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
3. The backward bridge delegates directly to the generic `GenericMCS.listDerivToTree`
   (Foundations), instantiated at `D := Bimodal.DerivationTree fc`.

This gives `algebraic_has_deduction_theorem` for any `fc`, enabling
`deductionTheorem {fc}` and `deductionWithMem {fc}` in `DeductionTheorem.lean`
to be rerouted without structural recursion.

This `fc`-parameterized bridge is defined first (before the base bridge) because the
base (`fc := .Base`) helpers below are thin delegations to these `_fc` definitions.
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

/-- `Bimodal.DerivationTree fc` is a `HilbertTree`: closed under assumption, modus ponens,
weakening, and the K/S axiom schemata at the empty context. Feeds the generic backward
combinators (`unfoldListImp`/`listDerivToTree`) below. Note: Bimodal's `imp_s`/`imp_k`
axiom constructors are swapped relative to the K/S schema names (documented at their
`HasAxiomImplyK`/`HasAxiomImplyS` instances above). The `@HilbertTree ... _ ...` positional
form (rather than `(F := ...)`) is required here because Bimodal's temporal `F` (future)
notation shadows the bare identifier `F` in this scope. -/
instance (fc : FrameClass) :
    @HilbertTree (Bimodal.Formula Atom) _ (Bimodal.DerivationTree fc) where
  assumption {Γ a} h := .assumption Γ a h
  mp {Γ φ ψ} d₁ d₂ := .modus_ponens Γ φ ψ d₁ d₂
  weakening {Γ Δ φ} h d := .weakening Γ Δ φ d h
  axiomK _ _ := .axiom [] _ (.imp_s _ _) (FrameClass.base_le fc)
  axiomS _ _ _ := .axiom [] _ (.imp_k _ _ _) (FrameClass.base_le fc)

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
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    exact list_deriv_mp ih₁ ih₂
  | @necessitation ψ _d ih =>
    exact ⟨Bimodal.DerivationTree.necessitation ψ ih.toDerivation⟩
  | @temporal_necessitation ψ _d ih =>
    exact ⟨Bimodal.DerivationTree.temporal_necessitation ψ ih.toDerivation⟩
  | @temporal_duality ψ _d ih =>
    exact ⟨Bimodal.DerivationTree.temporal_duality ψ ih.toDerivation⟩
  | @weakening Γ' Γ ψ _d h_sub ih =>
    exact list_deriv_monotonic h_sub ih

/-! ## FC-Parameterized Backward Bridge -/

/-- Backward bridge: `(bimodalAlgDSFc fc).Deriv Γ φ → DerivationTree fc Γ φ`.

Delegates to the generic `listDerivToTree` (Foundations), instantiated at
`D := Bimodal.DerivationTree fc`: `(bimodalAlgDSFc fc).Deriv Γ φ` and `(treeAlgDS
(Bimodal.DerivationTree fc)).Deriv Γ φ` are definitionally equal (both reduce to
`Nonempty (DerivationTree fc [] (listImp Γ φ))`, since `HilbertTMFc fc` and
`ClosedHilbert (Bimodal.DerivationTree fc)` share the same `derivation`). -/
noncomputable def listDerivToTreeFc {fc : FrameClass}
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (h : (bimodalAlgDSFc fc (Atom := Atom)).Deriv Γ φ) :
    Bimodal.DerivationTree fc Γ φ :=
  GenericMCS.listDerivToTree (D := Bimodal.DerivationTree fc) h

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

/-! ## Base Bridge (fc := .Base)

`bimodalAlgDS.Deriv Γ φ` and `(bimodalAlgDSFc .Base).Deriv Γ φ` are definitionally
equal: both reduce to `Nonempty (DerivationTree .Base [] (listImp Γ φ))`, since
`Bimodal.HilbertTM`'s `InferenceSystem.derivation φ := DerivationTree .Base [] φ`
literally matches `HilbertTMFc .Base`'s. The base helpers below are therefore
one-line delegations to their `_fc` counterparts at `fc := .Base`. -/

/-- Shorthand for the algebraic derivation system at `Bimodal.HilbertTM`. -/
@[reducible] def bimodalAlgDS : Metalogic.DerivationSystem (Bimodal.Formula Atom) :=
  @algebraicDerivationSystem (Bimodal.Formula Atom) _ _ Bimodal.HilbertTM _ _

/-- Forward bridge: given `d : DerivationTree FrameClass.Base Γ φ`, produce
`bimodalAlgDS.Deriv Γ φ`. Delegates to `derivTreeToListFc` at `fc := .Base`
(definitionally equal target). -/
lemma derivTreeToList
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (d : Bimodal.DerivationTree FrameClass.Base Γ φ) :
    (bimodalAlgDS (Atom := Atom)).Deriv Γ φ :=
  derivTreeToListFc d

/-- Backward bridge: `bimodalAlgDS.Deriv Γ φ → DerivationTree .Base Γ φ`.
Delegates to `listDerivToTreeFc` at `fc := .Base` (definitionally equal source). -/
noncomputable def listDerivToTree
    {Γ : Bimodal.Context Atom} {φ : Bimodal.Formula Atom}
    (h : (bimodalAlgDS (Atom := Atom)).Deriv Γ φ) :
    Bimodal.DerivationTree FrameClass.Base Γ φ :=
  listDerivToTreeFc (fc := .Base) h

/-! ## Full Derivability Equivalence -/

/-- Bidirectional derivability equivalence between `bimodalDerivationSystem` and
the algebraic derivation system at `S := Bimodal.HilbertTM`.

Not routed through the generic `GenericMCS.deriv_iff_algebraic_of_forward` assembler used by
the Propositional/Modal bridges: `Bimodal.HilbertTM` is its own bespoke `InferenceSystem` tag,
not the generic `ClosedHilbert (DerivationTree .Base)`, so `HilbertTree` instance search for the
assembler's target fails even though the two tags are extensionally/definitionally equivalent
(see the design note above). This 6-line form is already the maximally consolidated shape for
the Temporal/Bimodal base bridges. -/
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

end Cslib.Logic.Bimodal.Metalogic.Core
