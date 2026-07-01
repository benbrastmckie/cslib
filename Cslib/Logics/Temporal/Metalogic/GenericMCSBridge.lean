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

The base (`fc := .Base`) bridge is defined below as a thin delegation to the
`fc`-parameterized bridge (`*Fc` names): `temporalAlgDS.Deriv Γ φ` and
`temporalAlgDSFc .Base .Deriv Γ φ` are definitionally equal (both reduce to
`Nonempty (DerivationTree .Base [] (listImp Γ φ))`), so the base helpers below are
one-line delegations to the `_fc` versions at `fc := .Base`. The `_fc` machinery must
therefore be defined first (Lean scoping).

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

This `fc`-parameterized bridge is defined first (before the base bridge) because the
base (`fc := .Base`) helpers below are thin delegations to these `_fc` definitions.
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

/-- `DerivationTree fc` is a `HilbertTree`: closed under assumption, modus ponens,
weakening, and the K/S axiom schemata at the empty context. Feeds the generic backward
combinators (`unfoldListImp`/`listDerivToTree`) below. Note: Temporal's `imp_s`/`imp_k`
axiom constructors are swapped relative to the K/S schema names (documented at their
`HasAxiomImplyK`/`HasAxiomImplyS` instances above). -/
instance (fc : FrameClass) : HilbertTree (F := Temporal.Formula Atom) (DerivationTree fc) where
  assumption {Γ a} h := .assumption Γ a h
  mp {Γ φ ψ} d₁ d₂ := .modus_ponens Γ φ ψ d₁ d₂
  weakening {Γ Δ φ} h d := .weakening Γ Δ φ d h
  axiomK _ _ := .axiom [] _ (.imp_s _ _) (FrameClass.base_le fc)
  axiomS _ _ _ := .axiom [] _ (.imp_k _ _ _) (FrameClass.base_le fc)

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
produce `Γ ⊢[fc] φ` by iterating modus ponens with assumption trees. Delegates to the
generic `unfoldListImp` (Foundations), instantiated at `D := DerivationTree fc` via the
`HilbertTree` instance above. -/
noncomputable def unfoldListImpInTreeFc {fc : FrameClass}
    {Γ : Context Atom} {φ : Formula Atom}
    (Ψ : Context Atom)
    (d : DerivationTree fc Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    DerivationTree fc Γ φ :=
  GenericMCS.unfoldListImp Ψ d h_sub

/-! ## FC-Parameterized Backward Bridge -/

/-- Backward bridge: `(temporalAlgDSFc fc).Deriv Γ φ → DerivationTree fc Γ φ`.

Delegates to the generic `listDerivToTree` (Foundations), instantiated at
`D := DerivationTree fc`: `(temporalAlgDSFc fc).Deriv Γ φ` and `(treeAlgDS
(DerivationTree fc)).Deriv Γ φ` are definitionally equal (both reduce to
`Nonempty (DerivationTree fc [] (listImp Γ φ))`, since `HilbertBXFc fc` and
`ClosedHilbert (DerivationTree fc)` share the same `derivation`). -/
noncomputable def listDerivToTreeFc {fc : FrameClass}
    {Γ : Context Atom} {φ : Formula Atom}
    (h : (temporalAlgDSFc fc (Atom := Atom)).Deriv Γ φ) :
    DerivationTree fc Γ φ :=
  GenericMCS.listDerivToTree (D := DerivationTree fc) h

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

/-! ## Base Bridge (fc := .Base)

`temporalAlgDS.Deriv Γ φ` and `(temporalAlgDSFc .Base).Deriv Γ φ` are definitionally
equal: both reduce to `Nonempty (DerivationTree .Base [] (listImp Γ φ))`, since
`Temporal.HilbertBX`'s `InferenceSystem.derivation φ := DerivationTree .Base [] φ`
literally matches `HilbertBXFc .Base`'s. The base helpers below are therefore
one-line delegations to their `_fc` counterparts at `fc := .Base`. -/

/-- Shorthand for the algebraic derivation system at `Temporal.HilbertBX`. -/
@[reducible] def temporalAlgDS : Metalogic.DerivationSystem (Formula Atom) :=
  @algebraicDerivationSystem (Formula Atom) _ _ Temporal.HilbertBX _ _

/-- Forward bridge: given `d : DerivationTree FrameClass.Base Γ φ`, produce
`temporalAlgDS.Deriv Γ φ`. Delegates to `derivTreeToListFc` at `fc := .Base`
(definitionally equal target, §3.2). -/
lemma derivTreeToList
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base Γ φ) :
    (temporalAlgDS (Atom := Atom)).Deriv Γ φ :=
  derivTreeToListFc d

/-- Backward helper: given `Γ ⊢ listImp Ψ φ` (tree) and `Ψ ⊆ Γ`,
produce `Γ ⊢ φ`. Delegates to `unfoldListImpInTreeFc` at `fc := .Base`. -/
noncomputable def unfoldListImpInTree
    {Γ : Context Atom} {φ : Formula Atom}
    (Ψ : Context Atom)
    (d : DerivationTree FrameClass.Base Γ (listImp Ψ φ))
    (h_sub : ∀ a ∈ Ψ, a ∈ Γ) :
    DerivationTree FrameClass.Base Γ φ :=
  unfoldListImpInTreeFc (fc := .Base) Ψ d h_sub

/-- Backward bridge: `temporalAlgDS.Deriv Γ φ → DerivationTree .Base Γ φ`.
Delegates to `listDerivToTreeFc` at `fc := .Base` (definitionally equal source, §3.2). -/
noncomputable def listDerivToTree
    {Γ : Context Atom} {φ : Formula Atom}
    (h : (temporalAlgDS (Atom := Atom)).Deriv Γ φ) :
    DerivationTree FrameClass.Base Γ φ :=
  listDerivToTreeFc (fc := .Base) h

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

/-- `SetConsistent` under `temporalDerivationSystem` iff under `temporalAlgDS`.
Delegates to the generic `setConsistent_iff_congr` (Foundations). -/
theorem temporal_setConsistent_iff_algebraic
    {Ω : Set (Formula Atom)} :
    SetConsistent temporalDerivationSystem Ω ↔
    SetConsistent (temporalAlgDS (Atom := Atom)) Ω :=
  GenericMCS.setConsistent_iff_congr (fun _ _ => temporal_deriv_iff_algebraic)

/-- `SetMaximalConsistent` under `temporalDerivationSystem` iff under `temporalAlgDS`.
Delegates to the generic `setMaxConsistent_iff_congr` (Foundations). -/
theorem temporal_setMaxConsistent_iff_algebraic
    {Ω : Set (Formula Atom)} :
    SetMaximalConsistent temporalDerivationSystem Ω ↔
    SetMaximalConsistent (temporalAlgDS (Atom := Atom)) Ω :=
  GenericMCS.setMaxConsistent_iff_congr (fun _ _ => temporal_deriv_iff_algebraic)

end Cslib.Logic.Temporal
