/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Foundations.Logic.ProofSystem
public import Cslib.Logics.Temporal.ProofSystem.Derivation

/-! # Instance Registration for Temporal.HilbertBX

This module registers `InferenceSystem`, `ClassicalHilbert`, `TemporalNecessitation`,
all 22 `HasAxiom*`, and `TemporalBXHilbert` instances for the `Temporal.HilbertBX` tag type,
connecting the abstract typeclass hierarchy to the concrete derivation tree.

## Architecture

The `InferenceSystem` instance maps `HilbertBX⇓φ` to `DerivationTree .Base [] φ`.
This makes `InferenceSystem.DerivableIn HilbertBX φ = Nonempty (DerivationTree .Base [] φ)`.

## Naming Note

BimodalLogic uses swapped names: `prop_k` = distribution (cslib's `ImplyS`),
`prop_s` = weakening (cslib's `ImplyK`). The instances below map correctly.
-/

@[expose] public section


-- Do not open Cslib.Logic.Temporal to avoid scoped notation conflicts
-- (F, G, H, P, S, U are all scoped notation for temporal operators)
open Cslib.Logic

variable {Atom : Type u}

namespace Cslib.Logic.Temporal

section TempInstances

/-! ## InferenceSystem Instance -/

instance : InferenceSystem Temporal.HilbertBX (Temporal.Formula Atom) where
  derivation φ := Temporal.DerivationTree Temporal.FrameClass.Base
    ([] : Temporal.Context Atom) φ

/-! ## ModusPonens Instance -/

instance :
    ModusPonens Temporal.HilbertBX (F := Temporal.Formula Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Temporal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

/-! ## Propositional Axiom Instances -/

-- prop_s (weakening) -> cslib ImplyK, prop_k (distribution) -> cslib ImplyS
instance :
    HasAxiomImplyK Temporal.HilbertBX (F := Temporal.Formula Atom) where
  implyK := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.imp_s _ _) trivial⟩

instance :
    HasAxiomImplyS Temporal.HilbertBX (F := Temporal.Formula Atom) where
  implyS := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.imp_k _ _ _) trivial⟩

instance :
    HasAxiomEFQ Temporal.HilbertBX (F := Temporal.Formula Atom) where
  efq := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.efq _) trivial⟩

instance :
    HasAxiomPeirce Temporal.HilbertBX (F := Temporal.Formula Atom) where
  peirce := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.peirce _ _) trivial⟩

/-! ## ClassicalHilbert Instance -/

instance :
    ClassicalHilbert Temporal.HilbertBX (F := Temporal.Formula Atom) where

/-! ## TemporalNecessitation Instance -/

-- Hypothetical-syllogism helper (private): from ⊢ A → B and ⊢ B → C, derive ⊢ A → C.
-- Used to bridge between the new primitive G/H constructors and the Foundation-level encoding.
private def hypSyl {Atom : Type u}
    {A B C : Temporal.Formula Atom}
    (d1 : Temporal.DerivationTree Temporal.FrameClass.Base [] (A.imp B))
    (d2 : Temporal.DerivationTree Temporal.FrameClass.Base [] (B.imp C)) :
    Temporal.DerivationTree Temporal.FrameClass.Base [] (A.imp C) :=
  -- imp_s: ⊢ (B→C) → A → (B→C)
  let d3 := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
              ((B.imp C).imp (A.imp (B.imp C)))
              (Temporal.Axiom.imp_s (B.imp C) A) trivial
  -- ⊢ A → (B→C)
  let d4 := Temporal.DerivationTree.modus_ponens [] (B.imp C) (A.imp (B.imp C)) d3 d2
  -- imp_k: ⊢ (A → B→C) → (A→B) → A→C
  let d5 := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
              ((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C)))
              (Temporal.Axiom.imp_k A B C) trivial
  -- ⊢ (A→B) → A→C
  let d6 :=
    Temporal.DerivationTree.modus_ponens [] (A.imp (B.imp C)) ((A.imp B).imp (A.imp C)) d5 d4
  -- ⊢ A→C
  Temporal.DerivationTree.modus_ponens [] (A.imp B) (A.imp C) d6 d1

instance :
    TemporalNecessitation Temporal.HilbertBX (F := Temporal.Formula Atom) where
  -- tempNec: from ⊢ φ, derive ⊢ ¬F¬φ (the Foundation-level encoding of G φ).
  -- Strategy: temporal_necessitation gives ⊢ allFuture φ (primitive constructor);
  -- then allFuture_to_classic bridge axiom gives ⊢ allFuture φ → ¬F¬φ; then MP.
  tempNec := fun {φ} (h : InferenceSystem.DerivableIn Temporal.HilbertBX φ) => by
    obtain ⟨d⟩ := h
    let d_nec := Temporal.DerivationTree.temporal_necessitation φ d
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) [] _
      (Temporal.Axiom.allFuture_to_classic φ) trivial
    exact ⟨Temporal.DerivationTree.modus_ponens [] _ _ d_bridge d_nec⟩
  -- tempNecPast: from ⊢ φ, derive ⊢ ¬P¬φ (the Foundation-level encoding of H φ).
  -- Strategy: swap→necessitate→swap gives ⊢ allPast (swap(swap φ)) = allPast φ (via involution);
  -- then allPast_to_classic bridge axiom gives ⊢ allPast φ → ¬P¬φ; then MP.
  tempNecPast := fun {φ} (h : InferenceSystem.DerivableIn Temporal.HilbertBX φ) => by
    obtain ⟨d⟩ := h
    let d_swap := Temporal.DerivationTree.temporal_duality _ d
    let g_swap := Temporal.DerivationTree.temporal_necessitation _ d_swap
    -- d_final : DT [] (swapTemporal (allFuture (swapTemporal φ)))
    --         = DT [] (allPast (swapTemporal (swapTemporal φ)))  [by swapTemporal def]
    let d_final := Temporal.DerivationTree.temporal_duality _ g_swap
    -- Rewrite allPast (swap(swap φ)) to allPast φ using swapTemporal_involution
    have h_eq : Temporal.Formula.allPast (Temporal.Formula.swapTemporal
        (Temporal.Formula.swapTemporal φ)) = Temporal.Formula.allPast φ :=
      congrArg Temporal.Formula.allPast (Temporal.Formula.swapTemporal_involution φ)
    let d_allPast : Temporal.DerivationTree Temporal.FrameClass.Base []
        (Temporal.Formula.allPast φ) :=
      h_eq ▸ d_final
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) [] _
      (Temporal.Axiom.allPast_to_classic φ) trivial
    exact ⟨Temporal.DerivationTree.modus_ponens [] _ _ d_bridge d_allPast⟩

/-! ## Temporal Axiom Instances (22) -/

instance :
    HasAxiomSerialFuture Temporal.HilbertBX (F := Temporal.Formula Atom) where
  serialFuture := ⟨Temporal.DerivationTree.axiom [] _ Temporal.Axiom.serial_future trivial⟩

instance :
    HasAxiomSerialPast Temporal.HilbertBX (F := Temporal.Formula Atom) where
  serialPast := ⟨Temporal.DerivationTree.axiom [] _ Temporal.Axiom.serial_past trivial⟩

instance :
    HasAxiomLeftMonoUntilG Temporal.HilbertBX (F := Temporal.Formula Atom) where
  -- Foundation expects: ⊢ ¬F¬(φ→ψ) → (φ U χ → ψ U χ)   (old G encoding)
  -- We have axiom: ⊢ allFuture (φ→ψ) → (φ U χ → ψ U χ)   (new G constructor)
  -- Bridge via classic_to_allFuture: ⊢ ¬F¬(φ→ψ) → allFuture (φ→ψ), then chain via hypSyl.
  leftMonoUntilG := by
    intro φ ψ χ
    -- ⊢ ¬F¬(φ→ψ) → allFuture (φ→ψ)
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.classic_to_allFuture (φ.imp ψ)) trivial
    -- ⊢ allFuture (φ→ψ) → (φ U χ → ψ U χ)
    let d_ax := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.left_mono_until_G φ ψ χ) trivial
    exact ⟨hypSyl d_bridge d_ax⟩

instance :
    HasAxiomLeftMonoSinceH Temporal.HilbertBX (F := Temporal.Formula Atom) where
  leftMonoSinceH := by
    intro φ ψ χ
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.classic_to_allPast (φ.imp ψ)) trivial
    let d_ax := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.left_mono_since_H φ ψ χ) trivial
    exact ⟨hypSyl d_bridge d_ax⟩

instance :
    HasAxiomRightMonoUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  rightMonoUntil := by
    intro φ ψ χ
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.classic_to_allFuture (φ.imp ψ)) trivial
    let d_ax := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.right_mono_until φ ψ χ) trivial
    exact ⟨hypSyl d_bridge d_ax⟩

instance :
    HasAxiomRightMonoSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  rightMonoSince := by
    intro φ ψ χ
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.classic_to_allPast (φ.imp ψ)) trivial
    let d_ax := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.right_mono_since φ ψ χ) trivial
    exact ⟨hypSyl d_bridge d_ax⟩

instance :
    HasAxiomConnectFuture Temporal.HilbertBX (F := Temporal.Formula Atom) where
  -- Foundation expects: ⊢ φ → ¬F¬(Pφ)   where Pφ = somePast φ
  -- We have axiom: ⊢ φ → allFuture (somePast φ)
  -- Bridge via allFuture_to_classic: ⊢ allFuture (somePast φ) → ¬F¬(somePast φ)
  connectFuture := by
    intro φ
    let d_ax := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.connect_future φ) trivial
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.allFuture_to_classic φ.somePast) trivial
    exact ⟨hypSyl d_ax d_bridge⟩

instance :
    HasAxiomConnectPast Temporal.HilbertBX (F := Temporal.Formula Atom) where
  -- Foundation expects: ⊢ φ → ¬P¬(Fφ)
  -- We have axiom: ⊢ φ → allPast (someFuture φ)
  -- Bridge via allPast_to_classic
  connectPast := by
    intro φ
    let d_ax := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.connect_past φ) trivial
    let d_bridge := Temporal.DerivationTree.axiom (fc := Temporal.FrameClass.Base) []
      _ (Temporal.Axiom.allPast_to_classic φ.someFuture) trivial
    exact ⟨hypSyl d_ax d_bridge⟩

instance :
    HasAxiomEnrichmentUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  enrichmentUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.enrichment_until _ _ _) trivial⟩

instance :
    HasAxiomEnrichmentSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  enrichmentSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.enrichment_since _ _ _) trivial⟩

instance :
    HasAxiomSelfAccumUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  selfAccumUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.self_accum_until _ _) trivial⟩

instance :
    HasAxiomSelfAccumSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  selfAccumSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.self_accum_since _ _) trivial⟩

instance :
    HasAxiomAbsorbUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  absorbUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.absorb_until _ _) trivial⟩

instance :
    HasAxiomAbsorbSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  absorbSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.absorb_since _ _) trivial⟩

instance :
    HasAxiomLinearUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  linearUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.linear_until _ _ _ _) trivial⟩

instance :
    HasAxiomLinearSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  linearSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.linear_since _ _ _ _) trivial⟩

instance :
    HasAxiomUntilF Temporal.HilbertBX (F := Temporal.Formula Atom) where
  untilF :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.until_F _ _) trivial⟩

instance :
    HasAxiomSinceP Temporal.HilbertBX (F := Temporal.Formula Atom) where
  sinceP :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.since_P _ _) trivial⟩

instance :
    HasAxiomTempLinearity Temporal.HilbertBX (F := Temporal.Formula Atom) where
  tempLinearity :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.temp_linearity _ _) trivial⟩

instance :
    HasAxiomTempLinearityPast Temporal.HilbertBX (F := Temporal.Formula Atom) where
  tempLinearityPast :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.temp_linearity_past _ _) trivial⟩

instance :
    HasAxiomFUntilEquiv Temporal.HilbertBX (F := Temporal.Formula Atom) where
  fUntilEquiv :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.F_until_equiv _) trivial⟩

instance :
    HasAxiomPSinceEquiv Temporal.HilbertBX (F := Temporal.Formula Atom) where
  pSinceEquiv :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.P_since_equiv _) trivial⟩

/-! ## TemporalBXHilbert Instance -/

/-- The bundled `TemporalBXHilbert` instance for `Temporal.HilbertBX`. -/
instance :
    TemporalBXHilbert Temporal.HilbertBX (F := Temporal.Formula Atom) where

end TempInstances

end Cslib.Logic.Temporal
