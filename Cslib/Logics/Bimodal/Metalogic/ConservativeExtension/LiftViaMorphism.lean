/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.ProofSystemMorphism
public import Cslib.Logics.Bimodal.ProofSystem.Derivation

/-! # Bimodal `DerivationTree.lift` via Proof-System Morphisms

This module exhibits Bimodal's frame-class lifting combinator `DerivationTree.lift` as a
corollary of the generic functor `Cslib.Logic.Metalogic.Deriv.map` applied to a `ProofSigHom`
built from the frame-class ordering hypothesis `h_le : fc₁ ≤ fc₂`, the "Bimodal frame-class"
instance of the morphism-of-proof-systems abstraction.

## Design

Bimodal's `DerivationTree fc Γ φ` is parameterized by a frame class `fc : FrameClass`.
The axiom family `Ax φ := { a : Axiom φ // a.minFrameClass ≤ fc }` is already `Type`-valued,
matching the `ProofSig.Ax : F → Type` contract exactly — no lifting wrapper (like `PLift`) is
needed. The three closure constructors (necessitation, temporal_necessitation, temporal_duality)
are modeled as `bimodalSig.closures = [Formula.box, Formula.allFuture, Formula.swapTemporal]`.

The frame-class morphism has `g = id`, and the axiom-family map uses `le_trans` monotonicity:
`axMap φ ⟨a, hfc⟩ = ⟨a, le_trans hfc h_le⟩`. The closure map is the identity
(`clMap m hm = ⟨m, hm, fun _ => rfl⟩`) because `bimodalSig.closures` does not depend on `fc`.

## Key Results

- `toDeriv`: forward map `DerivationTree fc Γ φ → Metalogic.Deriv (bimodalSig fc) Γ φ`.
- `bimodalHom h_le`: the `ProofSigHom (bimodalSig fc₁) (bimodalSig fc₂)` induced by
  `h_le : fc₁ ≤ fc₂`.
- `toDeriv_lift h_le d`: `toDeriv (DerivationTree.lift h_le d)` is heterogeneously equal
  to `Metalogic.Deriv.map (bimodalHom h_le) (toDeriv d)`, exhibiting `DerivationTree.lift`
  as a `Deriv.map` corollary.

## Obstruction for ofDeriv / bimodalEquiv

The backward map `ofDeriv` requires case-splitting on `hm : m ∈ [Formula.box, Formula.allFuture,
Formula.swapTemporal]` (a `Prop`-valued `List.Mem`) to produce a `Type u`-valued `DerivationTree`.
This is large elimination of a non-singleton `Prop` inductive (`List.Mem` has constructors
`head` and `tail`) to `Type u`, which Lean 4's kernel forbids. A workaround via
`Classical.choice` yields a noncomputable definition but makes the round-trip
`ofDeriv ∘ toDeriv = id` unprovable (classical choice is opaque). The full constructor-
preserving equivalence (`bimodalEquiv`) thus awaits a revised `ProofSig` where `closures` uses
a `Type`-valued indexing (e.g., `Fin n → F → F`) instead of `List (F → F)`.

## Non-Invasive Overlay

This module does NOT modify `Derivation.lean`, `Axioms.lean`, or any downstream Bimodal file.
`DerivationTree.lift` is unchanged. -/

@[expose] public section

namespace Cslib.Logic.Bimodal

open Cslib.Logic.Metalogic

variable {Atom : Type}

/-! ## Proof-System Signature for Bimodal -/

/-- The proof-system signature for bimodal logic at frame class `fc`.

- `Ax φ := { a : Axiom φ // a.minFrameClass ≤ fc }` is the `Type`-valued subtype of axiom
  instances admissible at `fc`. The gate `a.minFrameClass ≤ fc` corresponds exactly to the
  `h_fc : h.minFrameClass ≤ fc` condition in the `DerivationTree.axiom` constructor.
- `closures := [Formula.box, Formula.allFuture, Formula.swapTemporal]` models the three
  empty-context closure rules (necessitation, temporal_necessitation, temporal_duality).
  Note: the `closures` list does NOT depend on `fc`, enabling the identity `clMap` in
  `bimodalHom`. -/
def bimodalSig (fc : FrameClass) : ProofSig (Formula Atom) where
  Ax φ := { a : Axiom φ // a.minFrameClass ≤ fc }
  closures := [Formula.box, Formula.allFuture, Formula.swapTemporal]

/-! ## Constructor-Preserving Forward Map -/

/-- Forward direction: every `DerivationTree fc Γ φ` maps to a
`Metalogic.Deriv (bimodalSig fc) Γ φ`.

Constructor correspondence:
- `axiom h hfc` maps to `ax ⟨h, hfc⟩` (packing into the gate subtype);
- `assumption h` maps to `assum h`;
- `modus_ponens` maps to `mp`;
- `necessitation phi d` maps to `close Formula.box _ phi (toDeriv d)`;
- `temporal_necessitation phi d` maps to `close Formula.allFuture _ phi (toDeriv d)`;
- `temporal_duality phi d` maps to `close Formula.swapTemporal _ phi (toDeriv d)`;
- `weakening` maps to `weak`. -/
def toDeriv {fc : FrameClass} {Γ : Context Atom} {φ : Formula Atom} :
    DerivationTree fc Γ φ → Metalogic.Deriv (bimodalSig fc) Γ φ
  | .axiom Γ φ h hfc => .ax Γ φ ⟨h, hfc⟩
  | .assumption Γ φ h => .assum Γ φ h
  | .modus_ponens Γ φ ψ d₁ d₂ => .mp Γ φ ψ (toDeriv d₁) (toDeriv d₂)
  | .necessitation φ d =>
      .close Formula.box (by simp [bimodalSig]) φ (toDeriv d)
  | .temporal_necessitation φ d =>
      .close Formula.allFuture (by simp [bimodalSig]) φ (toDeriv d)
  | .temporal_duality φ d =>
      .close Formula.swapTemporal (by simp [bimodalSig]) φ (toDeriv d)
  | .weakening Γ Δ φ d h => .weak Γ Δ φ (toDeriv d) h

/-! ## Proof-System Morphism from Frame-Class Ordering -/

/-- The proof-system morphism induced by a frame-class ordering `h_le : fc₁ ≤ fc₂`.

- `g := id`: the formula map is the identity (frame classes do not affect formula syntax);
- `g_imp := fun _ _ => rfl`: `id (φ → ψ) = (id φ) → (id ψ)` holds definitionally;
- `axMap φ ⟨a, hfc⟩ := ⟨a, le_trans hfc h_le⟩`: the monotone reindexing of axiom
  instances along `h_le` (if `a.minFrameClass ≤ fc₁` and `fc₁ ≤ fc₂`, then
  `a.minFrameClass ≤ fc₂`);
- `clMap m hm := ⟨m, hm, fun _ => rfl⟩`: the identity closure map. This works because
  `bimodalSig.closures` does not depend on `fc`, so `hm : m ∈ (bimodalSig fc₁).closures`
  and `hm : m ∈ (bimodalSig fc₂).closures` are proofs of definitionally equal propositions. -/
def bimodalHom {fc₁ fc₂ : FrameClass} (h_le : fc₁ ≤ fc₂) :
    ProofSigHom (bimodalSig (Atom := Atom) fc₁) (bimodalSig (Atom := Atom) fc₂) where
  g := id
  g_imp := fun _ _ => rfl
  axMap := fun _ ⟨a, hfc⟩ => ⟨a, le_trans hfc h_le⟩
  clMap := fun m hm => ⟨m, hm, fun _ => rfl⟩

/-! ## Corollary: DerivationTree.lift Factors Through Deriv.map -/

/-- **Intertwining**: `toDeriv` intertwines `DerivationTree.lift h_le` with the functorial
action `Metalogic.Deriv.map (bimodalHom h_le)`.

The HEq (rather than Eq) arises because `Metalogic.Deriv.map H` produces a derivation with
context `Γ.map H.g = Γ.map id`, equal to `Γ` propositionally (by `List.map_id`) but not
definitionally. The two sides have types:
- LHS: `Metalogic.Deriv (bimodalSig fc₂) Γ φ`
- RHS: `Metalogic.Deriv (bimodalSig fc₂) (Γ.map id) φ`

For the three closure cases (necessitation, temporal_necessitation, temporal_duality), the
context is `[]` on both sides, so `[].map id = []` definitionally, and HEq reduces to Eq.
The membership proof difference between LHS and RHS closure nodes is resolved by proof
irrelevance (`proof_irrel_heq`). -/
theorem toDeriv_lift {fc₁ fc₂ : FrameClass} (h_le : fc₁ ≤ fc₂)
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree fc₁ Γ φ) :
    HEq (toDeriv (DerivationTree.lift h_le d))
        (Metalogic.Deriv.map (bimodalHom h_le) (toDeriv d)) := by
  induction d with
  | «axiom» Γ φ h hfc =>
    simp only [DerivationTree.lift, toDeriv, Metalogic.Deriv.map, bimodalHom, id_eq]
    congr 1; exact (List.map_id Γ).symm
  | assumption Γ φ h =>
    simp only [DerivationTree.lift, toDeriv, Metalogic.Deriv.map, bimodalHom, id_eq]
    congr 1 <;> first | rw [List.map_id] | exact proof_irrel_heq _ _
  | modus_ponens Γ φ ψ d₁ d₂ ih₁ ih₂ =>
    simp only [DerivationTree.lift, toDeriv, Metalogic.Deriv.map, bimodalHom, id_eq]
    congr 1; rw [List.map_id]
  | necessitation φ d ih =>
    simp only [DerivationTree.lift, toDeriv, Metalogic.Deriv.map, bimodalHom, id_eq]
    congr 1
    first
      | exact proof_irrel_heq _ _
      | exact eq_of_heq ih
  | temporal_necessitation φ d ih =>
    simp only [DerivationTree.lift, toDeriv, Metalogic.Deriv.map, bimodalHom, id_eq]
    congr 1
    first
      | exact proof_irrel_heq _ _
      | exact eq_of_heq ih
  | temporal_duality φ d ih =>
    simp only [DerivationTree.lift, toDeriv, Metalogic.Deriv.map, bimodalHom, id_eq]
    congr 1
    first
      | exact proof_irrel_heq _ _
      | exact eq_of_heq ih
  | weakening Γ Δ φ d h ih =>
    simp only [DerivationTree.lift, toDeriv, Metalogic.Deriv.map, bimodalHom, id_eq]
    congr 1 <;>
      first
        | rw [List.map_id]
        | exact eq_of_heq ih
        | exact proof_irrel_heq _ _

end Cslib.Logic.Bimodal

end
