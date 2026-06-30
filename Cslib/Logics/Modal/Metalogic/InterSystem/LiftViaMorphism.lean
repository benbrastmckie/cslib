/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.ProofSystemMorphism
public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting

/-! # Modal Derivation Lifting via Proof-System Morphisms

This module exhibits the modal-logic axiom-monotonicity combinator `liftDerivation`
as a corollary of the generic functor `Cslib.Logic.Metalogic.Deriv.map` applied to a
`ProofSigHom` built from the subsumption hypothesis. This is Phase 3 of the
morphism-of-proof-systems abstraction (task 419).

## Design

Modal has one closure operator (necessitation `□`), so `modalSig.closures = [Proposition.box]`.
The `necessitation` constructor of `DerivationTree` corresponds to `close Proposition.box`
in `Metalogic.Deriv`. The axiom family lifts `Axioms : Proposition Atom → Prop` to a
`Type`-valued family `fun φ => PLift (Axioms φ)`, matching the `ProofSig.Ax : F → Type`
contract.

**Disambiguation**: `Cslib.Logic.Modal.Deriv` is the `Prop`-level derivability wrapper
(from `DerivationTree.lean`). `Cslib.Logic.Metalogic.Deriv` is the `Type`-level
free-derivation inductive (from `ProofSystemMorphism.lean`). This file uses the qualified
form `Metalogic.Deriv` throughout to avoid the name collision.

## Key Results

- `modalEquiv Axioms Γ φ`: constructor-preserving equivalence
  `DerivationTree Axioms Γ φ ≃ Metalogic.Deriv (modalSig Axioms) Γ φ`.
- `toDeriv_liftDerivation`: `toDeriv (liftDerivation h_sub d)` is heterogeneously equal
  to `Metalogic.Deriv.map (modalHom h_sub) (toDeriv d)`, exhibiting `liftDerivation` as
  a `Deriv.map` corollary.
- `Derivable_mono_via_morphism`: `Derivable_mono` factors through `Metalogic.Deriv.map`
  via the empty-context specialisation.

## Non-Invasive Overlay

This module does NOT modify `Lifting.lean` or any downstream proof. `liftDerivation` and
`Derivable_mono` are unchanged. -/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic.Metalogic

universe u

variable {Atom : Type u}

/-! ## Proof-System Signature for Modal Logic -/

/-- The proof-system signature for normal modal logic with axiom predicate `Axioms`.

`Ax φ := PLift (Axioms φ)` lifts the `Prop`-valued predicate to a `Type`-valued axiom
family, matching `ProofSig.Ax : F → Type`. Modal has one closure operator (necessitation,
`Proposition.box`), so `closures = [Proposition.box]`. -/
def modalSig (Axioms : Proposition Atom → Prop) : ProofSig (Proposition Atom) where
  Ax φ := PLift (Axioms φ)
  closures := [Proposition.box]

/-! ## Constructor-Preserving Equivalence -/

/-- Forward direction: every `Modal.DerivationTree` maps to a `Metalogic.Deriv (modalSig -)`.

Each constructor maps to the corresponding `Metalogic.Deriv` constructor:
- `ax h` ↦ `ax ⟨h⟩` (wrapping via `PLift.up`);
- `assumption h` ↦ `assum h`;
- `modus_ponens` ↦ `mp`;
- `necessitation φ d` ↦ `close Proposition.box mem φ (toDeriv d)`;
- `weakening` ↦ `weak`. -/
def toDeriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom} :
    DerivationTree Axioms Γ φ → Metalogic.Deriv (modalSig Axioms) Γ φ
  | .ax Γ φ h => .ax Γ φ ⟨h⟩
  | .assumption Γ φ h => .assum Γ φ h
  | .modus_ponens Γ φ ψ d₁ d₂ => .mp Γ φ ψ (toDeriv d₁) (toDeriv d₂)
  | .necessitation φ d =>
      .close Proposition.box (List.mem_singleton.mpr rfl) φ (toDeriv d)
  | .weakening Γ Δ φ d h => .weak Γ Δ φ (toDeriv d) h

/-- Backward direction: every `Metalogic.Deriv (modalSig -)` maps to a `Modal.DerivationTree`.

The `close m hm` constructor requires `m = Proposition.box` (since
`modalSig.closures = [Proposition.box]`), which `List.mem_singleton.mp hm` provides;
after substituting `m := Proposition.box` the necessitation rule applies. -/
def ofDeriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom} :
    Metalogic.Deriv (modalSig Axioms) Γ φ → DerivationTree Axioms Γ φ
  | .ax _ _ h => .ax _ _ h.down
  | .assum _ _ h => .assumption _ _ h
  | .mp _ φ ψ d₁ d₂ => .modus_ponens _ φ ψ (ofDeriv d₁) (ofDeriv d₂)
  | .close m hm φ d => by
      rcases List.mem_singleton.mp hm with rfl
      exact .necessitation φ (ofDeriv d)
  | .weak _ _ _ d h => .weakening _ _ _ (ofDeriv d) h

/-- Left inverse: `ofDeriv ∘ toDeriv = id`. -/
theorem ofDeriv_toDeriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ) :
    ofDeriv (toDeriv d) = d := by
  induction d with
  | ax _ _ _ => rfl
  | assumption _ _ _ => rfl
  | modus_ponens _ _ _ _ _ ih₁ ih₂ => simp only [toDeriv, ofDeriv, ih₁, ih₂]
  | necessitation _ _ ih =>
      simp only [toDeriv, ofDeriv, ih]
  | weakening _ _ _ _ _ ih => simp only [toDeriv, ofDeriv, ih]

/-- Right inverse: `toDeriv ∘ ofDeriv = id`. -/
theorem toDeriv_ofDeriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (e : Metalogic.Deriv (modalSig Axioms) Γ φ) :
    toDeriv (ofDeriv e) = e := by
  induction e with
  | ax _ _ h => cases h; rfl
  | assum _ _ _ => rfl
  | mp _ _ _ _ _ ih₁ ih₂ => simp only [ofDeriv, toDeriv, ih₁, ih₂]
  | close m hm φ d ih =>
      rcases List.mem_singleton.mp hm with rfl
      simp only [ofDeriv, toDeriv, ih]
  | weak _ _ _ _ _ ih => simp only [ofDeriv, toDeriv, ih]

/-- The constructor-preserving equivalence between `Modal.DerivationTree Axioms Γ φ` and
`Metalogic.Deriv (modalSig Axioms) Γ φ`. -/
def modalEquiv (Axioms : Proposition Atom → Prop)
    (Γ : List (Proposition Atom)) (φ : Proposition Atom) :
    DerivationTree Axioms Γ φ ≃ Metalogic.Deriv (modalSig Axioms) Γ φ where
  toFun := toDeriv
  invFun := ofDeriv
  left_inv := ofDeriv_toDeriv
  right_inv := toDeriv_ofDeriv

/-! ## Proof-System Morphism from Axiom Subsumption -/

/-- The proof-system morphism induced by an axiom subsumption `h_sub`.

- `g = id`: the formula map is identity;
- `g_imp φ ψ = rfl`: `id (φ → ψ) = (id φ) → (id ψ)` holds definitionally;
- `axMap φ h = ⟨h_sub φ h.down⟩`: lifts `h_sub` through `PLift`;
- `clMap m hm = ⟨m, hm, fun _ => rfl⟩`: box maps to box (same axiom set), and
  `id (box φ) = box (id φ)` is `rfl`. -/
def modalHom {A1 A2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, A1 φ → A2 φ) :
    ProofSigHom (modalSig A1) (modalSig A2) where
  g := id
  g_imp := fun _ _ => rfl
  axMap := fun φ h => ⟨h_sub φ h.down⟩
  clMap := fun m hm => ⟨m, hm, fun _ => rfl⟩

/-! ## Corollary: liftDerivation Factors Through Deriv.map -/

/-- **Intertwining**: `toDeriv` intertwines `liftDerivation h_sub` with the functorial
action `Metalogic.Deriv.map (modalHom h_sub)`.

The `HEq` arises because `Metalogic.Deriv.map H` produces a derivation with context
`Γ.map H.g = Γ.map id`, propositionally equal to `Γ` by `List.map_id` but not
definitionally. The two sides have types:
- LHS: `Metalogic.Deriv (modalSig A2) Γ φ`
- RHS: `Metalogic.Deriv (modalSig A2) (Γ.map id) φ`

This matches the heterogeneous style of `Metalogic.Deriv.map_id` and
`Metalogic.Deriv.map_comp`. -/
theorem toDeriv_liftDerivation
    {A1 A2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, A1 φ → A2 φ)
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree A1 Γ φ) :
    HEq (toDeriv (liftDerivation h_sub d))
        (Metalogic.Deriv.map (modalHom h_sub) (toDeriv d)) := by
  induction d with
  | ax Γ φ h =>
    simp only [liftDerivation, toDeriv, Metalogic.Deriv.map, modalHom, modalSig, id_eq]
    congr 1; exact (List.map_id Γ).symm
  | assumption Γ φ h =>
    simp only [liftDerivation, toDeriv, Metalogic.Deriv.map, modalHom, id_eq]
    congr 1 <;> first | rw [List.map_id] | exact proof_irrel_heq _ _
  | modus_ponens Γ φ ψ _ _ _ _ =>
    simp only [liftDerivation, toDeriv, Metalogic.Deriv.map, modalHom, id_eq]
    congr 1; rw [List.map_id]
  | necessitation φ d ih =>
    simp only [liftDerivation, toDeriv, Metalogic.Deriv.map, modalHom, id_eq]
    -- Both sides: `close Proposition.box _ φ _`; context is `[]`; `[].map id = []` definitionally.
    -- Subderivations related by `ih`.
    congr 1
    exact eq_of_heq ih
  | weakening Γ Δ φ _ _ _ =>
    simp only [liftDerivation, toDeriv, Metalogic.Deriv.map, modalHom, id_eq]
    congr 1 <;>
      first
        | rw [List.map_id]
        | exact eq_of_heq (by assumption)
        | exact proof_irrel_heq _ _

/-! ## Corollary: Derivable_mono Factors Through Deriv.map -/

/-- **`Derivable_mono` via morphism**: axiom-monotonicity for `Derivable` factors
through `Metalogic.Deriv.map (modalHom h_sub)`.

For the empty context `Γ = []`, `[].map id = []` definitionally, so `Deriv.map`
gives exactly `Metalogic.Deriv (modalSig A2) [] φ`, and `ofDeriv` produces
`DerivationTree A2 [] φ` without any reindexing cast. -/
theorem Derivable_mono_via_morphism
    {A1 A2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, A1 φ → A2 φ)
    {φ : Proposition Atom}
    (h : Derivable A1 φ) : Derivable A2 φ :=
  let ⟨d⟩ := h
  ⟨ofDeriv (Metalogic.Deriv.map (modalHom h_sub) (toDeriv d))⟩

end Cslib.Logic.Modal

end
