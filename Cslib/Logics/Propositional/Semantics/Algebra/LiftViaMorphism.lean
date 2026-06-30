/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.ProofSystemMorphism
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative

/-! # PL Derivation Lifting via Proof-System Morphisms

This module exhibits the propositional-logic axiom-monotonicity combinator
`liftDerivationTree` as a corollary of the generic functor
`Cslib.Logic.Metalogic.Deriv.map` applied to a `ProofSigHom` built from the
subsumption hypothesis. This is the Phase 2 "PL pilot" of the morphism-of-proof-systems
abstraction (task 419).

## Design

PL has no closure operators (no necessitation), so `plSig.closures = []`. The
axiom family lifts `Axioms : PL.Proposition Atom → Prop` to a `Type`-valued family
`fun φ => PLift (Axioms φ)`, matching the `ProofSig.Ax : F → Type` contract.

**Disambiguation note**: `Cslib.Logic.PL.Deriv` is the `Prop`-level derivability
wrapper (from `Derivation.lean`). `Cslib.Logic.Metalogic.Deriv` is the `Type`-level
free-derivation inductive (from `ProofSystemMorphism.lean`). This file uses the
qualified form `Metalogic.Deriv` throughout to avoid the name collision.

## Key Results

- `plEquiv Axioms Γ φ`: constructor-preserving equivalence
  `DerivationTree Axioms Γ φ ≃ Metalogic.Deriv (plSig Axioms) Γ φ`.
- `toDeriv_liftDerivationTree_heq`: `toDeriv (liftDerivationTree h_sub d)` is
  heterogeneously equal to `Metalogic.Deriv.map (plHom h_sub) (toDeriv d)`,
  exhibiting `liftDerivationTree` as a `Deriv.map` corollary.
- `derivable_mono_via_morphism`: `derivable_mono` factors cleanly (no HEq) through
  `Metalogic.Deriv.map (plHom h_sub)` via the empty-context specialisation.

## Non-Invasive Overlay

This module does NOT modify `ConjImpConservative.lean` or any downstream proof.
`liftDerivationTree` and `derivable_mono` are unchanged. -/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Metalogic

universe u

variable {Atom : Type u}

/-! ## Proof-System Signature for PL -/

/-- The proof-system signature for propositional logic with axiom predicate `Axioms`.

`Ax φ := PLift (Axioms φ)` lifts the `Prop`-valued predicate to a `Type`-valued
axiom family, matching `ProofSig.Ax : F → Type`. PL has no closure operators, so
`closures = []`. -/
def plSig (Axioms : PL.Proposition Atom → Prop) : ProofSig (PL.Proposition Atom) where
  Ax φ := PLift (Axioms φ)
  closures := []

/-! ## Constructor-Preserving Equivalence -/

/-- Forward direction: every `PL.DerivationTree` maps to a `Metalogic.Deriv (plSig -)`.

Each constructor maps to the corresponding `Metalogic.Deriv` constructor:
- `ax h` maps to `ax ⟨h⟩` (wrapping via `PLift.up`);
- `assumption h` maps to `assum h`;
- `modus_ponens` maps to `mp` (`HasImp.imp = PL.Proposition.imp` definitionally);
- `weakening` maps to `weak` (`∀ x ∈ Γ, x ∈ Δ` and `Γ ⊆ Δ` are definitionally equal
  at the kernel level). -/
def toDeriv {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    DerivationTree Axioms Γ φ → Metalogic.Deriv (plSig Axioms) Γ φ
  | .ax Γ φ h => .ax Γ φ ⟨h⟩
  | .assumption Γ φ h => .assum Γ φ h
  | .modus_ponens Γ φ ψ d₁ d₂ => .mp Γ φ ψ (toDeriv d₁) (toDeriv d₂)
  | .weakening Γ Δ φ d h => .weak Γ Δ φ (toDeriv d) h

/-- Backward direction: every `Metalogic.Deriv (plSig -)` maps to a `PL.DerivationTree`.

The `close` constructor is vacuous since `(plSig Axioms).closures = []`; `False.elim`
eliminates the absurd membership `hm : m ∈ []`. -/
def ofDeriv {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    Metalogic.Deriv (plSig Axioms) Γ φ → DerivationTree Axioms Γ φ
  | .ax _ _ h => .ax _ _ h.down
  | .assum _ _ h => .assumption _ _ h
  | .mp _ φ ψ d₁ d₂ => .modus_ponens _ φ ψ (ofDeriv d₁) (ofDeriv d₂)
  | .close _ hm _ _ => False.elim (List.not_mem_nil hm)
  | .weak _ _ _ d h => .weakening _ _ _ (ofDeriv d) h

/-- Left inverse: `ofDeriv ∘ toDeriv = id`. -/
theorem ofDeriv_toDeriv {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ φ) :
    ofDeriv (toDeriv d) = d := by
  induction d with
  | ax _ _ _ => rfl
  | assumption _ _ _ => rfl
  | modus_ponens _ _ _ _ _ ih₁ ih₂ => simp only [toDeriv, ofDeriv, ih₁, ih₂]
  | weakening _ _ _ _ _ ih => simp only [toDeriv, ofDeriv, ih]

/-- Right inverse: `toDeriv ∘ ofDeriv = id`. -/
theorem toDeriv_ofDeriv {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (e : Metalogic.Deriv (plSig Axioms) Γ φ) :
    toDeriv (ofDeriv e) = e := by
  induction e with
  | ax _ _ h => cases h; rfl
  | assum _ _ _ => rfl
  | mp _ _ _ _ _ ih₁ ih₂ => simp only [ofDeriv, toDeriv, ih₁, ih₂]
  | close _ hm _ _ => exact absurd hm List.not_mem_nil
  | weak _ _ _ _ _ ih => simp only [ofDeriv, toDeriv, ih]

/-- The constructor-preserving equivalence between `PL.DerivationTree Axioms Γ φ` and
`Metalogic.Deriv (plSig Axioms) Γ φ`. -/
def plEquiv (Axioms : PL.Proposition Atom → Prop)
    (Γ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom) :
    DerivationTree Axioms Γ φ ≃ Metalogic.Deriv (plSig Axioms) Γ φ where
  toFun := toDeriv
  invFun := ofDeriv
  left_inv := ofDeriv_toDeriv
  right_inv := toDeriv_ofDeriv

/-! ## Proof-System Morphism from Axiom Subsumption -/

/-- The proof-system morphism induced by an axiom subsumption `h_sub`.

- `g = id`: the formula map is identity;
- `g_imp φ ψ = rfl`: `id (φ → ψ) = (id φ) → (id ψ)` holds definitionally;
- `axMap φ h = ⟨h_sub φ h.down⟩`: lifts `h_sub` through `PLift`;
- `clMap`: vacuous via `False.elim` since `(plSig _).closures = []`. -/
def plHom {A1 A2 : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, A1 ψ → A2 ψ) :
    ProofSigHom (plSig A1) (plSig A2) where
  g := id
  g_imp := fun _ _ => rfl
  axMap := fun φ h => ⟨h_sub φ h.down⟩
  clMap := fun _ hm => False.elim (List.not_mem_nil hm)

/-! ## Corollary: liftDerivationTree Factors Through Deriv.map -/

/-- **Intertwining**: `toDeriv` intertwines `liftDerivationTree h_sub` with the
functorial action `Metalogic.Deriv.map (plHom h_sub)`.

The HEq (rather than Eq) arises because `Metalogic.Deriv.map H` produces a derivation
with context `Γ.map H.g = Γ.map id`, equal to `Γ` propositionally (by `List.map_id`)
but not definitionally. The two sides have types:
- LHS: `Metalogic.Deriv (plSig A2) Γ φ`
- RHS: `Metalogic.Deriv (plSig A2) (Γ.map id) φ`

This matches the heterogeneous style of `Metalogic.Deriv.map_id` and
`Metalogic.Deriv.map_comp` in `ProofSystemMorphism.lean`. -/
theorem toDeriv_liftDerivationTree
    {A1 A2 : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, A1 ψ → A2 ψ)
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree A1 Γ φ) :
    HEq (toDeriv (liftDerivationTree h_sub d))
        (Metalogic.Deriv.map (plHom h_sub) (toDeriv d)) := by
  induction d with
  | ax Γ φ h =>
    simp only [liftDerivationTree, toDeriv, Metalogic.Deriv.map, plHom, plSig, id_eq]
    congr 1; exact (List.map_id Γ).symm
  | assumption Γ φ h =>
    simp only [liftDerivationTree, toDeriv, Metalogic.Deriv.map, plHom, id_eq]
    congr 1 <;> first | rw [List.map_id] | exact proof_irrel_heq _ _
  | modus_ponens Γ φ ψ d₁ d₂ ih₁ ih₂ =>
    simp only [liftDerivationTree, toDeriv, Metalogic.Deriv.map, plHom, id_eq]
    congr 1; rw [List.map_id]
  | weakening Γ Δ φ d h ih =>
    simp only [liftDerivationTree, toDeriv, Metalogic.Deriv.map, plHom, id_eq]
    congr 1 <;>
      first
        | rw [List.map_id]
        | exact eq_of_heq ih
        | exact proof_irrel_heq _ _

/-! ## Corollary: derivable_mono Factors Through Deriv.map -/

/-- **`derivable_mono` via morphism**: axiom-monotonicity for `Derivable` factors
through `Metalogic.Deriv.map (plHom h_sub)`.

For the empty context `Γ = []`, `[].map id = []` definitionally, so `Deriv.map`
gives exactly `Metalogic.Deriv (plSig A2) [] φ`, and `ofDeriv` produces
`DerivationTree A2 [] φ` without any reindexing cast. -/
theorem derivable_mono_via_morphism
    {A1 A2 : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, A1 ψ → A2 ψ)
    {φ : PL.Proposition Atom}
    (h : Derivable A1 φ) : Derivable A2 φ :=
  let ⟨d⟩ := h
  ⟨ofDeriv (Metalogic.Deriv.map (plHom h_sub) (toDeriv d))⟩

end Cslib.Logic.PL

end
