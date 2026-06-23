/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DerivationTree

/-! # Generic Derivation Lifting for Modal Systems

This module provides the generic `liftDerivation` lemma and its corollary
`Derivable_mono`, which together establish that any derivation in a weaker
modal system can be lifted to a derivation in a stronger system, provided
the stronger system's axiom predicate subsumes the weaker one.

## Key Results

- `liftDerivation`: Structural induction lifting `DerivationTree Axioms1 Γ φ`
  to `DerivationTree Axioms2 Γ φ` via an axiom subsumption callback.
- `Derivable_mono`: Corollary lifting `Derivable Axioms1 φ` to `Derivable Axioms2 φ`.

## Usage

To prove that K-derivable formulas are T-derivable, apply `Derivable_mono` with
`KAxiom_implies_TAxiom` (from `AxiomSubsumption.lean`) as the callback.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-- Generic derivation lifting: given an axiom subsumption callback
`h_sub : ∀ φ, Axioms1 φ → Axioms2 φ`, any derivation tree in `Axioms1`
can be lifted to a derivation tree in `Axioms2`, preserving the context and
conclusion.

The proof is by structural induction on the derivation tree:
- `ax`: Apply `h_sub` to convert the axiom instance from `Axioms1` to `Axioms2`.
- `assumption`: Pass through unchanged.
- `modus_ponens`: Recurse on both subderivations.
- `necessitation`: Recurse on the single subderivation.
- `weakening`: Recurse on the subderivation, preserving the context inclusion proof. -/
def liftDerivation
    {Axioms1 Axioms2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, Axioms1 φ → Axioms2 φ)
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms1 Γ φ) :
    DerivationTree Axioms2 Γ φ :=
  match d with
  | .ax Γ φ h => .ax Γ φ (h_sub φ h)
  | .assumption Γ φ h => .assumption Γ φ h
  | .modus_ponens Γ φ ψ d₁ d₂ =>
      .modus_ponens Γ φ ψ (liftDerivation h_sub d₁) (liftDerivation h_sub d₂)
  | .necessitation φ d => .necessitation φ (liftDerivation h_sub d)
  | .weakening Γ Δ φ d h => .weakening Γ Δ φ (liftDerivation h_sub d) h

/-- Derivability monotonicity: if `Axioms1` is subsumed by `Axioms2` (every `Axioms1`
instance is an `Axioms2` instance), then every `Axioms1`-derivable formula is also
`Axioms2`-derivable.

This is the `Derivable`-level corollary of `liftDerivation`. -/
lemma Derivable_mono
    {Axioms1 Axioms2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, Axioms1 φ → Axioms2 φ)
    {φ : Proposition Atom}
    (h : Derivable Axioms1 φ) :
    Derivable Axioms2 φ := by
  obtain ⟨d⟩ := h
  exact ⟨liftDerivation h_sub d⟩

end Cslib.Logic.Modal

end
