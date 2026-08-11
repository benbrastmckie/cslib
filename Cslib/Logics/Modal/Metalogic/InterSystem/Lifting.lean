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

This module also provides the more general `Derivable_of_axiom_derivable` lift, used when
`Axioms1`-axiom instances are not literal `Axioms2`-axiom instances (no syntactic rename),
but each is nonetheless *derivable* in `Axioms2` (e.g. the intuitionistic Fischer-Servi
diamond schemata vs. classical `K`'s dual-diamond `diamondDuality` schemata). This is
strictly more general than `Derivable_mono`: an axiom→axiom callback is a special case of an
axiom→derivation callback (`Axioms1 φ → Axioms2 φ → Derivable Axioms2 φ` via `⟨.ax _ _ h⟩`).

## Key Results

- `liftDerivation`: Structural induction lifting `DerivationTree Axioms1 Γ φ`
  to `DerivationTree Axioms2 Γ φ` via an axiom subsumption callback.
- `Derivable_mono`: Corollary lifting `Derivable Axioms1 φ` to `Derivable Axioms2 φ`.
- `Derivable_of_axiom_derivable`: Generalized lift from an axiom→*derivation* callback
  `∀ φ, Axioms1 φ → Derivable Axioms2 φ`, i.e. each `Axioms1` axiom instance need only be
  *derivable* (not literally an axiom instance) in `Axioms2`.

## Usage

To prove that K-derivable formulas are T-derivable, apply `Derivable_mono` with
`KAxiom_implies_TAxiom` (from `AxiomSubsumption.lean`) as the callback.

To bridge two systems whose axioms are not syntactic renames of each other (e.g.
intuitionistic `IK` into classical `K`, `IntToClassical.lean`), apply
`Derivable_of_axiom_derivable` with a callback proving each `IKModalAxiom` instance
`Derivable`-in-`KAxiom` (rather than literally a `KAxiom` instance).
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

/-- Auxiliary structural-induction lemma underlying `Derivable_of_axiom_derivable`, stated
at arbitrary context `Γ` (needed because `necessitation`/`weakening` subderivations range
over arbitrary contexts, not just `[]`).

The proof recurses on the `Axioms1`-derivation tree:
- `ax`: discharge via the supplied callback `h_sub`, then weaken the resulting
  `Axioms2`-derivation from the empty context up to `Γ` (`DerivationTree.weakening`, using
  `∀ x ∈ [], x ∈ Γ` vacuously).
- `assumption`/`modus_ponens`/`necessitation`/`weakening`: closure of
  `Nonempty (DerivationTree Axioms2 _ _)` under the corresponding `DerivationTree`
  constructor, recursing on the immediate subderivation(s). -/
theorem derivable_of_axiom_derivable_aux
    {Axioms1 Axioms2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, Axioms1 φ → Derivable Axioms2 φ)
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms1 Γ φ) :
    Nonempty (DerivationTree Axioms2 Γ φ) := by
  induction d with
  | ax Γ φ h =>
      obtain ⟨d2⟩ := h_sub φ h
      exact ⟨d2.weakening [] Γ φ (by simp)⟩
  | assumption Γ φ h => exact ⟨.assumption Γ φ h⟩
  | modus_ponens Γ φ ψ _ _ ih₁ ih₂ =>
      obtain ⟨e₁⟩ := ih₁
      obtain ⟨e₂⟩ := ih₂
      exact ⟨.modus_ponens Γ φ ψ e₁ e₂⟩
  | necessitation φ _ ih =>
      obtain ⟨e⟩ := ih
      exact ⟨.necessitation φ e⟩
  | weakening Γ Δ φ _ h ih =>
      obtain ⟨e⟩ := ih
      exact ⟨.weakening Γ Δ φ e h⟩

/-- **Generalized axiom→derivation lift**: given a callback `h_sub` showing every `Axioms1`
axiom instance is *derivable* (not necessarily a literal axiom instance) in `Axioms2`, every
`Axioms1`-derivable formula is `Axioms2`-derivable.

Strictly more general than `Derivable_mono`, which is the special case where `h_sub` produces
a literal `Axioms2` axiom instance rather than an arbitrary derivation. Used for bridges where
the two systems' axioms are not syntactic renames of each other (`IntToClassical.lean`:
intuitionistic Fischer-Servi diamond schemata vs. classical `K`'s dual-diamond `diamondDuality`
schemata). -/
theorem Derivable_of_axiom_derivable
    {Axioms1 Axioms2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, Axioms1 φ → Derivable Axioms2 φ)
    {φ : Proposition Atom}
    (h : Derivable Axioms1 φ) :
    Derivable Axioms2 φ := by
  obtain ⟨d⟩ := h
  exact derivable_of_axiom_derivable_aux h_sub d

end Cslib.Logic.Modal

end
