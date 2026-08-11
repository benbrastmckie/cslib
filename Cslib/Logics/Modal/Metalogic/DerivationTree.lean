/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Logic.Metalogic.Consistency
public import Cslib.Foundations.Logic.Axioms
public import Cslib.Logics.Modal.ProofSystem.SchemaUnion
public import Cslib.Logics.Modal.ProofSystem.SchemaTags

/-! # DerivationTree -- Parameterized Syntactic Proof System for Normal Modal Logics

This module defines a Hilbert-style syntactic proof system parameterized over an axiom
predicate `Axioms : Proposition Atom -> Prop`, enabling use for any normal modal logic
(K, T, D, S4, S5, etc.).

## Key Components

- `S5Axiom`: An inductive type enumerating the axiom schemata of S5 (4 propositional + 4 modal).
- `DerivationTree Axioms`: A parameterized inductive type with 5 constructors
  representing proof trees.
- `Deriv Axioms`: A `Prop`-level wrapper (`Nonempty (DerivationTree Axioms Gamma phi)`).
- `Derivable Axioms`: Derivability from the empty context.
- `modalDerivationSystem Axioms`: A `DerivationSystem (Proposition Atom)` instance.

## Design

`DerivationTree` is a `Type` (not a `Prop`) to enable pattern matching and computable
height functions. The `Deriv` wrapper provides the `Prop` version for the generic
`DerivationSystem`.

## References

* BimodalLogic/Theories/Bimodal/ProofSystem/Derivation.lean -- reference pattern
* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS API
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Axiom Schemata -/

/-- Axiom schemata for S5 modal logic, as the schema-union combinator over `s5Tags` (the
original inductive presentation has been retired in favor of this definitionally-transparent
`SchemaUnion s5Tags` form, preserving the name and public API via redefinition-in-place).

The 16 axiom-schema families covered by `s5Tags` (`kCore ∪ {modalT, modalFour, modalB}`;
S5 = T + 4 + B, carrying `modalB` and NOT `modalFive`):
- **Propositional** (4): `implyK` (weakening), `implyS` (distribution), `efq` (ex falso),
  `peirce` (double negation elimination / Peirce's law)
- **Modal** (4): `modalK` (K distribution), `modalT` (reflexivity), `modalFour` (transitivity),
  `modalB` (symmetry)
- **And/Or/Diamond-duality characterization** (8): `andI`, `andE1`, `andE2`, `orI1`,
  `orI2`, `orE`, `diamondDualityFwd`, `diamondDualityBack` -- these characterize the native `and`/`or`/
  `diamond` constructors introduced when `Modal.Proposition` moved off the Łukasiewicz encoding
  (see `Modal/Basic.lean` module docstring and the plan's "Justification for New Axiom Schemata"
  section).

Together with modus ponens and necessitation, these axioms characterize S5. -/
abbrev S5Axiom : Proposition Atom → Prop := SchemaUnion s5Tags

/-- Deprecated alias for `S5Axiom`, kept in place (no relocation) so existing call sites
continue to compile. -/
@[deprecated (since := "2026-07-23")] alias ModalAxiom := S5Axiom

/-! ## Derivation Trees -/

/-- Derivation tree for normal modal logics, parameterized over an axiom predicate.

`DerivationTree Axioms Gamma phi` represents a proof tree showing that formula `phi` is derivable
from context `Gamma` using axioms satisfying `Axioms`. Since it is a `Type` (not `Prop`), we can
pattern match on it for computable functions like `height`.

The 5 constructors are:
1. **axiom**: Any axiom instance (satisfying `Axioms`) is derivable from any context.
2. **assumption**: Any formula in the context is derivable.
3. **modus_ponens**: From `Gamma |- phi -> psi` and `Gamma |- phi`, derive `Gamma |- psi`.
4. **necessitation**: From `|- phi` (empty context), derive `|- box phi`.
5. **weakening**: From `Gamma |- phi` and `Gamma <= Delta`, derive `Delta |- phi`. -/
inductive DerivationTree (Axioms : Proposition Atom → Prop) :
    List (Proposition Atom) → Proposition Atom → Type _ where
  /-- Axiom rule: axiom schema instances are derivable from any context. -/
  | ax (Γ : List (Proposition Atom)) (φ : Proposition Atom)
      (h : Axioms φ) : DerivationTree Axioms Γ φ
  /-- Assumption rule: formulas in the context are derivable. -/
  | assumption (Γ : List (Proposition Atom)) (φ : Proposition Atom)
      (h : φ ∈ Γ) : DerivationTree Axioms Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  | modus_ponens (Γ : List (Proposition Atom)) (φ ψ : Proposition Atom)
      (d₁ : DerivationTree Axioms Γ (φ.imp ψ))
      (d₂ : DerivationTree Axioms Γ φ) : DerivationTree Axioms Γ ψ
  /-- Necessitation: from `⊢ φ` (empty context), derive `⊢ □φ`. -/
  | necessitation (φ : Proposition Atom)
      (d : DerivationTree Axioms [] φ) : DerivationTree Axioms [] (Proposition.box φ)
  /-- Weakening: from `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
  | weakening (Γ Δ : List (Proposition Atom)) (φ : Proposition Atom)
      (d : DerivationTree Axioms Γ φ)
      (h : ∀ x ∈ Γ, x ∈ Δ) : DerivationTree Axioms Δ φ

namespace DerivationTree

/-! ## Height Measure -/

/-- Computable height function for derivation trees.

Used for well-founded recursion in the deduction theorem proof. -/
def height : DerivationTree Axioms Γ φ → Nat
  | .ax _ _ _ => 0
  | .assumption _ _ _ => 0
  | .modus_ponens _ _ _ d₁ d₂ => 1 + max d₁.height d₂.height
  | .necessitation _ d => 1 + d.height
  | .weakening _ _ _ d _ => 1 + d.height

/-! ## Height Properties -/

/-- The left premise of a modus ponens node is strictly shorter than the conclusion node. -/
theorem height_modus_ponens_left {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (φ → ψ)) (d₂ : DerivationTree Axioms Γ φ) :
    d₁.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

/-- The right premise of a modus ponens node is strictly shorter than the conclusion node. -/
theorem height_modus_ponens_right {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (φ → ψ)) (d₂ : DerivationTree Axioms Γ φ) :
    d₂.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

/-- The underlying derivation of a weakening node is strictly shorter than the weakening node. -/
theorem height_weakening {Γ Δ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ) (h : ∀ x ∈ Γ, x ∈ Δ) :
    d.height < (weakening Γ Δ φ d h).height := by
  simp [height]

end DerivationTree

/-! ## Derivability (Prop wrapper) -/

/-- `Deriv Axioms Gamma phi` holds iff there exists a derivation tree deriving `phi` from `Gamma`
using axioms satisfying `Axioms`. This is the `Prop`-level wrapper used by the generic
`DerivationSystem`. -/
def Deriv (Axioms : Proposition Atom → Prop) (Γ : List (Proposition Atom))
    (φ : Proposition Atom) : Prop :=
  Nonempty (DerivationTree Axioms Γ φ)

/-- `Derivable Axioms phi` means `phi` is derivable from the empty context using axioms
satisfying `Axioms`. -/
def Derivable (Axioms : Proposition Atom → Prop) (φ : Proposition Atom) : Prop :=
  Deriv Axioms [] φ

/-! ## Basic Combinators -/

/-- Modus ponens lifts from derivation trees to `Deriv`. -/
theorem mp_deriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (h₁ : Deriv Axioms Γ (φ → ψ)) (h₂ : Deriv Axioms Γ φ) : Deriv Axioms Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

/-- Weakening lifts from derivation trees to `Deriv`: if `φ` is derivable from `Γ` and
`Γ ⊆ Δ` then `φ` is derivable from `Δ`. -/
theorem weakening_deriv {Axioms : Proposition Atom → Prop}
    {Γ Δ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv Axioms Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) : Deriv Axioms Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

/-- Any assumption in the context is derivable. -/
theorem assumption_deriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : φ ∈ Γ) : Deriv Axioms Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The modal derivation system parameterized over an axiom predicate, connecting the
modal proof system to the generic MCS framework from `Consistency.lean`.

This provides `Deriv`, `weakening`, `assumption`, and `mp` as required by
`DerivationSystem (Proposition Atom)`. -/
def modalDerivationSystem (Axioms : Proposition Atom → Prop) :
    Metalogic.DerivationSystem (Proposition Atom) where
  Deriv := Deriv Axioms
  weakening := fun hd hsub => weakening_deriv hd hsub
  assumption := fun hmem => assumption_deriv hmem
  mp := fun h₁ h₂ => mp_deriv h₁ h₂

/-! ## Functoriality Along Atom Relabeling

`DerivationTree`/`Deriv`/`Derivable` lift along an atom relabeling `f : Atom → Atom'`, provided
the target axiom predicate accepts the image of every source axiom instance under `f` (a schema
compatibility hypothesis `hax`, satisfied e.g. by a combined pair-axiom system's `left`/`right`
constructors relative to a base axiom system and `Proposition.map Sum.inl`/`Sum.inr`). This is
the reusable infrastructure a doubled-atom-space construction needs to transport derivability
facts into the doubled space (`Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`). -/

/-- **`DerivationTree` functoriality along an atom relabeling.** If every `Axioms`-instance maps
into an `Axioms'`-instance under `f` (`hax`), a derivation of `φ` from `Γ` (under `Axioms`) maps
to a derivation of `φ.map f` from `Γ.map (Proposition.map f)` (under `Axioms'`). A `def` (not a
`theorem`), since `DerivationTree` is a `Type`, not a `Prop`; defined by structural recursion on
the derivation tree: the `ax` case uses `hax`; `assumption`/`weakening` transport
`List.map`-membership facts; `modus_ponens`/`necessitation` need no rewriting at all, since
`Proposition.map`'s `imp`/`box` homomorphism lemmas (`Basic.lean:155-165`) are proved by `rfl`, so
the mapped formula shapes already coincide definitionally. -/
def DerivationTree.map {Atom' : Type*} {Axioms : Proposition Atom → Prop}
    {Axioms' : Proposition Atom' → Prop} (f : Atom → Atom')
    (hax : ∀ ψ, Axioms ψ → Axioms' (ψ.map f)) :
    ∀ {Γ : List (Proposition Atom)} {φ : Proposition Atom},
      DerivationTree Axioms Γ φ →
      DerivationTree Axioms' (Γ.map (Proposition.map f)) (φ.map f)
  | _, _, .ax Γ φ h => .ax _ _ (hax φ h)
  | _, _, .assumption Γ φ h => .assumption _ _ (List.mem_map_of_mem h)
  | _, _, .modus_ponens Γ ψ χ d₁ d₂ =>
      .modus_ponens _ (ψ.map f) (χ.map f)
        (DerivationTree.map f hax d₁) (DerivationTree.map f hax d₂)
  | _, _, .necessitation ψ d =>
      DerivationTree.necessitation (ψ.map f) (DerivationTree.map f hax d)
  | _, _, .weakening Γ' Δ φ d h =>
      .weakening _ _ _ (DerivationTree.map f hax d)
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact List.mem_map_of_mem (h y hy))

/-- **`Deriv` functoriality along an atom relabeling.** `Prop`-level wrapper of
`DerivationTree.map`. -/
theorem Deriv.map {Atom' : Type*} {Axioms : Proposition Atom → Prop}
    {Axioms' : Proposition Atom' → Prop} (f : Atom → Atom')
    (hax : ∀ ψ, Axioms ψ → Axioms' (ψ.map f))
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv Axioms Γ φ) : Deriv Axioms' (Γ.map (Proposition.map f)) (φ.map f) := by
  obtain ⟨d⟩ := h
  exact ⟨DerivationTree.map f hax d⟩

/-- **`Derivable` functoriality along an atom relabeling.** `Derivable` is `Deriv` at the empty
context; `[].map _ = []` closes the context-transport side condition for free, so this is a thin
specialization of `Deriv.map`. This is the concrete lemma the `CS5` box-backward pair
construction consumes: instantiated at `f := Sum.inl`/`Sum.inr` and a combined pair-axiom system
`Axioms'` whose `left`/`right` constructors witness `hax`, it gives
`Derivable Axioms φ → Derivable Axioms' (φ.map Sum.inl)` (and the `Sum.inr` analogue). -/
theorem Derivable.map {Atom' : Type*} {Axioms : Proposition Atom → Prop}
    {Axioms' : Proposition Atom' → Prop} (f : Atom → Atom')
    (hax : ∀ ψ, Axioms ψ → Axioms' (ψ.map f))
    {φ : Proposition Atom} (h : Derivable Axioms φ) : Derivable Axioms' (φ.map f) :=
  Deriv.map f hax h

end Cslib.Logic.Modal
