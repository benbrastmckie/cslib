/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive

/-! # Shared Definitions for Propositional Tableau Systems

This module provides shared definitions needed by the three propositional tableau
systems: classical, intuitionistic, and minimal.

## Main Definitions

- `propAndOf?`, `propOrOf?`, `propImpOf?`, `propNegOf?`: Decomposition functions
  for `Proposition Atom` connectives, needed by `applyPropRule`.
- `instHashableProposition`: `Hashable (Proposition Atom)` instance via hash mixing.
- `Proposition.complexity`: Imported from `Cslib.Logics.Propositional.Subformula`.
  Size measure for fuel computation in the expansion loop.

## Design

The decomposition functions use pattern matching directly on the `Proposition`
constructors. `neg` is a derived connective (`¬φ := φ → ⊥`), so `propNegOf?` matches
on `imp _ bot`. Nested `imp` matching is order-sensitive with `propImpOf?`.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Decomposition Functions -/

/-- Decompose `φ` as `φ₁ ∧ φ₂`; returns `some (φ₁, φ₂)` or `none`. -/
def propAndOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .and a b => some (a, b)
  | _ => none

/-- Decompose `φ` as `φ₁ ∨ φ₂`; returns `some (φ₁, φ₂)` or `none`. -/
def propOrOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .or a b => some (a, b)
  | _ => none

/-- Decompose `φ` as `φ₁ → φ₂`, excluding the case `φ₂ = ⊥` (which is negation);
returns `some (φ₁, φ₂)` or `none`.

For classical tableau, use `propImpOf?` for proper implication and `propNegOf?` for negation.
For intuitionistic tableau, treat `¬φ = φ → ⊥` as a regular implication. -/
def propImpOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .imp _ .bot => none  -- This is negation ¬a, handled by propNegOf?
  | .imp a b => some (a, b)
  | _ => none

/-- Decompose `φ` as `¬φ₁` (i.e., `φ₁ → ⊥`); returns `some φ₁` or `none`. -/
def propNegOf? (φ : Proposition Atom) : Option (Proposition Atom) :=
  match φ with
  | .imp a .bot => some a
  | _ => none

/-! ## Hashable Instance -/

/-- A hash function for `Proposition Atom` using constructor-tag mixing.

Constructor tags: atom=0, bot=1, imp=2, and=3, or=4.
Subformula hashes are combined with `mixHash`. -/
def propHash [Hashable Atom] : Proposition Atom → UInt64
  | .atom x => mixHash 0 (hash x)
  | .bot => 1
  | .imp a b => mixHash (mixHash 2 (propHash a)) (propHash b)
  | .and a b => mixHash (mixHash 3 (propHash a)) (propHash b)
  | .or a b => mixHash (mixHash 4 (propHash a)) (propHash b)

/-- `Hashable` instance for `Proposition Atom`, required by `SignedFormula` and `Branch`
when the formula type is `Proposition Atom`. -/
instance instHashableProposition [Hashable Atom] : Hashable (Proposition Atom) where
  hash := propHash

/-! ## HasBot Instance -/

-- HasBot is already defined for Proposition via PropositionalConnectives in Defs.lean
-- The `HasBot.bot = .bot` holds by definition.

/-! ## Convenience Lemmas -/

/-- `propAndOf?` decomposes exactly the conjunction connective. -/
@[simp]
lemma propAndOf?_and (a b : Proposition Atom) : propAndOf? (.and a b) = some (a, b) := rfl

/-- `propAndOf?` returns `none` for non-conjunctions. -/
@[simp]
lemma propAndOf?_atom (x : Atom) : propAndOf? (.atom x) = none := rfl

/-- `propOrOf?` decomposes exactly the disjunction connective. -/
@[simp]
lemma propOrOf?_or (a b : Proposition Atom) : propOrOf? (.or a b) = some (a, b) := rfl

/-- `propImpOf?` decomposes implication when the consequent is not ⊥. -/
@[simp]
lemma propImpOf?_imp_nonbot (a b : Proposition Atom) (h : b ≠ .bot) :
    propImpOf? (.imp a b) = some (a, b) := by
  unfold propImpOf?
  open scoped Classical in
  cases b <;> simp_all

/-- `propImpOf?` returns `none` for negation `a → ⊥`. -/
@[simp]
lemma propImpOf?_neg (a : Proposition Atom) : propImpOf? (.imp a .bot) = none := rfl

/-- `propNegOf?` decomposes negation `a → ⊥`. -/
@[simp]
lemma propNegOf?_neg (a : Proposition Atom) : propNegOf? (.imp a .bot) = some a := rfl

end Cslib.Logic.PL

end
