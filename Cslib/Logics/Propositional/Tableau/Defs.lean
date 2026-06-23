/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.Tableau.ClosureCondition
public import Cslib.Foundations.Logic.Tableau.PropositionalRules

/-! # Shared Definitions for Propositional Tableau Systems

This module provides shared definitions needed by the three propositional tableau
systems: classical, intuitionistic, and minimal.

## Main Definitions

- `propAndOf?`, `propOrOf?`, `propImpOf?`, `propNegOf?`: Decomposition functions
  for `Proposition Atom` connectives, needed by `applyPropRule`.
- `instHashableProposition`: `Hashable (Proposition Atom)` instance via hash mixing.
- `instIsAtomicProposition`: `IsAtomic (Proposition Atom)` instance, recognizing
  only `Proposition.atom _` as atomic.
- `Proposition.complexity`: Size measure for fuel computation in the expansion loop.
  Bounds the number of expansion steps needed.

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

open Cslib.Logic.Tableau

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

/-- Decompose `φ` as `φ₁ → φ₂` treating all implications uniformly, including `¬φ = φ → ⊥`.

For intuitionistic tableau, we treat negation as implication to ⊥ uniformly. -/
def propImpOrNegOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .imp a b => some (a, b)
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

/-! ## IsAtomic Instance -/

/-- `IsAtomic` instance for `Proposition Atom`: only `atom _` constructors are atomic.

This is used by the `MinimalClosure` instance to identify atomic formulas, which are
the only formulas that can close a minimally tableau branch (T(p) and F(p) at the same
world, for atomic p). -/
instance instIsAtomicProposition : IsAtomic (Proposition Atom) where
  isAtom φ :=
    match φ with
    | .atom _ => true
    | _ => false

/-! ## Complexity Measure -/

/-- The complexity of a proposition, defined as the number of connective occurrences.

Used to compute the fuel bound for the tableau expansion loop. Each rule application
strictly reduces the complexity of the formulas on the branch, ensuring termination. -/
def Proposition.complexity : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => 1 + a.complexity + b.complexity
  | .and a b => 1 + a.complexity + b.complexity
  | .or a b => 1 + a.complexity + b.complexity

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

/-- Complexity is additive over subformulas. -/
@[simp]
lemma complexity_imp (a b : Proposition Atom) :
    (Proposition.imp a b).complexity = 1 + a.complexity + b.complexity := rfl

/-- Complexity is additive over conjunctions. -/
@[simp]
lemma complexity_and (a b : Proposition Atom) :
    (Proposition.and a b).complexity = 1 + a.complexity + b.complexity := rfl

/-- Complexity is additive over disjunctions. -/
@[simp]
lemma complexity_or (a b : Proposition Atom) :
    (Proposition.or a b).complexity = 1 + a.complexity + b.complexity := rfl

/-- Atoms have complexity 0. -/
@[simp]
lemma complexity_atom (x : Atom) : (Proposition.atom x : Proposition Atom).complexity = 0 := rfl

/-- Bot has complexity 0. -/
@[simp]
lemma complexity_bot : (Proposition.bot : Proposition Atom).complexity = 0 := rfl

end Cslib.Logic.PL

end
