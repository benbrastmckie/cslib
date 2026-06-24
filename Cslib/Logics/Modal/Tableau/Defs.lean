/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Logic.Tableau.PropositionalRules

/-! # Modal K Tableau Definitions

This module provides foundational definitions for the modal K tableau decision procedure.
It instantiates the label-generic Foundations tableau layer with
`F = Cslib.Logic.Modal.Proposition Atom` and `L = WorldIndex` (Nat), and defines
the Lukasiewicz decomposition functions for the modal formula type.

## Main Definitions

- `WorldIndex`: World labels for the tableau (just `Nat`).
- `Proposition.complexity`: Size measure for fuel computation.
- `Hashable (Proposition Atom)` instance: required by `Branch` and `SignedFormula` ops.
- `modalNegOf?`, `modalOrOf?`, `modalAndOf?`, `modalImpOf?`: Lukasiewicz decomposition
  functions for the Lukasiewicz-encoded connectives in `Proposition Atom`.
- `modalBoxOf?`, `modalDiaOf?`: Decomposition functions for modal connectives.

## Design

`Proposition Atom` uses Lukasiewicz encoding: `¬φ := φ → ⊥`, `φ ∨ ψ := ¬φ → ψ`,
`φ ∧ ψ := ¬(φ → ¬ψ)`, `◇φ := ¬□¬φ`. These are `abbrev`s, not constructors, so
decomposition is by pattern-matching on the underlying `imp`/`box` constructors.

The decomposition functions must be applied in the correct order to handle overlapping
patterns. Specifically, `modalImpOf?` excludes all encoded neg/or/and shapes.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Modal
open Cslib.Logic.Tableau

/-! ## World Index -/

/-- World labels for the modal K tableau. Each world is identified by a natural number. -/
abbrev WorldIndex := Nat

/-! ## Complexity Measure -/

/-- Structural complexity of a `Proposition Atom`, used as a fuel bound for the tableau loop.

This measures the number of connective nodes. Atoms and bot have complexity 0;
`imp` contributes 1 plus the complexities of its sub-formulas; `box` contributes
1 plus the complexity of its sub-formula. -/
def modalComplexity : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => 1 + modalComplexity φ + modalComplexity ψ
  | .box φ => 1 + modalComplexity φ

/-- Complexity is zero for atoms. -/
@[simp]
lemma modalComplexity_atom (p : Atom) : modalComplexity (.atom p : Proposition Atom) = 0 := rfl

/-- Complexity is zero for falsum. -/
@[simp]
lemma modalComplexity_bot : modalComplexity (.bot : Proposition Atom) = 0 := rfl

/-- Complexity of implication is one plus the complexities of the sub-formulas. -/
@[simp]
lemma modalComplexity_imp (φ ψ : Proposition Atom) :
    modalComplexity (Proposition.imp φ ψ) = 1 + modalComplexity φ + modalComplexity ψ := rfl

/-- Complexity of box is one plus the complexity of the sub-formula. -/
@[simp]
lemma modalComplexity_box (φ : Proposition Atom) :
    modalComplexity (Proposition.box φ) = 1 + modalComplexity φ := rfl

/-! ## Hashable Instance -/

/-- A hash function for `Proposition Atom` using constructor-tag mixing.

Constructor tags: atom=0, bot=1, imp=2, box=3.
Subformula hashes are combined with `mixHash`. -/
def modalPropHash [Hashable Atom] : Proposition Atom → UInt64
  | .atom x => mixHash 0 (hash x)
  | .bot => 1
  | .imp a b => mixHash (mixHash 2 (modalPropHash a)) (modalPropHash b)
  | .box a => mixHash 3 (modalPropHash a)

/-- `Hashable` instance for `Proposition Atom`, required by `SignedFormula` and `Branch`
when the formula type is `Proposition Atom`. -/
instance instHashableModalProposition [Hashable Atom] :
    Hashable (Proposition Atom) where
  hash := modalPropHash

/-! ## Lukasiewicz Decomposition Functions -/

/-- Decompose `φ` as negation `¬ψ = ψ → ⊥`; returns `some ψ` or `none`.

Only matches the pattern `imp a bot` (Lukasiewicz negation). -/
def modalNegOf? (φ : Proposition Atom) : Option (Proposition Atom) :=
  match φ with
  | .imp a .bot => some a
  | _ => none

/-- `modalNegOf?` decomposes Lukasiewicz negation. -/
@[simp]
lemma modalNegOf?_neg (a : Proposition Atom) : modalNegOf? (.imp a .bot) = some a := rfl

/-- `modalNegOf?` returns `none` for non-negations. -/
@[simp]
lemma modalNegOf?_atom (p : Atom) : modalNegOf? (.atom p) = none := rfl

/-- `modalNegOf?` returns `none` for bot. -/
@[simp]
lemma modalNegOf?_bot : modalNegOf? (.bot : Proposition Atom) = none := rfl

/-- Decompose `φ` as disjunction `ψ₁ ∨ ψ₂ = ¬ψ₁ → ψ₂ = (ψ₁ → ⊥) → ψ₂`;
returns `some (ψ₁, ψ₂)` or `none`. -/
def modalOrOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .imp (.imp a .bot) b => some (a, b)
  | _ => none

/-- `modalOrOf?` decomposes Lukasiewicz disjunction. -/
@[simp]
lemma modalOrOf?_or (a b : Proposition Atom) :
    modalOrOf? (Proposition.imp (Proposition.imp a Proposition.bot) b) = some (a, b) := rfl

/-- `modalOrOf?` returns `none` for atoms. -/
@[simp]
lemma modalOrOf?_atom (p : Atom) : modalOrOf? (.atom p) = none := rfl

/-- Decompose `φ` as conjunction `ψ₁ ∧ ψ₂ = ¬(ψ₁ → ¬ψ₂) = (ψ₁ → (ψ₂ → ⊥)) → ⊥`;
returns `some (ψ₁, ψ₂)` or `none`. -/
def modalAndOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .imp (.imp a (.imp b .bot)) .bot => some (a, b)
  | _ => none

/-- `modalAndOf?` decomposes Lukasiewicz conjunction. -/
@[simp]
lemma modalAndOf?_and (a b : Proposition Atom) :
    modalAndOf? (.imp (.imp a (.imp b .bot)) .bot) = some (a, b) := rfl

/-- `modalAndOf?` returns `none` for atoms. -/
@[simp]
lemma modalAndOf?_atom (p : Atom) : modalAndOf? (.atom p) = none := rfl

/-- Decompose `φ` as proper implication `ψ₁ → ψ₂`, excluding the encoded connectives:
negation (`ψ₁ → ⊥`), and disjunction (`(ψ₁ → ⊥) → ψ₂`); returns `some (ψ₁, ψ₂)` or `none`.

Note: conjunction `(ψ₁ → (ψ₂ → ⊥)) → ⊥` IS a negation (consequent is `⊥`), so it is
already excluded by the first pattern. -/
def modalImpOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .imp a b =>
    match b with
    | .bot => none  -- Exclude negation and conjunction-encoded (conseq = ⊥)
    | _ =>
      match a with
      | .imp _ .bot => none  -- Exclude disjunction (antecedent is negation)
      | _ => some (a, b)
  | _ => none

/-- `modalImpOf?` returns `none` for negation (`ψ → ⊥`). -/
@[simp]
lemma modalImpOf?_neg (a : Proposition Atom) :
    modalImpOf? (Proposition.imp a Proposition.bot) = none := rfl

/-- `modalImpOf?` returns `none` for Lukasiewicz disjunction (consequent is not bot). -/
@[simp]
lemma modalImpOf?_or_nonbot (a b : Proposition Atom) (hb : b ≠ Proposition.bot) :
    modalImpOf? (Proposition.imp (Proposition.imp a Proposition.bot) b) = none := by
  cases b <;> simp_all [modalImpOf?]

/-- `modalImpOf?` decomposes proper implication when consequent is not `⊥`
and antecedent is not a negation. -/
lemma modalImpOf?_imp {a b : Proposition Atom} (h1 : b ≠ Proposition.bot)
    (h2 : ∀ c : Proposition Atom, a ≠ Proposition.imp c Proposition.bot) :
    modalImpOf? (Proposition.imp a b) = some (a, b) := by
  -- modalImpOf? matches first on b (is it bot?), then on a (is it imp c bot?)
  -- We case split in the same order
  cases hb : b with
  | bot => exact absurd hb h1
  | _ =>
    cases ha : a with
    | imp c d =>
      cases hd : d with
      | bot => exact absurd (ha ▸ hd ▸ rfl) (h2 c)
      | _ => simp [modalImpOf?]
    | _ => simp [modalImpOf?]

/-- Decompose `φ` as box `□ψ`; returns `some ψ` or `none`. -/
def modalBoxOf? (φ : Proposition Atom) : Option (Proposition Atom) :=
  match φ with
  | .box a => some a
  | _ => none

/-- `modalBoxOf?` decomposes box formulas. -/
@[simp]
lemma modalBoxOf?_box (a : Proposition Atom) : modalBoxOf? (.box a) = some a := rfl

/-- `modalBoxOf?` returns `none` for non-box formulas. -/
@[simp]
lemma modalBoxOf?_atom (p : Atom) : modalBoxOf? (.atom p) = none := rfl

/-- `modalBoxOf?` returns `none` for implication. -/
@[simp]
lemma modalBoxOf?_imp (a b : Proposition Atom) : modalBoxOf? (.imp a b) = none := rfl

/-- Decompose `φ` as diamond `◇ψ = ¬□¬ψ = (□(ψ → ⊥)) → ⊥`;
returns `some ψ` or `none`. -/
def modalDiaOf? (φ : Proposition Atom) : Option (Proposition Atom) :=
  match φ with
  | .imp (.box (.imp a .bot)) .bot => some a
  | _ => none

/-- `modalDiaOf?` decomposes diamond formulas (Lukasiewicz-encoded). -/
@[simp]
lemma modalDiaOf?_dia (a : Proposition Atom) :
    modalDiaOf? (.imp (.box (.imp a .bot)) .bot) = some a := rfl

/-- `modalDiaOf?` returns `none` for atoms. -/
@[simp]
lemma modalDiaOf?_atom (p : Atom) : modalDiaOf? (.atom p) = none := rfl

/-- `modalDiaOf?` returns `none` for plain box formulas. -/
@[simp]
lemma modalDiaOf?_box (a : Proposition Atom) : modalDiaOf? (.box a) = none := rfl

/-! ## Basic Examples -/

/-- Example: negation decomposes correctly. -/
example (a : Proposition Atom) : modalNegOf? (Proposition.neg a) = some a := rfl

/-- Example: box decomposition works. -/
example (a : Proposition Atom) : modalBoxOf? (□a) = some a := rfl

/-- Example: diamond decomposition works. -/
example (a : Proposition Atom) : modalDiaOf? (◇a) = some a := rfl

end Cslib.Logic.Modal.Tableau

end
