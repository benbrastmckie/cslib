/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Logic.Tableau.PropositionalRules -- shake: keep

/-! # Modal K Tableau Definitions

This module provides foundational definitions for the modal K tableau decision procedure.
It instantiates the label-generic Foundations tableau layer with
`F = Cslib.Logic.Modal.Proposition Atom` and `L = WorldIndex` (Nat), and defines
the decomposition functions for the modal formula type.

## Main Definitions

- `WorldIndex`: World labels for the tableau (just `Nat`).
- `Proposition.complexity`: Size measure for fuel computation.
- `Hashable (Proposition Atom)` instance: required by `Branch` and `SignedFormula` ops.
- `modalNegOf?`: decomposition for the derived Lukasiewicz negation `¬φ := φ → ⊥`.
- `modalAndOf?`, `modalOrOf?`: decomposition for the native `and`/`or` constructors.
- `modalImpOf?`: decomposition for proper implication, excluding only the derived
  negation shape (since `and`/`or` are now separate constructors, not encoded via `imp`).
- `modalBoxOf?`, `modalDiaOf?`: decomposition for the native `box`/`diamond` constructors.

## Design

`Proposition Atom`'s `and`, `or`, and `diamond` are native constructors
(mirroring `PL.Proposition`), so the decomposers below are one-to-one structural
projections for those three connectives -- no Lukasiewicz bridging is needed. Only
negation (`¬φ := φ → ⊥`) remains a derived `abbrev`, so `modalNegOf?`/`modalImpOf?`
still pattern-match on the underlying `imp`/`bot` shape to detect it.

The decomposer *names* and their `@[simp]` reduction-lemma names are preserved from the
historical Lukasiewicz-encoded presentation (minimal-churn contract for the tableau
completeness/FMP files that call them); only the bodies and statements change to match
native shapes.

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
binary connectives (`imp`, `and`, `or`) contribute 1 plus the complexities of their
sub-formulas; unary modalities (`box`, `diamond`) contribute 1 plus the complexity of
their sub-formula. -/
def modalComplexity : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => 1 + modalComplexity φ + modalComplexity ψ
  | .and φ ψ => 1 + modalComplexity φ + modalComplexity ψ
  | .or φ ψ => 1 + modalComplexity φ + modalComplexity ψ
  | .box φ => 1 + modalComplexity φ
  | .diamond φ => 1 + modalComplexity φ

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

/-- Complexity of conjunction is one plus the complexities of the sub-formulas. -/
@[simp]
lemma modalComplexity_and (φ ψ : Proposition Atom) :
    modalComplexity (Proposition.and φ ψ) = 1 + modalComplexity φ + modalComplexity ψ := rfl

/-- Complexity of disjunction is one plus the complexities of the sub-formulas. -/
@[simp]
lemma modalComplexity_or (φ ψ : Proposition Atom) :
    modalComplexity (Proposition.or φ ψ) = 1 + modalComplexity φ + modalComplexity ψ := rfl

/-- Complexity of box is one plus the complexity of the sub-formula. -/
@[simp]
lemma modalComplexity_box (φ : Proposition Atom) :
    modalComplexity (Proposition.box φ) = 1 + modalComplexity φ := rfl

/-- Complexity of diamond is one plus the complexity of the sub-formula. -/
@[simp]
lemma modalComplexity_diamond (φ : Proposition Atom) :
    modalComplexity (Proposition.diamond φ) = 1 + modalComplexity φ := rfl

/-! ## Hashable Instance -/

/-- A hash function for `Proposition Atom` using constructor-tag mixing.

Constructor tags: atom=0, bot=1, imp=2, box=3, and=4, or=5, diamond=6.
Subformula hashes are combined with `mixHash`. -/
def modalPropHash [Hashable Atom] : Proposition Atom → UInt64
  | .atom x => mixHash 0 (hash x)
  | .bot => 1
  | .imp a b => mixHash (mixHash 2 (modalPropHash a)) (modalPropHash b)
  | .box a => mixHash 3 (modalPropHash a)
  | .and a b => mixHash (mixHash 4 (modalPropHash a)) (modalPropHash b)
  | .or a b => mixHash (mixHash 5 (modalPropHash a)) (modalPropHash b)
  | .diamond a => mixHash 6 (modalPropHash a)

/-- `Hashable` instance for `Proposition Atom`, required by `SignedFormula` and `Branch`
when the formula type is `Proposition Atom`. -/
instance instHashableModalProposition [Hashable Atom] :
    Hashable (Proposition Atom) where
  hash := modalPropHash

/-! ## Decomposition Functions -/

/-- Decompose `φ` as negation `¬ψ = ψ → ⊥`; returns `some ψ` or `none`.

Only matches the pattern `imp a bot` (negation remains a derived Lukasiewicz `abbrev`,
unaffected by `and`/`or`/`diamond` becoming native constructors). -/
def modalNegOf? (φ : Proposition Atom) : Option (Proposition Atom) :=
  match φ with
  | .imp a .bot => some a
  | _ => none

/-- `modalNegOf?` decomposes negation. -/
@[simp]
lemma modalNegOf?_neg (a : Proposition Atom) : modalNegOf? (.imp a .bot) = some a := rfl

/-- `modalNegOf?` returns `none` for non-negations. -/
@[simp]
lemma modalNegOf?_atom (p : Atom) : modalNegOf? (.atom p) = none := rfl

/-- `modalNegOf?` returns `none` for bot. -/
@[simp]
lemma modalNegOf?_bot : modalNegOf? (.bot : Proposition Atom) = none := rfl

/-- `modalNegOf?` only succeeds on the negation shape `ψ → ⊥`. -/
lemma modalNegOf?_eq_some {φ ψ : Proposition Atom} (h : modalNegOf? φ = some ψ) :
    φ = .imp ψ .bot := by
  unfold modalNegOf? at h; split at h <;> simp_all

/-- Decompose `φ` as disjunction `ψ₁ ∨ ψ₂` (native constructor);
returns `some (ψ₁, ψ₂)` or `none`. -/
def modalOrOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .or a b => some (a, b)
  | _ => none

/-- `modalOrOf?` decomposes disjunction. -/
@[simp]
lemma modalOrOf?_or (a b : Proposition Atom) :
    modalOrOf? (Proposition.or a b) = some (a, b) := rfl

/-- `modalOrOf?` returns `none` for atoms. -/
@[simp]
lemma modalOrOf?_atom (p : Atom) : modalOrOf? (.atom p) = none := rfl

/-- `modalOrOf?` only succeeds on the native disjunction shape `a ∨ b`.

Restated against the native `Proposition.or` constructor; the historical
Lukasiewicz-encoded characterization (`φ = .imp (.imp a .bot) b`) is false on this
version of `Proposition Atom` and must not be used. -/
lemma modalOrOf?_eq_some {φ a b : Proposition Atom} (h : modalOrOf? φ = some (a, b)) :
    φ = .or a b := by
  unfold modalOrOf? at h; split at h <;> simp_all

/-- Decompose `φ` as conjunction `ψ₁ ∧ ψ₂` (native constructor);
returns `some (ψ₁, ψ₂)` or `none`. -/
def modalAndOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .and a b => some (a, b)
  | _ => none

/-- `modalAndOf?` decomposes conjunction. -/
@[simp]
lemma modalAndOf?_and (a b : Proposition Atom) :
    modalAndOf? (.and a b) = some (a, b) := rfl

/-- `modalAndOf?` returns `none` for atoms. -/
@[simp]
lemma modalAndOf?_atom (p : Atom) : modalAndOf? (.atom p) = none := rfl

/-- `modalAndOf?` only succeeds on the native conjunction shape `a ∧ b`.

Restated against the native `Proposition.and` constructor; the historical
Lukasiewicz-encoded characterization (`φ = .imp (.imp a (.imp b .bot)) .bot`) is false on
this version of `Proposition Atom` and must not be used. -/
lemma modalAndOf?_eq_some {φ a b : Proposition Atom} (h : modalAndOf? φ = some (a, b)) :
    φ = .and a b := by
  unfold modalAndOf? at h; split at h <;> simp_all

/-- Decompose `φ` as proper implication `ψ₁ → ψ₂`, excluding the derived negation shape
(`ψ₁ → ⊥`); returns `some (ψ₁, ψ₂)` or `none`.

`and`/`or` are separate native constructors (not encoded via `imp`), so
`modalImpOf?` only needs to exclude negation, not the Lukasiewicz and/or shapes. -/
def modalImpOf? (φ : Proposition Atom) : Option (Proposition Atom × Proposition Atom) :=
  match φ with
  | .imp a b =>
    match b with
    | .bot => none  -- Exclude negation (conseq = ⊥)
    | _ => some (a, b)
  | _ => none

/-- `modalImpOf?` returns `none` for negation (`ψ → ⊥`). -/
@[simp]
lemma modalImpOf?_neg (a : Proposition Atom) :
    modalImpOf? (Proposition.imp a Proposition.bot) = none := rfl

/-- `modalImpOf?` decomposes proper implication when the consequent is not `⊥`. -/
@[simp]
lemma modalImpOf?_imp {a b : Proposition Atom} (h1 : b ≠ Proposition.bot) :
    modalImpOf? (Proposition.imp a b) = some (a, b) := by
  cases hb : b with
  | bot => exact absurd hb h1
  | _ => simp [modalImpOf?]

/-- `modalImpOf?` only succeeds on a proper implication `a → b`. -/
lemma modalImpOf?_eq_some {φ a b : Proposition Atom} (h : modalImpOf? φ = some (a, b)) :
    φ = .imp a b := by
  unfold modalImpOf? at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
  · exact absurd h (by simp)

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

/-- Decompose `φ` as diamond `◇ψ` (native constructor); returns `some ψ` or `none`. -/
def modalDiaOf? (φ : Proposition Atom) : Option (Proposition Atom) :=
  match φ with
  | .diamond a => some a
  | _ => none

/-- `modalDiaOf?` decomposes diamond formulas. -/
@[simp]
lemma modalDiaOf?_dia (a : Proposition Atom) :
    modalDiaOf? (.diamond a) = some a := rfl

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
