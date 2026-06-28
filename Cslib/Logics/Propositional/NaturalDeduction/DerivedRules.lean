/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Derived Rules for Natural Deduction

This module provides derived introduction and elimination rules for the
propositional connectives in the standalone natural deduction system
(`Theory.Derivation` with `Finset` contexts).

The ND system has 10 primitive constructors: axiom, assumption, andI, andE1, andE2,
orI1, orI2, orE, impI, impE. Ex falso quodlibet (botE) and the classical rules
(dne) are derived rules.

## Main Definitions

### Ex Falso Quodlibet (derived)
- `botE`: Bottom elimination, requires `[IsIntuitionistic T]`

### Negation
- `negI`: Negation introduction (wrapper for `impI`)
- `negE`: Negation elimination (wrapper for `impE`)

### Verum
- `topI`: Top introduction

### Conjunction (primitive wrappers, no classicality required)
- `andI`: Conjunction introduction (primitive)
- `andE1`: Left conjunction elimination (primitive)
- `andE2`: Right conjunction elimination (primitive)

### Disjunction (primitive wrappers, no classicality required)
- `orI1`: Left disjunction introduction (primitive)
- `orI2`: Right disjunction introduction (primitive)
- `orE`: Disjunction elimination (primitive)

### Double Negation Elimination
- `dne`: Double negation elimination (requires `[IsClassical T]`)

### Biconditional
- `iffI`: Biconditional introduction
- `iffE1`: Left biconditional elimination (no classicality required)
- `iffE2`: Right biconditional elimination (no classicality required)

### Prop-level Wrappers
All rules have `DerivableIn`-level versions with the suffix `DerivableIn`.

## Design

Conjunction and disjunction rules are now primitive constructors in the ND system,
so their introduction and elimination rules are trivial wrappers. The `botE` rule
requires `[IsIntuitionistic T]` (i.e., the theory contains ex falso quodlibet `⊥ → A`).
Biconditional elimination no longer requires classicality since `and` is primitive.

## References

* `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- standalone ND system
* `Cslib/Logics/Propositional/Defs.lean` -- connective definitions
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]
variable {T : Theory Atom}
variable {Γ : Ctx Atom}
variable {A B C : Proposition Atom}

/-! ## Ex Falso Quodlibet (derived) -/

/-- **Bottom Elimination** (botE): From `Gamma |- bot`, derive `Gamma |- A`.

Requires `[IsIntuitionistic T]` (the theory contains `⊥ → A`).
Derived via `impE` with the axiom `⊥ → A` from the theory. -/
def Theory.Derivation.botE [IsIntuitionistic T]
    (d : T.Derivation Γ ⊥) :
    T.Derivation Γ A :=
  Derivation.efq d

/-! ## Negation Rules -/

/-- **Negation Introduction** (negI): From `Gamma, A |- bot`, derive `Gamma |- neg A`.

Since `neg A := A -> bot`, this is simply implication introduction. -/
def Theory.Derivation.negI
    (d : T.Derivation (insert A Γ) ⊥) :
    T.Derivation Γ (¬A) :=
  Derivation.impI Γ d

/-- **Negation Elimination** (negE): From `Gamma |- neg A` and `Gamma |- A`,
derive `Gamma |- bot`.

Since `neg A := A -> bot`, this is simply implication elimination. -/
def Theory.Derivation.negE
    (d₁ : T.Derivation Γ (¬A))
    (d₂ : T.Derivation Γ A) :
    T.Derivation Γ ⊥ :=
  Derivation.impE d₁ d₂

/-! ## Verum -/

/-- **Top Introduction** (topI): `Gamma |- top` for any context.

Since `top := bot -> bot`, introduce the implication and use the assumption. -/
def Theory.Derivation.topI :
    T.Derivation Γ (⊤ : Proposition Atom) :=
  Derivation.impI Γ <| Derivation.ass <| by grind

/-! ## Conjunction Rules (primitive wrappers) -/

/-- **Double Negation Elimination** (DNE): From `Gamma |- neg neg A`,
derive `Gamma |- A`.

Uses the classical axiom `(neg neg A -> A) in T` via `IsClassical.dne`. -/
def Theory.Derivation.dne [IsClassical T]
    (d : T.Derivation Γ (¬¬A)) :
    T.Derivation Γ A :=
  Derivation.impE (Derivation.ax (IsClassical.dne A)) d

/-! ## Biconditional Rules -/

/-- **Biconditional Introduction** (iffI): From `Gamma |- A -> B` and
`Gamma |- B -> A`, derive `Gamma |- A iff B`.

Since `A iff B := (A -> B) and (B -> A)`, this is conjunction introduction
applied to the two implications. -/
def Theory.Derivation.iffI
    (d₁ : T.Derivation Γ (A → B))
    (d₂ : T.Derivation Γ (B → A)) :
    T.Derivation Γ (A ↔ B) :=
  Derivation.andI Γ d₁ d₂

/-- **Left Biconditional Elimination** (iffE1): From `Gamma |- A iff B`,
derive `Gamma |- A -> B`.

Since `A iff B := (A -> B) and (B -> A)`, this is left conjunction elimination. -/
def Theory.Derivation.iffE1
    (d : T.Derivation Γ (A ↔ B)) :
    T.Derivation Γ (A → B) :=
  Derivation.andE1 Γ d

/-- **Right Biconditional Elimination** (iffE2): From `Gamma |- A iff B`,
derive `Gamma |- B -> A`.

Since `A iff B := (A -> B) and (B -> A)`, this is right conjunction elimination. -/
def Theory.Derivation.iffE2
    (d : T.Derivation Γ (A ↔ B)) :
    T.Derivation Γ (B → A) :=
  Derivation.andE2 Γ d

/-! ## DerivableIn-level Wrappers -/

/-- Bottom elimination at the `DerivableIn` level. -/
theorem DerivableIn.botE [IsIntuitionistic T]
    (h : DerivableIn T (Γ ⊢ (⊥ : Proposition Atom))) :
    DerivableIn T (Γ ⊢ A) :=
  let ⟨d⟩ := h; ⟨d.botE⟩

/-- Negation introduction at the `DerivableIn` level. -/
theorem DerivableIn.negI
    (h : DerivableIn T ((insert A Γ) ⊢ (⊥ : Proposition Atom))) :
    DerivableIn T (Γ ⊢ ¬A) :=
  let ⟨d⟩ := h; ⟨d.negI⟩

/-- Negation elimination at the `DerivableIn` level. -/
theorem DerivableIn.negE
    (h₁ : DerivableIn T (Γ ⊢ ¬A))
    (h₂ : DerivableIn T (Γ ⊢ A)) :
    DerivableIn T (Γ ⊢ (⊥ : Proposition Atom)) :=
  let ⟨d₁⟩ := h₁; let ⟨d₂⟩ := h₂; ⟨d₁.negE d₂⟩

/-- Top introduction at the `DerivableIn` level. -/
theorem DerivableIn.topI :
    DerivableIn T (Γ ⊢ (⊤ : Proposition Atom)) :=
  ⟨Theory.Derivation.topI⟩

/-- Conjunction introduction at the `DerivableIn` level. -/
theorem DerivableIn.andI
    (h₁ : DerivableIn T (Γ ⊢ A))
    (h₂ : DerivableIn T (Γ ⊢ B)) :
    DerivableIn T (Γ ⊢ A ∧ B) :=
  let ⟨d₁⟩ := h₁; let ⟨d₂⟩ := h₂; ⟨Derivation.andI Γ d₁ d₂⟩

/-- Left conjunction elimination at the `DerivableIn` level. -/
theorem DerivableIn.andE1
    (h : DerivableIn T (Γ ⊢ A ∧ B)) :
    DerivableIn T (Γ ⊢ A) :=
  let ⟨d⟩ := h; ⟨Derivation.andE1 Γ d⟩

/-- Right conjunction elimination at the `DerivableIn` level. -/
theorem DerivableIn.andE2
    (h : DerivableIn T (Γ ⊢ A ∧ B)) :
    DerivableIn T (Γ ⊢ B) :=
  let ⟨d⟩ := h; ⟨Derivation.andE2 Γ d⟩

/-- Left disjunction introduction at the `DerivableIn` level. -/
theorem DerivableIn.orI1
    (h : DerivableIn T (Γ ⊢ A)) :
    DerivableIn T (Γ ⊢ A ∨ B) :=
  let ⟨d⟩ := h; ⟨Derivation.orI1 Γ d⟩

/-- Right disjunction introduction at the `DerivableIn` level. -/
theorem DerivableIn.orI2
    (h : DerivableIn T (Γ ⊢ B)) :
    DerivableIn T (Γ ⊢ A ∨ B) :=
  let ⟨d⟩ := h; ⟨Derivation.orI2 Γ d⟩

/-- Disjunction elimination at the `DerivableIn` level. -/
theorem DerivableIn.orE
    (h : DerivableIn T (Γ ⊢ A ∨ B))
    (hA : DerivableIn T ((insert A Γ) ⊢ C))
    (hB : DerivableIn T ((insert B Γ) ⊢ C)) :
    DerivableIn T (Γ ⊢ C) :=
  let ⟨d⟩ := h; let ⟨dA⟩ := hA; let ⟨dB⟩ := hB; ⟨Derivation.orE Γ d dA dB⟩

/-- Double negation elimination at the `DerivableIn` level. -/
theorem DerivableIn.dne [IsClassical T]
    (h : DerivableIn T (Γ ⊢ ¬¬A)) :
    DerivableIn T (Γ ⊢ A) :=
  let ⟨d⟩ := h; ⟨d.dne⟩

/-- Biconditional introduction at the `DerivableIn` level. -/
theorem DerivableIn.iffI
    (h₁ : DerivableIn T (Γ ⊢ A → B))
    (h₂ : DerivableIn T (Γ ⊢ B → A)) :
    DerivableIn T (Γ ⊢ A ↔ B) :=
  let ⟨d₁⟩ := h₁; let ⟨d₂⟩ := h₂; ⟨d₁.iffI d₂⟩

/-- Left biconditional elimination at the `DerivableIn` level. -/
theorem DerivableIn.iffE1
    (h : DerivableIn T (Γ ⊢ A ↔ B)) :
    DerivableIn T (Γ ⊢ A → B) :=
  let ⟨d⟩ := h; ⟨d.iffE1⟩

/-- Right biconditional elimination at the `DerivableIn` level. -/
theorem DerivableIn.iffE2
    (h : DerivableIn T (Γ ⊢ A ↔ B)) :
    DerivableIn T (Γ ⊢ B → A) :=
  let ⟨d⟩ := h; ⟨d.iffE2⟩

end Cslib.Logic.PL
