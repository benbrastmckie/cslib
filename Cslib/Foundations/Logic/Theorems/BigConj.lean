/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Theorems.Propositional.Core
public import Mathlib.Tactic.Attr.Core

/-! # Big Conjunction over Lists of Formulas

Defines `bigconj : List F → F` as a generic fold using only `HasBot.bot` and `HasImp.imp`,
plus derivability lemmas for `[ClassicalHilbert S]`.

## Scope

`bigconj` operates at the `HasBot`/`HasImp` typeclass level so that it can be instantiated
across all formula types in CSLib: propositional, modal, temporal, and bimodal. Since not
all of these types implement `HasAnd`, using the Lukasiewicz conjunction encoding
`φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥` is the maximally general choice here. Formula types
that do implement `HasAnd` (e.g., `PL.Proposition`) can use `HasAnd.and` directly for
native conjunction; `bigconj` provides a uniform interface across all types.

## Main Definitions

- `bigconj`: Big conjunction (`⊤` for empty, identity for singleton,
  nested conjunction for longer lists)
- `negBigconj`: Negation of big conjunction

## Main Results

- `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`: Simp lemmas
- `bigconj_mem_derivable`: If `φ ∈ L` and `⊢ bigconj L`,
  then `⊢ φ`
- `bigconj_derivable_intro`: If all members of `L` are derivable,
  then `⊢ bigconj L`

## Encoding

Conjunction uses the Lukasiewicz encoding:
`φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥`
-/

@[expose] public section

namespace Cslib.Logic.Theorems.BigConj

open Cslib.Logic

variable {F : Type*} [HasBot F] [HasImp F]

/-! ### Syntactic Definitions -/

/-- Big conjunction over a list of formulas.
    Base case: empty list folds to `⊤ := ⊥ → ⊥`.
    Singleton: just the formula.
    Longer: nested conjunction. -/
def bigconj : List F → F
  | [] => HasImp.imp HasBot.bot HasBot.bot
  | [φ] => φ
  | φ :: ψ :: rest =>
    HasImp.imp
      (HasImp.imp φ
        (HasImp.imp (bigconj (ψ :: rest)) HasBot.bot))
      HasBot.bot

/-- Negated big conjunction. -/
def negBigconj (L : List F) : F :=
  HasImp.imp (bigconj L) HasBot.bot

@[simp, scoped grind =] theorem bigconj_nil :
    bigconj (F := F) [] =
      HasImp.imp HasBot.bot HasBot.bot := rfl

@[simp, scoped grind =] theorem bigconj_singleton (φ : F) :
    bigconj [φ] = φ := rfl

@[simp, scoped grind =] theorem bigconj_cons_cons (φ ψ : F)
    (rest : List F) :
    bigconj (φ :: ψ :: rest) =
      HasImp.imp
        (HasImp.imp φ
          (HasImp.imp (bigconj (ψ :: rest)) HasBot.bot))
        HasBot.bot := rfl

@[simp, scoped grind =] theorem negBigconj_def (L : List F) :
    negBigconj L = HasImp.imp (bigconj L) HasBot.bot :=
  rfl

/-! ### Derivability Lemmas -/

variable {S : Type*} [InferenceSystem S F]
variable [ClassicalHilbert S (F := F)]

open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Theorems.Propositional.Core

section BigConj

/-- If `φ ∈ L` and `⊢ bigconj L`, then `⊢ φ`. -/
theorem bigconj_mem_derivable {L : List F} {φ : F}
    (hmem : φ ∈ L)
    (hconj : InferenceSystem.DerivableIn S (bigconj L)) :
    InferenceSystem.DerivableIn S φ := by
  induction L with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons a rest ih =>
    cases rest with
    | nil =>
      grind
    | cons b tail =>
      simp only [bigconj_cons_cons] at hconj
      cases hmem with
      | head => exact ModusPonens.mp lce_imp hconj
      | tail _ hmem' =>
        have := ModusPonens.mp rce_imp hconj
        exact ih hmem' this

/-- If all members of `L` are derivable, then `⊢ bigconj L`. -/
theorem bigconj_derivable_intro {L : List F}
    (h : ∀ φ ∈ L, InferenceSystem.DerivableIn S φ) :
    InferenceSystem.DerivableIn S (bigconj L) := by
  induction L with
  | nil =>
    simp only [bigconj_nil]
    exact identity (S := S) HasBot.bot
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [bigconj_singleton]
      exact h a (by simp)
    | cons b tail =>
      simp only [bigconj_cons_cons]
      have ha := h a (by simp)
      have hrest : ∀ φ ∈ (b :: tail),
          InferenceSystem.DerivableIn S φ := by
        intro φ hmem
        exact h φ (by simp [hmem])
      have ih_result := ih hrest
      have pair := pairing (S := S) a (bigconj (b :: tail))
      exact ModusPonens.mp
        (ModusPonens.mp pair ha) ih_result

end BigConj

end Cslib.Logic.Theorems.BigConj
