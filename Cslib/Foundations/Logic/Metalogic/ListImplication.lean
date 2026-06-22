/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Theorems.Combinators

/-! # List Implication

This module defines the syntactic list-implication function `listImp` and proves
the key lemmas needed for the algebraic deduction theorem:

- `listImp_axiom_k`: `⊢ φ → listImp Γ φ` (K is preserved under listImp)
- `listImp_axiom_s`: `⊢ listImp Γ (φ → ψ) → listImp Γ φ → listImp Γ ψ` (S is preserved)
- `list_flip_implication1`: `⊢ listImp (φ :: Γ) χ → listImp Γ (φ → χ)`
- `list_flip_implication2`: `⊢ listImp Γ (φ → χ) → listImp (φ :: Γ) χ`

These lemmas enable the deduction theorem to be proved algebraically (without
induction on derivation trees) following the Isabelle `Propositional_Logic_Class`
approach.

## References

* Isabelle `Propositional_Logic_Class.thy` -- the `listImp` construction
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.ListImplication

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

/-! ## List Implication Definition -/

/-- Syntactic list implication: `listImp [A, B, C] φ = A → (B → (C → φ))`.
This is a pure formula-level operation; it does not assert derivability. -/
def listImp : List F → F → F
  | [], φ => φ
  | (ψ :: Ψ), φ => HasImp.imp ψ (listImp Ψ φ)

omit [HasBot F] in
@[simp] theorem listImp_nil (φ : F) : listImp ([] : List F) φ = φ := rfl

omit [HasBot F] in
@[simp] theorem listImp_cons (ψ : F) (Ψ : List F) (φ : F) :
    listImp (ψ :: Ψ) φ = HasImp.imp ψ (listImp Ψ φ) := rfl

/-! ## listImp Preserves K -/

/-- `listImp` preserves the K axiom: `⊢ φ → listImp Γ φ`.
By induction: nil case is identity; cons case composes with K. -/
theorem listImp_axiom_k (φ : F) (Γ : List F) :
    InferenceSystem.DerivableIn S (HasImp.imp φ (listImp Γ φ)) := by
  induction Γ with
  | nil => exact identity φ
  | cons ψ Ψ ih =>
    -- ih : ⊢ φ → listImp Ψ φ
    -- Need: ⊢ φ → ψ → listImp Ψ φ  (since listImp (ψ :: Ψ) φ = ψ → listImp Ψ φ)
    -- K: ⊢ listImp Ψ φ → (ψ → listImp Ψ φ)
    exact imp_trans ih HasAxiomImplyK.implyK

/-! ## listImp Preserves S -/

/-- `listImp` preserves the S axiom:
    `⊢ listImp Γ (φ → ψ) → listImp Γ φ → listImp Γ ψ`.
By induction on Γ. The base case is the S axiom. The inductive step
composes S with the B-combinator. -/
theorem listImp_axiom_s (φ ψ : F) (Γ : List F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp (listImp Γ (HasImp.imp φ ψ))
        (HasImp.imp (listImp Γ φ) (listImp Γ ψ))) := by
  induction Γ with
  | nil =>
    -- Need: ⊢ (φ → ψ) → φ → ψ, which is identity on (φ → ψ)... no.
    -- listImp [] (φ → ψ) = (φ → ψ), listImp [] φ = φ, listImp [] ψ = ψ
    -- Need: ⊢ (φ → ψ) → φ → ψ, which is just identity
    exact identity _
  | cons χ Ψ ih =>
    -- ih : ⊢ listImp Ψ (φ → ψ) → listImp Ψ φ → listImp Ψ ψ
    -- Need: ⊢ (χ → listImp Ψ (φ → ψ)) → (χ → listImp Ψ φ) → (χ → listImp Ψ ψ)
    -- This is: distribute one more implication layer through S.
    -- Let A = listImp Ψ (φ → ψ), B = listImp Ψ φ, C = listImp Ψ ψ
    -- ih : ⊢ A → B → C
    -- Need: ⊢ (χ → A) → (χ → B) → (χ → C)
    -- B-combinator: ⊢ (A → B → C) → (χ → A) → (χ → (B → C))
    -- S: ⊢ (χ → (B → C)) → (χ → B) → (χ → C)
    -- Compose: b_combinator(ih) gives ⊢ (χ → A) → (χ → (B → C))
    -- Then imp_trans with S gives the result.
    have b_ih : InferenceSystem.DerivableIn S
        (HasImp.imp (HasImp.imp χ (listImp Ψ (HasImp.imp φ ψ)))
          (HasImp.imp χ (HasImp.imp (listImp Ψ φ) (listImp Ψ ψ)))) :=
      ModusPonens.mp b_combinator ih
    exact imp_trans b_ih HasAxiomImplyS.implyS

/-! ## Flip Lemmas -/

/-- Flip implication (direction 1):
    `⊢ listImp (φ :: Γ) χ → listImp Γ (φ → χ)`.
    Unfolding: `⊢ (φ → listImp Γ χ) → listImp Γ (φ → χ)`.
    By induction on Γ. The base case is identity. The inductive step
    uses flip, hypothetical syllogism (b_combinator), and implication_absorption. -/
theorem list_flip_implication1 (φ χ : F) : ∀ (Γ : List F),
    InferenceSystem.DerivableIn S
      (HasImp.imp (listImp (φ :: Γ) χ)
        (listImp Γ (HasImp.imp φ χ))) := by
  intro Γ
  induction Γ with
  | nil =>
    -- listImp (φ :: []) χ = φ → χ
    -- listImp [] (φ → χ) = φ → χ
    exact identity _
  | cons ψ Ψ ih =>
    -- listImp (φ :: ψ :: Ψ) χ = φ → ψ → listImp Ψ χ
    -- listImp (ψ :: Ψ) (φ → χ) = ψ → listImp Ψ (φ → χ)
    -- ih : ⊢ (φ → listImp Ψ χ) → listImp Ψ (φ → χ)
    --
    -- Strategy: We need ⊢ (φ → ψ → listImp Ψ χ) → ψ → listImp Ψ (φ → χ)
    --
    -- Step 1: flip gives ⊢ (φ → ψ → listImp Ψ χ) → ψ → φ → listImp Ψ χ
    --         i.e. ⊢ (φ → ψ → listImp Ψ χ) → ψ → listImp (φ :: Ψ) χ
    -- But we need the output under ψ, so we need:
    --   from ⊢ (A → B) → C and ⊢ D → A, get ⊢ D → (B → C)... that's not right.
    --
    -- Let me think differently. We need:
    --   ⊢ (φ → ψ → listImp Ψ χ) → (ψ → listImp Ψ (φ → χ))
    --
    -- flip: ⊢ (φ → ψ → listImp Ψ χ) → (ψ → φ → listImp Ψ χ)
    -- ih : ⊢ (φ → listImp Ψ χ) → listImp Ψ (φ → χ)
    -- b_combinator(ih): ⊢ (ψ → φ → listImp Ψ χ) → (ψ → listImp Ψ (φ → χ))
    -- Compose flip with b_combinator(ih):
    exact imp_trans flip (ModusPonens.mp b_combinator ih)

/-- Flip implication (direction 2):
    `⊢ listImp Γ (φ → χ) → listImp (φ :: Γ) χ`.
    Unfolding: `⊢ listImp Γ (φ → χ) → (φ → listImp Γ χ)`.
    By induction on Γ. The base case is identity. The inductive step
    uses flip and the S combinator. -/
theorem list_flip_implication2 (φ χ : F) : ∀ (Γ : List F),
    InferenceSystem.DerivableIn S
      (HasImp.imp (listImp Γ (HasImp.imp φ χ))
        (listImp (φ :: Γ) χ)) := by
  intro Γ
  induction Γ with
  | nil =>
    -- listImp [] (φ → χ) = φ → χ
    -- listImp (φ :: []) χ = φ → χ
    exact identity _
  | cons ψ Ψ ih =>
    -- listImp (ψ :: Ψ) (φ → χ) = ψ → listImp Ψ (φ → χ)
    -- listImp (φ :: ψ :: Ψ) χ = φ → ψ → listImp Ψ χ
    -- ih : ⊢ listImp Ψ (φ → χ) → (φ → listImp Ψ χ)
    --
    -- Need: ⊢ (ψ → listImp Ψ (φ → χ)) → (φ → ψ → listImp Ψ χ)
    --
    -- b_combinator(ih): ⊢ (ψ → listImp Ψ (φ → χ)) → (ψ → φ → listImp Ψ χ)
    -- flip: ⊢ (ψ → φ → listImp Ψ χ) → (φ → ψ → listImp Ψ χ)
    exact imp_trans (ModusPonens.mp b_combinator ih) flip

end Cslib.Logic.Metalogic.ListImplication
