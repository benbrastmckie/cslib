/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Normalization.Basic

/-! # Reduction and Normalization for Propositional Natural Deduction

This module defines the single-step reduction and fuel-bounded normalization functions.

## Main Definitions

- `Theory.Derivation.subsOne`: Single-hypothesis substitution for reduction steps.
- `Theory.Derivation.reduceRoot`: Single-step root reduction (proper redexes and commuting
  conversions).
- `Theory.Derivation.normalizeAux`: Fuel-bounded normalization function.
- `Theory.Derivation.normalize`: Normalization using a sufficient fuel bound.

## References

* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Ch. III–IV.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]
variable {T : Theory Atom}

/-! ## Single-Step Reduction and Normalization -/

/-- A convenience substitution for single-hypothesis replacement.
Given `D : T.Derivation (insert A Γ) B` and `E : T.Derivation Γ A`,
produces `T.Derivation Γ B` by substituting `E` for hypothesis `A`.
This implements the key β-reduction step for implication and disjunction redexes. -/
def Theory.Derivation.subsOne {A B : Proposition Atom} {Γ : Ctx Atom}
    (D : T.Derivation (insert A Γ) B)
    (E : T.Derivation Γ A) : T.Derivation Γ B := by
  have h : Γ = (insert A Γ) \ {A} ∪ Γ := by ext x; simp; tauto
  exact h ▸ D.subs (fun X hX => by rw [Finset.mem_singleton] at hX; exact hX ▸ E)

/-- Single-step outermost (root) reduction.
Returns `some d'` if the derivation has an outermost proper redex or commuting conversion,
or `none` otherwise.

Proper redexes (β-reductions):
- `impE (impI _ D) E`: implication redex
- `andE1 _ (andI _ D₁ _)`: left conjunction redex
- `andE2 _ (andI _ _ D₂)`: right conjunction redex
- `orE _ (orI1 _ D) DA _`: left disjunction redex
- `orE _ (orI2 _ D) _ DB`: right disjunction redex

Commuting conversions (permutative reductions):
- `andE1 G (orE G' D DA DB)`: push `andE1` inside `orE` branches
- `andE2 G (orE G' D DA DB)`: push `andE2` inside `orE` branches
- `impE (orE G D DA DB) E`: push `impE` inside `orE` branches -/
def Theory.Derivation.reduceRoot : T.Derivation G A → Option (T.Derivation G A)
  -- Proper redexes
  | impE (impI _ D) E => some (D.subsOne E)
  | andE1 _ (andI _ D₁ _) => some D₁
  | andE2 _ (andI _ _ D₂) => some D₂
  | orE _ (orI1 _ D) DA _ => some (DA.subsOne D)
  | orE _ (orI2 _ D) _ DB => some (DB.subsOne D)
  -- Commuting conversions: push elimination inside orE branches
  | andE1 G (orE _ D DA DB) =>
    some (orE G D (andE1 _ DA) (andE1 _ DB))
  | andE2 G (orE _ D DA DB) =>
    some (orE G D (andE2 _ DA) (andE2 _ DB))
  | impE (orE G D DA DB) E =>
    some (orE G D (impE DA (E.weakCtx (Finset.subset_insert _ _)))
                  (impE DB (E.weakCtx (Finset.subset_insert _ _))))
  | _ => none

/-- Fuel-bounded normalization: normalize subterms, then reduce at root. -/
def Theory.Derivation.normalizeAux : Nat → T.Derivation G A → T.Derivation G A
  | 0, d => d
  | n + 1, d =>
    let d' : T.Derivation G A :=
      match d with
      | ax h => ax h
      | ass h => ass h
      | andI G D₁ D₂ => andI G (D₁.normalizeAux n) (D₂.normalizeAux n)
      | andE1 G D => andE1 G (D.normalizeAux n)
      | andE2 G D => andE2 G (D.normalizeAux n)
      | orI1 G D => orI1 G (D.normalizeAux n)
      | orI2 G D => orI2 G (D.normalizeAux n)
      | orE G D DA DB => orE G (D.normalizeAux n) (DA.normalizeAux n) (DB.normalizeAux n)
      | impI G D => impI G (D.normalizeAux n)
      | impE D E => impE (D.normalizeAux n) (E.normalizeAux n)
      | efq D => efq (D.normalizeAux n)
    match d'.reduceRoot with
    | none => d'
    | some d'' => d''.normalizeAux n

/-- The normalization function, using `2^height` as a generous fuel bound. -/
def Theory.Derivation.normalize (d : T.Derivation G A) : T.Derivation G A :=
  d.normalizeAux (2 ^ d.height)

end Cslib.Logic.PL
