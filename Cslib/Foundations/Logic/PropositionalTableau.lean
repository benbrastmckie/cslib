/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

-- DEPRECATED: This file is superseded by Cslib.Foundations.Logic.Tableau. See task 297.

module

import Cslib.Init

/-! # Abstract Propositional Tableau Infrastructure

This module provides the generic building blocks for propositional tableau calculi,
parameterized over formula types equipped with connective typeclasses. The definitions
here are shared across modal, temporal, bimodal, and pure propositional tableau
implementations.

## Main Definitions

- `PropSign`: The two-element type of propositional signs (positive/negative).
- `PropSignedFormula`: A formula paired with a sign.
- `PropTableauRule`: The 8 standard propositional expansion rules (as an inductive type).
- `PropRuleResult`: The result type for a rule application (linear/branching/not applicable).
- `applyPropRule`: Generic application of one propositional rule to a signed formula.

## Propositional Rules

The 8 standard analytic tableau rules for propositional logic:

| Rule | Input | Output |
|------|-------|--------|
| `andPos` | T(φ ∧ ψ) | T(φ), T(ψ) — linear |
| `andNeg` | F(φ ∧ ψ) | F(φ) \| F(ψ) — branching |
| `orPos` | T(φ ∨ ψ) | T(φ) \| T(ψ) — branching |
| `orNeg` | F(φ ∨ ψ) | F(φ), F(ψ) — linear |
| `impPos` | T(φ → ψ) | F(φ) \| T(ψ) — branching |
| `impNeg` | F(φ → ψ) | T(φ), F(ψ) — linear |
| `negPos` | T(¬φ) | F(φ) — linear |
| `negNeg` | F(¬φ) | T(φ) — linear |

## Design Notes

This module abstracts over the formula type using connective typeclasses. A concrete
tableau implementation for a specific logic (e.g., bimodal) extends these rules with
additional modal/temporal rules and uses a concrete formula type.

The decomposition helpers (`andOf?`, `orOf?`, etc.) are left abstract; each concrete
implementation provides them based on how connectives are encoded (e.g., classical
`and φ ψ := ¬(φ → ¬ψ)` vs. primitive conjunction).

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic

/-! ## Propositional Sign -/

/-- The two-valued sign used in signed tableau formulas.

A positive sign (T) asserts that the formula is true in the model being constructed;
a negative sign (F) asserts that it is false. -/
inductive PropSign : Type where
  /-- Positive sign: the formula is asserted true. -/
  | pos : PropSign
  /-- Negative sign: the formula is asserted false. -/
  | neg : PropSign
  deriving Repr, DecidableEq, BEq, Hashable

/-! ## Propositional Signed Formulas -/

/-- A signed formula: a formula paired with a propositional sign.

Used as the basic unit in tableau branches. A branch is a set (or list) of signed
formulas. A branch is **closed** if it contains both `T(φ)` and `F(φ)` for some `φ`.
A branch is **open** (saturated) if no rule applies to any formula in it. -/
structure PropSignedFormula (F : Type*) where
  /-- The propositional sign of this signed formula. -/
  sign : PropSign
  /-- The formula component. -/
  formula : F
  deriving DecidableEq, BEq, Hashable

namespace PropSignedFormula

/-- Construct a positively signed formula. -/
def pos (φ : F) : PropSignedFormula F := ⟨.pos, φ⟩

/-- Construct a negatively signed formula. -/
def neg (φ : F) : PropSignedFormula F := ⟨.neg, φ⟩

end PropSignedFormula

/-! ## Propositional Tableau Rules -/

/-- The 8 standard propositional expansion rules for analytic tableaux.

These rules are named following Smullyan's uniform notation [Smullyan1968]. Rules are
either **linear** (add formulas to the current branch) or **branching** (split the current
branch into two or more sub-branches, each of which must be closed for the tableau to close). -/
inductive PropTableauRule : Type where
  /-- T(φ ∧ ψ) → T(φ), T(ψ) — linear conjunctive (α-rule). -/
  | andPos : PropTableauRule
  /-- F(φ ∧ ψ) → F(φ) | F(ψ) — branching disjunctive (β-rule). -/
  | andNeg : PropTableauRule
  /-- T(φ ∨ ψ) → T(φ) | T(ψ) — branching disjunctive (β-rule). -/
  | orPos : PropTableauRule
  /-- F(φ ∨ ψ) → F(φ), F(ψ) — linear conjunctive (α-rule). -/
  | orNeg : PropTableauRule
  /-- T(φ → ψ) → F(φ) | T(ψ) — branching disjunctive (β-rule). -/
  | impPos : PropTableauRule
  /-- F(φ → ψ) → T(φ), F(ψ) — linear conjunctive (α-rule). -/
  | impNeg : PropTableauRule
  /-- T(¬φ) → F(φ) — linear (double-negation / sign-flip rule). -/
  | negPos : PropTableauRule
  /-- F(¬φ) → T(φ) — linear (double-negation / sign-flip rule). -/
  | negNeg : PropTableauRule
  deriving Repr, DecidableEq, BEq, Hashable

/-! ## Rule Result -/

/-- The result of applying a propositional tableau rule to a signed formula.

- `linear`: Apply formulas to the current branch (non-branching, α-rule result).
- `branching`: Split into sub-branches (β-rule result). Each element of the outer list
  is a list of signed formulas to add to one branch. All branches must close.
- `notApplicable`: The rule does not apply to this signed formula. -/
inductive PropRuleResult (F : Type u) : Type u where
  /-- Linear (α-rule) result: add these signed formulas to the current branch. -/
  | linear (formulas : List (PropSignedFormula F)) : PropRuleResult F
  /-- Branching (β-rule) result: split into sub-branches. -/
  | branching (branches : List (List (PropSignedFormula F))) : PropRuleResult F
  /-- The rule does not apply to this signed formula. -/
  | notApplicable : PropRuleResult F

/-! ## Generic Rule Application -/

/-- Apply a propositional tableau rule to a signed formula, using abstract decomposition
functions for each connective.

Parameters:
- `andOf?`: Try to decompose `φ` as `φ₁ ∧ φ₂`; return `some (φ₁, φ₂)` or `none`.
- `orOf?`: Try to decompose `φ` as `φ₁ ∨ φ₂`; return `some (φ₁, φ₂)` or `none`.
- `impOf?`: Try to decompose `φ` as `φ₁ → φ₂`; return `some (φ₁, φ₂)` or `none`.
- `negOf?`: Try to decompose `φ` as `¬φ₁`; return `some φ₁` or `none`.
- `sf`: The signed formula to expand.

This function is parameterized over the decomposition functions so that it works for
any concrete formula type, whether conjunction is primitive (`HasAnd`) or classically
encoded as `¬(φ → ¬ψ)`.

The bimodal tableau uses classical encodings:
- `and φ ψ := ¬(φ → ¬ψ)` — recognized by `asAnd?`
- `or φ ψ := ¬φ → ψ` — recognized by `asOr?`
- `neg φ := φ → ⊥` — recognized by `asNeg?` -/
def applyPropRule {F : Type*}
    (andOf? : F → Option (F × F))
    (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F))
    (negOf? : F → Option F)
    (sf : PropSignedFormula F) (rule : PropTableauRule) : PropRuleResult F :=
  match rule, sf.sign, sf.formula with
  -- T(φ ∧ ψ) → T(φ), T(ψ)
  | .andPos, .pos, φ =>
    match andOf? φ with
    | some (ψ, χ) => .linear [.pos ψ, .pos χ]
    | none => .notApplicable
  -- F(φ ∧ ψ) → F(φ) | F(ψ)
  | .andNeg, .neg, φ =>
    match andOf? φ with
    | some (ψ, χ) => .branching [[.neg ψ], [.neg χ]]
    | none => .notApplicable
  -- T(φ ∨ ψ) → T(φ) | T(ψ)
  | .orPos, .pos, φ =>
    match orOf? φ with
    | some (ψ, χ) => .branching [[.pos ψ], [.pos χ]]
    | none => .notApplicable
  -- F(φ ∨ ψ) → F(φ), F(ψ)
  | .orNeg, .neg, φ =>
    match orOf? φ with
    | some (ψ, χ) => .linear [.neg ψ, .neg χ]
    | none => .notApplicable
  -- T(φ → ψ) → F(φ) | T(ψ)
  | .impPos, .pos, φ =>
    match impOf? φ with
    | some (ψ, χ) => .branching [[.neg ψ], [.pos χ]]
    | none => .notApplicable
  -- F(φ → ψ) → T(φ), F(ψ)
  | .impNeg, .neg, φ =>
    match impOf? φ with
    | some (ψ, χ) => .linear [.pos ψ, .neg χ]
    | none => .notApplicable
  -- T(¬φ) → F(φ)
  | .negPos, .pos, φ =>
    match negOf? φ with
    | some ψ => .linear [.neg ψ]
    | none => .notApplicable
  -- F(¬φ) → T(φ)
  | .negNeg, .neg, φ =>
    match negOf? φ with
    | some ψ => .linear [.pos ψ]
    | none => .notApplicable
  -- No other combinations apply
  | _, _, _ => .notApplicable

end Cslib.Logic
