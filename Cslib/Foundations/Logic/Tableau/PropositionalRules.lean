/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.RuleResult

/-! # Classical Propositional Tableau Rules

This module provides the 8 standard classical propositional expansion rules for analytic
tableaux, within the generic `RuleResult F L` framework.

## Propositional Rules (Smullyan Uniform Notation)

| Rule | Input | Output | Type |
|------|-------|--------|------|
| `andPos` | T(phi and psi) | T(phi), T(psi) | linear (alpha) |
| `andNeg` | F(phi and psi) | F(phi) branch F(psi) | branching (beta) |
| `orPos` | T(phi or psi) | T(phi) branch T(psi) | branching (beta) |
| `orNeg` | F(phi or psi) | F(phi), F(psi) | linear (alpha) |
| `impPos` | T(phi -> psi) | F(phi) branch T(psi) | branching (beta) |
| `impNeg` | F(phi -> psi) | T(phi), F(psi) | linear (alpha) |
| `negPos` | T(neg phi) | F(phi) | linear |
| `negNeg` | F(neg phi) | T(phi) | linear |

## Design

Rules are parameterized over decomposition functions (`andOf?`, `orOf?`, `impOf?`, `negOf?`)
so they work with any formula type, whether connectives are primitive (via `HasAnd` etc.) or
classically encoded (as in bimodal logic: `and phi psi := neg(phi -> neg psi)`).

All results preserve the label from the input signed formula: classical propositional rules
do not create new worlds.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-! ## Propositional Tableau Rule Enumeration -/

/-- The 8 standard propositional expansion rules for analytic tableaux.

Rules are named following Smullyan's uniform notation. Each rule name indicates the
connective and the sign of the formula being expanded. -/
inductive PropTableauRule : Type where
  /-- T(phi and psi) -> T(phi), T(psi) — linear conjunctive (alpha-rule). -/
  | andPos : PropTableauRule
  /-- F(phi and psi) -> F(phi) | F(psi) — branching disjunctive (beta-rule). -/
  | andNeg : PropTableauRule
  /-- T(phi or psi) -> T(phi) | T(psi) — branching disjunctive (beta-rule). -/
  | orPos : PropTableauRule
  /-- F(phi or psi) -> F(phi), F(psi) — linear conjunctive (alpha-rule). -/
  | orNeg : PropTableauRule
  /-- T(phi -> psi) -> F(phi) | T(psi) — branching disjunctive (beta-rule). -/
  | impPos : PropTableauRule
  /-- F(phi -> psi) -> T(phi), F(psi) — linear conjunctive (alpha-rule). -/
  | impNeg : PropTableauRule
  /-- T(neg phi) -> F(phi) — linear (sign-flip rule). -/
  | negPos : PropTableauRule
  /-- F(neg phi) -> T(phi) — linear (sign-flip rule). -/
  | negNeg : PropTableauRule
  deriving Repr, DecidableEq, BEq, Hashable

/-! ## Generic Rule Application -/

/-- Apply a single propositional tableau rule to a signed formula, using abstract
decomposition functions for each connective.

Parameters:
- `andOf?`: Decompose `phi` as `phi1 and phi2`; return `some (phi1, phi2)` or `none`.
- `orOf?`: Decompose `phi` as `phi1 or phi2`; return `some (phi1, phi2)` or `none`.
- `impOf?`: Decompose `phi` as `phi1 -> phi2`; return `some (phi1, phi2)` or `none`.
- `negOf?`: Decompose `phi` as `neg phi1`; return `some phi1` or `none`.
- `sf`: The signed formula to expand.
- `rule`: The rule to apply.

The result is `notApplicable` when the rule does not match the sign and connective of `sf`.
All applicable results preserve the label from `sf` (classical rules create no new worlds).

The decomposition functions are abstract to support both primitive connectives (via `HasAnd`,
`HasOr`, `HasImp`) and classically-encoded connectives
(bimodal: `and phi psi := neg(phi -> neg psi)`). -/
def applyPropRule {F : Type*} {L : Type*}
    (andOf? : F → Option (F × F))
    (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F))
    (negOf? : F → Option F)
    (sf : SignedFormula F L) (rule : PropTableauRule) : RuleResult F L :=
  let l := sf.label
  match rule, sf.sign, sf.formula with
  -- T(phi and psi) -> T(phi), T(psi)
  | .andPos, .pos, phi =>
    match andOf? phi with
    | some (psi, chi) => .linear [.pos psi l, .pos chi l]
    | none => .notApplicable
  -- F(phi and psi) -> F(phi) | F(psi)
  | .andNeg, .neg, phi =>
    match andOf? phi with
    | some (psi, chi) => .branching [[.neg psi l], [.neg chi l]]
    | none => .notApplicable
  -- T(phi or psi) -> T(phi) | T(psi)
  | .orPos, .pos, phi =>
    match orOf? phi with
    | some (psi, chi) => .branching [[.pos psi l], [.pos chi l]]
    | none => .notApplicable
  -- F(phi or psi) -> F(phi), F(psi)
  | .orNeg, .neg, phi =>
    match orOf? phi with
    | some (psi, chi) => .linear [.neg psi l, .neg chi l]
    | none => .notApplicable
  -- T(phi -> psi) -> F(phi) | T(psi)
  | .impPos, .pos, phi =>
    match impOf? phi with
    | some (psi, chi) => .branching [[.neg psi l], [.pos chi l]]
    | none => .notApplicable
  -- F(phi -> psi) -> T(phi), F(psi)
  | .impNeg, .neg, phi =>
    match impOf? phi with
    | some (psi, chi) => .linear [.pos psi l, .neg chi l]
    | none => .notApplicable
  -- T(neg phi) -> F(phi)
  | .negPos, .pos, phi =>
    match negOf? phi with
    | some psi => .linear [.neg psi l]
    | none => .notApplicable
  -- F(neg phi) -> T(phi)
  | .negNeg, .neg, phi =>
    match negOf? phi with
    | some psi => .linear [.pos psi l]
    | none => .notApplicable
  -- No other combinations apply
  | _, _, _ => .notApplicable

/-- Try all 8 propositional rules on a signed formula, returning the first applicable result.
Returns `notApplicable` only if no rule matches. -/
def tryAllPropRules {F : Type*} {L : Type*}
    (andOf? : F → Option (F × F))
    (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F))
    (negOf? : F → Option F)
    (sf : SignedFormula F L) : RuleResult F L :=
  let rules := [.andPos, .andNeg, .orPos, .orNeg, .impPos, .impNeg, .negPos, .negNeg]
  let results := rules.map (applyPropRule andOf? orOf? impOf? negOf? sf ·)
  results.find? (·.isApplicable) |>.getD .notApplicable

end Cslib.Logic.Tableau

end
