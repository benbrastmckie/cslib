/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.SignedFormula

/-! # Rule Result Type

This module defines `RuleResult F L`, the result type for applying a single tableau rule
to a signed formula.

## Main Definitions

- `RuleResult F L`: A four-variant inductive type.
  - `linear`: Alpha-rule result; add the list of signed formulas to the current branch.
  - `branching`: Beta-rule result; split into sub-branches (each must close).
  - `persistent`: Formulas that survive branch closure (for modal/temporal rules).
  - `notApplicable`: The rule does not match this signed formula.

## Variant Summary

| Variant | Lean 4 analog | Description |
|---------|--------------|-------------|
| `linear` | alpha-rule | Add formulas to current branch |
| `branching` | beta-rule | Split into sub-branches |
| `persistent` | modal necessity | Formula persists across branch splits |
| `notApplicable` | no match | Rule does not apply |

The `persistent` variant is included to support downstream modal and temporal tableau
calculi, where box-rules produce signed formulas that must be available
on every branch.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-! ## RuleResult -/

/-- The result of applying a tableau rule to a signed formula.

- `linear fs`: Alpha-rule result. Add the signed formulas `fs` to the current branch.
- `branching bss`: Beta-rule result. Split the current branch, adding formulas from
  `bss[i]` to the i-th sub-branch. All sub-branches must close.
- `persistent fs`: Modal/temporal necessity result. The signed formulas `fs` are added
  to the current branch and persist across any future branch splits.
- `notApplicable`: This rule does not match the signed formula; try another. -/
inductive RuleResult (F : Type*) (L : Type*) : Type _ where
  /-- Alpha-rule result: add these signed formulas to the current branch. -/
  | linear (formulas : List (SignedFormula F L)) : RuleResult F L
  /-- Beta-rule result: split into sub-branches, adding each list to one branch. -/
  | branching (branches : List (List (SignedFormula F L))) : RuleResult F L
  /-- Modal/temporal necessity result: these formulas persist across branch splits. -/
  | persistent (formulas : List (SignedFormula F L)) : RuleResult F L
  /-- This rule does not apply to the given signed formula. -/
  | notApplicable : RuleResult F L

namespace RuleResult

/-- `true` when the result is a `linear` rule application. -/
def isLinear : RuleResult F L → Bool
  | linear _ => true
  | _ => false

/-- `true` when the result is a `branching` rule application. -/
def isBranching : RuleResult F L → Bool
  | branching _ => true
  | _ => false

/-- `true` when the result is a `persistent` rule application. -/
def isPersistent : RuleResult F L → Bool
  | persistent _ => true
  | _ => false

/-- `true` when any rule variant except `notApplicable` matched. -/
def isApplicable : RuleResult F L → Bool
  | notApplicable => false
  | _ => true

end RuleResult

end Cslib.Logic.Tableau

end
