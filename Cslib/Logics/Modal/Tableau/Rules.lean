/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.PropositionalRules
public import Cslib.Logics.Modal.Tableau.Branch

/-! # Modal K Tableau Rules

This module defines the tableau rule application for the modal K decision procedure.
It combines the generic propositional rules from the Foundations layer with four
K-specific modal rules, all indexed by `WorldIndex` labels.

## Main Definitions

- `modalApplyOne`: Apply the first applicable rule to a signed modal formula.

## K Modal Rules

The four K modal rules are:

| Rule | Input | Output | Kind |
|------|-------|--------|------|
| `boxPos` | T(□φ)@w | T(φ)@w' for each w'∈successorsOf(acc,w) | persistent |
| `diamondPos` | T(◇φ)@w | create w', edge w→w', T(φ)@w' | linear |
| `boxNeg` | F(□φ)@w | create w', edge w→w', F(φ)@w' | linear |
| `diamondNeg` | F(◇φ)@w | F(φ)@w' for each w'∈successorsOf(acc,w) | persistent |

## K-Soundness Constraint

The `boxPos` rule propagates T(φ) ONLY to explicitly recorded successors of w in the
accessibility relation `acc`. This is the critical K vs S5 distinction: in K, the box
rule says "φ holds at all ACCESSIBLE worlds", not "at all worlds". The bimodal tableau
used "all known worlds" (S5-universal), which would be UNSOUND for K.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- Apply the first applicable rule to a signed modal formula.

Returns `(result, newAcc)` where:
- `result` is the `RuleResult` (linear, branching, persistent, or notApplicable)
- `newAcc` is the updated accessibility relation (modified only by modal existential rules)

The dispatch priority is:
1. Propositional rules (via `tryAllPropRules`), using `modalNegOf?`/`modalOrOf?`/
   `modalAndOf?`/`modalImpOf?` for the native `and`/`or` constructors and the derived
   negation `abbrev` (task 441).
2. K modal rules: `boxPos`, `diamondPos`, `boxNeg`, `diamondNeg`.

IMPORTANT: `boxPos` and `diamondNeg` use `.persistent` (source stays on branch to re-fire
when new successors are added). `diamondPos` and `boxNeg` use `.linear` (existential,
consumed after use). -/
def modalApplyOne
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let w := sf.label
  -- First try propositional rules
  let propResult := tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf
  if propResult.isApplicable then
    (propResult, acc)
  else
    -- Try K modal rules
    match sf.sign, sf.formula with
    -- boxPos: T(□φ)@w → T(φ)@w' for each recorded successor w' of w
    -- K-SOUND: propagate only to successorsOf w, not all worlds
    | .pos, .box φ =>
      let newForms := boxPropagation b acc φ w
      if newForms.isEmpty then
        (.notApplicable, acc)
      else
        (.persistent newForms, acc)
    -- diamondPos: T(◇φ)@w → create fresh w', add edge w→w', T(φ)@w'
    -- Also propagate box-positives from w to w' (they must hold at all successors)
    | .pos, .diamond φ =>
      let w' := modalNextWorld b
      let newAcc := acc.addEdge w w'
      -- The witness: T(φ) at the fresh world
      let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
      -- Propagate all existing T(□ψ)@w to w' (they must hold at ALL successors of w)
      let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
        (boxPositivesOf b).filterMap fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
            if b.any (· == sf') then none else some sf'
          else none
      -- Propagate all existing F(◇ψ)@w to w' as F(ψ)@w'
      -- Note: F(◇φ)@w means F(φ)@w' for all successors w'
      let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
        b.filterMap fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none
      (.linear (witness :: boxProps ++ diaNegProps), newAcc)
    -- boxNeg: F(□φ)@w → create fresh w', add edge w→w', F(φ)@w'
    -- Also propagate box-positives and diamond-negatives from w to w'
    | .neg, .box φ =>
      let w' := modalNextWorld b
      let newAcc := acc.addEdge w w'
      -- The witness: F(φ) at the fresh world
      let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
      -- Propagate all existing T(□ψ)@w to w' (must hold at all successors)
      let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
        (boxPositivesOf b).filterMap fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
            if b.any (· == sf') then none else some sf'
          else none
      -- Propagate all existing F(◇ψ)@w to w' as F(ψ)@w'
      let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
        b.filterMap fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none
      (.linear (witness :: boxProps ++ diaNegProps), newAcc)
    -- diamondNeg: F(◇φ)@w → F(φ)@w' for each recorded successor w'
    -- K-SOUND: propagate only to successorsOf w, not all worlds
    | .neg, .diamond φ =>
      let succs := acc.successorsOf w
      let newForms : List (SignedFormula (Proposition Atom) WorldIndex) :=
        succs.filterMap fun w' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
          if b.any (· == sf') then none else some sf'
      if newForms.isEmpty then
        (.notApplicable, acc)
      else
        (.persistent newForms, acc)
    -- No rule matched
    | _, _ => (.notApplicable, acc)

end Cslib.Logic.Modal.Tableau

end
