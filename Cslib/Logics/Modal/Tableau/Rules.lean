/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Tableau.PropositionalRules
public import Cslib.Logics.Modal.Tableau.Branch

/-! # Modal K Tableau Rules

This module defines the tableau rule application for the modal K decision procedure.
It combines the generic propositional rules from the Foundations layer with four
K-specific modal rules, all indexed by `WorldIndex` labels.

## Main Definitions

- `modalApplyOne`: Apply the first applicable rule to a signed modal formula.
- `tryAllPropRules_pos`/`_neg`: generic reduction lemmas for `tryAllPropRules`,
  relocated here from `Completeness.lean` — they mention no `Atom`-specific content and are
  needed by the shape lemmas below, which must live upstream of `Completeness.lean`.
- `modalApplyOne_boxPos_eq`/`_diamondNeg_eq`: the Propagating-class shape lemmas,
  relocated here from `CompletenessLoop.lean` with the persistent payload
  existentially-quantified so `RuleApplicationSpec`'s F9/F10 fields can be discharged by T/B/S5
  as well as K.
- `modalApplyOne_boxNeg_witness`/`_diamondPos_witness`: the Minting-class witness lemmas,
  relocated here from `CompletenessLoop.lean` unchanged, discharging F11/F12.

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
   negation `abbrev`.
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

/-! ## Generic `tryAllPropRules` Reduction Lemmas (Relocated from `Completeness.lean`)

These two lemmas are entirely generic over the decomposer functions and formula/label types
(no `Atom`-specific content) and are needed by the shape/witness lemmas below, which must live
upstream of `Completeness.lean` in the import chain. `Completeness.lean` retains access
transitively (`Completeness → Saturation → Rules`). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Reduction of `tryAllPropRules` on a positively-signed formula to a priority-ordered
case split on the four decomposition functions (and > or > imp > neg). -/
theorem tryAllPropRules_pos {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (φ : F) (l : L) :
    tryAllPropRules andOf? orOf? impOf? negOf? ⟨.pos, φ, l⟩ =
      match andOf? φ with
      | some (x, y) => .linear [⟨.pos, x, l⟩, ⟨.pos, y, l⟩]
      | none =>
        match orOf? φ with
        | some (x, y) => .branching [[⟨.pos, x, l⟩], [⟨.pos, y, l⟩]]
        | none =>
          match impOf? φ with
          | some (x, y) => .branching [[⟨.neg, x, l⟩], [⟨.pos, y, l⟩]]
          | none =>
            match negOf? φ with
            | some x => .linear [⟨.neg, x, l⟩]
            | none => .notApplicable := by
  rcases hA : andOf? φ with _ | ⟨x, y⟩ <;> rcases hO : orOf? φ with _ | ⟨x, y⟩ <;>
    rcases hI : impOf? φ with _ | ⟨x, y⟩ <;> rcases hN : negOf? φ with _ | x <;>
    simp [tryAllPropRules, List.map, List.find?, applyPropRule, RuleResult.isApplicable,
      SignedFormula.pos, SignedFormula.neg, hA, hO, hI, hN]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Reduction of `tryAllPropRules` on a negatively-signed formula. -/
theorem tryAllPropRules_neg {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (φ : F) (l : L) :
    tryAllPropRules andOf? orOf? impOf? negOf? ⟨.neg, φ, l⟩ =
      match andOf? φ with
      | some (x, y) => .branching [[⟨.neg, x, l⟩], [⟨.neg, y, l⟩]]
      | none =>
        match orOf? φ with
        | some (x, y) => .linear [⟨.neg, x, l⟩, ⟨.neg, y, l⟩]
        | none =>
          match impOf? φ with
          | some (x, y) => .linear [⟨.pos, x, l⟩, ⟨.neg, y, l⟩]
          | none =>
            match negOf? φ with
            | some x => .linear [⟨.pos, x, l⟩]
            | none => .notApplicable := by
  rcases hA : andOf? φ with _ | ⟨x, y⟩ <;> rcases hO : orOf? φ with _ | ⟨x, y⟩ <;>
    rcases hI : impOf? φ with _ | ⟨x, y⟩ <;> rcases hN : negOf? φ with _ | x <;>
    simp [tryAllPropRules, List.map, List.find?, applyPropRule, RuleResult.isApplicable,
      SignedFormula.pos, SignedFormula.neg, hA, hO, hI, hN]

/-! ## Shape and Witness Lemmas for the Propagating and Minting Rule Classes

These four lemmas classify `modalApplyOne`'s per-shape behaviour for the Propagating class
(`boxPos`/`diamondNeg`, never `.linear`/`.branching`) and the Minting class
(`boxNeg`/`diamondPos`, always applicable with a fresh witness). They are the K discharges for
`RuleApplicationSpec`'s F9-F12 fields (`GenericDriver.lean`), relocated here — upstream of
`GenericDriver.lean` — so `modalApplyOne_spec` can reach them. `TDriver.lean`'s
`modalApplyOneT_spec` reaches them too via the same import chain. -/

omit [Hashable Atom] in
/-- `boxPos`'s own rule-application result is always `.notApplicable` or `.persistent`, never
`.linear`/`.branching`: a formula with sign `.pos` and formula-component `.box ψ` never matches
any of the four Lukasiewicz-encoded propositional decomposers, so `tryAllPropRules` is not
applicable and `modalApplyOne` falls through to the `boxPos` dispatch arm above, which only ever
produces `.notApplicable` or `.persistent`. Stated against an opaque `sf` (rather than a literal
`⟨.pos, .box ψ, w⟩` constructor) so call sites never need to destructure a signed formula whose
components are entangled with an unrelated `rfl`-substitution elsewhere in the proof.

The persistent payload is **existentially quantified** (`RuleApplicationSpec`'s F9
`boxPosNotExpanding`): every use site discards it (it only contradicts the `.linear`/`.branching`
case split), and quantifying it is what lets T's/B's/S5's own Propagating payload (differing
from K's concrete `boxPropagation` list) discharge this fact too. -/
theorem modalApplyOne_boxPos_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .pos)
    (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOne sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, l⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  simp only [modalApplyOne]
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .box ψ, l⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  rw [if_neg (by simp [htry])]
  split_ifs with hemp
  · left; rfl
  · right; exact ⟨_, rfl⟩

omit [Hashable Atom] in
/-- `diamondNeg`'s own rule-application result is always `.notApplicable` or `.persistent`,
never `.linear`/`.branching`: a formula with sign `.neg` and formula-component `.diamond ψ`
never matches any propositional decomposer (`.diamond` is a native constructor distinct from
every prop-rule pattern), so `tryAllPropRules` is not applicable and `modalApplyOne` falls
through to the `diamondNeg` dispatch arm above, which only ever produces `.notApplicable` or
`.persistent` (symmetric to `modalApplyOne_boxPos_eq`'s `boxPos`).

Existentially-quantified payload, same rationale as `modalApplyOne_boxPos_eq` (F10
`diaNegNotExpanding`). -/
theorem modalApplyOne_diamondNeg_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .neg)
    (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOne sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, l⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  simp only [modalApplyOne]
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .diamond ψ, l⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
      = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  rw [if_neg (by simp [htry])]
  split_ifs with hemp
  · left; rfl
  · right; exact ⟨_, rfl⟩

omit [Hashable Atom] in
/-- `boxNeg`'s own rule-application result, unfolded directly: `F(□ψ)@w` always mints a fresh
witness world `w' := modalNextWorld b`, adds the edge `w → w'`, and heads the emitted `.linear`
list with the witness `F(ψ)@w'` (unlike `boxPos`/`diamondNeg`, `boxNeg` never checks an
emptiness guard, so it is always applicable). K discharge for `RuleApplicationSpec`'s F11
`boxNegWitness`. -/
theorem modalApplyOne_boxNeg_witness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOne (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  exact ⟨rfl, _, rfl⟩

omit [Hashable Atom] in
/-- `diamondPos`'s own rule-application result, unfolded directly: `T(◇ψ)@w` always mints a
fresh witness world `w' := modalNextWorld b`, adds the edge `w → w'`, and heads the emitted
`.linear` list with the witness `T(ψ)@w'` (`diamondPos` is native and, like `boxNeg`, never
checks an emptiness guard, so it is always applicable). Symmetric to
`modalApplyOne_boxNeg_witness`. K discharge for `RuleApplicationSpec`'s F12 `diaPosWitness`. -/
theorem modalApplyOne_diamondPos_witness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOne (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
      = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  exact ⟨rfl, _, rfl⟩

end Cslib.Logic.Modal.Tableau

end
