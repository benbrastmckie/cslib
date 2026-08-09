/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.GenericDriver
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.CompletenessLoop
public import Cslib.Logics.Modal.Tableau.Support.Accessibility
public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds
public import Cslib.Logics.Modal.Tableau.BDriver

/-! # TB-System Tableau Driver

This module instantiates the generic tableau driver (`Saturation.lean`'s `modalStepBranchGen`/
`modalExpandBranchesGen`/`modalTableauGen`) with the TB-augmented rule-application function
`modalApplyOneTB` (`FrameRules.lean`), and discharges the structural-hypothesis bundle
`RuleApplicationSpec` (`GenericDriver.lean`) for it.

`modalApplyOneTB` merges two arm families: B's predecessor-lookup backward-propagation arms
(`modalBBoxBack`/`modalBDiaNegBack`) and T's self-propagation arms (`modalTBoxSelf`/
`modalTDiaNegSelf`). Per `FrameRules.lean`'s layering decision, `modalApplyOneTB` wraps
`modalApplyOneB` (the inner layer, carrying the larger spec discharge) with the T self-arms
merged into the outer layer's `persistent` output.

## Main Definitions

- `modalStepBranchTB`/`modalExpandBranchesTB`/`modalTableauTB`: the TB-system analogues of
  `modalStepBranch`/`modalExpandBranches`/`modalTableau`, each the generic driver instantiated
  at `apply := modalApplyOneTB`.

## Main Results

- `modalApplyOneTB_spec : RuleApplicationSpec modalApplyOneTB`: the eleven-field structural
  discharge, mirroring `modalApplyOneB_spec` (`BDriver.lean`) and `modalApplyOneT_spec`
  (`TDriver.lean`). Every field is discharged by treating `modalApplyOneB`'s own result as an
  opaque witness satisfying `modalApplyOneB_spec` (rather than re-deriving B's contribution from
  `FrameRules.lean` primitives), and separately bounding the appended T self-conjunct via the
  same same-world-subformula argument `TDriver.lean` uses.
- `modalExpandBranchesTB_hintikka`: one-line instantiation of the generic top-loop Hintikka lemma
  at `(modalApplyOneTB, modalApplyOneTB_spec)`.

## Strategy

`modalApplyOneTB` agrees with `modalApplyOneB` outside the two T-relevant signed-formula shapes
(box-positive `T(□φ)@w`, diamond-negative `F(◇φ)@w`, `modalApplyOneTB_eq_of_not_boxPos_diaNeg`,
`FrameRules.lean`), so every `RuleApplicationSpec` field's "not shaped" case reduces directly to
`modalApplyOneB_spec`'s corresponding field. For the two T-relevant shapes, `modalApplyOneTB`
never mints a world (B's own accessibility output is reused unchanged, `modalApplyOneB_spec`'s
`freshLocal`/`boxPosNotExpanding`/`diaNegNotExpanding` rule out the `.linear`/`.branching` shapes
there) and only ever appends a single self-propagated formula (`modalTBoxSelf`/`modalTDiaNegSelf`)
at the *same* world, drawn from `modalSubfmls` of the source formula -- so each field's "shaped"
case combines `modalApplyOneB_spec`'s corresponding witness (applied to the same `sf`) with a
small direct argument for the appended self-conjunct, exactly as `TDriver.lean` combines K's
witness with the same self-conjunct argument.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## TB Driver Instantiation -/

/-- One-step branch expansion for the TB (reflexive-symmetric-frame) tableau: the generic driver
(`modalStepBranchGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneTB`
(`FrameRules.lean`). -/
def modalStepBranchTB
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneTB b e acc

/-- Fuel-based expansion of a list of TB-system branches: the generic driver
(`modalExpandBranchesGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneTB`. -/
def modalExpandBranchesTB
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneTB branches expandedSets accs fuel

/-- The TB-system (reflexive-symmetric-frame) modal tableau decision procedure: the generic
entry point (`modalTableauGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneTB`,
starting the signed tableau from `F(φ)` at world `0` (same fuel bound as K/T/B: TB never mints a
world outside the K `diamondPos`/`boxNeg` arms, so `modalFuel` is sufficient here too). -/
def modalTableauTB (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen modalApplyOneTB φ

/-! ## Shape Lemmas for the Two TB-Relevant Signed-Formula Shapes

Each lemma unfolds `modalApplyOneTB`'s one added layer over `modalApplyOneB`'s own (opaque)
result, mirroring `TDriver.lean`'s `modalApplyOneT_boxPos_fst`/`_snd` shape lemmas but with the
inner witness `modalApplyOneB` in place of `modalApplyOne`. -/

omit [Hashable Atom] in
/-- Direct unfolding of `modalApplyOneTB`'s `.fst` component at a box-positive shaped signed
formula, in terms of the underlying `modalApplyOneB` result. -/
lemma modalApplyOneTB_boxPos_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneTB (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOneB (⟨.pos, .box φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent bForms =>
            .persistent (bForms ++
              (modalTBoxSelf b φ w).filter (fun x => !(bForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTBoxSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneTB]
  cases (modalApplyOneB (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Direct unfolding of `modalApplyOneTB`'s `.snd` component at a box-positive shaped signed
formula: exactly `modalApplyOneB`'s own accessibility output. -/
lemma modalApplyOneTB_boxPos_snd
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneTB (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOneB (⟨.pos, .box φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneTB]
  cases (modalApplyOneB (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneTB_boxPos_fst` for the diamond-negative shape. -/
lemma modalApplyOneTB_diamondNeg_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneTB (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOneB (⟨.neg, .diamond φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent bForms =>
            .persistent (bForms ++
              (modalTDiaNegSelf b φ w).filter (fun x => !(bForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTDiaNegSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneTB]
  cases (modalApplyOneB (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneTB_boxPos_snd` for the diamond-negative shape. -/
lemma modalApplyOneTB_diamondNeg_snd
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneTB (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOneB (⟨.neg, .diamond φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneTB]
  cases (modalApplyOneB (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

/-! ## `modalTBoxSelf`/`modalTDiaNegSelf` Output Dichotomies

Local re-derivations of `TDriver.lean`'s `private lemma modalTBoxSelf_cases`/
`modalTDiaNegSelf_cases` (unavailable across files); proofs reproduced verbatim. -/

omit [Hashable Atom] in
/-- `modalTBoxSelf`'s output dichotomy: either empty, or the singleton self-propagated formula
`T(φ)@w`, in which case that formula was not already on the branch (from the `if`-guard). -/
private lemma modalTBoxSelf_cases_TB
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalTBoxSelf b φ w = [] ∨
      (modalTBoxSelf b φ w = [(⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)] ∧
        (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) := by
  simp only [modalTBoxSelf]
  split_ifs with h
  · left; rfl
  · right; exact ⟨rfl, by simpa using h⟩

omit [Hashable Atom] in
/-- Symmetric to `modalTBoxSelf_cases_TB` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_cases_TB
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalTDiaNegSelf b φ w = [] ∨
      (modalTDiaNegSelf b φ w = [(⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)] ∧
        (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) := by
  simp only [modalTDiaNegSelf]
  split_ifs with h
  · left; rfl
  · right; exact ⟨rfl, by simpa using h⟩

/-! ## Discharging `RuleApplicationSpec` for `modalApplyOneTB`

Phases 5-6 fill this section (F1-F7, then F8-F12 and the assembly). -/

end Cslib.Logic.Modal.Tableau

end
