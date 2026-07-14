/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Rules

/-! # Frame-Specific Modal Tableau Rules

This module adds the T-system (reflexive-frame) tableau rule on top of the modal K rules
(`Rules.lean`). Per the Strategy-B (closure-at-extraction) design: the T rule does **not**
need any accessibility edge to fire — it propagates `T(□φ)@w ⊢ T(φ)@w` and
`F(◇φ)@w ⊢ F(φ)@w` unconditionally at the *same* world `w`, justified purely by the frame
condition (`Std.Refl`) that will hold of the *extracted* model's relation, not by any edge
recorded in `acc`. This mirrors a self-loop `w → w` that reflexive closure (`Relation.ReflGen`)
adds "for free" at model-extraction time.

## Main Definitions

- `modalTBoxSelf`/`modalTDiaNegSelf`: the two T-specific propagation helpers (self-world,
  unconditional on `acc`).
- `modalApplyOneT`: apply the K rules (`modalApplyOne`) together with the T self-propagation
  arms, merging persistent-rule outputs. Reduces to `modalApplyOne` exactly outside the two
  T-relevant signed-formula shapes (`T(□φ)@w`, `F(◇φ)@w`).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## T-Specific Propagation Helpers -/

/-- The T self-propagation for box-positives: from `T(□φ)@w`, generate `T(φ)@w` (the *same*
world `w`, not a recorded successor), filtered to exclude formulas already on the branch.
Justified by the reflexivity of the extracted model's relation (Strategy B), not by any
`acc` edge. -/
def modalTBoxSelf (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w⟩
  if b.any (· == sf) then [] else [sf]

/-- The T self-propagation for diamond-negatives: from `F(◇φ)@w`, generate `F(φ)@w` (the
*same* world `w`), filtered to exclude formulas already on the branch. Dual of
`modalTBoxSelf`. -/
def modalTDiaNegSelf (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w⟩
  if b.any (· == sf) then [] else [sf]

/-! ## T-Augmented Rule Application -/

/-- Apply the K modal rules together with the T self-propagation arms. For the two
T-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`), the T self-propagation formulas are merged into
the K rule's `persistent` output (deduplicated); for every other signed-formula shape,
`modalApplyOneT` reduces to exactly `modalApplyOne` (the K rule dispatch), matching the
report's "no new worlds" claim: the T arms are pure `persistent` outputs at existing worlds,
never `linear`/`branching`. -/
def modalApplyOneT
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let selfNew := modalTBoxSelf b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ selfNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if selfNew.isEmpty then (.notApplicable, kAcc) else (.persistent selfNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let selfNew := modalTDiaNegSelf b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ selfNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if selfNew.isEmpty then (.notApplicable, kAcc) else (.persistent selfNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
/-- `modalApplyOneT` agrees with `modalApplyOne` outside the two T-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): the T arms never affect any other rule dispatch. -/
lemma modalApplyOneT_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneT sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneT
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

end Cslib.Logic.Modal.Tableau

end
