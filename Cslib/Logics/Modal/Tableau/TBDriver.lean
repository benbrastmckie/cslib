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
  at `modalApplyOneTB` and `modalApplyOneTB_spec.toAt φ0`.

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

Every field is discharged by treating `modalApplyOneB`'s own result as an opaque witness
satisfying `modalApplyOneB_spec` (`BDriver.lean`) -- rather than re-deriving B's contribution
from `FrameRules.lean` primitives -- and separately bounding the appended T self-conjunct via
the same same-world-subformula argument `TDriver.lean` uses for its own T self-conjunct. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Repackage a negated disjunction of the two T-relevant shapes into the conjunction of
negations `modalApplyOneTB_eq_of_not_boxPos_diaNeg` expects. Shared by every field's "not
shaped" case below. -/
private lemma not_shape_of_not_or_TB {sf : SignedFormula (Proposition Atom) WorldIndex}
    (hshape : ¬ ((sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))) :
    ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
  ⟨fun h => hshape (Or.inl h), fun h => hshape (Or.inr h)⟩

/-- The accessibility component of `modalApplyOneB` at a box-positive shaped signed formula is
always unchanged: combines `modalApplyOneB_spec.freshLocal` (ruling out the `.linear` shape via
`modalApplyOneB_spec.boxPosNotExpanding`, which forces `.notApplicable`/`.persistent`) with
`modalApplyOneB_spec.freshLocal` itself. Local analogue of `TDriver.lean`'s `private lemma
modalApplyOne_boxPos_acc_eq`/`BDriver.lean`'s `modalApplyOne_boxPos_acc_eq_B`, one layer up. -/
private lemma modalApplyOneB_boxPos_acc_eq_TB
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc := by
  rcases modalApplyOneB_spec.freshLocal
      (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc with
    heq | ⟨wsf, rest, hfst, -⟩
  · exact heq
  · rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with
      h | ⟨_, h⟩ <;> rw [h] at hfst <;> simp at hfst

/-- Symmetric to `modalApplyOneB_boxPos_acc_eq_TB` for the diamond-negative shape. -/
private lemma modalApplyOneB_diamondNeg_acc_eq_TB
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc := by
  rcases modalApplyOneB_spec.freshLocal
      (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc with
    heq | ⟨wsf, rest, hfst, -⟩
  · exact heq
  · rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
      h | ⟨_, h⟩ <;> rw [h] at hfst <;> simp at hfst

/-- **Field 1 (`freshLocal`)**: `modalApplyOneTB` never mints a world outside the shared K
`diamondPos`/`boxNeg` arms (inherited unchanged through `modalApplyOneB_spec`). Outside the two
T-relevant shapes this is exactly `modalApplyOneB_spec.freshLocal`; at the two T-relevant shapes,
`modalApplyOneTB` never touches `acc`
(`modalApplyOneB_boxPos_acc_eq_TB`/`modalApplyOneB_diamondNeg_acc_eq_TB`), so the left disjunct
holds. -/
private lemma modalApplyOneTB_freshLocal
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneTB sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneTB sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneTB sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl
        (modalApplyOneTB_boxPos_snd b acc φ w ▸ modalApplyOneB_boxPos_acc_eq_TB b acc φ w)
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl
        (modalApplyOneTB_diamondNeg_snd b acc φ w ▸
          modalApplyOneB_diamondNeg_acc_eq_TB b acc φ w)
  · rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_TB hshape)]
    exact modalApplyOneB_spec.freshLocal sf b acc

/-- **Field 2 (`outputsSubsetUniverse`)**: every formula `modalApplyOneTB sf b acc` can emit
stays inside `modalUniverse φ0`. Outside the two T-relevant shapes this is exactly
`modalApplyOneB_spec.outputsSubsetUniverse`; at the two T-relevant shapes, the emitted list is
`modalApplyOneB`'s own persistent output (already known to stay in the universe by
`modalApplyOneB_spec`'s field) merged with at most one self-propagated formula at the *same*
world, a subformula of the source (in the universe by `modalUniverse_mem_of_sameWorld_subfml`). -/
private lemma modalApplyOneTB_outputsSubsetUniverse
    (φ0 : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0) (hsf : sf ∈ b) (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    (match (modalApplyOneTB sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
      | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse φ0
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
      | .notApplicable => True) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_boxPos_fst]
      have hφ : φ ∈ modalSubfmls (Proposition.box φ) := by simp [modalSubfmls]
      have hself : ∀ x ∈ modalTBoxSelf b φ w, x ∈ modalUniverse φ0 := by
        rcases modalTBoxSelf_cases_TB b φ w with h | ⟨h, -⟩
        · rw [h]; simp
        · rw [h]
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact modalUniverse_mem_of_sameWorld_subfml hb hsf hφ .pos
      rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hself
      · rw [hk]
        have hbforms : ∀ x ∈ bForms, x ∈ modalUniverse φ0 := by
          have hout := modalApplyOneB_spec.outputsSubsetUniverse φ0
            (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
          rwa [hk] at hout
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hbforms x hx
        · exact hself x hx
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_diamondNeg_fst]
      have hφ : φ ∈ modalSubfmls (Proposition.diamond φ) := by simp [modalSubfmls]
      have hself : ∀ x ∈ modalTDiaNegSelf b φ w, x ∈ modalUniverse φ0 := by
        rcases modalTDiaNegSelf_cases_TB b φ w with h | ⟨h, -⟩
        · rw [h]; simp
        · rw [h]
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact modalUniverse_mem_of_sameWorld_subfml hb hsf hφ .neg
      rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hself
      · rw [hk]
        have hbforms : ∀ x ∈ bForms, x ∈ modalUniverse φ0 := by
          have hout := modalApplyOneB_spec.outputsSubsetUniverse φ0
            (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf
            hInv hW
          rwa [hk] at hout
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hbforms x hx
        · exact hself x hx
  · rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_TB hshape)]
    exact modalApplyOneB_spec.outputsSubsetUniverse φ0 sf b acc hb hsf hInv hW

omit [Hashable Atom] in
/-- Every formula `modalTBoxSelf` can emit is not already on the branch: local re-derivation of
`TDriver.lean`'s `private lemma modalTBoxSelf_not_mem`. -/
private lemma modalTBoxSelf_not_mem_TB
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) : ∀ x ∈ modalTBoxSelf b φ w, x ∉ b := by
  rcases modalTBoxSelf_cases_TB b φ w with h | ⟨h, hnot⟩
  · rw [h]; simp
  · rw [h]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnot

omit [Hashable Atom] in
/-- Symmetric to `modalTBoxSelf_not_mem_TB` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_not_mem_TB
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) : ∀ x ∈ modalTDiaNegSelf b φ w, x ∉ b := by
  rcases modalTDiaNegSelf_cases_TB b φ w with h | ⟨h, hnot⟩
  · rw [h]; simp
  · rw [h]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnot

/-- **Field 3 (`persistentFresh`)**. -/
private lemma modalApplyOneTB_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hpers : (modalApplyOneTB sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_boxPos_fst] at hpers
      rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · simp only [hk] at hpers
        split_ifs at hpers with hemp
        simp only [RuleResult.persistent.injEq] at hpers
        refine ⟨?_, fun x hx => ?_⟩
        · rw [← hpers]; intro hcontra; exact hemp (by simp [hcontra])
        · rw [← hpers] at hx; exact modalTBoxSelf_not_mem_TB b φ w x hx
      · rw [hk] at hpers
        simp only [RuleResult.persistent.injEq] at hpers
        obtain ⟨hbne, hball⟩ := modalApplyOneB_spec.persistentFresh
          (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc bForms hk
        refine ⟨?_, ?_⟩
        · intro hcontra
          rw [← hpers] at hcontra
          exact hbne (List.append_eq_nil_iff.mp hcontra).1
        · intro x hx
          rw [← hpers] at hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hball x hx
          · exact modalTBoxSelf_not_mem_TB b φ w x hx
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_diamondNeg_fst] at hpers
      rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · simp only [hk] at hpers
        split_ifs at hpers with hemp
        simp only [RuleResult.persistent.injEq] at hpers
        refine ⟨?_, fun x hx => ?_⟩
        · rw [← hpers]; intro hcontra; exact hemp (by simp [hcontra])
        · rw [← hpers] at hx; exact modalTDiaNegSelf_not_mem_TB b φ w x hx
      · rw [hk] at hpers
        simp only [RuleResult.persistent.injEq] at hpers
        obtain ⟨hbne, hball⟩ := modalApplyOneB_spec.persistentFresh
          (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc bForms hk
        refine ⟨?_, ?_⟩
        · intro hcontra
          rw [← hpers] at hcontra
          exact hbne (List.append_eq_nil_iff.mp hcontra).1
        · intro x hx
          rw [← hpers] at hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hball x hx
          · exact modalTDiaNegSelf_not_mem_TB b φ w x hx
  · rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_TB hshape)] at hpers
    exact modalApplyOneB_spec.persistentFresh sf b acc nf hpers

/-- **Field 4 (`rankStep`)**: the highest-risk field per the implementation plan's risk table --
discharged first among F4-F7. Reuses `modalApplyOneB_spec`'s own `rank'` witness (valid since
`modalApplyOneTB` never touches `acc` at the two T-relevant shapes, `modalApplyOneTB_boxPos_snd`/
`_diamondNeg_snd`) and separately bounds the appended self-conjunct: it is a subformula of the
source at the source's own world `w ≠ modalNextWorld b` (`modalNextWorld_gt`), so `rank' w = rank
w` by agreement, and `modalDepth φ < modalDepth (□φ) ≤ rank w` gives the bound -- exactly
`TDriver.lean`'s own argument, transported one layer up onto `modalApplyOneB_spec.rankStep`. -/
private lemma modalApplyOneTB_rankStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ w w', (modalApplyOneTB sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (match (modalApplyOneTB sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
        | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
        | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
        | .notApplicable => True) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      obtain ⟨rank', hagree, hedge', hdepth⟩ :=
        modalApplyOneB_spec.rankStep
          (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc hsfmem hInv rank hbound hedge
      have hwlt : w < modalNextWorld b :=
        modalNextWorld_gt b (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          hsfmem
      have hragree : rank' w = rank w := hagree w (Nat.ne_of_lt hwlt)
      have hφdepth : modalDepth φ ≤ rank' w := by
        have hbw : modalDepth (Proposition.box φ) ≤ rank w := hbound _ hsfmem
        simp only [modalDepth] at hbw
        omega
      refine ⟨rank', hagree, ?_, ?_⟩
      · rw [modalApplyOneTB_boxPos_snd]; exact hedge'
      · rw [modalApplyOneTB_boxPos_fst]
        rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with
            hk | ⟨bForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · intro x hx
            rcases modalTBoxSelf_cases_TB b φ w with h | ⟨h, -⟩
            · rw [h] at hemp; simp at hemp
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hφdepth
        · simp only [hk] at hdepth ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hdepth x hx
          · rcases modalTBoxSelf_cases_TB b φ w with h | ⟨h, -⟩
            · rw [h] at hx; simp at hx
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hφdepth
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      obtain ⟨rank', hagree, hedge', hdepth⟩ :=
        modalApplyOneB_spec.rankStep
          (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc hsfmem hInv rank hbound hedge
      have hwlt : w < modalNextWorld b :=
        modalNextWorld_gt b (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          hsfmem
      have hragree : rank' w = rank w := hagree w (Nat.ne_of_lt hwlt)
      have hφdepth : modalDepth φ ≤ rank' w := by
        have hbw : modalDepth (Proposition.diamond φ) ≤ rank w := hbound _ hsfmem
        simp only [modalDepth] at hbw
        omega
      refine ⟨rank', hagree, ?_, ?_⟩
      · rw [modalApplyOneTB_diamondNeg_snd]; exact hedge'
      · rw [modalApplyOneTB_diamondNeg_fst]
        rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
            hk | ⟨bForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · intro x hx
            rcases modalTDiaNegSelf_cases_TB b φ w with h | ⟨h, -⟩
            · rw [h] at hemp; simp at hemp
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hφdepth
        · simp only [hk] at hdepth ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hdepth x hx
          · rcases modalTDiaNegSelf_cases_TB b φ w with h | ⟨h, -⟩
            · rw [h] at hx; simp at hx
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hφdepth
  · rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_TB hshape)]
    exact modalApplyOneB_spec.rankStep sf b acc hsfmem hInv rank hbound hedge

/-- **Field 5 (`outDegStep`)**. -/
private lemma modalApplyOneTB_outDegStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ w, outDeg (modalApplyOneTB sf b acc).snd w =
      (List.filter (fun x => x.label == w && isMintingShaped x)
        (match (modalApplyOneTB sf b acc).fst with
          | .linear _ => e ++ [sf]
          | .branching _ => e ++ [sf]
          | .persistent _ => e
          | .notApplicable =>
            (e : List (SignedFormula (Proposition Atom) WorldIndex)))).length := by
  intro w
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, wl⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_boxPos_snd, modalApplyOneB_boxPos_acc_eq_TB, modalApplyOneTB_boxPos_fst]
      rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box φ, wl⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
    · obtain ⟨s, form, wl⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_diamondNeg_snd, modalApplyOneB_diamondNeg_acc_eq_TB,
        modalApplyOneTB_diamondNeg_fst]
      rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond φ, wl⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
  · rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_TB hshape)]
    exact modalApplyOneB_spec.outDegStep sf b e acc houtdeg w

/-- **Field 6 (`knownWorldsStep`)**: `modalApplyOneTB` never touches `acc`, so the left disjunct
always holds at the two T-relevant shapes, and the emitted list (`modalApplyOneB`'s own persistent
output, when present, merged with at most one self-propagated formula at the source's own --
hence known -- world) stays inside `modalKnownWorlds b` by `modalApplyOneB_spec`'s own field
combined with `label_mem_modalKnownWorlds`. -/
private lemma modalApplyOneTB_knownWorldsStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOneTB sf b acc).snd = acc ∧
      (match (modalApplyOneTB sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneTB sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneTB sf b acc).fst with
        | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
        | .branching _ => False
        | .persistent _ => False
        | .notApplicable => False)) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      left
      refine ⟨?_, ?_⟩
      · rw [modalApplyOneTB_boxPos_snd]; exact modalApplyOneB_boxPos_acc_eq_TB b acc φ w
      · rw [modalApplyOneTB_boxPos_fst]
        have hself : ∀ x ∈ modalTBoxSelf b φ w, x.label ∈ modalKnownWorlds b := by
          intro x hx
          rcases modalTBoxSelf_cases_TB b φ w with h | ⟨h, -⟩
          · rw [h] at hx; simp at hx
          · rw [h] at hx
            simp only [List.mem_singleton] at hx
            subst hx
            exact label_mem_modalKnownWorlds
              (sf := (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) hsfmem
        rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with
            hk | ⟨bForms, hk⟩
        · simp only [hk]
          split_ifs with hemp
          · trivial
          · exact hself
        · simp only [hk]
          have hB := modalApplyOneB_spec.knownWorldsStep
            (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
          rcases hB with ⟨-, hmatch⟩ | ⟨-, hfalse⟩
          · rw [hk] at hmatch
            intro x hx
            simp only [List.mem_append, List.mem_filter] at hx
            rcases hx with hx | ⟨hx, -⟩
            · exact hmatch x hx
            · exact hself x hx
          · rw [hk] at hfalse; exact hfalse.elim
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      left
      refine ⟨?_, ?_⟩
      · rw [modalApplyOneTB_diamondNeg_snd]; exact modalApplyOneB_diamondNeg_acc_eq_TB b acc φ w
      · rw [modalApplyOneTB_diamondNeg_fst]
        have hself : ∀ x ∈ modalTDiaNegSelf b φ w, x.label ∈ modalKnownWorlds b := by
          intro x hx
          rcases modalTDiaNegSelf_cases_TB b φ w with h | ⟨h, -⟩
          · rw [h] at hx; simp at hx
          · rw [h] at hx
            simp only [List.mem_singleton] at hx
            subst hx
            exact label_mem_modalKnownWorlds
              (sf := (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) hsfmem
        rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
            hk | ⟨bForms, hk⟩
        · simp only [hk]
          split_ifs with hemp
          · trivial
          · exact hself
        · simp only [hk]
          have hB := modalApplyOneB_spec.knownWorldsStep
            (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem
            hknown
          rcases hB with ⟨-, hmatch⟩ | ⟨-, hfalse⟩
          · rw [hk] at hmatch
            intro x hx
            simp only [List.mem_append, List.mem_filter] at hx
            rcases hx with hx | ⟨hx, -⟩
            · exact hmatch x hx
            · exact hself x hx
          · rw [hk] at hfalse; exact hfalse.elim
  · rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_TB hshape)]
    exact modalApplyOneB_spec.knownWorldsStep sf b acc hsfmem hknown

/-- **Field 7 (`branchingLength`)**: `modalApplyOneTB` never produces a `.branching` result at
either T-relevant shape (`modalApplyOneB_spec.boxPosNotExpanding`/`diaNegNotExpanding` force
`.notApplicable`/`.persistent`, and the outer T self-merge preserves that dichotomy), so the
shaped case is vacuous; the "not shaped" case reduces directly to
`modalApplyOneB_spec.branchingLength`. -/
private lemma modalApplyOneTB_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hbr : (modalApplyOneTB sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · exfalso
    rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_boxPos_fst] at hbr
      rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · simp only [hk] at hbr
        split_ifs at hbr
      · simp only [hk] at hbr
        simp at hbr
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneTB_diamondNeg_fst] at hbr
      rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
          hk | ⟨bForms, hk⟩
      · simp only [hk] at hbr
        split_ifs at hbr
      · simp only [hk] at hbr
        simp at hbr
  · rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_TB hshape)] at hbr
    exact modalApplyOneB_spec.branchingLength sf b acc brs hbr

/-! ## Discharging F8-F12 (the Hintikka/Saturation Chain Fields) -/

/-- **F8 (`localShapeInvariance`)**: outside the two T-relevant shapes (guaranteed here, since
`φ` is neither box- nor diamond-shaped), `modalApplyOneTB` agrees with `modalApplyOneB` on both
calls (`modalApplyOneTB_eq_of_not_boxPos_diaNeg`), so `modalApplyOneB_spec`'s own field
transports directly. -/
private lemma modalApplyOneTB_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOneTB ⟨s, φ, w⟩ b acc).1 = (modalApplyOneTB ⟨s, φ, w⟩ b' acc').1 := by
  have hnotshape : ∀ (b'' : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc'' : Accessibility),
      modalApplyOneTB (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc''
        = modalApplyOneB (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc'' := by
    intro b'' acc''
    apply modalApplyOneTB_eq_of_not_boxPos_diaNeg
    refine ⟨?_, ?_⟩
    · rintro ⟨-, ψ, hform⟩; exact hnb ψ hform
    · rintro ⟨-, ψ, hform⟩; exact hnd ψ hform
  rw [hnotshape b acc, hnotshape b' acc']
  exact modalApplyOneB_spec.localShapeInvariance s φ w hnb hnd b b' acc acc'

/-- **F9 (`boxPosNotExpanding`)**: `modalApplyOneTB`'s box-positive dispatch
(`modalApplyOneTB_boxPos_fst`) maps `modalApplyOneB`'s `.persistent bForms ↦ .persistent (bForms
++ selfNew...)` and `.notApplicable ↦ .notApplicable | .persistent selfNew` -- stays in the
Propagating class either way. -/
private lemma modalApplyOneTB_boxPosNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .pos)
    (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneTB sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneTB sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneTB_boxPos_fst]
  rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with
      hk | ⟨bForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

/-- **F10 (`diaNegNotExpanding`)**: dual of F9 for the diamond-negative shape, via
`modalApplyOneTB_diamondNeg_fst`. -/
private lemma modalApplyOneTB_diaNegNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .neg)
    (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneTB sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneTB sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneTB_diamondNeg_fst]
  rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
      hk | ⟨bForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

/-- **F11' (`boxNegWitness'`)**: `⟨.neg, .box ψ, w⟩` misses both TB-relevant shapes (it is
neither `.pos, .box` nor `.neg, .diamond`), so `modalApplyOneTB` agrees with `modalApplyOneB`
here (`modalApplyOneTB_eq_of_not_boxPos_diaNeg`), and `modalApplyOneB_spec`'s own existential
witness field transports directly -- K's own two mint arms, inherited unchanged through both
layers. -/
private lemma modalApplyOneTB_boxNegWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneTB (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneTB (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  have heq : modalApplyOneTB
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneB (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneTB_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩
  rw [heq]
  exact modalApplyOneB_spec.boxNegWitness' b acc ψ w

/-- **F12' (`diaPosWitness'`)**: dual of F11'. -/
private lemma modalApplyOneTB_diaPosWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneTB (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneTB (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  have heq : modalApplyOneTB
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneB (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc :=
    modalApplyOneTB_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩
  rw [heq]
  exact modalApplyOneB_spec.diaPosWitness' b acc ψ w

/-- **`modalApplyOneTB` satisfies `RuleApplicationSpec`**: the interface witness for the TB
driver, combining the eleven fields discharged above. This is the TB-system analogue of
`BDriver.lean`'s `modalApplyOneB_spec` and `TDriver.lean`'s `modalApplyOneT_spec`, and unblocks
reusing the K-style FMP termination measure and the generic Hintikka/saturation chain for
`modalTableauTB` via the `(apply, spec)`-bundled wrapper theorems. This is the **full**
`RuleApplicationSpec`, not `RuleApplicationSpecCore` -- TB is a Tier A corner, and a Core-only
discharge would silently move it to Tier B. -/
theorem modalApplyOneTB_spec : RuleApplicationSpec (Atom := Atom) modalApplyOneTB where
  freshLocal := modalApplyOneTB_freshLocal
  outputsSubsetUniverse := modalApplyOneTB_outputsSubsetUniverse
  persistentFresh := modalApplyOneTB_persistentFresh
  rankStep := modalApplyOneTB_rankStep
  outDegStep := modalApplyOneTB_outDegStep
  knownWorldsStep := modalApplyOneTB_knownWorldsStep
  branchingLength := modalApplyOneTB_branchingLength
  localShapeInvariance := modalApplyOneTB_localShapeInvariance
  boxPosNotExpanding := modalApplyOneTB_boxPosNotExpanding
  diaNegNotExpanding := modalApplyOneTB_diaNegNotExpanding
  boxNegWitness' := modalApplyOneTB_boxNegWitness'
  diaPosWitness' := modalApplyOneTB_diaPosWitness'

/-! ## TB Instantiation of the Generic Hintikka/Saturation Chain -/

/-- `modalStepBranchTB` is exactly `modalStepBranchGen modalApplyOneTB` -- true `rfl`. -/
theorem modalStepBranchTB_eq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchTB b e acc = modalStepBranchGen modalApplyOneTB b e acc := rfl

/-- `modalExpandBranchesTB` is exactly `modalExpandBranchesGen modalApplyOneTB` -- true `rfl`. -/
theorem modalExpandBranchesTB_eq
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesTB branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOneTB branches expandedSets accs fuel := rfl

/-- `modalTableauTB` is exactly `modalTableauGen modalApplyOneTB` -- true `rfl`. -/
theorem modalTableauTB_eq (φ : Proposition Atom) :
    modalTableauTB φ = modalTableauGen modalApplyOneTB φ := rfl

/-- **`modalExpandBranchesTB_hintikka`**: the TB-system instantiation of the generic top-loop
Hintikka lemma (`modalExpandBranchesGen_hintikka`, `CompletenessLoop.lean`), concluding in
`modalHintikkaSetGen modalApplyOneTB bR aR`. A genuine one-liner, exactly as
`modalExpandBranchesT_hintikka`/`modalExpandBranchesB_hintikka` were: direct application of
`modalExpandBranchesGen_hintikka` at `modalApplyOneTB` and `modalApplyOneTB_spec.toAt φ0`
(`RuleApplicationSpec.toAt`, `GenericDriver.lean`), with no TB-specific proof content
whatsoever. -/
theorem modalExpandBranchesTB_hintikka (φ0 : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ∃ rank, ModalLoopInvGen modalApplyOneTB φ0 bi ei ai rank) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesTB branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen modalApplyOneTB bR aR :=
  modalExpandBranchesGen_hintikka modalApplyOneTB φ0 (modalApplyOneTB_spec.toAt φ0) fuel

/-! ## Reuse Confirmation: `accSourcesKnown`/`accTargetsKnown` Top-Loop Propagation

`accSourcesKnown` (`BDriver.lean:841`), `modalStepBranchGen_preserves_accSourcesKnown`
(`BDriver.lean:860`), `modalExpandBranchesGen_openBranch_accSourcesKnown` (`BDriver.lean:1071`),
and `modalExpandBranchesGen_openBranch_accTargetsKnown` (`BDriver.lean:1100`) are all
parameterised on an arbitrary `apply : RuleApply Atom` together with its own `freshLocal`
witness -- they consume `modalApplyOneTB_spec.freshLocal` at the TB completeness call site
(`FrameCompleteness.lean`, Phase 10) with zero new proof content here. Confirmed, not
re-derived: TB's predecessor-reading arms are exactly B's (`modalApplyOneTB` wraps
`modalApplyOneB` verbatim for the backward-propagation family), and neither generic lemma
inspects `apply` beyond the `freshLocal` shape hypothesis both `modalApplyOneB_spec` and
`modalApplyOneTB_spec` already discharge. -/

end Cslib.Logic.Modal.Tableau

end
