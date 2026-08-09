/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.GenericDriver
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.CompletenessLoop

/-! # T-System Tableau Driver

This module instantiates the generic tableau driver (`Saturation.lean`'s `modalStepBranchGen`/
`modalExpandBranchesGen`/`modalTableauGen`) with the T-augmented rule-application function
`modalApplyOneT` (`FrameRules.lean`), and discharges the structural-hypothesis bundle
`RuleApplicationSpec` (`GenericDriver.lean`) for it.

## Main Definitions

- `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT`: the T-system analogues of
  `modalStepBranch`/`modalExpandBranches`/`modalTableau`, each the generic driver instantiated
  at `apply := modalApplyOneT`.

## Main Results

- `modalApplyOneT_spec : RuleApplicationSpec modalApplyOneT`: `modalApplyOneT` satisfies the
  seven-field structural-hypothesis bundle, so the K-style FMP termination measure transports to
  the T driver via `GenericDriver.lean`'s `(apply, spec)`-bundled wrapper theorems.

## Strategy

`modalApplyOneT` agrees with `modalApplyOne` (K) outside the two T-relevant signed-formula shapes
(box-positive `T(□φ)@w`, diamond-negative `F(◇φ)@w`,
`modalApplyOneT_eq_of_not_boxPos_diaNeg`), so every `RuleApplicationSpec` field's "not shaped"
case reduces directly to the corresponding K witness (`GenericDriver.lean`'s `modalApplyOne_spec`
fields). For the two T-relevant shapes, `modalApplyOneT` never mints a world (its accessibility
output is exactly K's, unchanged: `modalApplyOne`'s own dispatch for these two shapes is always
`.notApplicable`/`.persistent`, never `.linear`/`.branching`, so `modalApplyOne_fresh_local`
forces the accessibility component to be unchanged) and only ever *appends* a single
self-propagated formula (`modalTBoxSelf`/`modalTDiaNegSelf`) at the *same* world, drawn from
`modalSubfmls` of the source formula -- so each field's "shaped" case combines the corresponding
K witness (applied to the same `sf`) with a small direct argument for the appended self-conjunct,
using `FmpMeasure.lean`'s downstream reuse helpers `modalUniverse_mem_of_sameWorld_subfml`/
`label_mem_modalKnownWorlds` for the catalog and known-worlds membership facts.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## T Driver Instantiation -/

/-- One-step branch expansion for the T (reflexive-frame) tableau: the generic driver
(`modalStepBranchGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneT`
(`FrameRules.lean`). -/
def modalStepBranchT
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneT b e acc

/-- Fuel-based expansion of a list of T-system branches: the generic driver
(`modalExpandBranchesGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneT`. -/
def modalExpandBranchesT
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneT branches expandedSets accs fuel

/-- The T-system (reflexive-frame) modal tableau decision procedure: the generic entry point
(`modalTableauGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneT`, starting the
signed tableau from `F(φ)` at world `0` (same fuel bound as K: T never mints a world outside the
K `diamondPos`/`boxNeg` arms, so `modalFuel` is sufficient here too). -/
def modalTableauT (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen modalApplyOneT φ

/-! ## Shape Lemmas for the Two T-Relevant Signed-Formula Shapes

The box-positive/diamond-negative shape dichotomies are the canonical, existentially-quantified
`modalApplyOne_boxPos_eq`/`_diamondNeg_eq` in `Rules.lean` (the K discharges for
`RuleApplicationSpec`'s F9/F10 fields), reached here via the `Rules → Saturation → Completeness →
FmpMeasure → GenericDriver → TDriver` import chain. -/

omit [Hashable Atom] in
/-- The accessibility component of `modalApplyOne` at a box-positive shaped signed formula is
always unchanged: combines `modalApplyOne_boxPos_eq` (`Rules.lean`, ruling out the `.linear`
shape `modalApplyOne_fresh_local` needs for a new edge) with `modalApplyOne_fresh_local` itself. -/
private lemma modalApplyOne_boxPos_acc_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc := by
  rcases modalApplyOne_fresh_local
      (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc with
    heq | ⟨wsf, rest, hfst, -⟩
  · exact heq
  · rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with h | ⟨_, h⟩ <;>
      rw [h] at hfst <;> simp at hfst

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOne_boxPos_acc_eq` for the diamond-negative shape. -/
private lemma modalApplyOne_diamondNeg_acc_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc := by
  rcases modalApplyOne_fresh_local
      (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc with
    heq | ⟨wsf, rest, hfst, -⟩
  · exact heq
  · rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with h | ⟨_, h⟩ <;>
      rw [h] at hfst <;> simp at hfst

omit [Hashable Atom] in
/-- `modalTBoxSelf`'s output dichotomy: either empty, or the singleton self-propagated formula
`T(φ)@w`, in which case that formula was not already on the branch (from the `if`-guard). -/
private lemma modalTBoxSelf_cases
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
/-- Symmetric to `modalTBoxSelf_cases` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_cases
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalTDiaNegSelf b φ w = [] ∨
      (modalTDiaNegSelf b φ w = [(⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)] ∧
        (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) := by
  simp only [modalTDiaNegSelf]
  split_ifs with h
  · left; rfl
  · right; exact ⟨rfl, by simpa using h⟩

omit [Hashable Atom] in
/-- Every formula `modalTBoxSelf` can emit is not already on the branch: direct corollary of
`modalTBoxSelf_cases`. -/
private lemma modalTBoxSelf_not_mem
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) : ∀ x ∈ modalTBoxSelf b φ w, x ∉ b := by
  rcases modalTBoxSelf_cases b φ w with h | ⟨h, hnot⟩
  · rw [h]; simp
  · rw [h]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnot

omit [Hashable Atom] in
/-- Symmetric to `modalTBoxSelf_not_mem` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_not_mem
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) : ∀ x ∈ modalTDiaNegSelf b φ w, x ∉ b := by
  rcases modalTDiaNegSelf_cases b φ w with h | ⟨h, hnot⟩
  · rw [h]; simp
  · rw [h]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnot

omit [Hashable Atom] in
/-- Direct unfolding of `modalApplyOneT`'s `.fst` component at a box-positive shaped signed
formula, in terms of the underlying `modalApplyOne` (K) result.

De-privatized so `FrameCompleteness.lean`'s T soundness discharge
(`modalApplyOneT_boxPos_soundIn`) can consume it directly. -/
lemma modalApplyOneT_boxPos_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.pos, .box φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalTBoxSelf b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTBoxSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Direct unfolding of `modalApplyOneT`'s `.snd` component at a box-positive shaped signed
formula: exactly K's own accessibility output (`modalApplyOneT` never touches `acc` for this
shape).

De-privatized for the same reason as `modalApplyOneT_boxPos_fst`. -/
lemma modalApplyOneT_boxPos_snd
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.pos, .box φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneT_boxPos_fst` for the diamond-negative shape. De-privatized
so `modalApplyOneT_diaNeg_soundIn` can consume it directly. -/
lemma modalApplyOneT_diamondNeg_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalTDiaNegSelf b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTDiaNegSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneT_boxPos_snd` for the diamond-negative shape. De-privatized
for the same reason as `modalApplyOneT_diamondNeg_fst`. -/
lemma modalApplyOneT_diamondNeg_snd
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

/-! ## Discharging `RuleApplicationSpec` for `modalApplyOneT` -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Repackage a negated disjunction of the two T-relevant shapes into the conjunction of
negations `modalApplyOneT_eq_of_not_boxPos_diaNeg` expects. Shared by every field's "not
shaped" case below. -/
private lemma not_shape_of_not_or {sf : SignedFormula (Proposition Atom) WorldIndex}
    (hshape : ¬ ((sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))) :
    ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
  ⟨fun h => hshape (Or.inl h), fun h => hshape (Or.inr h)⟩

omit [Hashable Atom] in
/-- **Field 1 (`freshLocal`)**: `modalApplyOneT` never mints a world outside the shared K
`diamondPos`/`boxNeg` arms. Outside the two T-relevant shapes this is exactly K's own
`modalApplyOne_fresh_local`; at the two T-relevant shapes, `modalApplyOneT` never touches `acc`
(`modalApplyOne_boxPos_acc_eq`/`modalApplyOne_diamondNeg_acc_eq`), so the left disjunct holds. -/
private lemma modalApplyOneT_freshLocal
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneT sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneT sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneT sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl (modalApplyOneT_boxPos_snd b acc φ w ▸ modalApplyOne_boxPos_acc_eq b acc φ w)
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl
        (modalApplyOneT_diamondNeg_snd b acc φ w ▸ modalApplyOne_diamondNeg_acc_eq b acc φ w)
  · rw [modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_fresh_local sf b acc

omit [Hashable Atom] in
/-- **Field 2 (`outputsSubsetUniverse`)**: every formula `modalApplyOneT sf b acc` can emit
stays inside `modalUniverse φ0`. Outside the two T-relevant shapes this is exactly K's own
`modalApplyOne_outputs_subset`; at the two T-relevant shapes, the emitted list is K's own
persistent output (already known to stay in the universe by K's field) merged with at most one
self-propagated formula at the *same* world, a subformula of the source (in the universe by
`modalUniverse_mem_of_sameWorld_subfml`). -/
private lemma modalApplyOneT_outputsSubsetUniverse
    (φ0 : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0) (hsf : sf ∈ b) (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    (match (modalApplyOneT sf b acc).fst with
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
      rw [modalApplyOneT_boxPos_fst]
      have hφ : φ ∈ modalSubfmls (Proposition.box φ) := by simp [modalSubfmls]
      have hself : ∀ x ∈ modalTBoxSelf b φ w, x ∈ modalUniverse φ0 := by
        rcases modalTBoxSelf_cases b φ w with h | ⟨h, -⟩
        · rw [h]; simp
        · rw [h]
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact modalUniverse_mem_of_sameWorld_subfml hb hsf hφ .pos
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hself
      · rw [hk]
        have hkforms : ∀ x ∈ kForms, x ∈ modalUniverse φ0 := by
          have hout := modalApplyOne_outputs_subset φ0
            (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
          rwa [hk] at hout
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hkforms x hx
        · exact hself x hx
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneT_diamondNeg_fst]
      have hφ : φ ∈ modalSubfmls (Proposition.diamond φ) := by simp [modalSubfmls]
      have hself : ∀ x ∈ modalTDiaNegSelf b φ w, x ∈ modalUniverse φ0 := by
        rcases modalTDiaNegSelf_cases b φ w with h | ⟨h, -⟩
        · rw [h]; simp
        · rw [h]
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact modalUniverse_mem_of_sameWorld_subfml hb hsf hφ .neg
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
          hk | ⟨kForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hself
      · rw [hk]
        have hkforms : ∀ x ∈ kForms, x ∈ modalUniverse φ0 := by
          have hout := modalApplyOne_outputs_subset φ0
            (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf
            hInv hW
          rwa [hk] at hout
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hkforms x hx
        · exact hself x hx
  · rw [modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_outputs_subset φ0 sf b acc hb hsf hInv hW

omit [Hashable Atom] in
/-- **Field 4 (`rankStep`)**: given `rank` satisfying the depth-bound/edge invariants pre-call,
`modalApplyOneT sf b acc` yields a `rank'` (agreeing with `rank` off `modalNextWorld b`)
satisfying the edge invariant on the (unchanged, at the two T-relevant shapes) accessibility
output and the depth bound on the emitted formulas. Outside the two T-relevant shapes this is
exactly K's own `modalApplyOne_rank_step`; at the two T-relevant shapes, reuses K's own `rank'`
witness (valid since `modalApplyOneT` never touches `acc` there) and separately bounds the
appended self-conjunct: it is a subformula of the source at the source's own world `w ≠
modalNextWorld b` (`modalNextWorld_gt`), so `rank' w = rank w` by agreement, and
`modalDepth φ < modalDepth (□φ) ≤ rank w` gives the bound. -/
private lemma modalApplyOneT_rankStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ w w', (modalApplyOneT sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (match (modalApplyOneT sf b acc).fst with
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
        modalApplyOne_rank_step (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
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
      · rw [modalApplyOneT_boxPos_snd]; exact hedge'
      · rw [modalApplyOneT_boxPos_fst]
        rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · intro x hx
            rcases modalTBoxSelf_cases b φ w with h | ⟨h, -⟩
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
          · rcases modalTBoxSelf_cases b φ w with h | ⟨h, -⟩
            · rw [h] at hx; simp at hx
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hφdepth
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      obtain ⟨rank', hagree, hedge', hdepth⟩ :=
        modalApplyOne_rank_step
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
      · rw [modalApplyOneT_diamondNeg_snd]; exact hedge'
      · rw [modalApplyOneT_diamondNeg_fst]
        rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
            hk | ⟨kForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · intro x hx
            rcases modalTDiaNegSelf_cases b φ w with h | ⟨h, -⟩
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
          · rcases modalTDiaNegSelf_cases b φ w with h | ⟨h, -⟩
            · rw [h] at hx; simp at hx
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hφdepth
  · rw [modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_rank_step sf b acc hsfmem hInv rank hbound hedge

omit [Hashable Atom] in
/-- **Field 5 (`outDegStep`)**: the out-degree/expanded-set correspondence transports across a
`modalApplyOneT sf b acc` call. Outside the two T-relevant shapes this is exactly K's own
`modalApplyOne_outDeg_step`; at the two T-relevant shapes, both possible result shapes
(`.notApplicable`/`.persistent`) map to the *same* right-hand side (`e`, unchanged) and the
accessibility output is unchanged, so the equation reduces directly to `houtdeg` regardless of
which of the two shapes actually fires. -/
private lemma modalApplyOneT_outDegStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ w, outDeg (modalApplyOneT sf b acc).snd w =
      (List.filter (fun x => x.label == w && isMintingShaped x)
        (match (modalApplyOneT sf b acc).fst with
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
      rw [modalApplyOneT_boxPos_snd, modalApplyOne_boxPos_acc_eq, modalApplyOneT_boxPos_fst]
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, wl⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
    · obtain ⟨s, form, wl⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneT_diamondNeg_snd, modalApplyOne_diamondNeg_acc_eq,
        modalApplyOneT_diamondNeg_fst]
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, wl⟩) rfl φ rfl b acc with
          hk | ⟨kForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
  · rw [modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_outDeg_step sf b e acc houtdeg w

omit [Hashable Atom] in
/-- **Field 6 (`knownWorldsStep`)**: the known-worlds dichotomy for a single `modalApplyOneT sf b
acc` call. Outside the two T-relevant shapes this is exactly K's own
`modalApplyOne_knownWorlds_step`; at the two T-relevant shapes, `modalApplyOneT` never touches
`acc`, so the left disjunct always holds, and the emitted list (K's own persistent output, when
present, merged with at most one self-propagated formula at the source's own -- hence known --
world) stays inside `modalKnownWorlds b` by K's own field (whose right disjunct is impossible
here, since its match evaluates to `False` on a `.persistent`/`.notApplicable` shape) combined
with `label_mem_modalKnownWorlds`. -/
private lemma modalApplyOneT_knownWorldsStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOneT sf b acc).snd = acc ∧
      (match (modalApplyOneT sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneT sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneT sf b acc).fst with
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
      · rw [modalApplyOneT_boxPos_snd]; exact modalApplyOne_boxPos_acc_eq b acc φ w
      · rw [modalApplyOneT_boxPos_fst]
        have hself : ∀ x ∈ modalTBoxSelf b φ w, x.label ∈ modalKnownWorlds b := by
          intro x hx
          rcases modalTBoxSelf_cases b φ w with h | ⟨h, -⟩
          · rw [h] at hx; simp at hx
          · rw [h] at hx
            simp only [List.mem_singleton] at hx
            subst hx
            exact label_mem_modalKnownWorlds
              (sf := (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) hsfmem
        rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
        · simp only [hk]
          split_ifs with hemp
          · trivial
          · exact hself
        · simp only [hk]
          have hK := modalApplyOne_knownWorlds_step
            (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
          rcases hK with ⟨-, hmatch⟩ | ⟨-, hfalse⟩
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
      · rw [modalApplyOneT_diamondNeg_snd]; exact modalApplyOne_diamondNeg_acc_eq b acc φ w
      · rw [modalApplyOneT_diamondNeg_fst]
        have hself : ∀ x ∈ modalTDiaNegSelf b φ w, x.label ∈ modalKnownWorlds b := by
          intro x hx
          rcases modalTDiaNegSelf_cases b φ w with h | ⟨h, -⟩
          · rw [h] at hx; simp at hx
          · rw [h] at hx
            simp only [List.mem_singleton] at hx
            subst hx
            exact label_mem_modalKnownWorlds
              (sf := (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) hsfmem
        rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
            hk | ⟨kForms, hk⟩
        · simp only [hk]
          split_ifs with hemp
          · trivial
          · exact hself
        · simp only [hk]
          have hK := modalApplyOne_knownWorlds_step
            (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem
            hknown
          rcases hK with ⟨-, hmatch⟩ | ⟨-, hfalse⟩
          · rw [hk] at hmatch
            intro x hx
            simp only [List.mem_append, List.mem_filter] at hx
            rcases hx with hx | ⟨hx, -⟩
            · exact hmatch x hx
            · exact hself x hx
          · rw [hk] at hfalse; exact hfalse.elim
  · rw [modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_knownWorlds_step sf b acc hsfmem hknown

/-! ## Discharging F8-F12 (the Hintikka/Saturation Chain Fields) -/

omit [Hashable Atom] in
/-- **F8 (`localShapeInvariance`)**: outside the two T-relevant shapes (guaranteed here, since
`φ` is neither box- nor diamond-shaped), `modalApplyOneT` agrees with `modalApplyOne` on both
calls (`modalApplyOneT_eq_of_not_boxPos_diaNeg`), so K's own `modalApplyOne_fst_eq_of_not_box`
transports directly. -/
private lemma modalApplyOneT_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOneT ⟨s, φ, w⟩ b acc).1 = (modalApplyOneT ⟨s, φ, w⟩ b' acc').1 := by
  have hnotshape : ∀ (b'' : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc'' : Accessibility),
      modalApplyOneT (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc''
        = modalApplyOne (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc'' := by
    intro b'' acc''
    apply modalApplyOneT_eq_of_not_boxPos_diaNeg
    refine ⟨?_, ?_⟩
    · rintro ⟨-, ψ, hform⟩; exact hnb ψ hform
    · rintro ⟨-, ψ, hform⟩; exact hnd ψ hform
  rw [hnotshape b acc, hnotshape b' acc']
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

omit [Hashable Atom] in
/-- **F9 (`boxPosNotExpanding`)**: `modalApplyOneT`'s box-positive dispatch
(`modalApplyOneT_boxPos_fst`) maps K's `.persistent kForms ↦ .persistent (kForms ++ selfNew...)`
and `.notApplicable ↦ .notApplicable | .persistent selfNew` -- **stays in the Propagating class**
either way, with a different (but still existentially-quantifiable) payload than K's. -/
private lemma modalApplyOneT_boxPosNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .pos)
    (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneT sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneT sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneT_boxPos_fst]
  rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- **F10 (`diaNegNotExpanding`)**: dual of F9 for the diamond-negative shape, via
`modalApplyOneT_diamondNeg_fst`. -/
private lemma modalApplyOneT_diaNegNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .neg)
    (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneT sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneT sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneT_diamondNeg_fst]
  rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
      hk | ⟨kForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- **F11 (`boxNegWitness`)**: `⟨.neg, .box ψ, w⟩` has sign `.neg`, so it misses T's
`.pos, .box` self-propagation arm entirely (`FrameRules.lean`'s dispatch only touches
`.pos, .box`/`.neg, .diamond`) -- `modalApplyOneT` agrees with `modalApplyOne` here
(`modalApplyOneT_eq_of_not_boxPos_diaNeg`), so K's own `modalApplyOne_boxNeg_witness`
transports directly. -/
private lemma modalApplyOneT_boxNegWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneT (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  have heq : modalApplyOneT
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOne (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneT_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩
  rw [heq]
  exact modalApplyOne_boxNeg_witness b acc ψ w

omit [Hashable Atom] in
/-- **F12 (`diaPosWitness`)**: dual of F11 -- `⟨.pos, .diamond ψ, w⟩` misses T's
`.neg, .diamond` self-propagation arm, so `modalApplyOneT` agrees with `modalApplyOne` here too. -/
private lemma modalApplyOneT_diaPosWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneT (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  have heq : modalApplyOneT
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOne (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc :=
    modalApplyOneT_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩
  rw [heq]
  exact modalApplyOne_diamondPos_witness b acc ψ w

/-- **`modalApplyOneT` satisfies `RuleApplicationSpec`**: the interface witness for the T
driver, combining the eleven fields
discharged above. This is the T-system analogue of `GenericDriver.lean`'s
`modalApplyOne_spec` (K), and unblocks reusing the K-style FMP termination measure
(`FmpMeasure.lean`/`GenericDriver.lean`) and the generic Hintikka/saturation chain
(`CompletenessLoop.lean`) for `modalTableauT` via the `(apply, spec)`-bundled wrapper
theorems. Adding F8-F12 here is what makes `modalExpandBranchesT_hintikka` (below) a one-liner. -/
theorem modalApplyOneT_spec : RuleApplicationSpec (Atom := Atom) modalApplyOneT where
  freshLocal := modalApplyOneT_freshLocal
  outputsSubsetUniverse := modalApplyOneT_outputsSubsetUniverse
  persistentFresh := modalApplyOneT_persistentFresh
  rankStep := modalApplyOneT_rankStep
  outDegStep := modalApplyOneT_outDegStep
  knownWorldsStep := modalApplyOneT_knownWorldsStep
  branchingLength := modalApplyOneT_branchingLength
  localShapeInvariance := modalApplyOneT_localShapeInvariance
  boxPosNotExpanding := modalApplyOneT_boxPosNotExpanding
  diaNegNotExpanding := modalApplyOneT_diaNegNotExpanding
  boxNegWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOneT_boxNegWitness b acc ψ w).1,
      (modalApplyOneT_boxNegWitness b acc ψ w).2⟩
  diaPosWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOneT_diaPosWitness b acc ψ w).1,
      (modalApplyOneT_diaPosWitness b acc ψ w).2⟩

/-! ## T Instantiation of the Generic Hintikka/Saturation Chain -/

/-- `modalStepBranchT` is exactly `modalStepBranchGen modalApplyOneT` -- true `rfl`, since
`modalStepBranchT` is *defined* as that instantiation (`TDriver.lean:67-72`). -/
theorem modalStepBranchT_eq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchT b e acc = modalStepBranchGen modalApplyOneT b e acc := rfl

/-- `modalExpandBranchesT` is exactly `modalExpandBranchesGen modalApplyOneT` -- true `rfl`. -/
theorem modalExpandBranchesT_eq
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesT branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOneT branches expandedSets accs fuel := rfl

/-- `modalTableauT` is exactly `modalTableauGen modalApplyOneT` -- true `rfl`. -/
theorem modalTableauT_eq (φ : Proposition Atom) :
    modalTableauT φ = modalTableauGen modalApplyOneT φ := rfl

/-- **`modalExpandBranchesT_hintikka`**: the T-system instantiation of the generic top-loop
Hintikka lemma
(`modalExpandBranchesGen_hintikka`, `CompletenessLoop.lean`), concluding in
`modalHintikkaSetGen modalApplyOneT bR aR`.

**This is a genuine one-liner** -- direct application of `modalExpandBranchesGen_hintikka` at
`modalApplyOneT` and `modalApplyOneT_spec.toAt φ0` (`RuleApplicationSpec.toAt`,
`GenericDriver.lean`), with no T-specific proof content whatsoever. This
typechecks as a one-liner only because (a) F9/F10
(`GenericDriver.lean`) are stated with the existentially-quantified `∃ out` payload rather than
K's concrete `boxPropagation` shape, and (b) the crux `modalExpandBranchesGen_hintikka`
concludes in the generic `modalHintikkaSetGen apply bR aR` rather than the concrete
`modalHintikkaSet bR aR`. Had either criterion not held, T's own `.persistent
(kForms ++ selfNew.filter …)` payload (`modalApplyOneT_boxPos_fst` above) could not unify with a
K-shaped field, and this theorem would fail to elaborate -- forcing a T-specific re-derivation
that would reproduce the ~850-line duplication this generic infrastructure exists to eliminate. -/
theorem modalExpandBranchesT_hintikka (φ0 : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ∃ rank, ModalLoopInvGen modalApplyOneT φ0 bi ei ai rank) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesT branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen modalApplyOneT bR aR :=
  modalExpandBranchesGen_hintikka modalApplyOneT φ0 (modalApplyOneT_spec.toAt φ0) fuel

end Cslib.Logic.Modal.Tableau

end
