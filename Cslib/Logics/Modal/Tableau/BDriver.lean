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

/-! # B-System Tableau Driver

This module instantiates the generic tableau driver (`Saturation.lean`'s `modalStepBranchGen`/
`modalExpandBranchesGen`/`modalTableauGen`) with the B-augmented rule-application function
`modalApplyOneB` (`FrameRules.lean`), and discharges the structural-hypothesis bundle
`RuleApplicationSpec` (`GenericDriver.lean`) for it.

## Main Definitions

- `modalStepBranchB`/`modalExpandBranchesB`/`modalTableauB`: the B-system analogues of
  `modalStepBranch`/`modalExpandBranches`/`modalTableau`, each the generic driver instantiated
  at `apply := modalApplyOneB`.
- `accSourcesKnown`: a new bookkeeping invariant (the "twin" of `FmpMeasure.lean`'s
  `accTargetsKnown`), asserting every `acc`-edge *source* is a known world of `b`. Needed
  because B's backward-propagation rule emits at predecessor worlds -- *sources* of recorded
  edges -- rather than at `sf.label` itself (T's self-loop) or at *targets* of recorded edges
  (S4's forward 4-rule), so `accTargetsKnown` alone does not place them. Preserved by
  `modalStepBranchGen apply` exactly as `accTargetsKnown` is (same `freshLocal`-driven argument),
  and consumed by `FrameCompleteness.lean`'s B truth-lemma bridges to show
  `modalBBoxBack`/`modalBDiaNegBack`'s known-worlds filter (`FrameRules.lean`) never excludes a
  genuine predecessor reachable by a real derivation.

## Main Results

- `modalApplyOneB_spec : RuleApplicationSpec modalApplyOneB`: the eleven-field structural
  discharge, mirroring `modalApplyOneT_spec` (`TDriver.lean`). The backward-propagation arms
  (`modalBBoxBack`/`modalBDiaNegBack`) never mint a world and their emitted formulas' labels are
  bounded via `accFreshInv` (fields 2/4) and already known by filter-construction (field 6, no
  extra invariant needed there) -- so the discharge pattern matches T/S5 exactly, as
  `GenericDriver.lean`'s module docstring anticipates for B.
- `modalExpandBranchesB_hintikka`: one-line instantiation of the generic top-loop Hintikka lemma
  at `modalApplyOneB` and `modalApplyOneB_spec.toAt φ0`.

## Strategy

`modalApplyOneB` agrees with `modalApplyOne` (K) outside the two B-relevant signed-formula shapes
(box-positive `T(□φ)@w`, diamond-negative `F(◇φ)@w`, `modalApplyOneB_eq_of_not_boxPos_diaNeg`),
so every `RuleApplicationSpec` field's "not shaped" case reduces directly to the corresponding K
witness. For the two B-relevant shapes, `modalApplyOneB` never mints a world (its accessibility
output is exactly K's, unchanged) and only ever appends backward-propagated formulas at
*predecessor* worlds drawn from `acc`'s recorded edges -- bounded via `accFreshInv` (catalog
membership, rank) and pre-filtered to known worlds by construction (the known-worlds field).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## B Driver Instantiation -/

/-- One-step branch expansion for the B (symmetric-frame) tableau: the generic driver
(`modalStepBranchGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneB`
(`FrameRules.lean`). -/
def modalStepBranchB
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneB b e acc

/-- Fuel-based expansion of a list of B-system branches: the generic driver
(`modalExpandBranchesGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneB`. -/
def modalExpandBranchesB
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneB branches expandedSets accs fuel

/-- The B-system (symmetric-frame) modal tableau decision procedure: the generic entry point
(`modalTableauGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneB`, starting the
signed tableau from `F(φ)` at world `0` (same fuel bound as K: B never mints a world outside the
K `diamondPos`/`boxNeg` arms, so `modalFuel` is sufficient here too). -/
def modalTableauB (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen modalApplyOneB φ

/-! ## Shape Lemmas for the Two B-Relevant Signed-Formula Shapes -/

omit [Hashable Atom] in
/-- The accessibility component of `modalApplyOne` at a box-positive shaped signed formula is
always unchanged. Local re-derivation of `TDriver.lean`'s `private lemma
modalApplyOne_boxPos_acc_eq` (unavailable across files); proof reproduced verbatim. -/
private lemma modalApplyOne_boxPos_acc_eq_B
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
/-- Symmetric to `modalApplyOne_boxPos_acc_eq_B` for the diamond-negative shape. -/
private lemma modalApplyOne_diamondNeg_acc_eq_B
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
/-- Direct unfolding of `modalApplyOneB`'s `.fst` component at a box-positive shaped signed
formula, in terms of the underlying `modalApplyOne` (K) result. Kept public (unlike
`TDriver.lean`'s analogous `private` lemma) so `FrameCompleteness.lean`'s B truth-lemma bridges
can consume it directly without re-derivation. -/
lemma modalApplyOneB_boxPos_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.pos, .box φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalBBoxBack b acc φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalBBoxBack b acc φ w).isEmpty then .notApplicable
            else .persistent (modalBBoxBack b acc φ w)
          | other => other) := by
  simp only [modalApplyOneB]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Direct unfolding of `modalApplyOneB`'s `.snd` component at a box-positive shaped signed
formula: exactly K's own accessibility output. -/
lemma modalApplyOneB_boxPos_snd
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.pos, .box φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneB]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneB_boxPos_fst` for the diamond-negative shape. -/
lemma modalApplyOneB_diamondNeg_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalBDiaNegBack b acc φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalBDiaNegBack b acc φ w).isEmpty then .notApplicable
            else .persistent (modalBDiaNegBack b acc φ w)
          | other => other) := by
  simp only [modalApplyOneB]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneB_boxPos_snd` for the diamond-negative shape. -/
lemma modalApplyOneB_diamondNeg_snd
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneB]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

/-! ## Local Universe-Membership Helpers (Cross-World Variants)

`FmpMeasure.lean`'s `mem_modalUniverse_of`/`modalUniverse_mem_formula`/`modalUniverse_mem_label`/
`modalSubfmls_trans`/`modalUniverse_mem_of_sameWorld_subfml` are all `private`, and the last is
additionally pinned to the *same* world as the source formula (T/S4's shape). B's backward
propagation emits at a *different* (predecessor) world, so this section re-derives the small
constructor/extractor lemmas needed for a cross-world catalog-membership argument, driven by
`accFreshInv`'s numeric bound instead of a known-worlds membership fact. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Cross-world catalog membership: a signed formula `⟨s, ψ, v⟩` is in `U(φ0)` provided `ψ` is a
subformula of some `sf.formula` with `sf ∈ b ⊆ U(φ0)`, and `v` is bounded by `modalWorldBound
φ0` -- independent of `v` being `sf.label` (unlike `modalUniverse_mem_of_sameWorld_subfml`). -/
private lemma modalUniverse_mem_of_predWorld_subfml {φ0 : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    {sf : SignedFormula (Proposition Atom) WorldIndex} (hsf : sf ∈ b)
    {ψ : Proposition Atom} (hψ : ψ ∈ modalSubfmls sf.formula) (s : Sign)
    {v : WorldIndex} (hv : v ≤ modalWorldBound φ0) :
    (⟨s, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverse φ0 :=
  mem_modalUniverse_of hv (modalSubfmls_trans hψ (modalUniverse_mem_formula (hb sf hsf)))

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every `modalBPredecessorsOf`/`modalBBoxBack`/`modalBDiaNegBack`-relevant predecessor `v` of
`w` (i.e. `acc.hasEdge v w = true`) is bounded by `modalWorldBound φ0`, given `accFreshInv b acc`
and `modalMaxWorld b < modalWorldBound φ0`: `v < modalNextWorld b = modalMaxWorld b + 1 ≤
modalWorldBound φ0`. No known-worlds fact is needed here (unlike field 6 below), only the
numeric `accFreshInv` bound. -/
private lemma pred_label_le_worldBound {φ0 : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (hInv : accFreshInv b acc) (hW : modalMaxWorld b < modalWorldBound φ0)
    {v w : WorldIndex} (hedge : acc.hasEdge v w = true) : v ≤ modalWorldBound φ0 :=
  Nat.le_of_lt (Nat.lt_of_lt_of_le (hInv v w hedge).1 hW)

/-! ## Discharging `RuleApplicationSpec` for `modalApplyOneB` -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Repackage a negated disjunction of the two B-relevant shapes into the conjunction of
negations `modalApplyOneB_eq_of_not_boxPos_diaNeg` expects. Shared by every field's "not shaped"
case below. -/
private lemma not_shape_of_not_or_B {sf : SignedFormula (Proposition Atom) WorldIndex}
    (hshape : ¬ ((sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))) :
    ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
  ⟨fun h => hshape (Or.inl h), fun h => hshape (Or.inr h)⟩

omit [Hashable Atom] in
/-- **Field 1 (`freshLocal`)**. -/
private lemma modalApplyOneB_freshLocal
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneB sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneB sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneB sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl (modalApplyOneB_boxPos_snd b acc φ w ▸ modalApplyOne_boxPos_acc_eq_B b acc φ w)
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl
        (modalApplyOneB_diamondNeg_snd b acc φ w ▸ modalApplyOne_diamondNeg_acc_eq_B b acc φ w)
  · rw [modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_B hshape)]
    exact modalApplyOne_fresh_local sf b acc

omit [Hashable Atom] in
/-- **Field 2 (`outputsSubsetUniverse`)**. -/
private lemma modalApplyOneB_outputsSubsetUniverse
    (φ0 : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0) (hsf : sf ∈ b) (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    (match (modalApplyOneB sf b acc).fst with
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
      rw [modalApplyOneB_boxPos_fst]
      have hφ : φ ∈ modalSubfmls (Proposition.box φ) := by simp [modalSubfmls]
      have hback : ∀ x ∈ modalBBoxBack b acc φ w, x ∈ modalUniverse φ0 := by
        intro x hx
        obtain ⟨hxeq, hpred, -, -⟩ := modalBBoxBack_mem hx
        have hvle : x.label ≤ modalWorldBound φ0 :=
          pred_label_le_worldBound hInv hW (modalBPredecessorsOf_hasEdge hpred)
        rw [hxeq]
        exact modalUniverse_mem_of_predWorld_subfml hb hsf hφ .pos hvle
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hback
      · rw [hk]
        have hkforms : ∀ x ∈ kForms, x ∈ modalUniverse φ0 := by
          have hout := modalApplyOne_outputs_subset φ0
            (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
          rwa [hk] at hout
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hkforms x hx
        · exact hback x hx
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneB_diamondNeg_fst]
      have hφ : φ ∈ modalSubfmls (Proposition.diamond φ) := by simp [modalSubfmls]
      have hback : ∀ x ∈ modalBDiaNegBack b acc φ w, x ∈ modalUniverse φ0 := by
        intro x hx
        obtain ⟨hxeq, hpred, -, -⟩ := modalBDiaNegBack_mem hx
        have hvle : x.label ≤ modalWorldBound φ0 :=
          pred_label_le_worldBound hInv hW (modalBPredecessorsOf_hasEdge hpred)
        rw [hxeq]
        exact modalUniverse_mem_of_predWorld_subfml hb hsf hφ .neg hvle
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
          hk | ⟨kForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hback
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
        · exact hback x hx
  · rw [modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_B hshape)]
    exact modalApplyOne_outputs_subset φ0 sf b acc hb hsf hInv hW

omit [Hashable Atom] in
/-- **Field 3 (`persistentFresh`)**. -/
private lemma modalApplyOneB_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hpers : (modalApplyOneB sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneB_boxPos_fst] at hpers
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
      · simp only [hk] at hpers
        split_ifs at hpers with hemp
        simp only [RuleResult.persistent.injEq] at hpers
        refine ⟨?_, fun x hx => ?_⟩
        · rw [← hpers]; intro hcontra; exact hemp (by simp [hcontra])
        · rw [← hpers] at hx; exact (modalBBoxBack_mem hx).2.2.2
      · rw [hk] at hpers
        simp only [RuleResult.persistent.injEq] at hpers
        obtain ⟨hkne, hkall⟩ := modalApplyOne_persistent_props
          (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc kForms hk
        refine ⟨?_, ?_⟩
        · intro hcontra
          rw [← hpers] at hcontra
          exact hkne (List.append_eq_nil_iff.mp hcontra).1
        · intro x hx
          rw [← hpers] at hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hkall x hx
          · exact (modalBBoxBack_mem hx).2.2.2
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneB_diamondNeg_fst] at hpers
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
          hk | ⟨kForms, hk⟩
      · simp only [hk] at hpers
        split_ifs at hpers with hemp
        simp only [RuleResult.persistent.injEq] at hpers
        refine ⟨?_, fun x hx => ?_⟩
        · rw [← hpers]; intro hcontra; exact hemp (by simp [hcontra])
        · rw [← hpers] at hx; exact (modalBDiaNegBack_mem hx).2.2.2
      · rw [hk] at hpers
        simp only [RuleResult.persistent.injEq] at hpers
        obtain ⟨hkne, hkall⟩ := modalApplyOne_persistent_props
          (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc kForms hk
        refine ⟨?_, ?_⟩
        · intro hcontra
          rw [← hpers] at hcontra
          exact hkne (List.append_eq_nil_iff.mp hcontra).1
        · intro x hx
          rw [← hpers] at hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hkall x hx
          · exact (modalBDiaNegBack_mem hx).2.2.2
  · rw [modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_B hshape)] at hpers
    exact modalApplyOne_persistent_props sf b acc nf hpers

omit [Hashable Atom] in
/-- **Field 4 (`rankStep`)**: reuses K's own `rank'` witness (valid since `modalApplyOneB` never
touches `acc` at the two B-relevant shapes) and separately bounds the backward-propagated
formulas using `accFreshInv` + `hedge` directly: for a predecessor `v` of `w`
(`acc.hasEdge v w`), `hedge` gives `rank v = rank w + 1`, and `hbound` gives
`modalDepth φ + 1 ≤ rank w`, so `modalDepth φ ≤ rank w < rank v`. No known-worlds fact is
needed (unlike field 6). -/
private lemma modalApplyOneB_rankStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ w w', (modalApplyOneB sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (match (modalApplyOneB sf b acc).fst with
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
      have hback : ∀ x ∈ modalBBoxBack b acc φ w, modalDepth x.formula ≤ rank' x.label := by
        intro x hx
        obtain ⟨hxeq, hpred, -, -⟩ := modalBBoxBack_mem hx
        have hvw : acc.hasEdge x.label w = true := modalBPredecessorsOf_hasEdge hpred
        have hvlt : x.label < modalNextWorld b := (hInv x.label w hvw).1
        have hvagree : rank' x.label = rank x.label := hagree x.label (Nat.ne_of_lt hvlt)
        have hstep : rank w + 1 = rank x.label := hedge x.label w hvw
        have hbw : modalDepth (Proposition.box φ) ≤ rank w := hbound _ hsfmem
        simp only [modalDepth] at hbw
        rw [hxeq]
        simp only
        omega
      refine ⟨rank', hagree, ?_, ?_⟩
      · rw [modalApplyOneB_boxPos_snd]; exact hedge'
      · rw [modalApplyOneB_boxPos_fst]
        rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · exact hback
        · simp only [hk] at hdepth ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hdepth x hx
          · exact hback x hx
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
      have hback : ∀ x ∈ modalBDiaNegBack b acc φ w, modalDepth x.formula ≤ rank' x.label := by
        intro x hx
        obtain ⟨hxeq, hpred, -, -⟩ := modalBDiaNegBack_mem hx
        have hvw : acc.hasEdge x.label w = true := modalBPredecessorsOf_hasEdge hpred
        have hvlt : x.label < modalNextWorld b := (hInv x.label w hvw).1
        have hvagree : rank' x.label = rank x.label := hagree x.label (Nat.ne_of_lt hvlt)
        have hstep : rank w + 1 = rank x.label := hedge x.label w hvw
        have hbw : modalDepth (Proposition.diamond φ) ≤ rank w := hbound _ hsfmem
        simp only [modalDepth] at hbw
        rw [hxeq]
        simp only
        omega
      refine ⟨rank', hagree, ?_, ?_⟩
      · rw [modalApplyOneB_diamondNeg_snd]; exact hedge'
      · rw [modalApplyOneB_diamondNeg_fst]
        rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
            hk | ⟨kForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · exact hback
        · simp only [hk] at hdepth ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hdepth x hx
          · exact hback x hx
  · rw [modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_B hshape)]
    exact modalApplyOne_rank_step sf b acc hsfmem hInv rank hbound hedge

omit [Hashable Atom] in
/-- **Field 5 (`outDegStep`)**. -/
private lemma modalApplyOneB_outDegStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ w, outDeg (modalApplyOneB sf b acc).snd w =
      (List.filter (fun x => x.label == w && isMintingShaped x)
        (match (modalApplyOneB sf b acc).fst with
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
      rw [modalApplyOneB_boxPos_snd, modalApplyOne_boxPos_acc_eq_B, modalApplyOneB_boxPos_fst]
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, wl⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
    · obtain ⟨s, form, wl⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneB_diamondNeg_snd, modalApplyOne_diamondNeg_acc_eq_B,
        modalApplyOneB_diamondNeg_fst]
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, wl⟩) rfl φ rfl b acc with
          hk | ⟨kForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
  · rw [modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_B hshape)]
    exact modalApplyOne_outDeg_step sf b e acc houtdeg w

omit [Hashable Atom] in
/-- **Field 6 (`knownWorldsStep`)**: the known-worlds membership for backward-propagated
formulas comes directly from `modalBBoxBack`/`modalBDiaNegBack`'s own known-worlds filter
(`FrameRules.lean`) -- no extra invariant is needed, unlike field 4's numeric bound. This is
exactly why the filter is baked into the rule definitions rather than left as a side
condition. -/
private lemma modalApplyOneB_knownWorldsStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOneB sf b acc).snd = acc ∧
      (match (modalApplyOneB sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneB sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneB sf b acc).fst with
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
      · rw [modalApplyOneB_boxPos_snd]; exact modalApplyOne_boxPos_acc_eq_B b acc φ w
      · rw [modalApplyOneB_boxPos_fst]
        have hback : ∀ x ∈ modalBBoxBack b acc φ w, x.label ∈ modalKnownWorlds b :=
          fun x hx => (modalBBoxBack_mem hx).2.2.1
        rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
        · simp only [hk]
          split_ifs with hemp
          · trivial
          · exact hback
        · simp only [hk]
          have hK := modalApplyOne_knownWorlds_step
            (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
          rcases hK with ⟨-, hmatch⟩ | ⟨-, hfalse⟩
          · rw [hk] at hmatch
            intro x hx
            simp only [List.mem_append, List.mem_filter] at hx
            rcases hx with hx | ⟨hx, -⟩
            · exact hmatch x hx
            · exact hback x hx
          · rw [hk] at hfalse; exact hfalse.elim
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      left
      refine ⟨?_, ?_⟩
      · rw [modalApplyOneB_diamondNeg_snd]; exact modalApplyOne_diamondNeg_acc_eq_B b acc φ w
      · rw [modalApplyOneB_diamondNeg_fst]
        have hback : ∀ x ∈ modalBDiaNegBack b acc φ w, x.label ∈ modalKnownWorlds b :=
          fun x hx => (modalBDiaNegBack_mem hx).2.2.1
        rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
            hk | ⟨kForms, hk⟩
        · simp only [hk]
          split_ifs with hemp
          · trivial
          · exact hback
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
            · exact hback x hx
          · rw [hk] at hfalse; exact hfalse.elim
  · rw [modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_B hshape)]
    exact modalApplyOne_knownWorlds_step sf b acc hsfmem hknown

omit [Hashable Atom] in
/-- **Field 7 (`branchingLength`)**. -/
private lemma modalApplyOneB_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hbr : (modalApplyOneB sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · exfalso
    rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneB_boxPos_fst] at hbr
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
      · simp only [hk] at hbr
        split_ifs at hbr
      · simp only [hk] at hbr
        simp at hbr
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneB_diamondNeg_fst] at hbr
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩) rfl φ rfl b acc with
          hk | ⟨kForms, hk⟩
      · simp only [hk] at hbr
        split_ifs at hbr
      · simp only [hk] at hbr
        simp at hbr
  · rw [modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or_B hshape)] at hbr
    exact modalApplyOne_branching_length sf b acc brs hbr

/-! ## Discharging F8-F12 (the Hintikka/saturation chain fields) -/

omit [Hashable Atom] in
/-- **F8 (`localShapeInvariance`)**. -/
private lemma modalApplyOneB_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOneB ⟨s, φ, w⟩ b acc).1 = (modalApplyOneB ⟨s, φ, w⟩ b' acc').1 := by
  have hnotshape : ∀ (b'' : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc'' : Accessibility),
      modalApplyOneB (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc''
        = modalApplyOne (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc'' := by
    intro b'' acc''
    apply modalApplyOneB_eq_of_not_boxPos_diaNeg
    refine ⟨?_, ?_⟩
    · rintro ⟨-, ψ, hform⟩; exact hnb ψ hform
    · rintro ⟨-, ψ, hform⟩; exact hnd ψ hform
  rw [hnotshape b acc, hnotshape b' acc']
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

omit [Hashable Atom] in
/-- **F9 (`boxPosNotExpanding`)**. -/
private lemma modalApplyOneB_boxPosNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .pos)
    (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneB sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneB sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneB_boxPos_fst]
  rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- **F10 (`diaNegNotExpanding`)**. -/
private lemma modalApplyOneB_diaNegNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .neg)
    (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneB sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneB sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneB_diamondNeg_fst]
  rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
      hk | ⟨kForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- **F11 (`boxNegWitness`)**: `⟨.neg, .box ψ, w⟩` misses B's `.pos, .box` backward arm
entirely, so `modalApplyOneB` agrees with `modalApplyOne` here. -/
private lemma modalApplyOneB_boxNegWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneB (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  have heq : modalApplyOneB
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOne (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneB_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩
  rw [heq]
  exact modalApplyOne_boxNeg_witness b acc ψ w

omit [Hashable Atom] in
/-- **F12 (`diaPosWitness`)**: dual of F11. -/
private lemma modalApplyOneB_diaPosWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneB (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneB (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  have heq : modalApplyOneB
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOne (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc :=
    modalApplyOneB_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩
  rw [heq]
  exact modalApplyOne_diamondPos_witness b acc ψ w

/-- **`modalApplyOneB` satisfies `RuleApplicationSpec`**: the interface witness for the B
driver, combining the eleven fields discharged above. This is the B-system analogue of
`GenericDriver.lean`'s `modalApplyOne_spec` (K) and `TDriver.lean`'s `modalApplyOneT_spec` (T),
and unblocks reusing the K-style FMP termination measure and the generic Hintikka/saturation
chain for `modalTableauB` via the `(apply, spec)`-bundled wrapper theorems. -/
theorem modalApplyOneB_spec : RuleApplicationSpec (Atom := Atom) modalApplyOneB where
  freshLocal := modalApplyOneB_freshLocal
  outputsSubsetUniverse := modalApplyOneB_outputsSubsetUniverse
  persistentFresh := modalApplyOneB_persistentFresh
  rankStep := modalApplyOneB_rankStep
  outDegStep := modalApplyOneB_outDegStep
  knownWorldsStep := modalApplyOneB_knownWorldsStep
  branchingLength := modalApplyOneB_branchingLength
  localShapeInvariance := modalApplyOneB_localShapeInvariance
  boxPosNotExpanding := modalApplyOneB_boxPosNotExpanding
  diaNegNotExpanding := modalApplyOneB_diaNegNotExpanding
  boxNegWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOneB_boxNegWitness b acc ψ w).1,
      (modalApplyOneB_boxNegWitness b acc ψ w).2⟩
  diaPosWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOneB_diaPosWitness b acc ψ w).1,
      (modalApplyOneB_diaPosWitness b acc ψ w).2⟩

/-! ## B Instantiation of the Generic Hintikka/Saturation Chain -/

/-- `modalStepBranchB` is exactly `modalStepBranchGen modalApplyOneB` -- true `rfl`. -/
theorem modalStepBranchB_eq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchB b e acc = modalStepBranchGen modalApplyOneB b e acc := rfl

/-- `modalExpandBranchesB` is exactly `modalExpandBranchesGen modalApplyOneB` -- true `rfl`. -/
theorem modalExpandBranchesB_eq
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesB branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOneB branches expandedSets accs fuel := rfl

/-- `modalTableauB` is exactly `modalTableauGen modalApplyOneB` -- true `rfl`. -/
theorem modalTableauB_eq (φ : Proposition Atom) :
    modalTableauB φ = modalTableauGen modalApplyOneB φ := rfl

/-- **`modalExpandBranchesB_hintikka`**: the B-system instantiation of the generic top-loop
Hintikka lemma (`modalExpandBranchesGen_hintikka`, `CompletenessLoop.lean`), concluding in
`modalHintikkaSetGen modalApplyOneB bR aR`. A one-liner, exactly as `modalExpandBranchesT_hintikka`
was for T: direct application of `modalExpandBranchesGen_hintikka` at `modalApplyOneB` and
`modalApplyOneB_spec.toAt φ0` (`RuleApplicationSpec.toAt`, `GenericDriver.lean`), with no
B-specific proof content whatsoever. -/
theorem modalExpandBranchesB_hintikka (φ0 : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ∃ rank, ModalLoopInvGen modalApplyOneB φ0 bi ei ai rank) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesB branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen modalApplyOneB bR aR :=
  modalExpandBranchesGen_hintikka modalApplyOneB φ0 (modalApplyOneB_spec.toAt φ0) fuel

/-! ## `accSourcesKnown`: The Source-Side Twin of `accTargetsKnown`

B's backward-propagation arms emit at predecessor worlds -- *sources* of recorded `acc` edges.
`FmpMeasure.lean`'s `accTargetsKnown` bounds only edge *targets*, so the B completeness bridge
(`FrameCompleteness.lean`) needs the companion source-side fact: every edge source is a known
world of the branch. Proved by the same `RuleApplicationSpec.freshLocal`-driven argument as
`accTargetsKnown`'s own preservation lemma (`modalStepBranch_preserves_accTargetsKnown_gen`,
`FmpMeasure.lean`), reproduced here since that lemma's supporting `private` helpers
(`modalKnownWorlds_mono_append`, `mem_modalKnownWorlds`, `hasEdge_addEdge_cases`) are
unavailable across files. -/

/-- Every `acc`-edge *source* is a known world of `b`. The source-side twin of
`FmpMeasure.lean`'s `accTargetsKnown` (which bounds only edge *targets*). -/
def accSourcesKnown (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∀ w w', acc.hasEdge w w' → w ∈ modalKnownWorlds b

omit [DecidableEq Atom] [Hashable Atom] in
/-- `accSourcesKnown` holds trivially for the empty accessibility relation. -/
lemma accSourcesKnown_empty
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    accSourcesKnown b Accessibility.empty := by
  intro w w' hedge
  simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
  exact absurd hedge (by decide)

/-- **Single-step preservation of `accSourcesKnown`**: mirrors `FmpMeasure.lean`'s
`modalStepBranch_preserves_accTargetsKnown_gen` but for edge *sources*. Simpler than the
target-side proof for the new-edge case: the new edge's source is always `sf.label` for
`sf ∈ b` (`RuleApplicationSpec.freshLocal`'s own shape), hence known via
`label_mem_modalKnownWorlds` directly (no need to track the freshly-minted witness formula's
membership in the child branch, unlike the target-side argument). -/
theorem modalStepBranchGen_preserves_accSourcesKnown
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hknown : accSourcesKnown b acc) :
    ∀ b' ∈ newBs, accSourcesKnown b' newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hbsub : ∀ b' ∈ newBs, ∀ x ∈ modalKnownWorlds b, x ∈ modalKnownWorlds b' := by
    rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact modalKnownWorlds_mono_append nf b
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      obtain ⟨br, -, rfl⟩ := List.mem_map.mp hb'
      exact modalKnownWorlds_mono_append br b
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact modalKnownWorlds_mono_append nf b
    · rw [hfstc] at hsf; simp at hsf
  have hnewAcc : newAcc = (apply sf b acc).snd := by
    rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp at hsf
  intro b' hb' w w' hedge
  rw [hnewAcc] at hedge
  rcases hFreshLocal sf b acc with hsame | ⟨wsf, rest, hfst, hsnd⟩
  · rw [hsame] at hedge
    exact hbsub b' hb' w (hknown w w' hedge)
  · rw [hsnd] at hedge
    rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
    · exact hbsub b' hb' sf.label (label_mem_modalKnownWorlds hsfmem)
    · exact hbsub b' hb' w (hknown w w' hold)

/-! ## Generic Top-Loop Propagation

Generalizes the double induction below over an arbitrary step-preserved per-`(branch, acc)`
predicate `P` -- its body is predicate-agnostic (it never inspects `accSourcesKnown` beyond
threading it through as a hypothesis), so instantiating at `accSourcesKnown` re-derives the
original B theorem byte-for-byte, and instantiating at `FmpMeasure.lean`'s `accTargetsKnown`
supplies the generic `openBranch_accTargetsKnown` lemma `modalOpenBranchS5_countermodel`
requires as its `hTgt` argument (`FrameCompleteness.lean`). -/

/-- **Generic top-loop propagation**: mirrors `CompletenessLoop.lean`'s
`modalExpandBranchesGen_openBranch_initial_mem`'s double induction (outer on `fuel`, inner on
the pending worklist), threading an ABSTRACT per-`(branch, acc)`-pair invariant `P` (via
`List.zip`) rather than a single fixed formula's membership or a hardcoded concrete predicate,
updated at each step by the supplied single-step preservation hypothesis `hPresP`. -/
theorem modalExpandBranchesGen_openBranch_gen
    (apply : RuleApply Atom)
    (P : List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop)
    (hPresP : ∀ (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
        (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (newAcc : Accessibility),
      modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc) →
      P b acc → ∀ b' ∈ newBs, P b' newAcc)
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, P p.1 p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        P bR aR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs _hlen _hlenA hAll bR aR h
    simp only [modalExpandBranchesGen] at h
    cases hfs : (branches.zip accs).findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | none => simp only [hfs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨pb, pa⟩ := p
      simp only [hfs] at h
      injection h with hp1 hp2
      obtain ⟨q, hqmem, hf⟩ := List.exists_of_findSome?_eq_some hfs
      obtain ⟨qb, qa⟩ := q
      simp only [] at hf
      by_cases hcl : isModalClosed qb = true
      · rw [if_pos hcl] at hf
        exact absurd hf (by simp)
      · rw [if_neg hcl] at hf
        have hqp : (qb, qa) = (pb, pa) := Option.some.inj hf
        have hqfst : qb = bR := by
          have hh : qb = pb := congrArg Prod.fst hqp
          rw [hh]; exact hp1
        have hqsnd : qa = aR := by
          have hh : qa = pa := congrArg Prod.snd hqp
          rw [hh]; exact hp2
        rw [hqfst, hqsnd] at hqmem
        exact hAll (bR, aR) hqmem
  | succ fuel' ih =>
    intro branches expandedSets accs hlen hlenA hAll bR aR h
    simp only [modalExpandBranchesGen] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        (∀ p ∈ pending.zip pendingAccs, P p.1 p.2) →
        (∀ p ∈ done.zip doneAccs, P p.1 p.2) →
        modalExpandBranchesGen.processNext apply fuel' pending pendingExp pendingAccs done doneExp
            doneAccs = .openBranch bR aR →
        P bR aR from
      key branches expandedSets accs [] [] [] hlen hlenA rfl rfl hAll (by simp)
        (by simpa [modalExpandBranchesGen] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs done doneExp doneAccs _ _ _ _ _ _ hinner
      simp [modalExpandBranchesGen.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hlength_p hlenP_accs hdlength hdAccs hAll_p hAll_d hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength_p hlenP_accs
          simp only [modalExpandBranchesGen.processNext] at hinner
          have hah : P bh a := hAll_p (bh, a) (by simp)
          by_cases hcl : isModalClosed bh = true
          · rw [if_pos hcl] at hinner
            have hAll_bt : ∀ p ∈ bt.zip restAs, P p.1 p.2 := fun p hp =>
              hAll_p p (List.mem_cons_of_mem _ hp)
            have hAll_done_bh : ∀ p ∈ (done ++ [bh]).zip (doneAccs ++ [a]),
                P p.1 p.2 := by
              rw [List.zip_append hdAccs.symm]
              intro p hp
              simp only [List.mem_append, List.zip_cons_cons, List.zip_nil_right,
                List.mem_singleton] at hp
              rcases hp with hp | hp
              · exact hAll_d p hp
              · subst hp; exact hah
            exact ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
              hlength_p hlenP_accs (by simp [hdlength]) (by simp [hdAccs])
              hAll_bt hAll_done_bh hinner
          · simp only [Bool.not_eq_true] at hcl
            rw [if_neg (by simp [hcl])] at hinner
            cases hstep : modalStepBranchGen apply bh e a with
            | none =>
              rw [hstep] at hinner
              have hbeq : bh = bR ∧ a = aR := by cases hinner; exact ⟨rfl, rfl⟩
              rw [← hbeq.1, ← hbeq.2]; exact hah
            | some step =>
              obtain ⟨newBs, newExps, newAcc⟩ := step
              rw [hstep] at hinner
              have hNewBs_known : ∀ b' ∈ newBs, P b' newAcc :=
                hPresP bh e a newBs newExps newAcc hstep hah
              have hLenNBE : newExps.length = newBs.length := by
                obtain ⟨newExp, hEq⟩ :=
                  modalStepBranchGen_newExps_const apply bh e a newBs newExps newAcc hstep
                simp [hEq]
              have hAll_new : ∀ p ∈ (done ++ newBs ++ bt).zip
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs),
                  P p.1 p.2 := by
                rw [List.zip_append (by simp [hdAccs]), List.zip_append hdAccs.symm]
                intro p hp
                simp only [List.mem_append] at hp
                rcases hp with (hp | hp) | hp
                · exact hAll_d p hp
                · have hp' : p ∈ newBs.zip (List.replicate newBs.length newAcc) := hp
                  rw [List.zip_eq_zipWith] at hp'
                  simp only [List.mem_iff_getElem] at hp'
                  obtain ⟨n, hn, hpe⟩ := hp'
                  have hn' : n < newBs.length := by
                    simpa [List.length_zipWith, List.length_replicate] using hn
                  have : p = (newBs[n], newAcc) := by
                    simp only [List.getElem_zipWith, List.getElem_replicate] at hpe
                    rw [← hpe]
                  rw [this]
                  exact hNewBs_known _ (List.getElem_mem hn')
                · exact hAll_p p (List.mem_cons_of_mem _ hp)
              exact ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                (by simp [hdlength, hlength_p, hLenNBE])
                (by simp [hdAccs, hlenP_accs])
                hAll_new bR aR hinner

/-- **Top-loop propagation of `accSourcesKnown`** -- zero-regression re-derivation from the
generic form above at `P := accSourcesKnown`,
`hPresP := modalStepBranchGen_preserves_accSourcesKnown apply hFreshLocal`. Exact name and
statement unchanged from the pre-generalization version. -/
theorem modalExpandBranchesGen_openBranch_accSourcesKnown
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, accSourcesKnown p.1 p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        accSourcesKnown bR aR :=
  modalExpandBranchesGen_openBranch_gen apply accSourcesKnown
    (fun b e acc newBs newExps newAcc hstep hknown =>
      modalStepBranchGen_preserves_accSourcesKnown apply hFreshLocal b e acc newBs newExps newAcc
        hstep hknown)
    fuel

/-- **Top-loop propagation of `accTargetsKnown`** (`FmpMeasure.lean`) -- the genuinely missing
generic lemma this phase closes: re-derivation from the generic form above at
`P := accTargetsKnown`, `hPresP := modalStepBranch_preserves_accTargetsKnown_gen apply
hFreshLocal`. Needed as `modalOpenBranchS5_countermodel`'s `hTgt` argument
(`FrameCompleteness.lean`): the step-level fact was already generic and S5-ready
(`modalStepBranch_preserves_accTargetsKnown_gen`), but no top-loop propagation existed until
now. -/
theorem modalExpandBranchesGen_openBranch_accTargetsKnown
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, accTargetsKnown p.1 p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        accTargetsKnown bR aR :=
  modalExpandBranchesGen_openBranch_gen apply accTargetsKnown
    (fun b e acc newBs newExps newAcc hstep hknown =>
      modalStepBranch_preserves_accTargetsKnown_gen apply hFreshLocal b e acc newBs newExps newAcc
        hstep hknown)
    fuel

end Cslib.Logic.Modal.Tableau

end
