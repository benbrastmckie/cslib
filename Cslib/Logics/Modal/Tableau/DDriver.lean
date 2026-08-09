/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Mathlib.Tactic.Ring
public import Cslib.Logics.Modal.Tableau.GenericDriver
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.CompletenessLoop

/-! # D-System Tableau Driver

This module instantiates the generic tableau driver (`Saturation.lean`'s `modalStepBranchGen`/
`modalExpandBranchesGen`/`modalTableauGen`) with the D-augmented (serial-frame) rule-application
function `modalApplyOneD` (`FrameRules.lean`), and discharges the structural-hypothesis bundle
`RuleApplicationSpecAt` (`GenericDriver.lean`) for it at the dual-closed universe seed
`modalDualAugment φ`.

## Route E2

`modalApplyOneD`'s dual arms (`T(□ψ)@w ⊢ T(◇ψ)@w`, `F(◇ψ)@w ⊢ F(□ψ)@w`) satisfy every
`RuleApplicationSpec` field except `outputsSubsetUniverse` (F2): the emitted dual `◇ψ`/`□ψ` is
generally not a subformula of a plain seed `φ0`
(`modalApplyOneD_outputsSubsetUniverse_fails`, below). Route E2 fixes this additively, without
weakening F2 for any other rule in the cube:

- `modalDualAugment φ` -- a dual-closed universe seed, `φ` conjoined with the dual of every
  box/diamond subformula of `φ`.
- `RuleApplicationSpecAt φ0 apply` (`GenericDriver.lean`) -- the additive sibling of
  `RuleApplicationSpec` that narrows F2 to a single fixed `φ0` instead of `∀ φ0, …`.
- `modalApplyOneD_specAt : RuleApplicationSpecAt (modalDualAugment φ) modalApplyOneD` -- D's
  twelve-field witness at the dual-closed seed.

## Main Definitions

- `modalDualAugment`: the dual-closed universe seed.
- `modalStepBranchD`/`modalExpandBranchesD`/`modalTableauD`: the D-system analogues of
  `modalStepBranch`/`modalExpandBranches`/`modalTableau`, each the generic driver instantiated
  at `apply := modalApplyOneD`.

## Main Results

- `modalApplyOneD_outputsSubsetUniverse_fails`: F2 provably fails for `modalApplyOneD` at a
  plain (non-dual-closed) seed -- the universe reason Route E2 exists to fix.
- `modalApplyOneD_specAt : RuleApplicationSpecAt (modalDualAugment φ) modalApplyOneD`: the
  twelve-field structural-hypothesis witness at the dual-closed seed, so the K-style FMP
  termination measure transports to the D driver via `GenericDriver.lean`'s `(apply, spec)`
  wrapper theorems narrowed to `…At`.

## Strategy

`modalApplyOneD` agrees with `modalApplyOne` (K) outside the two D-relevant signed-formula shapes
(box-positive `T(□φ)@w`, diamond-negative `F(◇φ)@w`,
`modalApplyOneD_eq_of_not_boxPos_diaNeg`), so every field's "not shaped" case reduces directly to
the corresponding K witness, exactly as `TDriver.lean` does for T's self-propagation. The
difference from T is entirely in F2: T's self-propagated output `φ` is already a subformula of
the seed (`□φ ∈ modalSubfmls φ0 → φ ∈ modalSubfmls φ0`), so T discharges F2 at *any* `φ0`; D's
dual output `◇φ`/`□φ` is only ever guaranteed to be in the universe at the one seed
`modalDualAugment φ0` this module builds, which is why D discharges the narrower
`RuleApplicationSpecAt` instead of `RuleApplicationSpec`.

## Preserved Asset

`specs/598_serial_rule_spec_decision_tableau/prototype/DSerialPrototype.lean` is a 351-line
prototype that compiled sorry-free/axiom-free at HEAD `ad19c80d`; several lemmas below are lifted
from it verbatim or near-verbatim (noted per-lemma).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## The Dual-Closed Universe Seed -/

/-- The dual list of `φ`: for every `□ψ ∈ modalSubfmls φ`, the entry `◇ψ`; for every
`◇ψ ∈ modalSubfmls φ`, the entry `□ψ`. Every entry of this list is either box- or
diamond-shaped, never `.and`-shaped -- used below to discharge the "self-node" case of the
folded-conjunction membership lemmas. -/
def modalDualList (φ : Proposition Atom) : List (Proposition Atom) :=
  (modalSubfmls φ).filterMap fun ψ => match ψ with
    | .box a => some (.diamond a)
    | .diamond a => some (.box a)
    | _ => none

/-- The dual-closed universe seed: `φ` conjoined with `modalDualList φ` (the dual of every
box/diamond subformula of `φ`), folded as a right-nested conjunction so `modalSubfmls`
recursion picks up every dual entry. The tableau branch itself still starts from plain `φ`
(`[F(φ)@0]`, `modalTableauD` below); `modalDualAugment φ` is used only to anchor the universe
(`modalUniverse`, `modalWorldBound`, `modalFuel`) that D's dual arms need to stay inside. -/
def modalDualAugment (φ : Proposition Atom) : Proposition Atom :=
  (modalDualList φ).foldr (fun x acc => Proposition.and x acc) φ

omit [DecidableEq Atom] [Hashable Atom] in
/-- Membership transport into a right-nested conjunction fold from the base formula. -/
private lemma mem_modalSubfmls_foldrAnd_of_base (L : List (Proposition Atom))
    (b x : Proposition Atom) (h : x ∈ modalSubfmls b) :
    x ∈ modalSubfmls (L.foldr (fun y acc => Proposition.and y acc) b) := by
  induction L with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.foldr_cons, modalSubfmls, List.mem_cons, List.mem_append]
    exact Or.inr ih

omit [DecidableEq Atom] [Hashable Atom] in
/-- Membership transport into a right-nested conjunction fold from a folded list element. -/
private lemma mem_modalSubfmls_foldrAnd_of_mem (L : List (Proposition Atom))
    (b x y : Proposition Atom) (hy : y ∈ L) (h : x ∈ modalSubfmls y) :
    x ∈ modalSubfmls (L.foldr (fun z acc => Proposition.and z acc) b) := by
  induction L with
  | nil => simp at hy
  | cons a l ih =>
    simp only [List.foldr_cons, modalSubfmls, List.mem_cons, List.mem_append]
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inl (Or.inr h)
    · exact Or.inr (ih hy)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Elimination for a right-nested conjunction fold, restricted to `x` that is never
`.and`-shaped (discharges the "self-node" case at every fold depth uniformly, since every
self-node of the fold is `.and`-shaped). -/
private lemma mem_modalSubfmls_foldrAnd_elim_of_not_and (L : List (Proposition Atom))
    (b x : Proposition Atom) (hx : ∀ p q, x ≠ Proposition.and p q)
    (h : x ∈ modalSubfmls (L.foldr (fun y acc => Proposition.and y acc) b)) :
    (∃ y ∈ L, x ∈ modalSubfmls y) ∨ x ∈ modalSubfmls b := by
  induction L with
  | nil => exact Or.inr (by simpa using h)
  | cons a l ih =>
    simp only [List.foldr_cons, modalSubfmls, List.mem_cons, List.mem_append] at h
    rcases h with (heq | h) | h
    · exact absurd heq (hx a _)
    · exact Or.inl ⟨a, List.mem_cons_self, h⟩
    · rcases ih h with ⟨y, hy, hx'⟩ | hb
      · exact Or.inl ⟨y, List.mem_cons_of_mem a hy, hx'⟩
      · exact Or.inr hb

omit [DecidableEq Atom] [Hashable Atom] in
/-- **`φ ∈ modalSubfmls (modalDualAugment φ)`**: the initial branch `[F(φ)@0]` lies in
`modalUniverse (modalDualAugment φ)`. -/
lemma modalDualAugment_self_mem (φ : Proposition Atom) :
    φ ∈ modalSubfmls (modalDualAugment φ) :=
  mem_modalSubfmls_foldrAnd_of_base (modalDualList φ) φ φ (modalSubfmls_self_mem φ)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every member of `modalDualList φ` is itself in `modalSubfmls (modalDualAugment φ)`. -/
private lemma modalDualList_mem_dualAugment (φ : Proposition Atom) :
    ∀ y ∈ modalDualList φ, y ∈ modalSubfmls (modalDualAugment φ) := fun y hy =>
  mem_modalSubfmls_foldrAnd_of_mem (modalDualList φ) φ y y hy (modalSubfmls_self_mem y)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Unpacking `modalDualList` membership: every entry is a dual of a box/diamond member of
`modalSubfmls φ`. -/
private lemma mem_modalDualList_iff (φ x : Proposition Atom) :
    x ∈ modalDualList φ ↔
      (∃ a, (Proposition.box a) ∈ modalSubfmls φ ∧ x = .diamond a) ∨
      (∃ a, (Proposition.diamond a) ∈ modalSubfmls φ ∧ x = .box a) := by
  unfold modalDualList
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨ψ, hψ, heq⟩
    cases ψ with
    | box a => exact Or.inl ⟨a, hψ, by simpa using heq.symm⟩
    | diamond a => exact Or.inr ⟨a, hψ, by simpa using heq.symm⟩
    | _ => simp_all
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨_, ha, rfl⟩
    · exact ⟨_, ha, rfl⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Dual closure, box-positive direction**: `□ψ ∈ modalSubfmls (modalDualAugment φ) →
◇ψ ∈ modalSubfmls (modalDualAugment φ)`. Exactly what D's box-positive arm needs to keep
`outputsSubsetUniverse` (F2) at the seed `modalDualAugment φ`. One round of dual-augmentation
suffices: `□ψ` is either already a subformula of `φ` (so `◇ψ ∈ modalDualList φ`, directly in the
seed) or a subformula of a dual-list entry `y`, whose own defining box/diamond occurrence is
already a subformula of `φ` -- in either sub-case `□ψ` transports (`modalSubfmls_trans`) back to
a subformula of `φ`, reducing to the direct case. -/
lemma modalDualAugment_box_dual (φ ψ : Proposition Atom)
    (h : (Proposition.box ψ) ∈ modalSubfmls (modalDualAugment φ)) :
    (Proposition.diamond ψ) ∈ modalSubfmls (modalDualAugment φ) := by
  -- Shared final step, reused by every branch that reduces to `□ψ ∈ modalSubfmls φ`.
  have hfinal : (Proposition.box ψ) ∈ modalSubfmls φ →
      (Proposition.diamond ψ) ∈ modalSubfmls (modalDualAugment φ) := fun hbφ =>
    modalDualList_mem_dualAugment φ _
      ((mem_modalDualList_iff φ _).mpr (Or.inl ⟨ψ, hbφ, rfl⟩))
  rcases mem_modalSubfmls_foldrAnd_elim_of_not_and (modalDualList φ) φ
      (Proposition.box ψ) (by simp) h with ⟨y, hy, hmem⟩ | hmem
  · rcases (mem_modalDualList_iff φ y).mp hy with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · -- y = ◇a, □a ∈ modalSubfmls φ; □ψ ∈ modalSubfmls (◇a) = ◇a :: modalSubfmls a
      simp only [modalSubfmls, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exact absurd heq (by simp)
      · have hba : (Proposition.box ψ) ∈ modalSubfmls (Proposition.box a) :=
          List.mem_cons_of_mem _ hmem
        exact hfinal (modalSubfmls_trans hba ha)
    · -- y = □a, ◇a ∈ modalSubfmls φ; □ψ ∈ modalSubfmls (□a) = □a :: modalSubfmls a
      simp only [modalSubfmls, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · -- □ψ = □a, i.e. ψ = a: ◇ψ = ◇a ∈ modalSubfmls φ directly (that's `ha`).
        have hψa : ψ = a := by simpa using heq
        subst hψa
        exact mem_modalSubfmls_foldrAnd_of_base (modalDualList φ) φ _ ha
      · have hada : a ∈ modalSubfmls (Proposition.diamond a) :=
          List.mem_cons_of_mem _ (modalSubfmls_self_mem a)
        have haφ : a ∈ modalSubfmls φ := modalSubfmls_trans hada ha
        exact hfinal (modalSubfmls_trans hmem haφ)
  · exact hfinal hmem

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Dual closure, diamond-negative direction**: dual of `modalDualAugment_box_dual`, needed
by D's diamond-negative arm. -/
lemma modalDualAugment_dia_dual (φ ψ : Proposition Atom)
    (h : (Proposition.diamond ψ) ∈ modalSubfmls (modalDualAugment φ)) :
    (Proposition.box ψ) ∈ modalSubfmls (modalDualAugment φ) := by
  -- Shared final step, reused by every branch that reduces to `◇ψ ∈ modalSubfmls φ`.
  have hfinal : (Proposition.diamond ψ) ∈ modalSubfmls φ →
      (Proposition.box ψ) ∈ modalSubfmls (modalDualAugment φ) := fun hdφ =>
    modalDualList_mem_dualAugment φ _
      ((mem_modalDualList_iff φ _).mpr (Or.inr ⟨ψ, hdφ, rfl⟩))
  rcases mem_modalSubfmls_foldrAnd_elim_of_not_and (modalDualList φ) φ
      (Proposition.diamond ψ) (by simp) h with ⟨y, hy, hmem⟩ | hmem
  · rcases (mem_modalDualList_iff φ y).mp hy with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · -- y = ◇a, □a ∈ modalSubfmls φ; ◇ψ ∈ modalSubfmls (◇a) = ◇a :: modalSubfmls a
      simp only [modalSubfmls, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · -- ◇ψ = ◇a, i.e. ψ = a: □ψ = □a ∈ modalSubfmls φ directly (that's `ha`).
        have hψa : ψ = a := by simpa using heq
        subst hψa
        exact mem_modalSubfmls_foldrAnd_of_base (modalDualList φ) φ _ ha
      · have haba : a ∈ modalSubfmls (Proposition.box a) :=
          List.mem_cons_of_mem _ (modalSubfmls_self_mem a)
        have haφ : a ∈ modalSubfmls φ := modalSubfmls_trans haba ha
        exact hfinal (modalSubfmls_trans hmem haφ)
    · -- y = □a, ◇a ∈ modalSubfmls φ; ◇ψ ∈ modalSubfmls (□a) = □a :: modalSubfmls a
      simp only [modalSubfmls, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exact absurd heq (by simp)
      · have hda : (Proposition.diamond ψ) ∈ modalSubfmls (Proposition.diamond a) :=
          List.mem_cons_of_mem _ hmem
        exact hfinal (modalSubfmls_trans hda ha)
  · exact hfinal hmem

/-! ## Depth Preservation -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- `◇ψ` and `□ψ` have the same modal depth: both add one to `ψ`'s own depth. Machine-checked
`rfl`, first established in the preserved prototype
(`specs/598_serial_rule_spec_decision_tableau/prototype/DSerialPrototype.lean`). The only
arithmetic difference from T's `rankStep` shape: T emits a strictly shallower formula, D emits
an equally-deep one; both satisfy the `≤` `RuleApplicationSpec.rankStep` requires. -/
lemma modalDepth_diamond_eq_box (ψ : Proposition Atom) :
    modalDepth (Proposition.diamond ψ) = modalDepth (Proposition.box ψ) := rfl

omit [DecidableEq Atom] [Hashable Atom] in
/-- Modal depth is monotone under `modalSubfmls`: a driver-local restatement of
`FmpMeasure.lean`'s `private` `modalDepth_le_of_mem_modalSubfmls` (privacy prevents reuse across
files -- a known, tracked duplication pattern in this driver family). -/
private lemma modalDepth_le_of_mem_modalSubfmls' {ψ φ : Proposition Atom}
    (h : ψ ∈ modalSubfmls φ) : modalDepth ψ ≤ modalDepth φ := by
  induction φ with
  | atom p => simp only [modalSubfmls, List.mem_singleton] at h; subst h; exact le_refl _
  | bot => simp only [modalSubfmls, List.mem_singleton] at h; subst h; exact le_refl _
  | imp a b iha ihb =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | ha) | hb
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega
    · have := ihb hb; simp only [modalDepth]; omega
  | and a b iha ihb =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | ha) | hb
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega
    · have := ihb hb; simp only [modalDepth]; omega
  | or a b iha ihb =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | ha) | hb
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega
    · have := ihb hb; simp only [modalDepth]; omega
  | box a iha =>
    simp only [modalSubfmls, List.mem_cons] at h
    rcases h with rfl | ha
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega
  | diamond a iha =>
    simp only [modalSubfmls, List.mem_cons] at h
    rcases h with rfl | ha
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every entry of `modalDualList φ` has modal depth at most `modalDepth φ`: a dual entry
`◇a`/`□a` has the same depth as the box/diamond occurrence `□a`/`◇a` it dualizes
(`modalDepth_diamond_eq_box`), which is itself a subformula of `φ`
(`modalDepth_le_of_mem_modalSubfmls'`). -/
private lemma modalDualList_depth_le (φ : Proposition Atom) :
    ∀ y ∈ modalDualList φ, modalDepth y ≤ modalDepth φ := by
  intro y hy
  rcases (mem_modalDualList_iff φ y).mp hy with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [modalDepth_diamond_eq_box]; exact modalDepth_le_of_mem_modalSubfmls' ha
  · rw [← modalDepth_diamond_eq_box]; exact modalDepth_le_of_mem_modalSubfmls' ha

omit [DecidableEq Atom] [Hashable Atom] in
/-- Folded-conjunction depth, generic form: `modalDepth` of a right-nested conjunction fold is
the running maximum of the list's depths against the base depth. -/
private lemma modalDepth_foldrAnd (L : List (Proposition Atom)) (b : Proposition Atom) :
    modalDepth (L.foldr (fun y acc => Proposition.and y acc) b) =
      L.foldr (fun y acc => max (modalDepth y) acc) (modalDepth b) := by
  induction L with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, modalDepth, ih]

omit [DecidableEq Atom] [Hashable Atom] in
/-- A right-nested `modalDepth`-max-fold over a list all of whose entries have depth `≤` the
base value equals the base value. -/
private lemma foldr_max_eq_of_all_le (L : List (Proposition Atom)) (b : Nat)
    (hL : ∀ y ∈ L, modalDepth y ≤ b) :
    L.foldr (fun y acc => max (modalDepth y) acc) b = b := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    have ha : modalDepth a ≤ b := hL a List.mem_cons_self
    have hl : ∀ y ∈ l, modalDepth y ≤ b := fun y hy => hL y (List.mem_cons_of_mem a hy)
    simp only [List.foldr_cons, ih hl]
    omega

omit [DecidableEq Atom] [Hashable Atom] in
/-- **`modalDepth (modalDualAugment φ) = modalDepth φ`**: dual augmentation does not change
modal depth, so no `modalWorldBound`/`modalFuel` constant needs to change on account of depth --
consistent with `modalSubfmlsDual_length_le`'s machine-checked measurement (the preserved
prototype) that the dual-closed subformula list keeps the same length bound as the plain one. -/
lemma modalDualAugment_depth_eq (φ : Proposition Atom) :
    modalDepth (modalDualAugment φ) = modalDepth φ := by
  unfold modalDualAugment
  rw [modalDepth_foldrAnd]
  exact foldr_max_eq_of_all_le _ _ (modalDualList_depth_le φ)

/-! ## Entry-Measure Bound at the Dual-Closed Seed -/

omit [Hashable Atom] in
/-- **Entry-measure bound at a fixed seed `φ0`, for an arbitrary initial formula `φ`**: a
generalization of `FmpMeasure.lean`'s `modalExpMeasure_entry_le_fuel` (whose statement fixes
`φ0 = φ`), needed because D's tableau starts from plain `F(φ)@0` but must be measured against
the *dual-closed* seed `φ0 := modalDualAugment φ`. Proof is the identical
`modalWork U b e ≤ 2|U|` then `3 ^ (2|U|) ≤ modalFuel` chain as the original, re-run with `φ0`
kept separate from the branch's own formula `φ` throughout (the chain never actually needs the
two to coincide). -/
lemma modalExpMeasure_entry_le_fuel_at (φ0 φ : Proposition Atom) :
    modalExpMeasure (modalUniverse φ0)
      [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] ≤ modalFuel φ0 := by
  have hmeas : modalExpMeasure (modalUniverse φ0)
      [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      = 3 ^ modalWork (modalUniverse φ0)
          [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] := by
    simp [modalExpMeasure]
  rw [hmeas]
  have hwork : modalWork (modalUniverse φ0)
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 2 * (modalUniverse φ0).length := by
    unfold modalWork
    have h1 : (modalUniverse φ0).countP
        (fun sf => !(([(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]).any
          (· == sf))) ≤ (modalUniverse φ0).length :=
      List.countP_le_length
    have h2 : (modalUniverse φ0).countP
        (fun sf => !((([] : List (SignedFormula (Proposition Atom) WorldIndex))).any
          (· == sf))) = (modalUniverse φ0).length := by
      simp
    omega
  have hUlen := modalUniverse_length_le φ0
  have hexp : 2 * (modalUniverse φ0).length ≤
      4 * (2 * modalComplexity φ0 + 1) * ((2 * modalComplexity φ0 + 1) ^
        (modalComplexity φ0 + 1) + 1) := by
    have h2U : 2 * (modalUniverse φ0).length ≤
        2 * (2 * (2 * modalComplexity φ0 + 1) * (modalWorldBound φ0 + 1)) :=
      Nat.mul_le_mul_left 2 hUlen
    have heq : 2 * (2 * (2 * modalComplexity φ0 + 1) * (modalWorldBound φ0 + 1)) =
        4 * (2 * modalComplexity φ0 + 1) * ((2 * modalComplexity φ0 + 1) ^
          (modalComplexity φ0 + 1) + 1) := by
      unfold modalWorldBound; ring
    rw [heq] at h2U
    exact h2U
  have hfinal : modalWork (modalUniverse φ0)
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] ≤
      4 * (2 * modalComplexity φ0 + 1) * ((2 * modalComplexity φ0 + 1) ^
        (modalComplexity φ0 + 1) + 1) := le_trans hwork hexp
  calc 3 ^ modalWork (modalUniverse φ0)
        [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 3 ^ (4 * (2 * modalComplexity φ0 + 1) * ((2 * modalComplexity φ0 + 1) ^
          (modalComplexity φ0 + 1) + 1)) := Nat.pow_le_pow_right (by norm_num) hfinal
    _ = modalFuel φ0 := rfl

/-! ## D Driver Instantiation -/

/-- One-step branch expansion for the D (serial-frame) tableau: the generic driver
(`modalStepBranchGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneD`
(`FrameRules.lean`). -/
def modalStepBranchD
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneD b e acc

/-- Fuel-based expansion of a list of D-system branches: the generic driver
(`modalExpandBranchesGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneD`. -/
def modalExpandBranchesD
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneD branches expandedSets accs fuel

/-- The D-system (serial-frame) modal tableau decision procedure: starts the signed tableau from
`F(φ)` at world `0`, exactly as `modalTableauGen` does, but fuelled at the *dual-closed* seed
`modalDualAugment φ` rather than at `φ` itself -- D's dual arms are only guaranteed to stay
inside `modalUniverse (modalDualAugment φ)` (`RuleApplicationSpecAt`), so the termination
argument needs the bigger universe's fuel bound (`modalExpMeasure_entry_le_fuel_at`). Not
literally `modalTableauGen modalApplyOneD φ` (which would fuel at plain `φ`) for this reason. -/
def modalTableauD (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalExpandBranchesD [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
    [Accessibility.empty] (modalFuel (modalDualAugment φ))

/-! ## Shape Lemmas for the Two D-Relevant Signed-Formula Shapes

The box-positive/diamond-negative shape dichotomies are the canonical, existentially-quantified
`modalApplyOne_boxPos_eq`/`_diamondNeg_eq` in `Rules.lean` (the K discharges for
`RuleApplicationSpec`'s F9/F10 fields), reached here via the `Rules → Saturation → Completeness →
FmpMeasure → GenericDriver → DDriver` import chain. Mirrors `TDriver.lean:87-260`'s section of
the same name, with T's self-propagation helpers (`modalTBoxSelf`/`modalTDiaNegSelf`) replaced by
D's dual-propagation helpers (`modalDBoxDual`/`modalDDiaNegDual`, `FrameRules.lean`). -/

omit [Hashable Atom] in
/-- The accessibility component of `modalApplyOne` at a box-positive shaped signed formula is
always unchanged. Driver-local restatement of `TDriver.lean`'s `private`
`modalApplyOne_boxPos_acc_eq` (privacy prevents reuse across files -- the known, tracked
duplication pattern in this driver family). -/
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
/-- `modalDBoxDual`'s output dichotomy: either empty, or the singleton dual formula `T(◇φ)@w`,
in which case that formula was not already on the branch (from the `if`-guard). -/
private lemma modalDBoxDual_cases
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalDBoxDual b φ w = [] ∨
      (modalDBoxDual b φ w = [(⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom)
          WorldIndex)] ∧
        (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) := by
  simp only [modalDBoxDual]
  split_ifs with h
  · left; rfl
  · right; exact ⟨rfl, by simpa using h⟩

omit [Hashable Atom] in
/-- Symmetric to `modalDBoxDual_cases` for `modalDDiaNegDual`. -/
private lemma modalDDiaNegDual_cases
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalDDiaNegDual b φ w = [] ∨
      (modalDDiaNegDual b φ w = [(⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom)
          WorldIndex)] ∧
        (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) := by
  simp only [modalDDiaNegDual]
  split_ifs with h
  · left; rfl
  · right; exact ⟨rfl, by simpa using h⟩

omit [Hashable Atom] in
/-- Every formula `modalDBoxDual` can emit is not already on the branch: direct corollary of
`modalDBoxDual_cases`. -/
private lemma modalDBoxDual_not_mem
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) : ∀ x ∈ modalDBoxDual b φ w, x ∉ b := by
  rcases modalDBoxDual_cases b φ w with h | ⟨h, hnot⟩
  · rw [h]; simp
  · rw [h]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnot

omit [Hashable Atom] in
/-- Symmetric to `modalDBoxDual_not_mem` for `modalDDiaNegDual`. -/
private lemma modalDDiaNegDual_not_mem
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) : ∀ x ∈ modalDDiaNegDual b φ w, x ∉ b := by
  rcases modalDDiaNegDual_cases b φ w with h | ⟨h, hnot⟩
  · rw [h]; simp
  · rw [h]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnot

omit [Hashable Atom] in
/-- Direct unfolding of `modalApplyOneD`'s `.fst` component at a box-positive shaped signed
formula, in terms of the underlying `modalApplyOne` (K) result. -/
lemma modalApplyOneD_boxPos_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.pos, .box φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalDBoxDual b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalDBoxDual b φ w).isEmpty then .notApplicable
            else .persistent (modalDBoxDual b φ w)
          | other => other) := by
  simp only [modalApplyOneD]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- **Lifted from the preserved prototype** (machine-checked there): the accessibility component
of `modalApplyOneD` at a box-positive shaped signed formula is exactly K's own accessibility
output (`modalApplyOneD` never touches `acc` for this shape). What F5/F6 (`outDegStep`/
`knownWorldsStep`, phase 7) turn on. -/
lemma modalApplyOneD_boxPos_snd (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.pos, .box φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneD]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneD_boxPos_fst` for the diamond-negative shape. -/
lemma modalApplyOneD_diamondNeg_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalDDiaNegDual b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalDDiaNegDual b φ w).isEmpty then .notApplicable
            else .persistent (modalDDiaNegDual b φ w)
          | other => other) := by
  simp only [modalApplyOneD]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- **Lifted from the preserved prototype** (machine-checked there): symmetric to
`modalApplyOneD_boxPos_snd` for the diamond-negative shape. -/
lemma modalApplyOneD_diaNeg_snd (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneD]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Repackage a negated disjunction of the two D-relevant shapes into the conjunction of
negations `modalApplyOneD_eq_of_not_boxPos_diaNeg` expects. Shared by every field's "not shaped"
case below (phases 6-8). -/
private lemma not_shape_of_not_or {sf : SignedFormula (Proposition Atom) WorldIndex}
    (hshape : ¬ ((sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))) :
    ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
  ⟨fun h => hshape (Or.inl h), fun h => hshape (Or.inr h)⟩

end Cslib.Logic.Modal.Tableau

end
