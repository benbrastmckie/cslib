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

/-! ## Discharging F1-F4 for `modalApplyOneD` at `RuleApplicationSpecAt (modalDualAugment φ)`

Mirrors `TDriver.lean`'s discharge of the corresponding K-termination fields, F1-F3 reused
essentially verbatim from the preserved prototype (machine-checked there), F4 (`rankStep`)
re-derived with `modalDepth_diamond_eq_box` in place of T's strict depth decrease. F2
(`outputsSubsetUniverse`) is the one field genuinely different from every other rule in the
cube: it is proved only at the fixed dual-closed seed `modalDualAugment φ`, never at an arbitrary
`φ0` (`modalApplyOneD_outputsSubsetUniverse_fails`, above, is the machine-checked refutation at a
plain seed). -/

omit [Hashable Atom] in
/-- **F1 (`freshLocal`)**: `modalApplyOneD` never mints a world -- both dual arms are
`persistent`. Lifted from the preserved prototype (machine-checked there). -/
lemma modalApplyOneD_freshLocal
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneD sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneD sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneD sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl
        (modalApplyOneD_boxPos_snd b acc φ w ▸ modalApplyOne_boxPos_acc_eq b acc φ w)
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl
        (modalApplyOneD_diaNeg_snd b acc φ w ▸ modalApplyOne_diamondNeg_acc_eq b acc φ w)
  · rw [modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_fresh_local sf b acc

omit [DecidableEq Atom] [Hashable Atom] in
/-- Restatement of `FmpMeasure.lean`'s `private` `modalUniverse_mem_label` (privacy prevents
reuse across files). -/
private lemma modalUniverse_mem_label' {φ0 : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverse φ0) :
    x.label ≤ modalWorldBound φ0 := by
  simp only [modalUniverse, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;> (subst heq; exact Nat.lt_succ_iff.mp hw)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Dual-closed analogue of `FmpMeasure.lean`'s `modalUniverse_mem_of_sameWorld_subfml`: given
`sf.formula = □ψ` with `sf` a branch member inside `modalUniverse (modalDualAugment φ)`, the
dual `◇ψ` at `sf`'s own world is also inside that universe (`modalDualAugment_box_dual`,
phase 4). -/
private lemma modalUniverse_dualAugment_mem_box_dual {φ ψ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hb : ∀ x ∈ b, x ∈ modalUniverse (modalDualAugment φ))
    {sf : SignedFormula (Proposition Atom) WorldIndex} (hsf : sf ∈ b)
    (hform : sf.formula = Proposition.box ψ) (s : Sign) :
    (⟨s, Proposition.diamond ψ, sf.label⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverse (modalDualAugment φ) := by
  have hmemU : sf ∈ modalUniverse (modalDualAugment φ) := hb sf hsf
  have hform' : (Proposition.box ψ) ∈ modalSubfmls (modalDualAugment φ) :=
    hform ▸ modalUniverse_mem_formula hmemU
  exact mem_modalUniverse_of (modalUniverse_mem_label' hmemU)
    (modalDualAugment_box_dual φ ψ hform')

omit [DecidableEq Atom] [Hashable Atom] in
/-- Symmetric to `modalUniverse_dualAugment_mem_box_dual`, using `modalDualAugment_dia_dual`. -/
private lemma modalUniverse_dualAugment_mem_dia_dual {φ ψ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hb : ∀ x ∈ b, x ∈ modalUniverse (modalDualAugment φ))
    {sf : SignedFormula (Proposition Atom) WorldIndex} (hsf : sf ∈ b)
    (hform : sf.formula = Proposition.diamond ψ) (s : Sign) :
    (⟨s, Proposition.box ψ, sf.label⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverse (modalDualAugment φ) := by
  have hmemU : sf ∈ modalUniverse (modalDualAugment φ) := hb sf hsf
  have hform' : (Proposition.diamond ψ) ∈ modalSubfmls (modalDualAugment φ) :=
    hform ▸ modalUniverse_mem_formula hmemU
  exact mem_modalUniverse_of (modalUniverse_mem_label' hmemU)
    (modalDualAugment_dia_dual φ ψ hform')

omit [Hashable Atom] in
/-- **F2 (`outputsSubsetUniverse`), at the fixed seed `modalDualAugment φ`**: the field that
genuinely fails for `modalApplyOneD` at a plain seed
(`modalApplyOneD_outputsSubsetUniverse_fails`, above) holds at the dual-closed seed. Mirrors
`TDriver.lean`'s `modalApplyOneT_outputsSubsetUniverse`, with the self-propagated-subformula
membership argument (`modalUniverse_mem_of_sameWorld_subfml`) replaced by the dual-closure
membership argument built just above. States at a fixed `φ0`, never `∀ φ0` -- the whole point of
the `RuleApplicationSpecAt` sibling. -/
lemma modalApplyOneD_outputsSubsetUniverse_at (φ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse (modalDualAugment φ)) (hsf : sf ∈ b)
    (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound (modalDualAugment φ)) :
    (match (modalApplyOneD sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse (modalDualAugment φ)
      | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse (modalDualAugment φ)
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse (modalDualAugment φ)
      | .notApplicable => True) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∨
      (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)
  · rcases hshape with ⟨hsign, ψ, hform⟩ | ⟨hsign, ψ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneD_boxPos_fst]
      have hself : ∀ x ∈ modalDBoxDual b ψ w, x ∈ modalUniverse (modalDualAugment φ) := by
        rcases modalDBoxDual_cases b ψ w with h | ⟨h, -⟩
        · rw [h]; simp
        · rw [h]
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact modalUniverse_dualAugment_mem_box_dual hb hsf rfl .pos
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hself
      · rw [hk]
        have hkforms : ∀ x ∈ kForms, x ∈ modalUniverse (modalDualAugment φ) := by
          have hout := modalApplyOne_outputs_subset (modalDualAugment φ)
            (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
          rwa [hk] at hout
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hkforms x hx
        · exact hself x hx
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneD_diamondNeg_fst]
      have hself : ∀ x ∈ modalDDiaNegDual b ψ w, x ∈ modalUniverse (modalDualAugment φ) := by
        rcases modalDDiaNegDual_cases b ψ w with h | ⟨h, -⟩
        · rw [h]; simp
        · rw [h]
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact modalUniverse_dualAugment_mem_dia_dual hb hsf rfl .neg
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
          hk | ⟨kForms, hk⟩
      · rw [hk]; split_ifs with hemp
        · trivial
        · exact hself
      · rw [hk]
        have hkforms : ∀ x ∈ kForms, x ∈ modalUniverse (modalDualAugment φ) := by
          have hout := modalApplyOne_outputs_subset (modalDualAugment φ)
            (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf
            hInv hW
          rwa [hk] at hout
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hkforms x hx
        · exact hself x hx
  · rw [modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_outputs_subset (modalDualAugment φ) sf b acc hb hsf hInv hW

omit [Hashable Atom] in
/-- **F3 (`persistentFresh`)**: whenever `modalApplyOneD sf b acc` produces a `.persistent`
result, the emitted formulas are nonempty and fresh. At the two D-relevant shapes, composes K's
own `modalApplyOne_persistent_props` with `modalDBoxDual_not_mem`/`modalDDiaNegDual_not_mem`
(phase 5); at every other shape `modalApplyOneD` reduces to `modalApplyOne` directly. -/
lemma modalApplyOneD_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneD sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq, modalApplyOneD_boxPos_fst] at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      simp only [RuleResult.persistent.injEq] at hca
      obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
      have hself : ∀ x ∈ modalDBoxDual b ψ sf.label, x ∉ b := modalDBoxDual_not_mem b ψ sf.label
      refine ⟨?_, ?_⟩
      · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
      · intro x hx
        rw [← hca] at hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hkfresh x hx
        · exact hself x hx
    · rw [hk] at hca
      split_ifs at hca with hemp
      simp only [RuleResult.persistent.injEq] at hca
      subst hca
      exact ⟨by simpa using hemp, modalDBoxDual_not_mem b ψ sf.label⟩
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq, modalApplyOneD_diamondNeg_fst] at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        simp only [RuleResult.persistent.injEq] at hca
        obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
        have hself : ∀ x ∈ modalDDiaNegDual b ψ sf.label, x ∉ b :=
          modalDDiaNegDual_not_mem b ψ sf.label
        refine ⟨?_, ?_⟩
        · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
        · intro x hx
          rw [← hca] at hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hkfresh x hx
          · exact hself x hx
      · rw [hk] at hca
        split_ifs at hca with hemp
        simp only [RuleResult.persistent.injEq] at hca
        subst hca
        exact ⟨by simpa using hemp, modalDDiaNegDual_not_mem b ψ sf.label⟩
    · rw [modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩] at hca
      exact modalApplyOne_persistent_props sf b acc nf hca

omit [Hashable Atom] in
/-- **F4 (`rankStep`)**: given `rank` satisfying the depth-bound/edge invariants pre-call,
`modalApplyOneD sf b acc` yields a `rank'` satisfying both invariants. Mirrors `TDriver.lean`'s
`modalApplyOneT_rankStep`; the only arithmetic difference is `modalDepth_diamond_eq_box` (phase
4) in place of T's strict depth decrease -- D's dual emits an equally-deep formula, not a
strictly shallower one, but both satisfy the `≤` this field needs. -/
lemma modalApplyOneD_rankStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ w w', (modalApplyOneD sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (match (modalApplyOneD sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
        | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
        | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
        | .notApplicable => True) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, ψ, hform⟩ | ⟨hsign, ψ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      obtain ⟨rank', hagree, hedge', hdepth⟩ :=
        modalApplyOne_rank_step (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc hsfmem hInv rank hbound hedge
      have hwlt : w < modalNextWorld b :=
        modalNextWorld_gt b (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          hsfmem
      have hragree : rank' w = rank w := hagree w (Nat.ne_of_lt hwlt)
      have hψdepth : modalDepth (Proposition.diamond ψ) ≤ rank' w := by
        have hbw : modalDepth (Proposition.box ψ) ≤ rank w := hbound _ hsfmem
        rw [modalDepth_diamond_eq_box]
        omega
      refine ⟨rank', hagree, ?_, ?_⟩
      · rw [modalApplyOneD_boxPos_snd]; exact hedge'
      · rw [modalApplyOneD_boxPos_fst]
        rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · intro x hx
            rcases modalDBoxDual_cases b ψ w with h | ⟨h, -⟩
            · rw [h] at hemp; simp at hemp
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hψdepth
        · simp only [hk] at hdepth ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hdepth x hx
          · rcases modalDBoxDual_cases b ψ w with h | ⟨h, -⟩
            · rw [h] at hx; simp at hx
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hψdepth
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      obtain ⟨rank', hagree, hedge', hdepth⟩ :=
        modalApplyOne_rank_step
          (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc hsfmem hInv rank hbound hedge
      have hwlt : w < modalNextWorld b :=
        modalNextWorld_gt b (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          hsfmem
      have hragree : rank' w = rank w := hagree w (Nat.ne_of_lt hwlt)
      have hψdepth : modalDepth (Proposition.box ψ) ≤ rank' w := by
        have hbw : modalDepth (Proposition.diamond ψ) ≤ rank w := hbound _ hsfmem
        rw [← modalDepth_diamond_eq_box]
        omega
      refine ⟨rank', hagree, ?_, ?_⟩
      · rw [modalApplyOneD_diaNeg_snd]; exact hedge'
      · rw [modalApplyOneD_diamondNeg_fst]
        rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
            hk | ⟨kForms, hk⟩
        · simp only [hk] at hdepth ⊢
          split_ifs with hemp
          · trivial
          · intro x hx
            rcases modalDDiaNegDual_cases b ψ w with h | ⟨h, -⟩
            · rw [h] at hemp; simp at hemp
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hψdepth
        · simp only [hk] at hdepth ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hdepth x hx
          · rcases modalDDiaNegDual_cases b ψ w with h | ⟨h, -⟩
            · rw [h] at hx; simp at hx
            · rw [h] at hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact hψdepth
  · rw [modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_rank_step sf b acc hsfmem hInv rank hbound hedge

/-! ## Discharging F5-F7 for `modalApplyOneD`

Mirrors `TDriver.lean`'s discharge of the same three fields. D never touches `acc` at the two
D-relevant shapes and never produces `.branching` there either (phase 5's `_boxPos_snd`/
`_diaNeg_snd` lemmas are exactly the accessibility-unchanged fact), so K's own
`outDegStep`/`knownWorldsStep`/`branchingLength` proofs transport with the self-conjunct's
known-world membership as the only new content, exactly as T's do. -/

omit [Hashable Atom] in
/-- **F5 (`outDegStep`)**: the out-degree/expanded-set correspondence transports across a
`modalApplyOneD sf b acc` call. Outside the two D-relevant shapes this is exactly K's own
`modalApplyOne_outDeg_step`; at the two D-relevant shapes, both possible result shapes
(`.notApplicable`/`.persistent`) map to the *same* right-hand side (`e`, unchanged) and the
accessibility output is unchanged, so the equation reduces directly to `houtdeg` regardless of
which of the two shapes actually fires. -/
lemma modalApplyOneD_outDegStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ w, outDeg (modalApplyOneD sf b acc).snd w =
      (List.filter (fun x => x.label == w && isMintingShaped x)
        (match (modalApplyOneD sf b acc).fst with
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
      rw [modalApplyOneD_boxPos_snd, modalApplyOne_boxPos_acc_eq, modalApplyOneD_boxPos_fst]
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, wl⟩) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
    · obtain ⟨s, form, wl⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      rw [modalApplyOneD_diaNeg_snd, modalApplyOne_diamondNeg_acc_eq,
        modalApplyOneD_diamondNeg_fst]
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, wl⟩) rfl φ rfl b acc with
          hk | ⟨kForms, hk⟩
      · simp only [hk]
        split_ifs <;> exact houtdeg w
      · simp only [hk]
        exact houtdeg w
  · rw [modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_outDeg_step sf b e acc houtdeg w

omit [Hashable Atom] in
/-- **F6 (`knownWorldsStep`)**: the known-worlds dichotomy for a single `modalApplyOneD sf b
acc` call. Outside the two D-relevant shapes this is exactly K's own
`modalApplyOne_knownWorlds_step`; at the two D-relevant shapes, `modalApplyOneD` never touches
`acc`, so the left disjunct always holds, and the emitted list (K's own persistent output, when
present, merged with at most one dual formula at the source's own -- hence known -- world) stays
inside `modalKnownWorlds b` by K's own field combined with `label_mem_modalKnownWorlds`. -/
lemma modalApplyOneD_knownWorldsStep
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOneD sf b acc).snd = acc ∧
      (match (modalApplyOneD sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneD sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneD sf b acc).fst with
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
      · rw [modalApplyOneD_boxPos_snd]; exact modalApplyOne_boxPos_acc_eq b acc φ w
      · rw [modalApplyOneD_boxPos_fst]
        have hself : ∀ x ∈ modalDBoxDual b φ w, x.label ∈ modalKnownWorlds b := by
          intro x hx
          rcases modalDBoxDual_cases b φ w with h | ⟨h, -⟩
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
      · rw [modalApplyOneD_diaNeg_snd]; exact modalApplyOne_diamondNeg_acc_eq b acc φ w
      · rw [modalApplyOneD_diamondNeg_fst]
        have hself : ∀ x ∈ modalDDiaNegDual b φ w, x.label ∈ modalKnownWorlds b := by
          intro x hx
          rcases modalDDiaNegDual_cases b φ w with h | ⟨h, -⟩
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
  · rw [modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or hshape)]
    exact modalApplyOne_knownWorlds_step sf b acc hsfmem hknown

omit [Hashable Atom] in
/-- **F7 (`branchingLength`)**: `modalApplyOneD` never introduces branching at the two
D-relevant shapes (K's own dispatch is `persistent`/`notApplicable` only there, and the D-merge
never turns either into `.branching`), so any `.branching` result must come from the `_, _`
fallthrough, i.e. from `modalApplyOne` directly, where K's own `modalApplyOne_branching_length`
applies. -/
lemma modalApplyOneD_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneD sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq, modalApplyOneD_boxPos_fst] at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      simp only [RuleResult.branching.injEq] at hca
      rw [← hca]
      exact modalApplyOne_branching_length _ b acc kbrs hk
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      split_ifs at hca
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq, modalApplyOneD_diamondNeg_fst] at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        simp only [RuleResult.branching.injEq] at hca
        rw [← hca]
        exact modalApplyOne_branching_length _ b acc kbrs hk
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        split_ifs at hca
    · have heq : modalApplyOneD sf b acc = modalApplyOne sf b acc :=
        modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOne_branching_length sf b acc brs hca

/-! ## Discharging F8-F12 and Assembling the `RuleApplicationSpecAt` Bundle

F8, F11', F12' below are lifted from the preserved prototype (machine-checked there, essentially
verbatim). F9/F10 are new here (the prototype's own docstring claims them but its body does not
actually state them as separate lemmas): both are quick corollaries of phase 5's
`modalApplyOneD_boxPos_fst`/`_diamondNeg_fst`, mirroring `TDriver.lean`'s
`modalApplyOneT_boxPosNotExpanding`/`_diaNegNotExpanding`. -/

omit [Hashable Atom] in
/-- **F8 (`localShapeInvariance`)**: lifted from the preserved prototype. -/
lemma modalApplyOneD_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOneD ⟨s, φ, w⟩ b acc).1 = (modalApplyOneD ⟨s, φ, w⟩ b' acc').1 := by
  have hnotshape : ∀ (b'' : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc'' : Accessibility),
      modalApplyOneD (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc''
        = modalApplyOne (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc'' := by
    intro b'' acc''
    apply modalApplyOneD_eq_of_not_boxPos_diaNeg
    exact ⟨by rintro ⟨-, ψ, hform⟩; exact hnb ψ hform,
           by rintro ⟨-, ψ, hform⟩; exact hnd ψ hform⟩
  rw [hnotshape b acc, hnotshape b' acc']
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

omit [Hashable Atom] in
/-- **F9 (`boxPosNotExpanding`)**: `modalApplyOneD`'s box-positive dispatch
(`modalApplyOneD_boxPos_fst`) maps K's `.persistent kForms ↦ .persistent (kForms ++ dualNew...)`
and `.notApplicable ↦ .notApplicable | .persistent dualNew` -- **stays in the Propagating
class** either way. This is the field the task's original premise assumed was unsatisfiable for
D; it is not -- the genuinely failing field is F2 (`outputsSubsetUniverse`), not this one. -/
lemma modalApplyOneD_boxPosNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .pos)
    (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneD sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneD sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneD_boxPos_fst]
  rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- **F10 (`diaNegNotExpanding`)**: dual of F9 for the diamond-negative shape, via
`modalApplyOneD_diamondNeg_fst`. -/
lemma modalApplyOneD_diaNegNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .neg)
    (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneD sf b acc).1 = .notApplicable ∨
      ∃ out, (modalApplyOneD sf b acc).1 = .persistent out := by
  obtain ⟨s, φ, w⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  rw [modalApplyOneD_diamondNeg_fst]
  rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
      hk | ⟨kForms, hk⟩
  · simp only [hk]; split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · simp only [hk]; exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- **F11' (`boxNegWitness'`)**: `⟨.neg, .box ψ, w⟩` has sign `.neg`, so it misses D's
`.pos, .box`/`.neg, .diamond` dual arms entirely -- `modalApplyOneD` agrees with `modalApplyOne`
here, so K's own `modalApplyOne_boxNeg_witness` transports directly. Lifted from the preserved
prototype (machine-checked there). -/
lemma modalApplyOneD_boxNegWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneD (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  rw [modalApplyOneD_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩]
  exact modalApplyOne_boxNeg_witness b acc ψ w

omit [Hashable Atom] in
/-- **F12' (`diaPosWitness'`)**: dual of F11' -- `⟨.pos, .diamond ψ, w⟩` misses D's dual arms
too. Lifted from the preserved prototype (machine-checked there). -/
lemma modalApplyOneD_diaPosWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneD (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  rw [modalApplyOneD_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩]
  exact modalApplyOne_diamondPos_witness b acc ψ w

/-- **`modalApplyOneD` satisfies `RuleApplicationSpecAt (modalDualAugment φ)`**: the interface
witness for the D driver, combining the twelve fields discharged above (phases 6-8). This is the
D-system analogue of `TDriver.lean`'s `modalApplyOneT_spec`, narrowed to `…At` because F2
(`outputsSubsetUniverse`) only holds at the fixed dual-closed seed `modalDualAugment φ`, never at
an arbitrary `φ0` -- exactly what `RuleApplicationSpecAt` (`GenericDriver.lean`) exists to
express. Unblocks reusing the K-style FMP termination measure
(`FmpMeasure.lean`/`GenericDriver.lean`'s `…At`-narrowed wrappers) for `modalTableauD`. -/
theorem modalApplyOneD_specAt (φ : Proposition Atom) :
    RuleApplicationSpecAt (modalDualAugment φ) (Atom := Atom) modalApplyOneD where
  freshLocal := modalApplyOneD_freshLocal
  outputsSubsetUniverse := modalApplyOneD_outputsSubsetUniverse_at φ
  persistentFresh := modalApplyOneD_persistentFresh
  rankStep := modalApplyOneD_rankStep
  outDegStep := modalApplyOneD_outDegStep
  knownWorldsStep := modalApplyOneD_knownWorldsStep
  branchingLength := modalApplyOneD_branchingLength
  localShapeInvariance := modalApplyOneD_localShapeInvariance
  boxPosNotExpanding := modalApplyOneD_boxPosNotExpanding
  diaNegNotExpanding := modalApplyOneD_diaNegNotExpanding
  boxNegWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOneD_boxNegWitness b acc ψ w).1,
      (modalApplyOneD_boxNegWitness b acc ψ w).2⟩
  diaPosWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOneD_diaPosWitness b acc ψ w).1,
      (modalApplyOneD_diaPosWitness b acc ψ w).2⟩

end Cslib.Logic.Modal.Tableau

end
