/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.Completeness
public import Cslib.Logics.Modal.Tableau.Soundness

/-! # Modal K Tableau Completeness Loop: Combined-Invariant Single-Step Preservation

This module bundles the five loop invariants needed to run the modal K tableau's completeness
fuel-induction (task 442 Phase 5b): world/expanded-set universe closure and the rank-map
bookkeeping (`ModalPotentialInv`, `FmpMeasure.lean`), the Φ-based world-bound witness
(`modalStepBranch_worldBound`), and the Hintikka expanded-set invariant on the branch's expanded
set (`modalStepBranch_hintikka_inv`, `Completeness.lean`). It proves that one `modalStepBranch`
step preserves this bundle on every child branch it produces, while the base-3 counting measure
(`modalExpMeasure`) strictly decreases.

## Main Definitions

- `ModalLoopInv`: the bundled per-branch loop invariant threaded across the completeness
  fuel-induction.

## Main Results

- `modalStep_preserves_invariant`: one `modalStepBranch` step preserves `ModalLoopInv` (under a
  single shared rank map `rank'`) on every child branch/expanded-set pair, and strictly decreases
  `modalExpMeasure` by at least one.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## The Bundled Loop Invariant -/

/-- **Bundled loop invariant** (task 442 Phase 5a) threaded across the completeness
fuel-induction (Phase 5b): the `ModalPotentialInv` bundle (branch/expanded-set universe
closure, `acc` freshness/known-targets, out-degree correspondence, rank-map bookkeeping,
`FmpMeasure.lean:2215`), the Φ-based potential bound needed by `modalStepBranch_worldBound` to
conclude the a-priori world bound survives a step, and the Hintikka expanded-set invariant
(`modalHintikkaClause`, `Completeness.lean`) recording that every already-expanded formula's
witness obligation is already met on the branch. Bundling these lets the fuel induction carry a
single hypothesis instead of ten separate ones. -/
structure ModalLoopInv (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat) : Prop where
  /-- The `ModalPotentialInv` bundle: universe closure, `acc` bookkeeping, rank map. -/
  potentialInv : ModalPotentialInv φ0 b e acc rank
  /-- The Φ-bound consumed by `modalStepBranch_worldBound`/`modalStepBranch_potential_step` to
  conclude the a-priori world bound is an exact loop invariant (not merely non-increasing). -/
  phiBound : modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank + 1 ≤
    modalCap (modalSubfmls φ0).length (modalDepth φ0)
  /-- Every already-expanded formula's Hintikka witness obligation is already met on `b`. -/
  hintikkaInv : ∀ sf ∈ e, modalHintikkaClause sf.sign sf.formula sf.label b acc
  /-- Every box-shaped formula in the expanded set `e` has sign `.neg` (i.e. is `boxNeg`-shaped,
  `F(□φ)@w`). Needed because `modalHintikkaClause` (used by `hintikkaInv`) is vacuously `True`
  for *any* box-shaped formula regardless of sign, whereas `modalHintikkaSet`'s second conjunct
  only carves out `.neg, .box _`; the `.pos, .box _` (`boxPos`) case genuinely needs its
  `.persistent` clause discharged. This is sound because `boxPos`'s own `modalApplyOne` result
  is always `.notApplicable` or `.persistent` (never `.linear`/`.branching`,
  `modalApplyOne_posBox_eq` below), so a `boxPos`-shaped formula can never be the `sf_exp` that
  gets appended to `e` by a `modalStepBranch` step. -/
  eBoxOnlyNeg : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg
  /-- Every `boxNeg`-shaped formula `F(□ψ)@w` in the expanded set `e` already has a witness
  successor on the branch: `∃ w', acc.hasEdge w w' ∧ F(ψ)@w' ∈ b`. Needed for `modalHintikkaSet`'s
  third conjunct, which is a genuine existential claim not captured by `hintikkaInv`/
  `modalHintikkaClause` (vacuous for all box-shaped formulas). Sound because `boxNeg` is *always*
  applicable (`Rules.lean:115-139` never checks an emptiness guard, unlike `boxPos`/`diamondNeg`),
  so once `F(□ψ)@w` is expanded (added to `e`), its witness `F(ψ)@w'` and edge `w → w'` are
  created immediately (`modalApplyOne_boxNeg_witness` below) and persist unchanged thereafter
  (branches only grow, `acc` edges are only added). -/
  eBoxNegWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b

/-! ## Local Helper Lemmas

These re-derive three facts that are `private` to `FmpMeasure.lean` (hence unavailable across
files): the branch-side universe closure `bClosure` survives a step (mirroring the `private`
`modalStepBranch_eClosure`'s case-split shape but driven by `modalApplyOne_outputs_subset`
instead), the expanded-set closure `eClosure` survives a step (an exact copy of
`modalStepBranch_eClosure`'s proof, since it is `private` there), and the a-priori world bound
holds directly from a Φ-bound witness (an exact copy of `modalStepBranch_worldBound`'s closing
calc chain, generalized over an arbitrary potential term `Φ` so it applies to the pre-step branch
`b` itself, not just a step's output). -/

/-- When `modalStepBranch b e acc = none`, every formula on `b` is either already in the
expanded set `e` or has `modalApplyOne` (evaluated at `b`, `acc`) return `notApplicable` (the
branch is saturated). Local copy of the `private` `modalStepBranch_none_saturated`
(`Completeness.lean:683`), reproduced here since that declaration is not reusable across
files. -/
private lemma modalLoop_stepBranch_none_saturated
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    (hstep : modalStepBranch b e acc = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (modalApplyOne sf b acc).1 = .notApplicable := by
  simp only [modalStepBranch] at hstep
  rw [List.findSome?_eq_none_iff] at hstep
  have hbody := hstep sf hsfb
  by_cases hany : e.any (· == sf) = true
  · left
    simp only [List.any_eq_true] at hany
    obtain ⟨sf', hme, heq⟩ := hany
    simp only [beq_iff_eq] at heq
    exact heq ▸ hme
  · right
    simp only [Bool.not_eq_true] at hany
    simp only [hany] at hbody
    rcases hca : modalApplyOne sf b acc with ⟨res, newAcc⟩
    simp only [hca] at hbody
    rcases res with out | brs | out | _
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · rfl

private lemma modalLoopSf_pos (φ0 : Proposition Atom) : 1 ≤ (modalSubfmls φ0).length :=
  List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem φ0))

private lemma modalLoopSf_one_imp_depth_zero (φ0 : Proposition Atom)
    (h : (modalSubfmls φ0).length = 1) : modalDepth φ0 = 0 := by
  cases φ0 with
  | atom p => rfl
  | bot => rfl
  | imp a c =>
    exfalso
    simp only [modalSubfmls, List.length_cons, List.length_append] at h
    have ha : 1 ≤ (modalSubfmls a).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem a))
    have hc : 1 ≤ (modalSubfmls c).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem c))
    omega
  | box a =>
    exfalso
    simp only [modalSubfmls, List.length_cons] at h
    have ha : 1 ≤ (modalSubfmls a).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem a))
    omega

/-- The a-priori world bound holds for any branch `bb` whose Φ-sum (`modalMaxWorld bb + Φ`) is
bounded by `modalCap Sf (modalDepth φ0)`, for an arbitrary potential term `Φ`. Generalizes the
closing calc chain of `modalStepBranch_worldBound` (`FmpMeasure.lean:2451`) so it applies
directly to a Φ-bound hypothesis on any branch, not only to a step's output. -/
private lemma modalMaxWorld_lt_worldBound_of_phiBound
    (φ0 : Proposition Atom) (bb : List (SignedFormula (Proposition Atom) WorldIndex))
    (Φ : Nat)
    (hPhiBound : modalMaxWorld bb + Φ + 1 ≤
      modalCap (modalSubfmls φ0).length (modalDepth φ0)) :
    modalMaxWorld bb < modalWorldBound φ0 := by
  have hmwlt : modalMaxWorld bb < modalCap (modalSubfmls φ0).length (modalDepth φ0) :=
    calc modalMaxWorld bb < modalMaxWorld bb + Φ + 1 :=
          Nat.lt_succ_of_le (Nat.le_add_right (modalMaxWorld bb) Φ)
      _ ≤ modalCap (modalSubfmls φ0).length (modalDepth φ0) := hPhiBound
  have hSfpos : 1 ≤ (modalSubfmls φ0).length := modalLoopSf_pos φ0
  have hSfdeg : (modalSubfmls φ0).length = 1 → modalDepth φ0 = 0 :=
    modalLoopSf_one_imp_depth_zero φ0
  have hcapbound : modalCap (modalSubfmls φ0).length (modalDepth φ0) ≤
      (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) := modalCap_le_pow hSfpos hSfdeg
  have hSfle : (modalSubfmls φ0).length ≤ 2 * modalComplexity φ0 + 1 :=
    modalSubfmls_length_le φ0
  have hpow1 : (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) ≤
      (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) := Nat.pow_le_pow_left hSfle _
  have hdc : modalDepth φ0 ≤ modalComplexity φ0 := modalDepth_le_complexity φ0
  have hpow2 : (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) ≤
      (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hWB : modalWorldBound φ0 = (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) := rfl
  calc modalMaxWorld bb < modalCap (modalSubfmls φ0).length (modalDepth φ0) := hmwlt
    _ ≤ (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) := hcapbound
    _ ≤ (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) := hpow1
    _ ≤ (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) := hpow2
    _ = modalWorldBound φ0 := hWB.symm

/-- Preservation of the branch-side universe closure across a `modalStepBranch` step: every
formula on each child branch stays inside `U(φ0)`, combining the source branch-closure `hb` with
`modalApplyOne_outputs_subset` (P1) applied to the consumed formula. Mirrors the shallow
top-level case split of the `private` `modalStepBranch_eClosure` (`FmpMeasure.lean:2166`), but
for the branch side rather than the expanded-set side. -/
private lemma modalLoop_bClosure
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hAccInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverse φ0 := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hclosure := modalApplyOne_outputs_subset φ0 sf b acc hb hsfmem hAccInv hW
  rcases hfstc : (modalApplyOne sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x hx
    · exact hb x hx
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x (List.mem_flatten.mpr ⟨br, hbrmem, hx⟩)
    · exact hb x hx
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x hx
    · exact hb x hx
  · rw [hfstc] at hsf; simp at hsf

/-- Preservation of the expanded-set universe closure across a `modalStepBranch` step: an exact
copy of the `private` `modalStepBranch_eClosure` (`FmpMeasure.lean:2166`), reproduced here since
that declaration is not reusable across files. -/
private lemma modalLoop_eClosure
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverse φ0) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfU : sf ∈ modalUniverse φ0 := hb sf hsfmem
  rcases hfstc : (modalApplyOne sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfU
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfU
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact heclosure
  · rw [hfstc] at hsf; simp at hsf

/-- Every `modalStepBranch` step produces children that all share the same freshly-expanded
set `newExp` (either `e` unchanged, for the `.persistent` case, or `e ++ [sf]`, for the
`.linear`/`.branching` cases), i.e. `newExps` is exactly `newBs.map (fun _ => newExp)`. This is
the generic fact `modalExpMeasure_step_lt`'s hypothesis shape (`FmpMeasure.lean:3029`) assumes as
given; here it is derived from a generic `hstep`. -/
private lemma modalStepBranch_newExps_const
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc)) :
    ∃ newExp, newExps = newBs.map (fun _ => newExp) := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (modalApplyOne sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -⟩ := hsf
    exact ⟨e ++ [sf], rfl⟩
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -⟩ := hsf
    exact ⟨e ++ [sf], by simp [List.map_map, Function.comp_def]⟩
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -⟩ := hsf
    exact ⟨e, rfl⟩
  · rw [hfstc] at hsf; simp at hsf

/-- `boxPos`'s own rule-application result is always `.notApplicable` or `.persistent`, never
`.linear`/`.branching`: a formula with sign `.pos` and formula-component `.box ψ` never matches
any of the four Lukasiewicz-encoded propositional decomposers (all match only `.imp`-headed
formulas, `Defs.lean:110-172`), so `tryAllPropRules` is not applicable and `modalApplyOne` falls
through to the `boxPos` dispatch arm (`Rules.lean:83-88`), which only ever produces
`.notApplicable` or `.persistent`. Stated against an opaque `sf` (rather than a literal
`⟨.pos, .box ψ, w⟩` constructor) so call sites never need to destructure a signed formula whose
components are entangled with an unrelated `rfl`-substitution elsewhere in the proof. -/
private lemma modalApplyOne_posBox_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsign : sf.sign = .pos)
    (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne sf b acc).1 = .notApplicable ∨
      (modalApplyOne sf b acc).1 = .persistent (boxPropagation b acc ψ sf.label) := by
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
  · right; rfl

/-- Preservation of the `eBoxOnlyNeg` invariant across a `modalStepBranch` step: mirrors
`modalLoop_eClosure`'s case split, but for the persistent case the new expanded set is exactly
the old one (`eBoxOnlyNeg` transfers directly), while for the linear/branching cases the freshly
appended `sf_exp` must itself have sign `.neg` whenever its formula is box-shaped — since if
`sf_exp` were `.pos`-box-shaped, `modalApplyOne_posBox_eq` would force its own result to be
`.notApplicable`/`.persistent`, contradicting the linear/branching case split. -/
private lemma modalLoop_eBoxOnlyNeg
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg) :
    ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ ψ, sf.formula = .box ψ → sf.sign = .neg := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (modalApplyOne sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newExps = [e ++ [sf_exp]]
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hspos : sf.sign = .pos := by cases hs : sf.sign with
        | pos => rfl
        | neg => exact absurd hs hcon
      have hform_exp : sf_exp.formula = Proposition.box ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.pos := by rw [← heq]; exact hspos
      rcases modalApplyOne_posBox_eq sf_exp hsign_exp ψ hform_exp b acc with h | h <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- branching: newExps = brs.map (fun _ => e ++ [sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hspos : sf.sign = .pos := by cases hs : sf.sign with
        | pos => rfl
        | neg => exact absurd hs hcon
      have hform_exp : sf_exp.formula = Proposition.box ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.pos := by rw [← heq]; exact hspos
      rcases modalApplyOne_posBox_eq sf_exp hsign_exp ψ hform_exp b acc with h | h <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- persistent: newExps = [e] (unchanged)
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact he
  · rw [hfstc] at hsf; simp at hsf

/-- An existing accessibility edge survives adding a new one. -/
private lemma hasEdge_addEdge_mono {acc : Accessibility} {w w' x y : WorldIndex}
    (h : acc.hasEdge w w' = true) : (acc.addEdge x y).hasEdge w w' = true := by
  simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
  simp [h]

/-- Local restatement of `modalApplyOne`'s accessibility-output dichotomy (mirrors the `private`
`modalApplyOne_fresh_local`, `FmpMeasure.lean:859`, not reusable across files): the resulting
`acc` component is either unchanged, or `acc.addEdge sf.label wsf.label` for some fresh witness
`wsf` heading a `.linear` result. -/
private lemma modalLoop_snd_eq_or_addEdge
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOne sf b acc).fst = RuleResult.linear (wsf :: rest)
      ∧ (modalApplyOne sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  unfold modalApplyOne
  extract_lets w propResult
  repeat' first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl, rfl⟩
    | split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl, rfl⟩
    | (left; simp only [apply_ite Prod.snd, ite_self])

/-- Accessibility edges only grow across one `modalApplyOne` application: an edge present
before the step is still present in the (possibly-updated) accessibility relation afterward. -/
private lemma modalApplyOne_hasEdge_mono
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (modalApplyOne sf b acc).snd.hasEdge w w' = true := by
  rcases modalLoop_snd_eq_or_addEdge sf b acc with heq | ⟨wsf, rest, -, heq⟩
  · rw [heq]; exact h
  · rw [heq]; exact hasEdge_addEdge_mono h

/-- `boxNeg`'s own rule-application result, unfolded directly: `F(□ψ)@w` always mints a fresh
witness world `w' := modalNextWorld b`, adds the edge `w → w'`, and heads the emitted `.linear`
list with the witness `F(ψ)@w'` (`Rules.lean:115-139`; unlike `boxPos`/`diamondNeg`, `boxNeg`
never checks an emptiness guard, so it is always applicable). -/
private lemma modalApplyOne_boxNeg_witness
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

/-- Preservation of the `eBoxNegWitness` invariant across a `modalStepBranch` step: mirrors
`modalLoop_eBoxOnlyNeg`'s case split. For old `e`-elements the witness/edge from `he` transfers
to every child branch/accessibility via `b ⊆ b'` (branches only grow) and
`modalApplyOne_hasEdge_mono` (`acc`-edges only grow); for a freshly-appended `sf_exp` that is
itself `boxNeg`-shaped, `modalApplyOne_boxNeg_witness` constructs the witness and edge directly. -/
private lemma modalLoop_eBoxNegWitness
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', newAcc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b' := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (modalApplyOne sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newBs = [nf ++ b], newExps = [e ++ [sf_exp]], newAcc from modalApplyOne's snd
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (modalApplyOne sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyOne_hasEdge_mono sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨hsndeq, rest, hfsteq⟩ := modalApplyOne_boxNeg_witness b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      simp only [RuleResult.linear.injEq] at hfstc
      refine ⟨modalNextWorld b, ?_, ?_⟩
      · rw [hnewAcc, hsfexp_eq, hsndeq]
        simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, beq_self_eq_true,
          Bool.true_and, Bool.true_or]
      · rw [← hfstc]
        exact List.mem_append.mpr (Or.inl (List.mem_cons_self))
  · -- branching: newBs = brs.map (·++b), newExps = brs.map (fun _=>e++[sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp hb'
    rw [← hsf.2.1] at he'; obtain ⟨x', -, rfl⟩ := List.mem_map.mp he'
    have hnewAcc : newAcc = (modalApplyOne sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyOne_hasEdge_mono sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨hsndeq, rest, hfsteq⟩ := modalApplyOne_boxNeg_witness b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      -- boxNeg's own result is `.linear`, never `.branching`: contradiction
      simp at hfstc
  · -- persistent: newBs = [nf ++ b], newExps = [e] (unchanged), newAcc = acc
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (modalApplyOne sf_exp b acc).snd := hsf.2.2.symm
    obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
    exact ⟨w', hnewAcc ▸ modalApplyOne_hasEdge_mono sf_exp b acc hedge,
      List.mem_append.mpr (Or.inr hwit)⟩
  · rw [hfstc] at hsf; simp at hsf

/-! ## The Combined-Invariant Single-Step Preservation Lemma -/

/-- **Combined-invariant single-step preservation** (task 442 Phase 5a): given the bundled loop
invariant `ModalLoopInv` holds pre-step and `modalStepBranch b e acc = some (newBs, newExps,
newAcc)`, there is a single shared rank map `rank'` under which the bundle holds on every child
branch/expanded-set pair, and the base-3 counting measure `modalExpMeasure` strictly decreases.
Composes P2 (`modalStepBranch_worldBound`, `modalStepBranch_potential_step`), P3
(`modalExpMeasure_step_lt`, supplying its `hb`/`hInv`/`hW` hypotheses from the bundle), P4
(`modalStepBranch_hintikka_inv`), and the green `modalStepBranch_preserves_accFreshInv`. -/
lemma modalStep_preserves_invariant
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalLoopInv φ0 b e acc rank) :
    ∃ rank' : WorldIndex → Nat,
      (∀ p ∈ newBs.zip newExps, ModalLoopInv φ0 p.1 p.2 newAcc rank') ∧
      modalExpMeasure (modalUniverse φ0) newBs newExps + 1 ≤
        modalExpMeasure (modalUniverse φ0) [b] [e] := by
  obtain ⟨hpot, hphi, hhint, hboxneg, hboxwit⟩ := hinv
  have hWb : modalMaxWorld b < modalWorldBound φ0 :=
    modalMaxWorld_lt_worldBound_of_phiBound φ0 b _ hphi
  obtain ⟨rank', -, hrb', hre', hpotential⟩ :=
    modalStepBranch_potential_step φ0 b e acc newBs newExps newAcc rank hstep hpot
  have hFreshAll : ∀ b' ∈ newBs, accFreshInv b' newAcc :=
    modalStepBranch_preserves_accFreshInv b e acc newBs newExps newAcc hstep hpot.accFresh
  have hKnownAll : ∀ b' ∈ newBs, accTargetsKnown b' newAcc :=
    modalStepBranch_preserves_accTargetsKnown b e acc newBs newExps newAcc hstep hpot.accKnown
  have hOutDegAll : ∀ e' ∈ newExps, ∀ w, outDeg newAcc w =
      (e'.filter (fun x => x.label == w && isMintingShaped x)).length :=
    modalStepBranch_preserves_outDegEq b e acc newBs newExps newAcc hstep hpot.outDegEq
  have hNodupAll : ∀ e' ∈ newExps, e'.Nodup :=
    modalStepBranch_preserves_expandedNodup b e acc newBs newExps newAcc hstep hpot.eNodup
  have hBClosureAll : ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverse φ0 :=
    modalLoop_bClosure φ0 b e acc newBs newExps newAcc hstep hpot.bClosure hpot.accFresh hWb
  have hEClosureAll : ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 :=
    modalLoop_eClosure φ0 b e acc newBs newExps newAcc hstep hpot.bClosure hpot.eClosure
  have hHintikkaAll := modalStepBranch_hintikka_inv b e acc newBs newExps newAcc hstep hhint
  have hBoxNegAll := modalLoop_eBoxOnlyNeg b e acc newBs newExps newAcc hstep hboxneg
  have hBoxWitAll := modalLoop_eBoxNegWitness b e acc newBs newExps newAcc hstep hboxwit
  refine ⟨rank', ?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    exact ⟨⟨hBClosureAll p.1 hp1, hNodupAll p.2 hp2, hEClosureAll p.2 hp2,
        hFreshAll p.1 hp1, hKnownAll p.1 hp1, hOutDegAll p.2 hp2, hrb' p.1 hp1, hre'⟩,
      by rw [hpotential p.1 hp1]; exact hphi, hHintikkaAll p hp, hBoxNegAll p.2 hp2,
      hBoxWitAll p.1 hp1 p.2 hp2⟩
  · obtain ⟨newExp, hNewExpEq⟩ :=
      modalStepBranch_newExps_const b e acc newBs newExps newAcc hstep
    have hstep' : modalStepBranch b e acc = some (newBs, newBs.map (fun _ => newExp), newAcc) := by
      rw [hNewExpEq] at hstep; exact hstep
    have hdrop := modalExpMeasure_step_lt φ0 [] [] newBs [] [] newExp b e acc newAcc
      rfl hpot.bClosure hpot.accFresh hWb hstep'
    simp only [List.nil_append, List.append_nil] at hdrop
    rw [hNewExpEq]
    exact hdrop

/-! ## The Top-Loop Hintikka Lemma (task 442 Phase 5b) -/

/-- **Top-loop Hintikka lemma** (task 442 Phase 5b): if `modalExpandBranches` returns an open
branch, that branch (with its accessibility relation) is a modal Hintikka set, provided the
bundled loop invariant `ModalLoopInv` (Phase 5a) holds for every branch/expanded-set/`acc` triple
in the initial worklist under *some* per-index rank map, and the worklist's `modalExpMeasure` is
bounded by the available fuel.

Proved by induction on `fuel`, mirroring `classicalExpandBranches_hintikka`
(`Classical/Completeness.lean:924`): the `fuel = 0` case is vacuous (the measure bound forces
`branches = []`, so `modalExpandBranches`'s fuel-exhausted lookup returns `.closed`, never
`.openBranch`); the `fuel = n + 1` case is an inner induction on the `processNext` worklist,
mirroring `modalExpandBranches_closed_unsat`'s three-parallel-list threading
(`Soundness.lean:164`) with an additional `ModalLoopInv`-existence hypothesis at every index.
A `modalStepBranch = none` saturated leaf is closed via `modalLoop_stepBranch_none_saturated`
(each `sf ∈ b` is either in `e` — where `ModalLoopInv.hintikkaInv`/`.eBoxOnlyNeg` discharge
`modalHintikkaSet`'s second conjunct — or has `modalApplyOne`-result `notApplicable`, discharging
it directly) and `ModalLoopInv.eBoxNegWitness` (third conjunct, using that `boxNeg` is always
applicable so a saturated `F(□ψ)@w` is necessarily in `e`). An expansion step advances via
`modalStep_preserves_invariant` (P5a) for the invariant and `modalExpMeasure_step_lt` for the
measure bound, splitting the new worklist's indices into the unchanged `done`/`bt` regions and
the freshly-produced `newBs` region (all sharing the single constant expanded-set `newExp` and
accessibility relation `newAcc`, `modalStepBranch_newExps_const`). -/
lemma modalExpandBranches_hintikka (φ0 : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ∃ rank, ModalLoopInv φ0 bi ei ai rank) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranches branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSet bR aR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs hlen hlenA hfuel _hInv bR aR h
    have hm : modalExpMeasure (modalUniverse φ0) branches expandedSets = 0 :=
      Nat.le_zero.mp hfuel
    have hbranches : branches = [] := by
      rcases branches with _ | ⟨bh, bt⟩
      · rfl
      · exfalso
        rcases expandedSets with _ | ⟨e, es⟩
        · simp only [List.length_nil, List.length_cons] at hlen; omega
        · simp only [modalExpMeasure, List.zip_cons_cons, List.map_cons, List.sum_cons] at hm
          have h3 := Nat.one_le_pow (modalWork (modalUniverse φ0) bh e) 3 (by omega)
          omega
    subst hbranches
    simp [modalExpandBranches] at h
  | succ fuel' ih =>
    intro branches expandedSets accs hlen hlenA hfuel hInv bR aR h
    simp only [modalExpandBranches] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
            (ai : Accessibility),
          (done ++ pending)[i]? = some bi → (doneExp ++ pendingExp)[i]? = some ei →
          (doneAccs ++ pendingAccs)[i]? = some ai →
          ∃ rank, ModalLoopInv φ0 bi ei ai rank) →
        modalExpMeasure (modalUniverse φ0) (done ++ pending) (doneExp ++ pendingExp) ≤
          fuel' + 1 →
        modalExpandBranches.processNext fuel' pending pendingExp pendingAccs done doneExp
            doneAccs = .openBranch bR aR →
        modalHintikkaSet bR aR from
      key branches expandedSets accs [] [] [] hlen hlenA rfl rfl hInv hfuel
        (by simpa [modalExpandBranches] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs done doneExp doneAccs _ _ _ _ _ _ hinner
      simp [modalExpandBranches.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hlength_p hlenP_accs hdlength hdAccs hInv_all hmeas hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength_p hlenP_accs
          simp only [modalExpandBranches.processNext] at hinner
          by_cases hcl : isModalClosed bh = true
          · -- Closed branch: skip and recurse on the inner induction
            rw [if_pos hcl] at hinner
            apply ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
            · simpa using hlength_p
            · simpa using hlenP_accs
            · simp [hdlength]
            · simp [hdAccs]
            · intro i bi ei ai hib hie hia
              apply hInv_all i bi ei ai
              · convert hib using 2; simp
              · convert hie using 2; simp
              · convert hia using 2; simp
            · convert hmeas using 2 <;> simp
            · exact hinner
          · simp only [Bool.not_eq_true] at hcl
            rw [if_neg (by simp [hcl])] at hinner
            cases hstep : modalStepBranch bh e a with
            | none =>
              -- Saturated open branch: bh/a are the returned bR/aR
              rw [hstep] at hinner
              obtain ⟨hbeq, haeq⟩ : bh = bR ∧ a = aR := by
                cases hinner; exact ⟨rfl, rfl⟩
              have hbeq' : bR = bh := hbeq.symm
              have haeq' : aR = a := haeq.symm
              subst hbeq'; subst haeq'
              have hbh_idx : (done ++ bR :: bt)[done.length]? = some bR := by
                rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp [Nat.sub_self]
              have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                rw [List.getElem?_append_right (by omega)]; simp [hdlength, Nat.sub_self]
              have ha_idx : (doneAccs ++ aR :: restAs)[done.length]? = some aR := by
                rw [List.getElem?_append_right (by omega)]; simp [hdAccs, Nat.sub_self]
              obtain ⟨rank, hinv⟩ := hInv_all done.length bR e aR hbh_idx he_idx ha_idx
              refine ⟨hcl, ?_, ?_⟩
              · -- Conjunct 2: rule-application clause for every sf ∈ bR
                intro sf hsfmem
                obtain ⟨s, φ, l⟩ := sf
                cases φ with
                | atom p =>
                  rcases modalLoop_stepBranch_none_saturated hstep ⟨s, .atom p, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .atom p, l⟩ hine
                    simp only [modalHintikkaClause] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | bot =>
                  rcases modalLoop_stepBranch_none_saturated hstep ⟨s, .bot, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .bot, l⟩ hine
                    simp only [modalHintikkaClause] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | imp a c =>
                  rcases modalLoop_stepBranch_none_saturated hstep ⟨s, .imp a c, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .imp a c, l⟩ hine
                    simp only [modalHintikkaClause] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | box ψ' =>
                  cases s with
                  | pos =>
                    -- boxPos still falls into `_, _`; `eBoxOnlyNeg` rules out `sf ∈ e`
                    rcases modalLoop_stepBranch_none_saturated hstep ⟨.pos, .box ψ', l⟩ hsfmem
                      with hine | hna
                    · exact absurd (hinv.eBoxOnlyNeg ⟨.pos, .box ψ', l⟩ hine ψ' rfl) (by simp)
                    · simp [hna]
                  | neg =>
                    -- boxNeg = F(□ψ')@w: matches `modalHintikkaSet`'s first branch directly
                    trivial
              · -- Conjunct 3: box-negative witness existence
                intro ψ' w hmem
                rcases modalLoop_stepBranch_none_saturated hstep _ hmem with hine | hna
                · exact hinv.eBoxNegWitness _ hine ψ' w rfl
                · exfalso
                  obtain ⟨-, rest, hlin⟩ := modalApplyOne_boxNeg_witness bR aR ψ' w
                  rw [hlin] at hna
                  simp at hna
            | some step =>
              obtain ⟨newBs, newExps, newAcc⟩ := step
              rw [hstep] at hinner
              have hstepEq : modalStepBranch bh e a = some (newBs, newExps, newAcc) := hstep
              obtain ⟨rank, hinv⟩ :=
                hInv_all done.length bh e a
                  (by rw [List.getElem?_append_right (Nat.le_refl done.length)]
                      simp [Nat.sub_self])
                  (by rw [List.getElem?_append_right (by omega)]; simp [hdlength, Nat.sub_self])
                  (by rw [List.getElem?_append_right (by omega)]; simp [hdAccs, Nat.sub_self])
              obtain ⟨newExp, hNewExpEq⟩ :=
                modalStepBranch_newExps_const bh e a newBs newExps newAcc hstepEq
              subst hNewExpEq
              have hstepEq' :
                  modalStepBranch bh e a = some (newBs, newBs.map (fun _ => newExp), newAcc) :=
                hstepEq
              obtain ⟨rank', hinvAll, -⟩ :=
                modalStep_preserves_invariant φ0 bh e a rank newBs (newBs.map (fun _ => newExp))
                  newAcc hstepEq' hinv
              have hWb : modalMaxWorld bh < modalWorldBound φ0 :=
                modalMaxWorld_lt_worldBound_of_phiBound φ0 bh _ hinv.phiBound
              have hstep_lt := modalExpMeasure_step_lt φ0 done bt newBs doneExp es newExp bh e a
                newAcc hdlength.symm hinv.potentialInv.bClosure hinv.potentialInv.accFresh hWb
                hstepEq'
              apply ih (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es)
                (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              · simp only [List.length_append, List.length_map, hdlength]
                omega
              · simp only [List.length_append, List.length_replicate, hdAccs]
                omega
              · omega
              · intro i bi ei ai hib hie hia
                rcases Nat.lt_or_ge i done.length with hlt1 | hge1
                · apply hInv_all i bi ei ai
                  · rw [List.append_assoc, List.getElem?_append_left hlt1] at hib
                    rwa [List.getElem?_append_left hlt1]
                  · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hie
                    rwa [List.getElem?_append_left (by omega)]
                  · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hia
                    rwa [List.getElem?_append_left (by omega)]
                · rcases Nat.lt_or_ge i (done.length + newBs.length) with hlt2 | hge2
                  · -- Region: newBs (all sharing newExp/newAcc)
                    have hj : i - done.length < newBs.length := by omega
                    have hbi_newBs : newBs[i - done.length]? = some bi := by
                      rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                      rwa [List.getElem?_append_left hj] at hib
                    have hbi_mem : bi ∈ newBs := List.mem_of_getElem? hbi_newBs
                    have hei_eq : ei = newExp := by
                      rw [List.append_assoc,
                          List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                      rw [List.getElem?_append_left
                            (by simp only [List.length_map]; omega)] at hie
                      rw [List.getElem?_map,
                          show newBs[i - doneExp.length]? = some bi from by
                            rw [show i - doneExp.length = i - done.length from by omega]
                            exact hbi_newBs] at hie
                      simp only [Option.map_some, Option.some.injEq] at hie
                      exact hie.symm
                    have hei_eq' : newExp = ei := hei_eq.symm
                    subst hei_eq'
                    have hai_eq : ai = newAcc := by
                      rw [List.append_assoc,
                          List.getElem?_append_right (by omega : doneAccs.length ≤ i)] at hia
                      rw [List.getElem?_append_left
                            (by simp only [List.length_replicate]; omega)] at hia
                      exact List.eq_of_mem_replicate (List.mem_of_getElem? hia)
                    subst hai_eq
                    have hexp_idx : (newBs.map (fun _ => newExp))[i - done.length]? =
                        some newExp := by
                      rw [List.getElem?_map, hbi_newBs]; rfl
                    have hzip_idx :
                        (newBs.zip (newBs.map (fun _ => newExp)))[i - done.length]? =
                          some (bi, newExp) :=
                      List.getElem?_zip_eq_some.mpr ⟨hbi_newBs, hexp_idx⟩
                    refine ⟨rank', ?_⟩
                    exact hinvAll (bi, newExp) (List.mem_of_getElem? hzip_idx)
                  · -- Region: bt (shifted index)
                    have hbi_bt : bt[i - done.length - newBs.length]? = some bi := by
                      rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                      rw [List.getElem?_append_right
                            (by omega : newBs.length ≤ i - done.length)] at hib
                      exact hib
                    have hei_es : es[i - done.length - newBs.length]? = some ei := by
                      rw [List.append_assoc,
                          List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                      rw [List.getElem?_append_right
                            (by simp only [List.length_map]; omega :
                              (newBs.map (fun _ => newExp)).length ≤ i - doneExp.length)] at hie
                      rwa [show i - doneExp.length - (newBs.map (fun _ => newExp)).length =
                            i - done.length - newBs.length from by
                          simp only [List.length_map]; omega] at hie
                    have hai_restAs : restAs[i - done.length - newBs.length]? = some ai := by
                      rw [List.append_assoc,
                          List.getElem?_append_right (by omega : doneAccs.length ≤ i)] at hia
                      rw [List.getElem?_append_right
                            (by simp only [List.length_replicate]; omega :
                              (List.replicate newBs.length newAcc).length ≤
                                i - doneAccs.length)] at hia
                      rwa [show i - doneAccs.length -
                            (List.replicate newBs.length newAcc).length =
                            i - done.length - newBs.length from by
                          simp only [List.length_replicate]; omega] at hia
                    apply hInv_all (done.length + 1 + (i - done.length - newBs.length)) bi ei ai
                    · rw [List.getElem?_append_right
                            (by omega : done.length ≤
                              done.length + 1 + (i - done.length - newBs.length))]
                      rw [show done.length + 1 + (i - done.length - newBs.length) - done.length
                            = (i - done.length - newBs.length) + 1 from by omega]
                      rw [List.getElem?_cons_succ]; exact hbi_bt
                    · rw [List.getElem?_append_right
                            (by omega : doneExp.length ≤
                              done.length + 1 + (i - done.length - newBs.length))]
                      rw [show done.length + 1 + (i - done.length - newBs.length) -
                            doneExp.length = (i - done.length - newBs.length) + 1 from by omega]
                      rw [List.getElem?_cons_succ]; exact hei_es
                    · rw [List.getElem?_append_right
                            (by omega : doneAccs.length ≤
                              done.length + 1 + (i - done.length - newBs.length))]
                      rw [show done.length + 1 + (i - done.length - newBs.length) -
                            doneAccs.length = (i - done.length - newBs.length) + 1 from by omega]
                      rw [List.getElem?_cons_succ]; exact hai_restAs
              · exact hinner

end Cslib.Logic.Modal.Tableau

end
