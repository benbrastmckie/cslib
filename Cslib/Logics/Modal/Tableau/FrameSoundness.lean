/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Soundness
public import Cslib.Logics.Modal.Tableau.FrameRules

/-! # Frame-Relativized Modal Tableau Soundness

This module introduces the frame-relativized soundness vocabulary shared by the
frame-specific tableau extensions (T, S4, S5, B, 5) built on top of the modal K
tableau. It generalizes `kValid` (`Soundness.lean`) and `branchSatisfiable`
(`SoundnessStep.lean`) with an explicit frame-condition predicate `FC`, and re-derives
K soundness through the generalized vocabulary to confirm the K arms port unchanged.

## Main Definitions

- `FrameCondition`: a predicate on accessibility relations (e.g. `Std.Refl`, `IsTrans`,
  `Std.Symm`, `Relation.RightEuclidean`), parametric in the (fixed-universe) world type,
  matching the existing `kValid`/`branchSatisfiable` convention of quantifying `World` at
  a single fixed universe (`Type`, not `Type*`).
- `frameValid FC φ`: `φ` is satisfied in all Kripke models whose relation satisfies `FC`.
- `branchSatisfiableIn FC b acc`: a branch `b` is satisfiable via a model whose relation
  satisfies `FC` and extends `acc` (the "`m.r` superset of `acc` edges" contract, preserved
  verbatim from `branchSatisfiable`).

## Main Results

- `branchSatisfiableIn_trivial_imp`: the trivial-`FC` instance of `branchSatisfiableIn`
  implies the (frame-free) `branchSatisfiable`.
- `modalTableau_sound_frame`: `modalTableau φ = .closed → frameValid trivialFC φ`, i.e. K
  soundness re-derived through `frameValid`. Downstream phases add per-system arms
  (`frameValid (fun {_} r => Std.Refl r) φ`, etc.) without touching this file.

## Strategy

Per-system phases do **not** need to reprove the K fuel-induction soundness argument
(`modalExpandBranches_closed_unsat`); instead they build their own frame-specific tableau
loop (new rules, new saturation) and their own soundness fuel induction over
`branchSatisfiableIn FC`, discharging the frame-condition witness via the relevant
`Satisfies.t`/`Satisfies.b`/`Satisfies.four`/`Satisfies.five` semantic validity theorem.
This file only fixes the shared vocabulary and confirms it is a strict generalization of
the existing K result.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v
variable {Atom : Type v}

/-! ## Frame-Relativized Validity -/

/-- A frame condition: a predicate on accessibility relations, universally quantified over
the (fixed-universe) world type. Matches the `kValid`/`branchSatisfiable` convention of
quantifying `World` at a single fixed universe (`Type`). Typical instances: `Std.Refl`,
`IsTrans`, `Std.Symm`, `Relation.RightEuclidean`, or the trivial `fun _ => True`. -/
abbrev FrameCondition := ∀ {World : Type}, (World → World → Prop) → Prop

/-- The trivial frame condition, satisfied by every relation. Instantiating `frameValid`
with `trivialFC` recovers exactly `kValid` (see `frameValid_trivialFC_iff_kValid`). -/
def trivialFC : FrameCondition := fun {_} _ => True

/-- Frame-relativized validity: `φ` is satisfied in every Kripke model whose accessibility
relation satisfies the frame condition `FC`, at every world. Generalizes `kValid`
(`Soundness.lean:322`) by adding the `FC m.r` hypothesis; `frameValid trivialFC` is
`kValid` in all but name. -/
def frameValid (FC : FrameCondition) (φ : Proposition Atom) : Prop :=
  ∀ (World : Type) (m : Model World Atom), FC m.r → ∀ (w : World), Satisfies m w φ

/-- `frameValid` with the trivial frame condition is exactly `kValid`. -/
lemma frameValid_trivialFC_iff_kValid (φ : Proposition Atom) :
    frameValid trivialFC φ ↔ kValid φ := by
  constructor
  · intro h World m w
    exact h World m trivial w
  · intro h World m _ w
    exact h World m w

/-! ## Frame-Relativized Branch Satisfiability -/

/-- Frame-relativized branch satisfiability: a branch `b` with accessibility relation `acc`
is satisfiable-in-`FC` if there exists a Kripke model `m` (over the world type `WorldIndex`'s
target `W`), a world assignment `f`, such that:
- `m.r` satisfies the frame condition `FC`;
- `m.r` extends the recorded accessibility edges (`acc.hasEdge w w' → m.r (f w) (f w')`,
  the one-directional "`m.r` superset of `acc` edges" contract, preserved verbatim from
  `branchSatisfiable`);
- every `T(φ)@w ∈ b` is satisfied and every `F(φ)@w ∈ b` is falsified.

Generalizes `branchSatisfiable` (`SoundnessStep.lean:63`) by adding the `FC m.r` conjunct.
Per-system phases (T, S4, S5, B, 5) instantiate this with their own frame condition and
build a dedicated fuel-induction soundness argument for their own (frame-specific) tableau
loop; this file only fixes the shared signature. -/
def branchSatisfiableIn (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
    FC m.r ∧
    (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula)

/-- The trivial-`FC` instance of `branchSatisfiableIn` implies the frame-free
`branchSatisfiable`: dropping the (trivially-true) frame-condition witness recovers exactly
the K notion of branch satisfiability. This is the bridge lemma that lets
`modalTableau_sound_frame` reuse the existing K fuel-induction result
(`modalExpandBranches_closed_unsat`) without reproving it generically over `FC`. -/
lemma branchSatisfiableIn_trivial_imp [DecidableEq Atom] [Hashable Atom]
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : branchSatisfiableIn trivialFC b acc) :
    branchSatisfiable.{v, 0} b acc := by
  obtain ⟨W, m, f, -, hedges, hb⟩ := h
  exact ⟨W, m, f, hedges, hb⟩

/-! ## K Soundness Re-Derived Through `frameValid` -/

/-- The modal K tableau is sound through the frame-relativized vocabulary: if the tableau
closes on `F(φ)`, then `φ` is `frameValid` for the trivial frame condition. Re-derives
`modalTableau_sound` (K) through `frameValid`/`branchSatisfiableIn`, confirming the K arms
port unchanged: the proof is the same contrapositive argument, routed through
`branchSatisfiableIn_trivial_imp` to reuse `modalExpandBranches_closed_unsat` verbatim. -/
theorem modalTableau_sound_frame [DecidableEq Atom] [Hashable Atom] (φ : Proposition Atom)
    (h : modalTableau φ = .closed) :
    frameValid trivialFC φ := by
  rw [frameValid_trivialFC_iff_kValid]
  exact modalTableau_sound φ h

/-! ## T (Reflexive Frame) -/

/-- The reflexive frame condition: `Std.Refl m.r`. Instantiates `frameValid`/
`branchSatisfiableIn` for the modal logic T (`Cube.T`, `{m | Std.Refl m.r}`). -/
def reflFC : FrameCondition := fun {_} r => Std.Refl r

/-- T-validity: `φ` is satisfied in every reflexive Kripke model, at every world. Matches
`Cube.T`. -/
def tValid (φ : Proposition Atom) : Prop := frameValid reflFC φ

/-! ### T-Rule Semantic Soundness

The two T-specific tableau arms (`modalTBoxSelf`, `modalTDiaNegSelf` in `FrameRules.lean`)
propagate `T(□φ)@w ⊢ T(φ)@w` and `F(◇φ)@w ⊢ F(φ)@w` unconditionally at the *same* world `w`.
Their soundness reduces directly to reflexivity: in a reflexive model, `w` is always its own
successor, so `Satisfies m (f w) (□φ)` already gives `Satisfies m (f w) φ` (and dually for
`◇`) -- no accessibility edge or fuel-induction argument is needed at the rule level. -/

/-- Adding `T(φ)@w` to a branch witnessing `branchSatisfiableIn reflFC` preserves
`branchSatisfiableIn reflFC`, given `T(□φ)@w` is already on the branch: the semantic core of
the T box-positive self-propagation arm (`modalTBoxSelf`). -/
lemma branchSatisfiableIn_reflFC_boxPos_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn reflFC b acc)
    {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    branchSatisfiableIn reflFC (⟨.pos, φ, w⟩ :: b) acc := by
  obtain ⟨W, m, f, hrefl, hedges, hb⟩ := h
  refine ⟨W, m, f, hrefl, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun _ => ?_, fun hcontra => by simp at hcontra⟩
    have hbox : Satisfies m (f w) (.box φ) := (hb _ hmem).1 rfl
    exact hbox (f w) (hrefl.refl (f w))
  · exact hb sf hold

/-- Adding `F(φ)@w` to a branch witnessing `branchSatisfiableIn reflFC` preserves
`branchSatisfiableIn reflFC`, given `F(◇φ)@w` is already on the branch: the semantic core of
the T diamond-negative self-propagation arm (`modalTDiaNegSelf`). -/
lemma branchSatisfiableIn_reflFC_diaNeg_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn reflFC b acc)
    {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    branchSatisfiableIn reflFC (⟨.neg, φ, w⟩ :: b) acc := by
  obtain ⟨W, m, f, hrefl, hedges, hb⟩ := h
  refine ⟨W, m, f, hrefl, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun hcontra => by simp at hcontra, fun _ hφ => ?_⟩
    have hdianeg : ¬ Satisfies m (f w) (.diamond φ) := (hb _ hmem).2 rfl
    exact hdianeg (Satisfies.diamond_iff.mpr ⟨f w, hrefl.refl (f w), hφ⟩)
  · exact hb sf hold

/-- Rule-level T soundness for the box-positive arm: every formula produced by
`modalTBoxSelf` (given `T(□φ)@w` already on the branch) preserves `branchSatisfiableIn
reflFC` when added to the branch. Connects `FrameRules.lean`'s concrete rule output to the
semantic soundness lemma `branchSatisfiableIn_reflFC_boxPos_mem`. -/
lemma modalTBoxSelf_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn reflFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalTBoxSelf b φ w, branchSatisfiableIn reflFC (sf :: b) acc := by
  intro sf hsf
  unfold modalTBoxSelf at hsf
  by_cases hcase :
      b.any (· == (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, List.mem_singleton] at hsf
    subst hsf
    exact branchSatisfiableIn_reflFC_boxPos_mem h hmem

/-- Rule-level T soundness for the diamond-negative arm: every formula produced by
`modalTDiaNegSelf` (given `F(◇φ)@w` already on the branch) preserves `branchSatisfiableIn
reflFC` when added to the branch. Connects `FrameRules.lean`'s concrete rule output to the
semantic soundness lemma `branchSatisfiableIn_reflFC_diaNeg_mem`. -/
lemma modalTDiaNegSelf_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn reflFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalTDiaNegSelf b φ w, branchSatisfiableIn reflFC (sf :: b) acc := by
  intro sf hsf
  unfold modalTDiaNegSelf at hsf
  by_cases hcase :
      b.any (· == (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, List.mem_singleton] at hsf
    subst hsf
    exact branchSatisfiableIn_reflFC_diaNeg_mem h hmem

/-! ## S4 (Reflexive-Transitive Frame) -/

/-- The reflexive-transitive frame condition: `Std.Refl m.r ∧ IsTrans World m.r`.
Instantiates `frameValid`/`branchSatisfiableIn` for the modal logic S4 (`Cube.S4`,
`K ∪ T ∪ Four`, `Cube.lean:81`). -/
def s4FC : FrameCondition := fun {World} r => Std.Refl r ∧ IsTrans World r

/-- S4-validity: `φ` is satisfied in every reflexive-transitive Kripke model, at every
world. Matches `Cube.S4`. -/
def s4Valid (φ : Proposition Atom) : Prop := frameValid s4FC φ

/-! ### 4-Rule Semantic Soundness

The two 4-specific tableau arms (`modalFourBoxProp`, `modalFourDiaNegProp` in
`FrameRules.lean`) propagate the box/diamond formula *itself* (not its unwrapped body)
across a recorded successor edge: `T(□φ)@w`, `w → w'` yields `T(□φ)@w'`, and dually for
`F(◇φ)@w`. Their soundness reduces directly to transitivity of `m.r`, **not** to
`Satisfies.four` (`Basic.lean:348`, stated in diamond form `◇◇φ → ◇φ`, with no box-side
dual): given `Satisfies m (f w) (□φ)` and `m.r (f w) (f w')` (from the recorded edge), every
`m.r`-successor `u` of `f w'` is also an `m.r`-successor of `f w` by `IsTrans.trans`, so
`Satisfies m (f w') (□φ)` -- this mirrors the T arms' direct appeal to `Std.Refl` above,
generalized to `IsTrans`. -/

/-- Bridge from `Accessibility.successorsOf` membership to `hasEdge`: if `w'` is returned by
`successorsOf acc w`, the edge `w → w'` is recorded in `acc`. Local mirror of
`FmpMeasure.lean`'s private `mem_successorsOf_hasEdge`, restated here since that lemma is
private to its own file. -/
private lemma mem_successorsOf_hasEdge' {acc : Accessibility} {w w' : WorldIndex}
    (h : w' ∈ acc.successorsOf w) : acc.hasEdge w w' = true := by
  simp only [Accessibility.successorsOf, List.mem_filterMap] at h
  obtain ⟨⟨src, tgt⟩, hmem, heq⟩ := h
  split at heq
  · rename_i hsrc
    simp only [Option.some.injEq] at heq
    simp only [Accessibility.hasEdge, List.any_eq_true, Bool.and_eq_true]
    exact ⟨(src, tgt), hmem, hsrc, by rw [beq_iff_eq]; exact heq⟩
  · simp at heq

/-- Adding `T(□φ)@w'` to a branch witnessing `branchSatisfiableIn s4FC` preserves
`branchSatisfiableIn s4FC`, given `T(□φ)@w` is already on the branch and `w → w'` is a
recorded edge: the semantic core of the 4-rule box-positive propagation arm
(`modalFourBoxProp`). Proved directly from `IsTrans.trans`, per the module-docstring note
above (not via `Satisfies.four`). -/
lemma branchSatisfiableIn_s4FC_boxPos_trans_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn s4FC b acc)
    {φ : Proposition Atom} {w w' : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge w w' = true) :
    branchSatisfiableIn s4FC (⟨.pos, .box φ, w'⟩ :: b) acc := by
  obtain ⟨W, m, f, ⟨hrefl, htrans⟩, hedges, hb⟩ := h
  refine ⟨W, m, f, ⟨hrefl, htrans⟩, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun _ => ?_, fun hcontra => by simp at hcontra⟩
    have hbox : Satisfies m (f w) (.box φ) := (hb _ hmem).1 rfl
    intro u hu
    exact hbox u (htrans.trans (f w) (f w') u (hedges w w' hedge) hu)
  · exact hb sf hold

/-- Adding `F(◇φ)@w'` to a branch witnessing `branchSatisfiableIn s4FC` preserves
`branchSatisfiableIn s4FC`, given `F(◇φ)@w` is already on the branch and `w → w'` is a
recorded edge: the semantic core of the 4-rule diamond-negative propagation arm
(`modalFourDiaNegProp`). Dual of `branchSatisfiableIn_s4FC_boxPos_trans_mem`. -/
lemma branchSatisfiableIn_s4FC_diaNeg_trans_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn s4FC b acc)
    {φ : Proposition Atom} {w w' : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge w w' = true) :
    branchSatisfiableIn s4FC (⟨.neg, .diamond φ, w'⟩ :: b) acc := by
  obtain ⟨W, m, f, ⟨hrefl, htrans⟩, hedges, hb⟩ := h
  refine ⟨W, m, f, ⟨hrefl, htrans⟩, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun hcontra => by simp at hcontra, fun _ => ?_⟩
    have hdianeg : ¬ Satisfies m (f w) (.diamond φ) := (hb _ hmem).2 rfl
    intro hdia'
    apply hdianeg
    obtain ⟨u, hu, hφu⟩ := Satisfies.diamond_iff.mp hdia'
    exact Satisfies.diamond_iff.mpr ⟨u, htrans.trans (f w) (f w') u (hedges w w' hedge) hu, hφu⟩
  · exact hb sf hold

/-- Rule-level 4-soundness for the box-positive arm: every formula produced by
`modalFourBoxProp` (given `T(□φ)@w` already on the branch) preserves `branchSatisfiableIn
s4FC` when added to the branch. Connects `FrameRules.lean`'s concrete rule output to the
semantic soundness lemma `branchSatisfiableIn_s4FC_boxPos_trans_mem`. -/
lemma modalFourBoxProp_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn s4FC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalFourBoxProp b acc φ w, branchSatisfiableIn s4FC (sf :: b) acc := by
  intro sf hsf
  unfold modalFourBoxProp at hsf
  simp only [List.mem_filterMap] at hsf
  obtain ⟨w', hw', hsf⟩ := hsf
  by_cases hcase :
      b.any (· == (⟨.pos, .box φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, Option.some.injEq] at hsf
    subst hsf
    exact branchSatisfiableIn_s4FC_boxPos_trans_mem h hmem (mem_successorsOf_hasEdge' hw')

/-- Rule-level 4-soundness for the diamond-negative arm: every formula produced by
`modalFourDiaNegProp` (given `F(◇φ)@w` already on the branch) preserves `branchSatisfiableIn
s4FC` when added to the branch. Connects `FrameRules.lean`'s concrete rule output to the
semantic soundness lemma `branchSatisfiableIn_s4FC_diaNeg_trans_mem`. -/
lemma modalFourDiaNegProp_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn s4FC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalFourDiaNegProp b acc φ w, branchSatisfiableIn s4FC (sf :: b) acc := by
  intro sf hsf
  unfold modalFourDiaNegProp at hsf
  simp only [List.mem_filterMap] at hsf
  obtain ⟨w', hw', hsf⟩ := hsf
  by_cases hcase :
      b.any (· == (⟨.neg, .diamond φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, Option.some.injEq] at hsf
    subst hsf
    exact branchSatisfiableIn_s4FC_diaNeg_trans_mem h hmem (mem_successorsOf_hasEdge' hw')

end Cslib.Logic.Modal.Tableau

end
