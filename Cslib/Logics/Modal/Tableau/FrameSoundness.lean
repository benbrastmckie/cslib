/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Soundness
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.S5Simplification
public import Cslib.Logics.Modal.Tableau.FiveSimplification
public import Cslib.Logics.Modal.Tableau.Support.Accessibility
public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds
import Cslib.Foundations.Relation.Euclidean
import Mathlib.Data.List.Forall2

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
lemma branchSatisfiableIn_trivial_imp [Hashable Atom]
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : branchSatisfiableIn trivialFC b acc) :
    branchSatisfiable.{v, 0} b acc := by
  obtain ⟨W, m, f, -, hedges, hb⟩ := h
  exact ⟨W, m, f, hedges, hb⟩

/-! ## Frame-Relativized Closed-Branch Unsatisfiability -/

/-- A classically closed modal branch is unsatisfiable-in-`FC`, for any
frame condition `FC`. Trivial generalization of `modalClosed_unsat` (`SoundnessStep.lean:92`):
dropping the `FC m.r` witness from a `branchSatisfiableIn FC` hypothesis recovers exactly the
frame-free `branchSatisfiable` hypothesis `modalClosed_unsat` consumes. Feeds the closed-leaf
case of the generic fuel induction `modalExpandBranchesGen_closed_unsatIn` below. -/
lemma modalClosed_unsatIn [DecidableEq Atom] (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hclosed : isModalClosed b = true) (acc : Accessibility) :
    ¬ branchSatisfiableIn FC b acc := by
  intro ⟨W, m, f, _, hedges, hb⟩
  exact modalClosed_unsat b hclosed acc ⟨W, m, f, hedges, hb⟩

/-- `FC`-lifted variant of `negImp_alpha_preserved`
(`SoundnessStep.lean`) for the generic `impNeg` arm of the frame-relativized crux
(`modalStepBranchGen_preserves_satIn` below): if `F(A → C)@lbl` fails to be satisfied by
`(m, f)` (with `FC m.r`), and `b` (with accessibility `acc`) is otherwise `branchSatisfiableIn
FC`, then `[T(A)@lbl, F(C)@lbl] ++ b` is `branchSatisfiableIn FC`. Identical proof to the K
original, with the `FC m.r` witness threaded through unchanged (the model `(W, m)` is never
rebuilt). -/
lemma negImp_alpha_preserved_gen (FC : FrameCondition)
    {A C : Proposition Atom} {lbl : WorldIndex}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : FC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
                    (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula))
    (hneg : ¬Satisfies m (f lbl) (Proposition.imp A C)) :
    branchSatisfiableIn FC ([⟨.pos, A, lbl⟩, ⟨.neg, C, lbl⟩] ++ b) acc := by
  simp only [Satisfies] at hneg
  have hsa : Satisfies m (f lbl) A := by by_contra h; exact hneg (fun ha => absurd ha h)
  have hnc : ¬Satisfies m (f lbl) C := fun hC => hneg (fun _ => hC)
  refine ⟨W, m, f, hFC, hacc, ?_⟩
  intro sf' hmem'
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
  rcases hmem' with (rfl | rfl) | hmem_old
  · exact ⟨fun _ => hsa, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun _ => hnc⟩
  · exact hb sf' hmem_old

/-! ## The Generic Frame-Relativized Soundness Crux -/

/-- **The crux**: `modalStepBranchGen apply` preserves `branchSatisfiableIn
FC` at a single step, given three raw frame-relativized soundness hypotheses on `apply`:

- `hAgree` (S-agree): `apply` agrees with `modalApplyOne` off the two propagating shapes
  (`T(□φ)@w`, `F(◇φ)@w`). Discharged by `fun _ _ _ _ => rfl` for K
  (`apply := modalApplyOne`), and by `modalApplyOneT_eq_of_not_boxPos_diaNeg` verbatim for T.
- `hBoxPos` (S-boxPos): frame-relativized semantic soundness of `apply`'s box-positive output,
  given `T(□φ)@lbl ∈ b`. Discharged by `modalApplyOne_boxPos_sound` (`SoundnessStep.lean`) for
  K (`FC` unused).
- `hDiaNeg` (S-diaNeg): dual of `hBoxPos` for the diamond-negative shape. Discharged by
  `modalApplyOne_diaNeg_sound` (`SoundnessStep.lean`) for K.

This is the ~400-line FC-threaded port of `modalStepBranch_preserves_sat`
(`SoundnessStep.lean`, the K monolith): every propositional/minting arm is ported via `hAgree`
to reduce to `modalApplyOne`, threading the (unchanged) `FC m.r` witness through every
`refine ⟨…, W, m, f, hFC, hacc, …⟩` tuple (the ambient Kripke model `(W, m)` is never
rebuilt -- only `f` is pointwise extended by the two minting arms); the two propagating arms
(box-positive, diamond-negative) are replaced wholesale by `hBoxPos`/`hDiaNeg`. -/
theorem modalStepBranchGen_preserves_satIn [DecidableEq Atom] [Hashable Atom]
    (FC : FrameCondition) (apply : RuleApply Atom)
    (hAgree : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
        (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
        (¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) →
        apply sf b acc = modalApplyOne sf b acc)
    (hBoxPos : ∀ {W : Type} (m : Model W Atom) (f : WorldIndex → W)
        (φ : Proposition Atom) (lbl : WorldIndex)
        (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
        FC m.r →
        (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) →
        (∀ sf ∈ b, sfSat m f sf) →
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        (apply ⟨.pos, .box φ, lbl⟩ b acc).snd = acc ∧
        RuleResultSat m f (apply ⟨.pos, .box φ, lbl⟩ b acc).fst)
    (hDiaNeg : ∀ {W : Type} (m : Model W Atom) (f : WorldIndex → W)
        (φ : Proposition Atom) (lbl : WorldIndex)
        (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
        FC m.r →
        (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) →
        (∀ sf ∈ b, sfSat m f sf) →
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        (apply ⟨.neg, .diamond φ, lbl⟩ b acc).snd = acc ∧
        RuleResultSat m f (apply ⟨.neg, .diamond φ, lbl⟩ b acc).fst)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiableIn FC b acc)
    (hInv : accFreshInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiableIn FC b' newAcc := by
  obtain ⟨W, m, f, hFC, hacc, hb⟩ := hsat
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  obtain ⟨sign, formula, lbl⟩ := sf
  have hsf_b := hb ⟨sign, formula, lbl⟩ hsfmem
  by_cases hshape :
      (sign = Sign.pos ∧ ∃ φ, formula = Proposition.box φ) ∨
      (sign = Sign.neg ∧ ∃ φ, formula = Proposition.diamond φ)
  · -- The two propagating shapes: discharge via hBoxPos/hDiaNeg directly.
    rcases hshape with ⟨hs, φ, hform⟩ | ⟨hs, φ, hform⟩
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := hBoxPos m f φ lbl b acc hFC hacc hb hsfmem
      rcases hres :
          (apply (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := hDiaNeg m f φ lbl b acc hFC hacc hb hsfmem
      rcases hres :
          (apply (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
  · -- Every other shape: `apply` agrees with `modalApplyOne` (hAgree), port the K arm verbatim.
    have heq : apply ⟨sign, formula, lbl⟩ b acc = modalApplyOne ⟨sign, formula, lbl⟩ b acc :=
      hAgree ⟨sign, formula, lbl⟩ b acc (not_or.mp hshape)
    rw [heq] at hsf
    cases sign with
    | pos =>
      have hpos : Satisfies m (f lbl) formula := hsf_b.1 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp only [Satisfies] at hpos
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, List.find?_cons_of_pos, Option.getD_some,
          ↓reduceIte, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        obtain ⟨hφ, hψ⟩ := hpos
        refine ⟨[⟨.pos, φ, lbl⟩, ⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun _ => hφ, fun h => by simp at h⟩
        · exact ⟨fun _ => hψ, fun h => by simp at h⟩
        · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        cases hpos with
        | inl hφ =>
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hφ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        | inr hψ =>
          refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hψ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [Satisfies] at hpos
            exact fun ha => hpos ha
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hpos
          rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
          · refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
              W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun _ => hpos hφ, fun h => by simp at h⟩
            · exact hb sf' hmem_old
          · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun h => by simp at h, fun _ => hφ⟩
            · exact hb sf' hmem_old
      | box φ => exact absurd (Or.inl ⟨rfl, φ, rfl⟩) hshape
      | diamond φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        simp only [Satisfies] at hpos
        obtain ⟨ww, hwwr, hwwφ⟩ := hpos
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.pos, .diamond φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · refine ⟨fun _ => ?_, fun h => by simp at h⟩
            simp only [witness, f', if_pos rfl]
            exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
    | neg =>
      have hneg : ¬Satisfies m (f lbl) formula := hsf_b.2 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
        · refine ⟨[⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hneg hφ⟩
          · exact hb sf' hmem_old
        · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hφ⟩
          · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨hφ, hψ⟩ := hneg
        refine ⟨[⟨.neg, φ, lbl⟩, ⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun h => by simp at h, fun _ => hφ⟩
        · exact ⟨fun h => by simp at h, fun _ => hψ⟩
        · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hneg
          push Not at hneg
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hneg.1, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          exact ⟨_, List.mem_cons_self,
            negImp_alpha_preserved_gen FC hFC hacc hb hneg⟩
      | box φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨ww, hwwr, hwwφ⟩ := hneg
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let newAcc' := acc.addEdge lbl w'
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.neg, .box φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · constructor
            · intro h; simp at h
            · intro _
              simp only [witness, f', if_pos rfl]
              exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
      | diamond φ => exact absurd (Or.inr ⟨rfl, φ, rfl⟩) hshape

/-! ## Generic Frame-Relativized Fuel Induction -/

/-- `modalExpandBranchesGen apply` closing implies every branch is
unsatisfiable-in-`FC`. Port of `modalExpandBranches_closed_unsat` (`Soundness.lean`), swapping
in the generic step (`modalStepBranchGen_preserves_satIn` above), the generic freshness
lemma `modalStepBranch_preserves_accFreshInv_gen`, and
`modalClosed_unsatIn` above. Takes the same three raw soundness hypotheses as the crux above plus
`hFreshLocal` (the `RuleApplicationSpec` F1 shape) for the fuel wrapper's freshness
maintenance. -/
theorem modalExpandBranchesGen_closed_unsatIn [DecidableEq Atom] [Hashable Atom]
    (FC : FrameCondition) (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
        (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
        (apply sf b acc).snd = acc ∨
        (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
          (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (hAgree : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
        (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
        (¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) →
        apply sf b acc = modalApplyOne sf b acc)
    (hBoxPos : ∀ {W : Type} (m : Model W Atom) (f : WorldIndex → W)
        (φ : Proposition Atom) (lbl : WorldIndex)
        (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
        FC m.r →
        (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) →
        (∀ sf ∈ b, sfSat m f sf) →
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        (apply ⟨.pos, .box φ, lbl⟩ b acc).snd = acc ∧
        RuleResultSat m f (apply ⟨.pos, .box φ, lbl⟩ b acc).fst)
    (hDiaNeg : ∀ {W : Type} (m : Model W Atom) (f : WorldIndex → W)
        (φ : Proposition Atom) (lbl : WorldIndex)
        (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
        FC m.r →
        (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) →
        (∀ sf ∈ b, sfSat m f sf) →
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        (apply ⟨.neg, .diamond φ, lbl⟩ b acc).snd = acc ∧
        RuleResultSat m f (apply ⟨.neg, .diamond φ, lbl⟩ b acc).fst)
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => accFreshInv b acc) branches accs →
      modalExpandBranchesGen apply branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiableIn FC b acc) branches accs := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs hlength hlength_accs hFresh h
    simp only [modalExpandBranchesGen] at h
    split at h
    · simp at h
    · rename_i hfind
      refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩
      intro b a hmem
      have hfn := (List.findSome?_eq_none_iff.mp hfind) _ hmem
      have hcl : isModalClosed b = true := by
        cases h : isModalClosed b with
        | true => rfl
        | false => simp [h] at hfn
      exact modalClosed_unsatIn FC b hcl a
  | succ fuel' ih =>
    intro branches expandedSets accs hlength hlength_accs hFresh h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        List.Forall₂ (fun b a => accFreshInv b a) pending pendingAccs →
        List.Forall₂ (fun b a => accFreshInv b a) done doneAccs →
        modalExpandBranchesGen.processNext apply
          fuel' pending pendingExp pendingAccs done doneExp doneAccs = .closed →
        List.Forall₂ (fun b a => ¬branchSatisfiableIn FC b a) pending pendingAccs from
      key branches expandedSets accs [] [] []
        hlength hlength_accs rfl rfl hFresh List.Forall₂.nil
        (by simpa [modalExpandBranchesGen] using h)
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ _ _ hFresh_pending _ _
      cases hFresh_pending
      exact List.Forall₂.nil
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hpendingExpLen hpendingAccsLen hdoneExpLen hdoneAccsLen
        hFresh_pending hFresh_done hinner
      cases pendingAccs with
      | nil => simp at hpendingAccsLen
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hpendingExpLen
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hpendingExpLen hpendingAccsLen
          cases hFresh_pending with
          | cons hInv_bh hFresh_rest =>
            simp only [modalExpandBranchesGen.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              apply List.Forall₂.cons
              · exact modalClosed_unsatIn FC bh hcl a
              · exact ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                    (by simp [hpendingExpLen])
                    (by simp [hpendingAccsLen])
                    (by simp [hdoneExpLen])
                    (by simp [hdoneAccsLen])
                    hFresh_rest
                    (List.rel_append hFresh_done
                      (List.Forall₂.cons hInv_bh List.Forall₂.nil))
                    hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep_eq : modalStepBranchGen apply bh e a with
              | none => rw [hstep_eq] at hinner; simp at hinner
              | some step =>
                obtain ⟨newBs, newExps, newAcc⟩ := step
                rw [hstep_eq] at hinner
                have hnewExpLen : newExps.length = newBs.length := by
                  unfold modalStepBranchGen at hstep_eq
                  obtain ⟨sf, -, hf⟩ := List.exists_of_findSome?_eq_some hstep_eq
                  rcases h_apply : (apply sf bh a) with ⟨result, _⟩
                  simp only [h_apply] at hf
                  cases result with
                  | notApplicable => simp at hf
                  | _ =>
                    split_ifs at hf
                    simp only [Option.some.injEq, Prod.mk.injEq] at hf
                    obtain ⟨rfl, rfl, -⟩ := hf; simp [List.length_map]
                have hFreshNew : List.Forall₂ (fun b a => accFreshInv b a)
                    newBs (List.replicate newBs.length newAcc) :=
                  forall₂_replicate_right.mpr
                    (modalStepBranch_preserves_accFreshInv_gen apply hFreshLocal
                      bh e a newBs newExps newAcc hstep_eq hInv_bh)
                have hFreshAll : List.Forall₂ (fun b a => accFreshInv b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  List.rel_append (List.rel_append hFresh_done hFreshNew) hFresh_rest
                have hunsat_all :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn FC b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                    (by simp only [List.length_append]; omega)
                    (by simp only [List.length_append, List.length_replicate]; omega)
                    hFreshAll hinner
                have hunsat_newBs_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn FC b a)
                    (newBs ++ bt) (List.replicate newBs.length newAcc ++ restAs) := by
                  have h := List.forall₂_drop done.length hunsat_all
                  rw [List.append_assoc done newBs bt, List.drop_left,
                      List.append_assoc doneAccs (List.replicate newBs.length newAcc) restAs,
                      List.drop_left' hdoneAccsLen] at h
                  exact h
                have hunsat_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn FC b a)
                    bt restAs := by
                  have h := List.forall₂_drop newBs.length hunsat_newBs_bt
                  rw [List.drop_left,
                      List.drop_left' List.length_replicate] at h
                  exact h
                have hunsat_newBs :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn FC b a)
                    newBs (List.replicate newBs.length newAcc) := by
                  have h := List.forall₂_take newBs.length hunsat_newBs_bt
                  rw [List.take_left,
                      List.take_left' List.length_replicate] at h
                  exact h
                have hbh_unsat : ¬branchSatisfiableIn FC bh a := by
                  intro hbh_sat
                  obtain ⟨b', hb'_mem, hb'_sat⟩ :=
                    modalStepBranchGen_preserves_satIn FC apply hAgree hBoxPos hDiaNeg
                      bh e a newBs newExps newAcc hstep_eq hbh_sat hInv_bh
                  exact (forall₂_replicate_right.mp hunsat_newBs b' hb'_mem) hb'_sat
                exact List.Forall₂.cons hbh_unsat hunsat_bt

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

/-- `modalTableau_sound_frame`, re-derived through
the *generic* frame-relativized chain (`modalExpandBranchesGen_closed_unsatIn` above)
instantiated at `apply := modalApplyOne`, `FC := trivialFC`, discharging `hAgree` by `rfl`
(`modalApplyOne` agrees with itself), `hBoxPos`/`hDiaNeg` by
`modalApplyOne_boxPos_sound`/`modalApplyOne_diaNeg_sound` above (`FC` unused), and `hFreshLocal` by
`modalApplyOne_fresh` (`Soundness.lean`). This exhibits K as a trivial universe-0 instance of
the generic soundness chain **without** touching K's canonical `Type*` API
(`modalStepBranch_preserves_sat`, `modalExpandBranches_closed_unsat`, `modalTableau_sound`,
`kValid`, `modalTableau_decides`, `instDecidableKValid` all remain byte-identical and
untouched). -/
theorem modalTableau_sound_frame_gen [DecidableEq Atom] [Hashable Atom] (φ : Proposition Atom)
    (h : modalTableau φ = .closed) :
    frameValid trivialFC φ := by
  intro World m _ w
  by_contra hnotsat
  have hsat : branchSatisfiableIn trivialFC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, trivial,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hunsat := modalExpandBranchesGen_closed_unsatIn trivialFC modalApplyOne
    modalApplyOne_fresh
    (fun _ _ _ _ => rfl)
    (fun m f φ lbl b acc _ hacc hb hmem => modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem)
    (fun m f φ lbl b acc _ hacc hb hmem => modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem)
    (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil)
    (by
      rw [← modalExpandBranches_eq]
      simpa only [modalTableau] using h)
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

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
    exact branchSatisfiableIn_s4FC_boxPos_trans_mem h hmem (mem_successorsOf_hasEdge hw')

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
    exact branchSatisfiableIn_s4FC_diaNeg_trans_mem h hmem (mem_successorsOf_hasEdge hw')

/-! ### Propagation-Adequacy Invariant (S4-Keyed)

The S4-keyed ordered driver's loop guard (`LoopChecking.lean`'s `blockingWorldS4Keyed`) can add a
*redirect* edge `v → wBlock` that is not a genuine `m.r` edge of any witnessing model: `wBlock` is
an existing (possibly much older) world being reused rather than a freshly minted one. This
breaks `branchSatisfiableIn`'s edge conjunct `acc.hasEdge w w' → m.r (f w) (f w')` outright for
such an edge. `branchPropAdequateIn` below is the weakened invariant Route P's soundness argument
uses instead: the edge conjunct is replaced by a branch-content-driven one that only demands the
box/diamond propagation payload an edge could ever transmit is already correct at its target, not
that the edge is a real `m.r` edge. The branch-formula conjunct is unchanged. -/

/-- **The propagation-adequacy invariant.** Weakens `branchSatisfiableIn s4FC`'s edge conjunct
`acc.hasEdge w w' → m.r (f w) (f w')` to: for every recorded edge `w → w'`, `f w'` satisfies
`□ψ` for every `T(□ψ)@w ∈ b`, and falsifies `◇ψ` for every `F(◇ψ)@w ∈ b`. The branch-formula
conjunct is verbatim unchanged from `branchSatisfiableIn`. `branchSatisfiableIn_imp_
branchPropAdequateIn` below shows this costs nothing for a genuine `branchSatisfiableIn s4FC`
witness (in particular one built purely from mint edges); the weakening only matters once a
redirect edge is present. -/
def branchPropAdequateIn (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
    FC m.r ∧
    (∀ w w', acc.hasEdge w w' = true →
      (∀ ψ, (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        Satisfies m (f w') (.box ψ)) ∧
      (∀ ψ, (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        ¬ Satisfies m (f w') (.diamond ψ))) ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula)

/-- A genuine `branchSatisfiableIn s4FC` witness already satisfies the weaker
`branchPropAdequateIn s4FC`: the mint-edge case is free. Proved by the identical
transitivity argument as `branchSatisfiableIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem`
above, generalized from "the one new formula being added" to "every edge already recorded in
`acc`" (available uniformly here since a real `branchSatisfiableIn` edge conjunct, unlike
`branchPropAdequateIn`'s, does not depend on branch membership at all). -/
lemma branchSatisfiableIn_imp_branchPropAdequateIn
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn s4FC b acc) :
    branchPropAdequateIn s4FC b acc := by
  obtain ⟨W, m, f, ⟨hrefl, htrans⟩, hedges, hb⟩ := h
  refine ⟨W, m, f, ⟨hrefl, htrans⟩, ?_, hb⟩
  intro w w' hedge
  refine ⟨?_, ?_⟩
  · intro ψ hmem
    have hbox : Satisfies m (f w) (.box ψ) := (hb _ hmem).1 rfl
    intro u hu
    exact hbox u (htrans.trans (f w) (f w') u (hedges w w' hedge) hu)
  · intro ψ hmem
    have hdianeg : ¬ Satisfies m (f w) (.diamond ψ) := (hb _ hmem).2 rfl
    intro hdia'
    apply hdianeg
    obtain ⟨u, hu, hφu⟩ := Satisfies.diamond_iff.mp hdia'
    exact Satisfies.diamond_iff.mpr ⟨u, htrans.trans (f w) (f w') u (hedges w w' hedge) hu, hφu⟩

/-- Adequacy analogue of `branchSatisfiableIn_s4FC_boxPos_trans_mem`: adding `T(□φ)@w'` to a
branch witnessing `branchPropAdequateIn s4FC` preserves `branchPropAdequateIn s4FC`, given
`T(□φ)@w ∈ b` and a recorded edge `w → w'`, **provided** `w'` is already "box-ready" for `φ`
along every edge it already has recorded (`hready`): for every existing successor `v` of `w'`,
`T(□φ)@v` is already on the branch. Unlike `branchSatisfiableIn` (whose edge conjunct is
branch-independent, so untouched by adding a new element), `branchPropAdequateIn`'s edge conjunct
is driven by branch membership, so adding `T(□φ)@w'` reopens the conjunct's obligation at every
edge already recorded *out of* `w'` -- without `hready` the bare analogue is false in general.
`hready` is exactly what the S4-keyed ordered driver's mint-readiness discipline
(`LoopChecking.lean`'s `_mintReady`) is designed to supply at every real call site: a
world only ever acquires an outgoing (redirect) edge once it is mint-ready, i.e. once its own
box-content has already stabilized. The redirect-edge instance of this discharge obligation was
to have been established by `blockedRedirect_boxctx_mem`, but that lemma was false as stated and
has been removed (`LoopChecking.lean`'s "Redirect-Inertness Assembly" comment;
`reports/02_redirect-inertness-divergence-audit.md` §2.2) -- `hready`'s discharge for redirect
edges is an open obligation pending the re-plan. The audit's §5.1 additionally flags that even a
corrected `hready` discharge cannot rely on this invariant's edge conjunct as currently stated for
plain mint-edge chains either (a transient gap, not specific to redirects); see that section for
the disjunctive-edge-conjunct repair under consideration. -/
lemma branchPropAdequateIn_s4FC_boxPos_trans_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchPropAdequateIn s4FC b acc)
    {φ : Proposition Atom} {w w' : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge w w' = true)
    (hready : ∀ v, acc.hasEdge w' v = true →
      (⟨.pos, .box φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    branchPropAdequateIn s4FC (⟨.pos, .box φ, w'⟩ :: b) acc := by
  obtain ⟨W, m, f, hFC, hedgeconj, hb⟩ := h
  have hboxw' : Satisfies m (f w') (.box φ) := (hedgeconj w w' hedge).1 φ hmem
  refine ⟨W, m, f, hFC, ?_, ?_⟩
  · intro u u' huedge
    refine ⟨?_, ?_⟩
    · intro ψ hmem'
      simp only [List.mem_cons, SignedFormula.mk.injEq] at hmem'
      rcases hmem' with ⟨-, hformeq, hueq⟩ | hold
      · have hψ : ψ = φ := (Proposition.box.injEq _ _).mp hformeq
        subst hueq; subst hψ
        exact (hb _ (hready u' huedge)).1 rfl
      · exact (hedgeconj u u' huedge).1 ψ hold
    · intro ψ hmem'
      simp only [List.mem_cons, SignedFormula.mk.injEq] at hmem'
      rcases hmem' with ⟨hsigneq, -, -⟩ | hold
      · exact absurd hsigneq (by simp)
      · exact (hedgeconj u u' huedge).2 ψ hold
  · intro sf hmem'
    rcases List.mem_cons.mp hmem' with rfl | hold
    · exact ⟨fun _ => hboxw', fun hcontra => by simp at hcontra⟩
    · exact hb sf hold

/-- Dual of `branchPropAdequateIn_s4FC_boxPos_trans_mem` for the diamond-negative shape:
adding `F(◇φ)@w'` to a branch witnessing `branchPropAdequateIn s4FC` preserves it, given
`F(◇φ)@w ∈ b`, a recorded edge `w → w'`, and the analogous "diamond-ready" hypothesis for `w'`. -/
lemma branchPropAdequateIn_s4FC_diaNeg_trans_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchPropAdequateIn s4FC b acc)
    {φ : Proposition Atom} {w w' : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge w w' = true)
    (hready : ∀ v, acc.hasEdge w' v = true →
      (⟨.neg, .diamond φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    branchPropAdequateIn s4FC (⟨.neg, .diamond φ, w'⟩ :: b) acc := by
  obtain ⟨W, m, f, hFC, hedgeconj, hb⟩ := h
  have hdianegw' : ¬ Satisfies m (f w') (.diamond φ) := (hedgeconj w w' hedge).2 φ hmem
  refine ⟨W, m, f, hFC, ?_, ?_⟩
  · intro u u' huedge
    refine ⟨?_, ?_⟩
    · intro ψ hmem'
      simp only [List.mem_cons, SignedFormula.mk.injEq] at hmem'
      rcases hmem' with ⟨hsigneq, -, -⟩ | hold
      · exact absurd hsigneq (by simp)
      · exact (hedgeconj u u' huedge).1 ψ hold
    · intro ψ hmem'
      simp only [List.mem_cons, SignedFormula.mk.injEq] at hmem'
      rcases hmem' with ⟨-, hformeq, hueq⟩ | hold
      · have hψ : ψ = φ := (Proposition.diamond.injEq _ _).mp hformeq
        subst hueq; subst hψ
        exact (hb _ (hready u' huedge)).2 rfl
      · exact (hedgeconj u u' huedge).2 ψ hold
  · intro sf hmem'
    rcases List.mem_cons.mp hmem' with rfl | hold
    · exact ⟨fun hcontra => by simp at hcontra, fun _ => hdianegw'⟩
    · exact hb sf hold

/-- Rule-level adequacy soundness for the box-positive 4-rule arm: every formula produced by
`modalFourBoxProp` (given `T(□φ)@w` already on the branch), under the `hready` side condition at
every target successor, preserves `branchPropAdequateIn s4FC` when added to the branch.
Adequacy analogue of `modalFourBoxProp_sound`. -/
lemma modalFourBoxProp_sound_adequate [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchPropAdequateIn s4FC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hready : ∀ w' v, acc.hasEdge w w' = true → acc.hasEdge w' v = true →
      (⟨.pos, .box φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalFourBoxProp b acc φ w, branchPropAdequateIn s4FC (sf :: b) acc := by
  intro sf hsf
  unfold modalFourBoxProp at hsf
  simp only [List.mem_filterMap] at hsf
  obtain ⟨w', hw', hsf⟩ := hsf
  by_cases hcase :
      b.any (· == (⟨.pos, .box φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, Option.some.injEq] at hsf
    subst hsf
    have hedge := mem_successorsOf_hasEdge hw'
    exact branchPropAdequateIn_s4FC_boxPos_trans_mem h hmem hedge
      (fun v hv => hready w' v hedge hv)

/-- Rule-level adequacy soundness for the diamond-negative 4-rule arm: dual of
`modalFourBoxProp_sound_adequate`. -/
lemma modalFourDiaNegProp_sound_adequate [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchPropAdequateIn s4FC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hready : ∀ w' v, acc.hasEdge w w' = true → acc.hasEdge w' v = true →
      (⟨.neg, .diamond φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalFourDiaNegProp b acc φ w, branchPropAdequateIn s4FC (sf :: b) acc := by
  intro sf hsf
  unfold modalFourDiaNegProp at hsf
  simp only [List.mem_filterMap] at hsf
  obtain ⟨w', hw', hsf⟩ := hsf
  by_cases hcase :
      b.any (· == (⟨.neg, .diamond φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, Option.some.injEq] at hsf
    subst hsf
    have hedge := mem_successorsOf_hasEdge hw'
    exact branchPropAdequateIn_s4FC_diaNeg_trans_mem h hmem hedge
      (fun v hv => hready w' v hedge hv)

/-- Adequacy analogue of the K box-positive rule's propagation payload
(`modalApplyOne_boxPos_sound`), the third `branchPropAdequateIn` consumer named by the research
alongside the two 4-rules above: adding `T(φ)@w'` (the *unwrapped* body, not `T(□φ)@w'`) to a
branch witnessing `branchPropAdequateIn s4FC` preserves it, given `T(□φ)@w ∈ b` and a recorded
edge `w → w'`. `s4FC`'s reflexive half (`Std.Refl m.r`, a genuine semantic fact about the
witness model, untouched by the edge conjunct's weakening) gives `Satisfies m (f w') φ` directly
from `Satisfies m (f w') (.box φ)` (itself immediate from the edge conjunct at `(w, w')`) -- no
`acc`-chasing needed for `sf` itself. If `φ` is itself box-shaped, `sf` reopens the edge
conjunct's obligation exactly as in the 4-rule case above; `hready` supplies it (vacuously true
when `φ` is not box-shaped). -/
lemma branchPropAdequateIn_boxPos_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchPropAdequateIn s4FC b acc)
    {φ : Proposition Atom} {w w' : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge w w' = true)
    (hready : ∀ ψ, φ = .box ψ → ∀ v, acc.hasEdge w' v = true →
      (⟨.pos, .box ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    branchPropAdequateIn s4FC (⟨.pos, φ, w'⟩ :: b) acc := by
  obtain ⟨W, m, f, hFC, hedgeconj, hb⟩ := h
  have hboxw' : Satisfies m (f w') (.box φ) := (hedgeconj w w' hedge).1 φ hmem
  have hsatw' : Satisfies m (f w') φ := hboxw' (f w') (hFC.1.refl (f w'))
  refine ⟨W, m, f, hFC, ?_, ?_⟩
  · intro u u' huedge
    refine ⟨?_, ?_⟩
    · intro ψ hmem'
      simp only [List.mem_cons, SignedFormula.mk.injEq] at hmem'
      rcases hmem' with ⟨-, hformeq, hueq⟩ | hold
      · subst hueq
        exact (hb _ (hready ψ hformeq.symm u' huedge)).1 rfl
      · exact (hedgeconj u u' huedge).1 ψ hold
    · intro ψ hmem'
      simp only [List.mem_cons, SignedFormula.mk.injEq] at hmem'
      rcases hmem' with ⟨hsigneq, -, -⟩ | hold
      · exact absurd hsigneq (by simp)
      · exact (hedgeconj u u' huedge).2 ψ hold
  · intro sf hmem'
    rcases List.mem_cons.mp hmem' with rfl | hold
    · exact ⟨fun _ => hsatw', fun hcontra => by simp at hcontra⟩
    · exact hb sf hold

/-- The `branchPropAdequateIn` transfer of `modalClosed_unsatIn`: a classically closed branch is
not `branchPropAdequateIn`-satisfiable. Direct transcription of `modalClosed_unsat`
(`SoundnessStep.lean:92`): that proof's closure argument consumes only the branch-formula
conjunct (its own `intro ⟨W, m, f, _, hb⟩` discards the edge witness entirely), which is
byte-for-byte the same shape in `branchPropAdequateIn` as in `branchSatisfiable`/
`branchSatisfiableIn`, so the same tactic script applies verbatim against the extra-discarded
edge-adequacy witness. -/
lemma modalClosed_unsat_propAdequateIn [DecidableEq Atom]
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hclosed : isModalClosed b = true) (acc : Accessibility) :
    ¬ branchPropAdequateIn s4FC b acc := by
  intro ⟨W, m, f, _, _, hb⟩
  simp only [isModalClosed, ClosureCondition.isClosed, ClosureCondition.findClosure] at hclosed
  have hsome : (ClosureCondition.findClosure b).isSome = true := hclosed
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨cr, hcr⟩ := hsome
  cases hfind : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) with
  | some sf =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true, SignedFormula.isPos] at hpred
    obtain ⟨hpos, hbot⟩ := hpred
    have hsat := (hb sf hmem).1 (by
      cases h : sf.sign with
      | pos => rfl
      | neg => simp [h, Sign.isPos] at hpos)
    have hformbot : sf.formula = (HasBot.bot : Proposition Atom) :=
      LawfulBEq.eq_of_beq hbot
    rw [hformbot] at hsat
    change False at hsat
    exact hsat
  | none =>
    simp only [hfind, ClosureCondition.findClosure] at hcr
    cases hcontra : Branch.findContradiction b with
    | none => simp [hfind, hcontra] at hclosed
    | some pair =>
      obtain ⟨phi, l⟩ := pair
      simp only [Branch.findContradiction] at hcontra
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.exists_of_findSome?_eq_some hcontra
      simp only [SignedFormula.isPos] at hsfcond
      by_cases hpos : sf.sign = .pos
      · simp only [hpos, Sign.isPos, ite_true, Option.ite_some_none_eq_some] at hsfcond
        obtain ⟨hany, _⟩ := hsfcond
        have htrue := (hb sf hsfmem).1 (by simp [hpos])
        obtain ⟨sf_neg, hmemneg, hsfneg⟩ := List.any_eq_true.mp hany
        simp only [Bool.and_eq_true] at hsfneg
        obtain ⟨⟨hsneg, hformEq⟩, hlabEq⟩ := hsfneg
        have hneg : sf_neg.sign = .neg := by
          cases h : sf_neg.sign with
          | pos => simp [h] at hsneg
          | neg => rfl
        have hformfeq : sf_neg.formula = sf.formula := LawfulBEq.eq_of_beq hformEq
        have hlabfeq : sf_neg.label = sf.label := LawfulBEq.eq_of_beq hlabEq
        have hfalse := (hb sf_neg hmemneg).2 (by simp [hneg])
        rw [hformfeq, hlabfeq] at hfalse
        exact absurd htrue hfalse
      · cases hsf : sf.sign with
        | pos => exact absurd hsf hpos
        | neg => simp [hsf, Sign.isPos] at hsfcond

/-! **`blockedRedirect_propAdequate` -- REMOVED.** It composed
`blockedRedirect_boxctx_mem`/`blockedRedirect_diaNeg_mem` (`LoopChecking.lean`, since removed --
both were **false as stated**, see that file's "Redirect-Inertness Assembly" comment and
`reports/02_redirect-inertness-divergence-audit.md` §2.2) with the ambient model's branch-formula
conjunct. Beyond inheriting the two false premises, this assembly's own proof strategy is
independently dead: it discards the ambient edge conjunct (`_` in `obtain ⟨W, m, f, hFC, _, hb⟩
:= h`) and reuses the ambient model `m` unchanged. The audit refutes that strategy directly
(§3.1): a 4-world reflexive-transitive counterexample (`W = {a0,a1,a2,a3}`, `r` = the
reflexive-transitive closure of `{(a0,a1),(a0,a2),(a1,a3)}`, `p` false at `a3`) satisfies the
branch and every `acc` edge conjunct while falsifying `□p` at `f 1` -- so no repair of the two
consumed lemmas alone would have made this assembly's proof go through; any replacement needs a
different route entirely (the report recommends boxed birth-content keys, making the whole
argument a direct consequence of `S4LoopInv.keyLowerBd`). Do not re-attempt this composition as
written. -/

/-! ## B (Symmetric Frame) -/

/-- The symmetric frame condition: `Std.Symm m.r`. Instantiates `frameValid`/
`branchSatisfiableIn` for the modal logic B (`Cube.B`, `{m | Std.Symm m.r}`). -/
def symmFC : FrameCondition := fun {_} r => Std.Symm r

/-- B-validity: `φ` is satisfied in every Kripke model whose relation is symmetric, at every
world. Matches `Cube.B`. -/
def bValid (φ : Proposition Atom) : Prop := frameValid symmFC φ

/-! ### B-Rule Semantic Soundness

The two B-specific tableau arms (`modalBBoxBack`, `modalBDiaNegBack` in `FrameRules.lean`)
propagate `T(□φ)@w` (with a recorded edge `v → w`) `⊢ T(φ)@v`, and dually `F(◇φ)@w ⊢ F(φ)@v`,
backward along the *predecessor* `v`. Their soundness reduces directly to symmetry: given
`m.r (f v) (f w)` (from the recorded edge, via `hedges`), symmetry gives `m.r (f w) (f v)`, and
`Satisfies m (f w) (□φ)` then gives `Satisfies m (f v) φ` (dually for `◇`) -- no fuel-induction
argument is needed at the rule level, matching T's `reflFC` precedent (`Std.Refl`'s `.refl`
lever replaced by `Std.Symm`'s `.symm` lever). -/

/-- Adding `T(φ)@v` to a branch witnessing `branchSatisfiableIn symmFC` preserves
`branchSatisfiableIn symmFC`, given `T(□φ)@w` is already on the branch and `v → w` is a
recorded edge (`acc.hasEdge v w`): the semantic core of the B box-positive backward
propagation arm (`modalBBoxBack`). -/
lemma branchSatisfiableIn_symmFC_boxPos_pred_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn symmFC b acc)
    {φ : Proposition Atom} {v w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge v w = true) :
    branchSatisfiableIn symmFC (⟨.pos, φ, v⟩ :: b) acc := by
  obtain ⟨W, m, f, hsymm, hedges, hb⟩ := h
  refine ⟨W, m, f, hsymm, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun _ => ?_, fun hcontra => by simp at hcontra⟩
    have hbox : Satisfies m (f w) (.box φ) := (hb _ hmem).1 rfl
    have hmvw : m.r (f v) (f w) := hedges v w hedge
    have hmwv : m.r (f w) (f v) := hsymm.symm (f v) (f w) hmvw
    exact hbox (f v) hmwv
  · exact hb sf hold

/-- Adding `F(φ)@v` to a branch witnessing `branchSatisfiableIn symmFC` preserves
`branchSatisfiableIn symmFC`, given `F(◇φ)@w` is already on the branch and `v → w` is a
recorded edge: the semantic core of the B diamond-negative backward propagation arm
(`modalBDiaNegBack`). Dual of `branchSatisfiableIn_symmFC_boxPos_pred_mem`. -/
lemma branchSatisfiableIn_symmFC_diaNeg_pred_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn symmFC b acc)
    {φ : Proposition Atom} {v w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge v w = true) :
    branchSatisfiableIn symmFC (⟨.neg, φ, v⟩ :: b) acc := by
  obtain ⟨W, m, f, hsymm, hedges, hb⟩ := h
  refine ⟨W, m, f, hsymm, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun hcontra => by simp at hcontra, fun _ hφ => ?_⟩
    have hdianeg : ¬ Satisfies m (f w) (.diamond φ) := (hb _ hmem).2 rfl
    have hmvw : m.r (f v) (f w) := hedges v w hedge
    have hmwv : m.r (f w) (f v) := hsymm.symm (f v) (f w) hmvw
    exact hdianeg (Satisfies.diamond_iff.mpr ⟨f v, hmwv, hφ⟩)
  · exact hb sf hold

/-- Rule-level B soundness for the box-positive backward arm: every formula produced by
`modalBBoxBack` (given `T(□φ)@w` already on the branch) preserves `branchSatisfiableIn symmFC`
when added to the branch. Connects `FrameRules.lean`'s concrete rule output to the semantic
soundness lemma `branchSatisfiableIn_symmFC_boxPos_pred_mem`. -/
lemma modalBBoxBack_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn symmFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalBBoxBack b acc φ w, branchSatisfiableIn symmFC (sf :: b) acc := by
  intro sf hsf
  obtain ⟨hxeq, hpred, -, -⟩ := modalBBoxBack_mem hsf
  have hedge : acc.hasEdge sf.label w = true := modalBPredecessorsOf_hasEdge hpred
  rw [hxeq]
  exact branchSatisfiableIn_symmFC_boxPos_pred_mem h hmem hedge

/-- Rule-level B soundness for the diamond-negative backward arm: every formula produced by
`modalBDiaNegBack` (given `F(◇φ)@w` already on the branch) preserves `branchSatisfiableIn
symmFC` when added to the branch. Dual of `modalBBoxBack_sound`. -/
lemma modalBDiaNegBack_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn symmFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalBDiaNegBack b acc φ w, branchSatisfiableIn symmFC (sf :: b) acc := by
  intro sf hsf
  obtain ⟨hxeq, hpred, -, -⟩ := modalBDiaNegBack_mem hsf
  have hedge : acc.hasEdge sf.label w = true := modalBPredecessorsOf_hasEdge hpred
  rw [hxeq]
  exact branchSatisfiableIn_symmFC_diaNeg_pred_mem h hmem hedge

/-! ## TB (Reflexive-Symmetric Frame) -/

/-- The reflexive-symmetric frame condition: `Std.Refl m.r ∧ Std.Symm m.r`. Instantiates
`frameValid`/`branchSatisfiableIn` for the modal logic TB (`Cube.TB`,
`K ∪ T ∪ B`). Conjoins `reflFC` and `symmFC` pointwise, mirroring how `s4FC`/`s5FC` conjoin
their own component conditions. -/
def tbFC : FrameCondition := fun {_} r => Std.Refl r ∧ Std.Symm r

/-- TB-validity: `φ` is satisfied in every Kripke model whose relation is both reflexive and
symmetric, at every world. Matches `Cube.TB`. -/
def tbValid (φ : Proposition Atom) : Prop := frameValid tbFC φ

/-! ### TB-Rule Semantic Soundness

TB's rule arms are exactly T's self-propagation arms (`modalTBoxSelf`, `modalTDiaNegSelf`) and
B's predecessor-backward arms (`modalBBoxBack`, `modalBDiaNegBack`), merged by
`modalApplyOneTB` (`FrameRules.lean`). Since `tbFC r = Std.Refl r ∧ Std.Symm r`, every T-side
obligation is discharged by projecting `.1` into `reflFC`, and every B-side obligation by
projecting `.2` into `symmFC` -- the same projection pattern `s5FC_imp_fiveFC` already uses. -/

/-- `tbFC`'s reflexivity conjunct implies `reflFC`: the projection lever every T-side TB
soundness obligation uses. -/
theorem tbFC_imp_reflFC {World : Type} {r : World → World → Prop} (h : tbFC r) : reflFC r := h.1

/-- `tbFC`'s symmetry conjunct implies `symmFC`: the projection lever every B-side TB
soundness obligation uses. -/
theorem tbFC_imp_symmFC {World : Type} {r : World → World → Prop} (h : tbFC r) : symmFC r := h.2

/-- Adding `T(φ)@w` to a branch witnessing `branchSatisfiableIn tbFC` preserves
`branchSatisfiableIn tbFC`, given `T(□φ)@w` is already on the branch: the semantic core of the
TB box-positive self-propagation arm (`modalTBoxSelf`), projected from `reflFC` through
`tbFC_imp_reflFC`. -/
lemma branchSatisfiableIn_tbFC_boxPos_self_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc)
    {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    branchSatisfiableIn tbFC (⟨.pos, φ, w⟩ :: b) acc := by
  obtain ⟨W, m, f, hFC, hedges, hb⟩ := h
  refine ⟨W, m, f, hFC, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun _ => ?_, fun hcontra => by simp at hcontra⟩
    have hbox : Satisfies m (f w) (.box φ) := (hb _ hmem).1 rfl
    have hrefl : Std.Refl m.r := tbFC_imp_reflFC hFC
    exact hbox (f w) (hrefl.refl (f w))
  · exact hb sf hold

/-- Adding `F(φ)@w` to a branch witnessing `branchSatisfiableIn tbFC` preserves
`branchSatisfiableIn tbFC`, given `F(◇φ)@w` is already on the branch: the semantic core of the
TB diamond-negative self-propagation arm (`modalTDiaNegSelf`). Dual of
`branchSatisfiableIn_tbFC_boxPos_self_mem`. -/
lemma branchSatisfiableIn_tbFC_diaNeg_self_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc)
    {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    branchSatisfiableIn tbFC (⟨.neg, φ, w⟩ :: b) acc := by
  obtain ⟨W, m, f, hFC, hedges, hb⟩ := h
  refine ⟨W, m, f, hFC, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun hcontra => by simp at hcontra, fun _ hφ => ?_⟩
    have hdianeg : ¬ Satisfies m (f w) (.diamond φ) := (hb _ hmem).2 rfl
    have hrefl : Std.Refl m.r := tbFC_imp_reflFC hFC
    exact hdianeg (Satisfies.diamond_iff.mpr ⟨f w, hrefl.refl (f w), hφ⟩)
  · exact hb sf hold

/-- Adding `T(φ)@v` to a branch witnessing `branchSatisfiableIn tbFC` preserves
`branchSatisfiableIn tbFC`, given `T(□φ)@w` is already on the branch and `v → w` is a recorded
edge: the semantic core of the TB box-positive predecessor-backward arm (`modalBBoxBack`),
projected from `symmFC` through `tbFC_imp_symmFC`. -/
lemma branchSatisfiableIn_tbFC_boxPos_pred_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc)
    {φ : Proposition Atom} {v w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge v w = true) :
    branchSatisfiableIn tbFC (⟨.pos, φ, v⟩ :: b) acc := by
  obtain ⟨W, m, f, hFC, hedges, hb⟩ := h
  refine ⟨W, m, f, hFC, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun _ => ?_, fun hcontra => by simp at hcontra⟩
    have hbox : Satisfies m (f w) (.box φ) := (hb _ hmem).1 rfl
    have hsymm : Std.Symm m.r := tbFC_imp_symmFC hFC
    have hmvw : m.r (f v) (f w) := hedges v w hedge
    have hmwv : m.r (f w) (f v) := hsymm.symm (f v) (f w) hmvw
    exact hbox (f v) hmwv
  · exact hb sf hold

/-- Adding `F(φ)@v` to a branch witnessing `branchSatisfiableIn tbFC` preserves
`branchSatisfiableIn tbFC`, given `F(◇φ)@w` is already on the branch and `v → w` is a recorded
edge: the semantic core of the TB diamond-negative predecessor-backward arm
(`modalBDiaNegBack`). Dual of `branchSatisfiableIn_tbFC_boxPos_pred_mem`. -/
lemma branchSatisfiableIn_tbFC_diaNeg_pred_mem
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc)
    {φ : Proposition Atom} {v w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hedge : acc.hasEdge v w = true) :
    branchSatisfiableIn tbFC (⟨.neg, φ, v⟩ :: b) acc := by
  obtain ⟨W, m, f, hFC, hedges, hb⟩ := h
  refine ⟨W, m, f, hFC, hedges, ?_⟩
  intro sf hmem'
  rcases List.mem_cons.mp hmem' with rfl | hold
  · refine ⟨fun hcontra => by simp at hcontra, fun _ hφ => ?_⟩
    have hdianeg : ¬ Satisfies m (f w) (.diamond φ) := (hb _ hmem).2 rfl
    have hsymm : Std.Symm m.r := tbFC_imp_symmFC hFC
    have hmvw : m.r (f v) (f w) := hedges v w hedge
    have hmwv : m.r (f w) (f v) := hsymm.symm (f v) (f w) hmvw
    exact hdianeg (Satisfies.diamond_iff.mpr ⟨f v, hmwv, hφ⟩)
  · exact hb sf hold

/-- Rule-level TB soundness for the box-positive self-propagation arm: every formula produced
by `modalTBoxSelf` (given `T(□φ)@w` already on the branch) preserves `branchSatisfiableIn tbFC`
when added to the branch. -/
lemma modalTBoxSelf_tbFC_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalTBoxSelf b φ w, branchSatisfiableIn tbFC (sf :: b) acc := by
  intro sf hsf
  unfold modalTBoxSelf at hsf
  by_cases hcase :
      b.any (· == (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, List.mem_singleton] at hsf
    subst hsf
    exact branchSatisfiableIn_tbFC_boxPos_self_mem h hmem

/-- Rule-level TB soundness for the diamond-negative self-propagation arm: every formula
produced by `modalTDiaNegSelf` (given `F(◇φ)@w` already on the branch) preserves
`branchSatisfiableIn tbFC` when added to the branch. Dual of `modalTBoxSelf_tbFC_sound`. -/
lemma modalTDiaNegSelf_tbFC_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalTDiaNegSelf b φ w, branchSatisfiableIn tbFC (sf :: b) acc := by
  intro sf hsf
  unfold modalTDiaNegSelf at hsf
  by_cases hcase :
      b.any (· == (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
  · simp [hcase] at hsf
  · simp only [hcase, Bool.false_eq_true, if_false, List.mem_singleton] at hsf
    subst hsf
    exact branchSatisfiableIn_tbFC_diaNeg_self_mem h hmem

/-- Rule-level TB soundness for the box-positive predecessor-backward arm: every formula
produced by `modalBBoxBack` (given `T(□φ)@w` already on the branch) preserves
`branchSatisfiableIn tbFC` when added to the branch. -/
lemma modalBBoxBack_tbFC_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalBBoxBack b acc φ w, branchSatisfiableIn tbFC (sf :: b) acc := by
  intro sf hsf
  obtain ⟨hxeq, hpred, -, -⟩ := modalBBoxBack_mem hsf
  have hedge : acc.hasEdge sf.label w = true := modalBPredecessorsOf_hasEdge hpred
  rw [hxeq]
  exact branchSatisfiableIn_tbFC_boxPos_pred_mem h hmem hedge

/-- Rule-level TB soundness for the diamond-negative predecessor-backward arm: every formula
produced by `modalBDiaNegBack` (given `F(◇φ)@w` already on the branch) preserves
`branchSatisfiableIn tbFC` when added to the branch. Dual of `modalBBoxBack_tbFC_sound`. -/
lemma modalBDiaNegBack_tbFC_sound [DecidableEq Atom] [Hashable Atom]
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (h : branchSatisfiableIn tbFC b acc) {φ : Proposition Atom} {w : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ sf ∈ modalBDiaNegBack b acc φ w, branchSatisfiableIn tbFC (sf :: b) acc := by
  intro sf hsf
  obtain ⟨hxeq, hpred, -, -⟩ := modalBDiaNegBack_mem hsf
  have hedge : acc.hasEdge sf.label w = true := modalBPredecessorsOf_hasEdge hpred
  rw [hxeq]
  exact branchSatisfiableIn_tbFC_diaNeg_pred_mem h hmem hedge

/-! ## S5 (Equivalence Frame), Five, KB5

The frame-condition surface for S5's universal-cluster tableau (`S5Simplification.lean`) and
the 5/KB5 semantic bridge. `s5FC` mirrors `s4FC` (reflexive +
transitive) with `IsTrans` replaced by `Relation.RightEuclidean`: reflexive + (right)
Euclidean is equivalent to an equivalence relation (`Relation.symm_rightEuclidean_iff_trans`,
`Cslib/Foundations/Relation/Euclidean.lean`, together with reflexivity giving symmetry and
transitivity). `fiveFC`/`kb5FC` mirror `symmFC`/`s4FC` for the pure-Euclidean (`Cube.Five`)
and symmetric-plus-Euclidean (`Cube.KB5`) frame classes respectively. -/

/-- The S5 (equivalence) frame condition: `Std.Refl m.r ∧ Relation.RightEuclidean m.r`.
Instantiates `frameValid`/`branchSatisfiableIn` for the modal logic S5 (`Cube.S5`,
`K ∪ T ∪ Four ∪ Five`, `Cube.lean:85`): a reflexive right-Euclidean relation is an equivalence
relation (`Relation.symm_rightEuclidean_iff_trans` gives transitivity from Euclideanness once
symmetry is available, and reflexivity + Euclideanness together give symmetry via
`Relation.RightEuclidean.reflOn_cod`-style projections), matching S5's single-cluster model
property. -/
def s5FC : FrameCondition := fun {_} r => Std.Refl r ∧ Relation.RightEuclidean r

/-- S5-validity: `φ` is satisfied in every Kripke model whose relation is an equivalence
relation (reflexive + right-Euclidean), at every world. Matches `Cube.S5`. -/
def s5Valid (φ : Proposition Atom) : Prop := frameValid s5FC φ

/-- The pure-Euclidean frame condition: `Relation.RightEuclidean m.r`. Instantiates
`frameValid`/`branchSatisfiableIn` for the modal logic 5 (`Cube.Five`,
`{m | Relation.RightEuclidean m.r}`, `Cube.lean:45`). -/
def fiveFC : FrameCondition := fun {_} r => Relation.RightEuclidean r

/-- 5-validity: `φ` is satisfied in every Kripke model whose relation is right-Euclidean, at
every world. Matches `Cube.Five`. -/
def fiveValid (φ : Proposition Atom) : Prop := frameValid fiveFC φ

/-- The KB5 frame condition: `Std.Symm m.r ∧ Relation.RightEuclidean m.r`. Instantiates
`frameValid`/`branchSatisfiableIn` for the modal logic KB5 (`Cube.KB5`,
`K ∪ B ∪ Five`, `Cube.lean:73`). -/
def kb5FC : FrameCondition := fun {_} r => Std.Symm r ∧ Relation.RightEuclidean r

/-- KB5-validity: `φ` is satisfied in every Kripke model whose relation is symmetric and
right-Euclidean, at every world. Matches `Cube.KB5`. -/
def kb5Valid (φ : Proposition Atom) : Prop := frameValid kb5FC φ

/-! ## S5 vs 5/KB5 Frame-Class Separation

The standing, machine-checked (sorry-free, zero-axiom) proof that `s5FC` is a *strictly*
larger frame class than `fiveFC`/`kb5FC`, so no `s5Valid` decision procedure can ever decide
`fiveValid`/`kb5Valid` by composition -- the durable record that rules out
"simplifying" the Euclidean route into the S5 one. See `FrameCompleteness.lean`'s "5/KB5 Coverage
via the S5 Route" note for the full narrative and `kb5FC_imp_fiveFC`/`fiveValid_imp_kb5Valid`
above for the (independent) one-level-down `kb5FC ⇒ fiveFC` bridge needed for soundness.
-/

/-- `s5FC` entails `fiveFC` by projection: S5 frames are Euclidean frames with reflexivity added.
-/
theorem s5FC_imp_fiveFC {World : Type} {r : World → World → Prop} (h : s5FC r) : fiveFC r := h.2

/-- **Inclusion**: `fiveValid φ → s5Valid φ`. Validity over the larger (Euclidean) frame class is
the stronger requirement, so it descends to the smaller (S5) class. -/
theorem fiveValid_imp_s5Valid (φ : Proposition Atom) (h : fiveValid φ) : s5Valid φ :=
  fun World m hFC w => h World m hFC.2 w

/-- The one-world empty frame: the separating countermodel for `□p → p`. `r` is the empty
relation, and `p` is false at the sole world. -/
private def emptyFrame : Model Unit Unit where
  r := fun _ _ => False
  v := fun _ _ => False

/-- The empty relation is `RightEuclidean` -- vacuously, since it has no edges to chain. -/
private instance : Relation.RightEuclidean emptyFrame.r where
  rightEuclidean hab _ := absurd hab id

/-- The empty relation is `Std.Symm` -- vacuously, for the same reason. This is what makes the
countermodel serve `kb5FC` as well as `fiveFC`. -/
private instance : Std.Symm emptyFrame.r where
  symm _ _ hab := absurd hab id

/-- `□p` holds vacuously at the sole world of the empty frame: there is no accessible world. -/
private theorem box_atom_holds : Satisfies emptyFrame () (.box (.atom ())) :=
  fun _ hr => absurd hr id

/-- `p` fails at the sole world of the empty frame. -/
private theorem atom_fails : ¬ Satisfies emptyFrame () (.atom ()) := id

/-- **`□p → p` is `s5Valid`**, discharged by reflexivity alone -- this is the `T` axiom. -/
theorem boxImp_s5Valid (p : Unit) : s5Valid (.imp (.box (.atom p)) (.atom p)) := by
  intro World m hFC w hbox
  exact hbox w (hFC.1.refl w)

/-- **`□p → p` is NOT `fiveValid`**: the one-world empty frame is Euclidean and refutes it.
Reflexivity is exactly what `fiveFC` drops, and exactly what the proof above needed. -/
theorem boxImp_not_fiveValid : ¬ fiveValid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := by
  intro h
  exact atom_fails
    (h Unit emptyFrame (inferInstanceAs (Relation.RightEuclidean emptyFrame.r)) () box_atom_holds)

/-- **`□p → p` is NOT `kb5Valid`** either: the same countermodel is symmetric. So the gap is not
repaired by moving from 5 to KB5 -- `kb5FC` drops reflexivity too. -/
theorem boxImp_not_kb5Valid : ¬ kb5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := by
  intro h
  exact atom_fails (h Unit emptyFrame ⟨inferInstance, inferInstance⟩ () box_atom_holds)

/-- **`fiveValid ⊊ s5Valid`**: the inclusion is strict, witnessed by `□p → p`.

A sound+complete decision procedure for `s5Valid` cannot decide `fiveValid`: the S5 tableau's
closure sits on the wrong side of a strict inclusion. -/
theorem fiveValid_ssubset_s5Valid :
    (∀ φ : Proposition Unit, fiveValid φ → s5Valid φ) ∧
    (∃ φ : Proposition Unit, s5Valid φ ∧ ¬ fiveValid φ) :=
  ⟨fun φ => fiveValid_imp_s5Valid φ,
   ⟨.imp (.box (.atom ())) (.atom ()), boxImp_s5Valid (), boxImp_not_fiveValid⟩⟩

/-- `s5FC` entails `kb5FC`: reflexivity and right-Euclideanness together give symmetry. Proved
directly (`rightEuclidean ab (refl a) : r b a`) rather than via the `[Std.Refl r] : Std.Symm r`
instance at `Euclidean.lean:53`, so the argument is legible without instance-resolution context.
-/
theorem s5FC_imp_kb5FC {World : Type} {r : World → World → Prop} (h : s5FC r) : kb5FC r := by
  obtain ⟨hrefl, heucl⟩ := h
  exact ⟨⟨fun a _ ab => heucl.rightEuclidean ab (hrefl.refl a)⟩, heucl⟩

/-- **Inclusion**: `kb5Valid φ → s5Valid φ`. -/
theorem kb5Valid_imp_s5Valid (φ : Proposition Atom) (h : kb5Valid φ) : s5Valid φ :=
  fun World m hFC w => h World m (s5FC_imp_kb5FC hFC) w

/-- The same, for KB5: `kb5Valid ⊊ s5Valid`. -/
theorem kb5Valid_ssubset_s5Valid :
    (∀ φ : Proposition Unit, kb5Valid φ → s5Valid φ) ∧
    (∃ φ : Proposition Unit, s5Valid φ ∧ ¬ kb5Valid φ) :=
  ⟨fun φ => kb5Valid_imp_s5Valid φ,
   ⟨.imp (.box (.atom ())) (.atom ()), boxImp_s5Valid (), boxImp_not_kb5Valid⟩⟩

/-! ## S5 Soundness Bridge

`modalApplyOneS5`'s accessibility output is unconditionally identical to K's
(`modalApplyOneS5_snd_eq`, `S5Simplification.lean`), so the `freshLocal`/`knownWorlds`-step
dichotomies K's own machinery
established (`modalApplyOne_fresh_local`, `modalApplyOne_knownWorlds_step`, `FmpMeasure.lean`)
lift directly to `modalApplyOneS5`. These structural facts (independent of any Kripke semantics)
underwrite the new reachability invariant `accReachableInv`: every known world of a branch is
reachable from world `0` via the recorded accessibility edges. Combined with `s5FC`'s
equivalence-relation closure (`Std.Refl` + `Relation.RightEuclidean`), reachability from a common
origin gives full pairwise relatedness -- exactly what the universal box/diamond rules
(`modalS5BoxAll`/`modalS5DiaNegAll`) need to be semantically sound. -/

variable [DecidableEq Atom] [Hashable Atom]

omit [Hashable Atom] in
/-- `modalApplyOneS5` satisfies the same `freshLocal` dichotomy as `modalApplyOne`
(`modalApplyOne_fresh_local`, `FmpMeasure.lean:802`): either the accessibility relation is left
unchanged, or the result is `.linear (wsf :: rest)` with a fresh edge `sf.label → wsf.label`
added. Case 1 lifts via `modalApplyOneS5_snd_eq` (unconditional accessibility agreement); case 2
lifts via `modalApplyOneS5_eq_of_linear` (full agreement whenever K's own result is `.linear`). -/
lemma modalApplyOneS5_fresh_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (modalApplyOneS5 sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneS5 sf b acc).fst = RuleResult.linear (wsf :: rest)
      ∧ (modalApplyOneS5 sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  rcases modalApplyOne_fresh_local sf b acc with hsame | ⟨wsf, rest, hfst, hsnd⟩
  · exact Or.inl (by rw [modalApplyOneS5_snd_eq]; exact hsame)
  · have heq := modalApplyOneS5_eq_of_linear sf b acc (wsf :: rest) hfst
    exact Or.inr ⟨wsf, rest, by rw [heq]; exact hfst, by rw [heq]; exact hsnd⟩

/-! ### The Reachability Invariant

`modalApplyOneS5_knownWorlds_step` (`S5Simplification.lean:860`) is
the S5 analogue of K's `modalApplyOne_knownWorlds_step` used directly below. -/

/-- Every known world of a branch is reachable from world `0` via the recorded accessibility
edges (the reflexive-transitive closure of `acc.hasEdge`). This is the extra invariant S5
soundness needs beyond `accFreshInv`: since the universal rules (`modalS5BoxAll`/
`modalS5DiaNegAll`) propagate to *every* known world (not just directly-`acc`-connected ones),
their semantic soundness needs *every* known world related to a common origin in the model, not
just directly-`acc`-connected pairs. Composed with `s5FC`'s equivalence-relation closure, common
reachability from `0` gives full pairwise relatedness. -/
def accReachableInv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∀ w ∈ modalKnownWorlds b, Relation.ReflTransGen (fun a c => acc.hasEdge a c) 0 w

omit [DecidableEq Atom] [Hashable Atom] in
/-- `accReachableInv` holds for the initial singleton branch `[⟨.neg, φ, 0⟩]` against the empty
accessibility relation: its only known world is `0` itself, reachable from `0` by reflexivity. -/
lemma accReachableInv_initial (φ : Proposition Atom) :
    accReachableInv [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]
      Accessibility.empty := by
  intro w hw
  have : w = 0 := by
    simpa [modalKnownWorlds] using hw
  subst this
  exact Relation.ReflTransGen.refl

omit [DecidableEq Atom] [Hashable Atom] in
/-- Common reachability from world `0` (via `acc`'s edges, related into the model through
`hacc`) gives full relatedness to `0` under `s5FC`: `Std.Refl` handles the base case, and each
edge-step composes via `Relation.RightEuclidean.rightEuclidean` applied twice (once to symmetrize
the accumulated witness, once to compose it with the new edge's `hacc`-derived relatedness). This
is the semantic payoff of `accReachableInv`: two known worlds, both reachable from `0`, are
related to each other in *any* model whose relation is an equivalence relation, not just
directly-`acc`-connected pairs. -/
lemma reachable_imp_related_s5
    {acc : Accessibility} {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : s5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    {w : WorldIndex} (hreach : Relation.ReflTransGen (fun a c => acc.hasEdge a c) 0 w) :
    m.r (f 0) (f w) := by
  induction hreach with
  | refl => exact hFC.1.refl (f 0)
  | tail hprev hedge ih =>
    have hstep : m.r (f _) (f _) := hacc _ _ hedge
    have hsymm : m.r (f _) (f 0) := hFC.2.rightEuclidean ih (hFC.1.refl (f 0))
    exact hFC.2.rightEuclidean hsymm hstep

omit [DecidableEq Atom] [Hashable Atom] in
/-- Two worlds, both known on a branch satisfying `accReachableInv`, are related in *either*
direction under `s5FC`: the pointwise combination of `reachable_imp_related_s5` (twice, from the
common origin `0`) via one more `rightEuclidean` application. This is exactly the fact the S5
universal rules need: `T(□φ)@lbl ∈ b` propagates to *every* known world `w'`, regardless of any
recorded direct edge between `lbl` and `w'`. -/
lemma accReachableInv_related_s5
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : s5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hreach : accReachableInv b acc)
    {w w' : WorldIndex} (hw : w ∈ modalKnownWorlds b) (hw' : w' ∈ modalKnownWorlds b) :
    m.r (f w) (f w') :=
  hFC.2.rightEuclidean (reachable_imp_related_s5 hFC hacc (hreach w hw))
    (reachable_imp_related_s5 hFC hacc (hreach w' hw'))

/-! ### The Euclidean (Non-Reflexive) Reachability Discharge

`fiveFC := Relation.RightEuclidean r` drops `s5FC`'s reflexivity conjunct, so
`reachable_imp_related_s5`'s base case (`hFC.1.refl (f 0)`) is unavailable -- and genuinely
false at the frame level (witnessed by a `Fin 3` counterexample: `RightEuclidean` with
`¬ r 0 2`). This is resolved by restricting root-triggered propagation to direct successors
(`modalFiveBoxAll`/`modalFiveDiaNegAll`'s `hasEdge 0 w'` guard) and discharging non-root-triggered
propagation through the **codomain equivalence** (`Relation.rooted_cluster_isEquiv`)
rather than frame reflexivity. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every known, non-root world reachable from `0` is related **in the model** to some direct
root successor's image: `reachable_imp_related_s5`'s analogue without reflexivity, landing on
`m.r (f s) (f w)` for a genuine direct successor `s` of `0` (`acc.hasEdge 0 s`) instead of directly
on `m.r (f 0) (f w)` (which is false in general for pure `RightEuclidean`). The induction's tail
step composes the accumulated witness `s` with the new edge via `RightEuclidean.rightEuclidean`,
recovering the needed symmetry from the **codomain equivalence** (`rooted_cluster_isEquiv`,
consuming that both `f s` and the previous node's image lie in `cod m.r`) rather than from frame
reflexivity. -/
lemma reachable_imp_cod_related_five
    {acc : Accessibility} {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : fiveFC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    {w : WorldIndex} (hw0 : w ≠ 0)
    (hreach : Relation.ReflTransGen (fun a c => acc.hasEdge a c) 0 w) :
    ∃ s, acc.hasEdge 0 s = true ∧ m.r (f s) (f w) := by
  haveI : Relation.RightEuclidean m.r := hFC
  revert hw0
  induction hreach with
  | refl => intro h; exact absurd rfl h
  | tail hprev hedge ih =>
    rename_i w0 w
    intro _
    by_cases hw00 : w0 = (0 : WorldIndex)
    · subst hw00
      refine ⟨w, hedge, ?_⟩
      exact Relation.RightEuclidean.reflOn_cod.of_cod (hacc 0 w hedge)
    · obtain ⟨s, hs0, hsw0⟩ := ih hw00
      have hs_cod : f s ∈ Relation.cod m.r := ⟨f 0, hacc 0 s hs0⟩
      have hw0_cod : f w0 ∈ Relation.cod m.r := ⟨f s, hsw0⟩
      have hEquiv := Relation.rooted_cluster_isEquiv (r := m.r)
      have hsymm : m.r (f w0) (f s) :=
        hEquiv.symm (⟨f s, hs_cod⟩ : Relation.cod m.r) ⟨f w0, hw0_cod⟩ hsw0
      have hstep : m.r (f w0) (f w) := hacc w0 w hedge
      exact ⟨s, hs0, Relation.RightEuclidean.rightEuclidean hsymm hstep⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Two **non-root** known worlds, both known on a branch satisfying `accReachableInv`, are
related in the model under `fiveFC`: the Route (1) analogue of `accReachableInv_related_s5`,
needed only for the non-root-triggered propagation arm (the root-triggered arm is discharged
directly by `hacc` on the `modalFiveBoxAll_root_hasEdge`/`modalFiveDiaNegAll_root_hasEdge`
witness, with no need for this lemma). Each side is anchored at its own direct-root-successor
witness (`reachable_imp_cod_related_five`), the two anchors are related via one `rightEuclidean`
composition sharing `f 0` as common source, and the two composition legs are re-oriented via the
codomain equivalence exactly as in `reachable_imp_cod_related_five`'s own tail step. -/
lemma accReachableInv_related_five
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : fiveFC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hreach : accReachableInv b acc)
    {w w' : WorldIndex} (hw : w ∈ modalKnownWorlds b) (hw' : w' ∈ modalKnownWorlds b)
    (hwne : w ≠ 0) (hw'ne : w' ≠ 0) :
    m.r (f w) (f w') := by
  haveI : Relation.RightEuclidean m.r := hFC
  obtain ⟨s, hs0, hsw⟩ := reachable_imp_cod_related_five hFC hacc hwne (hreach w hw)
  obtain ⟨s', hs'0, hs'w'⟩ := reachable_imp_cod_related_five hFC hacc hw'ne (hreach w' hw')
  have h0s : m.r (f 0) (f s) := hacc 0 s hs0
  have h0s' : m.r (f 0) (f s') := hacc 0 s' hs'0
  have hC : m.r (f s) (f s') := Relation.RightEuclidean.rightEuclidean h0s h0s'
  have hD : m.r (f w) (f s') := Relation.RightEuclidean.rightEuclidean hsw hC
  have hw_cod : f w ∈ Relation.cod m.r := ⟨f s, hsw⟩
  have hs'_cod : f s' ∈ Relation.cod m.r := ⟨f 0, h0s'⟩
  have hEquiv := Relation.rooted_cluster_isEquiv (r := m.r)
  have hD' : m.r (f s') (f w) :=
    hEquiv.symm (⟨f w, hw_cod⟩ : Relation.cod m.r) ⟨f s', hs'_cod⟩ hD
  exact Relation.RightEuclidean.rightEuclidean hD' hs'w'

/-! ### The KB5 Full-Cluster Reachability Discharge

`kb5FC := Std.Symm m.r ∧ Relation.RightEuclidean m.r` adds symmetry on top of `fiveFC`, which
gives a **direct** induction on `accReachableInv`'s `ReflTransGen` path -- no cod-equivalence
detour needed, unlike `reachable_imp_cod_related_five`/`accReachableInv_related_five` above. At
each step `a → b` of the path: if `a = 0` the edge is itself a direct root witness (`hacc`
applied directly); otherwise the accumulated witness `m.r (f 0) (f a)` symmetrizes to
`m.r (f a) (f 0)` (`Std.Symm`) and composes with the new edge's `m.r (f a) (f b)` via
`RightEuclidean.rightEuclidean` (`x := f a, y := f 0, z := f b`) to give `m.r (f 0) (f b)`
directly. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every world reachable from `0` via the recorded accessibility edges (`ReflTransGen`), other
than `0` itself, is related **to `0`** in the model under `kb5FC` -- no root-successor anchor
needed (contrast `reachable_imp_cod_related_five`, which lands on a direct-successor witness
`s` rather than `0` itself, since `fiveFC` alone cannot symmetrize). This is the semantic payoff
of `kb5FC`'s extra `Std.Symm` conjunct: the whole known non-root cluster relates directly back to
the root, matching `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`'s unconditional (non-edge-gated)
propagation target set. -/
lemma reachable_imp_related_kb5
    {acc : Accessibility} {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : kb5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    {w : WorldIndex} (hw0 : w ≠ 0)
    (hreach : Relation.ReflTransGen (fun a c => acc.hasEdge a c) 0 w) :
    m.r (f 0) (f w) := by
  haveI : Std.Symm m.r := hFC.1
  haveI : Relation.RightEuclidean m.r := hFC.2
  revert hw0
  induction hreach with
  | refl => intro h; exact absurd rfl h
  | tail hprev hedge ih =>
    rename_i w0 w
    intro _
    by_cases hw00 : w0 = (0 : WorldIndex)
    · subst hw00
      exact hacc 0 w hedge
    · have h0w0 : m.r (f 0) (f w0) := ih hw00
      have hw00' : m.r (f w0) (f 0) := Std.Symm.symm _ _ h0w0
      have hstep : m.r (f w0) (f w) := hacc w0 w hedge
      exact Relation.RightEuclidean.rightEuclidean hw00' hstep

omit [DecidableEq Atom] [Hashable Atom] in
/-- Two known non-root worlds, both reachable from `0` on a branch satisfying `accReachableInv`,
are related in the model under `kb5FC`: each anchors directly to `f 0`
(`reachable_imp_related_kb5`), then one more `RightEuclidean` composition (via symmetrizing the
first leg) relates them to each other. Mirrors `accReachableInv_related_five`'s role but via the
simpler direct-anchor route `kb5FC`'s symmetry affords. -/
lemma accReachableInv_related_kb5
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : kb5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hreach : accReachableInv b acc)
    {w w' : WorldIndex} (hw : w ∈ modalKnownWorlds b) (hw' : w' ∈ modalKnownWorlds b)
    (hwne : w ≠ 0) (hw'ne : w' ≠ 0) :
    m.r (f w) (f w') := by
  haveI : Std.Symm m.r := hFC.1
  haveI : Relation.RightEuclidean m.r := hFC.2
  have h0w : m.r (f 0) (f w) := reachable_imp_related_kb5 hFC hacc hwne (hreach w hw)
  have h0w' : m.r (f 0) (f w') := reachable_imp_related_kb5 hFC hacc hw'ne (hreach w' hw')
  exact Relation.RightEuclidean.rightEuclidean h0w h0w'

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Root self-reflexivity discharge** (`Relation.symm_rightEuclidean_root_refl`): if
the known cluster of `b` has *some* non-root member `v`, the root is related to itself in the
model under `kb5FC`. This is exactly the semantic justification for
`modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`'s self-target arm (fires unconditionally whenever the
cluster is nonempty): `v`'s anchor `m.r (f 0) (f v)` (`reachable_imp_related_kb5`) symmetrizes to
`m.r (f v) (f 0)`, and `RightEuclidean` applied to that pair with itself (`x := f v, y := f 0,
z := f 0`)
gives `m.r (f 0) (f 0)` directly -- the model-level mirror of
`Relation.symm_rightEuclidean_root_refl`. -/
lemma accReachableInv_kb5_root_refl
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : kb5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hreach : accReachableInv b acc)
    {v : WorldIndex} (hv : v ∈ modalKnownWorlds b) (hvne : v ≠ 0) :
    m.r (f 0) (f 0) := by
  haveI : Std.Symm m.r := hFC.1
  haveI : Relation.RightEuclidean m.r := hFC.2
  have h0v : m.r (f 0) (f v) := reachable_imp_related_kb5 hFC hacc hvne (hreach v hv)
  have hv0 : m.r (f v) (f 0) := Std.Symm.symm _ _ h0v
  exact Relation.RightEuclidean.rightEuclidean hv0 hv0

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every emitted label of `xs` known in `b` puts every known world of `xs ++ b` back inside
`modalKnownWorlds b`: the converse direction to `modalKnownWorlds_mono_append`, needed when
the appended formulas' labels are already known (the S5 universal-propagation and K
propositional/propagation arms). -/
private lemma modalKnownWorlds_append_subset_of_labels_known
    {xs b : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hxs : ∀ x ∈ xs, x.label ∈ modalKnownWorlds b) :
    ∀ w ∈ modalKnownWorlds (xs ++ b), w ∈ modalKnownWorlds b := by
  intro w hw
  rw [mem_modalKnownWorlds] at hw
  obtain ⟨sf, hsf, rfl⟩ := hw
  rcases List.mem_append.mp hsf with hxsf | hbsf
  · exact hxs sf hxsf
  · rw [mem_modalKnownWorlds]; exact ⟨sf, hbsf, rfl⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `acc.addEdge w w'` only ever grows the edge set: every edge already recorded in `acc`
survives. Converse direction to `hasEdge_addEdge_cases`; needed to lift `accReachableInv`'s
reachability witnesses forward under `Relation.ReflTransGen.mono` when an edge is added. -/
private lemma hasEdge_addEdge_mono_FS {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : acc.hasEdge a a' = true) :
    (acc.addEdge w w').hasEdge a a' = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true]
  exact Or.inr h

omit [DecidableEq Atom] [Hashable Atom] in
/-- The new edge `w → w'` recorded by `acc.addEdge w w'` is itself present. -/
private lemma hasEdge_addEdge_self_FS (acc : Accessibility) (w w' : WorldIndex) :
    (acc.addEdge w w').hasEdge w w' = true := by
  simp [Accessibility.addEdge, Accessibility.hasEdge]

/-! ### `accReachableInv` Preservation for `modalApplyOneFive`

Stated directly over `modalApplyOneFive` (no `RuleApply`/`S5SoundSpec` abstraction: Five has only
the one shipped rule), consuming `modalApplyOneFiveProp_knownWorlds_step` and
`modalApplyOneFive_agree_or_reuse` (`FiveSimplification.lean`) in place of the S5 chain's
`modalApplyOneS5_knownWorlds_step` and `S5SoundSpec` hypothesis. Mirrors
`modalStepBranchS5Gen_preserves_accReachableInv`'s proof structure exactly, specialized at
`apply := modalApplyOneFive`. -/

/-- A `modalStepBranchGen modalApplyOneFive` step preserves `accReachableInv`, given
`accTargetsKnown`. At a **reuse** call (`modalApplyOneFive_agree_or_reuse`'s right disjunct) the
target `sf'.label` is a world already known on `b`, so no new world appears and every witness
transfers under `hasEdge_addEdge_mono_FS`; at an **agree** call,
`modalApplyOneFiveProp_knownWorlds_step`'s "acc unchanged" branch transfers reachability directly
(every new label was already known), and its "mint" branch extends the popped formula's own
(already-known, hence already-reachable) witness by the one fresh edge. -/
lemma modalStepBranchFive_preserves_accReachableInv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneFive b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc)
    (hInv : accReachableInv b acc) :
    ∀ b' ∈ newBs, accReachableInv b' newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsflabel_known : sf.label ∈ modalKnownWorlds b := (mem_modalKnownWorlds b sf.label).mpr
    ⟨sf, hsfmem, rfl⟩
  rcases modalApplyOneFive_agree_or_reuse sf b acc with heq | ⟨sf', hsf'mem, heq⟩
  swap
  · -- Reuse: the emitted formula is already on `b`, so the child branch knows no new world;
    -- every reachability witness survives the one added edge by monotonicity.
    rw [heq] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, rfl⟩ := hsf
    intro b' hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro w hw
    have hsf'known : sf'.label ∈ modalKnownWorlds b :=
      (mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hsf'mem, rfl⟩
    have hknown' : ∀ x ∈ [sf'], x.label ∈ modalKnownWorlds b := by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact hsf'known
    exact Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _
      (hInv w (modalKnownWorlds_append_subset_of_labels_known hknown' w hw))
  rw [heq] at hsf
  rcases modalApplyOneFiveProp_knownWorlds_step sf b acc hsfmem hknown with
    ⟨hsndeq, hdich⟩ | ⟨hsndeq, hdich⟩
  · -- acc unchanged: every new label of the child branch was already known on `b`.
    rcases hfstc : (modalApplyOneFiveProp sf b acc).fst with nf | brs | nf | _
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hdich w hw)
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'
      obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
      have hbr_known : ∀ x ∈ br, x.label ∈ modalKnownWorlds b :=
        fun x hx => hdich x (List.mem_flatten.mpr ⟨br, hbrmem, hx⟩)
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hbr_known w hw)
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hdich w hw)
    · rw [hfstc] at hsf; simp at hsf
  · -- mint case: one fresh edge `sf.label → modalNextWorld b` added.
    rcases hfstc : (modalApplyOneFiveProp sf b acc).fst with nf | brs | nf | _
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      obtain ⟨-, hlabels⟩ := hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      intro w hw
      rw [mem_modalKnownWorlds] at hw
      obtain ⟨sf', hsf', rfl⟩ := hw
      rcases List.mem_append.mp hsf' with hnew | hold
      · -- the fresh world: extend sf.label's (already-known) reachability witness by one hop.
        rw [hlabels sf' hnew]
        exact (Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _ (hInv sf.label
          hsflabel_known)).tail (hasEdge_addEdge_self_FS acc sf.label (modalNextWorld b))
      · exact Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _
          (hInv sf'.label ((mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hold, rfl⟩))
    · rw [hfstc] at hdich; exact hdich.elim
    · rw [hfstc] at hdich; exact hdich.elim
    · rw [hfstc] at hsf; simp at hsf

/-! ### The Agree-or-Reuse Per-Call Contract

The S5 soundness chain below is stated over an abstract `apply : RuleApply Atom` constrained by
`S5SoundSpec` rather than over `modalApplyOneS5` directly. `S5SoundSpec` is the exact per-call
contract the whole chain consumes, and it is deliberately the weakest one that both the
unguarded universal rule and the witness-reuse rule satisfy:

* `modalApplyOneS5` satisfies it by always taking the left disjunct (`Or.inl rfl`), so every
  theorem below specializes back to its original statement as a free corollary.
* `modalApplyOneS5w` satisfies it because its two reuse arms emit `.linear [sf']` for a signed
  formula `sf'` **already on the branch**, together with the single edge `sf.label → sf'.label`.

The right disjunct's `sf' ∈ b` is what makes the reuse edge cheap to discharge semantically: it
simultaneously supplies the *formula* obligation (`sf'` is already satisfied by any model of `b`,
so re-asserting it is free) and the *edge* obligation (`sf'.label` is a known world of `b`, so
`accReachableInv_related_s5` relates it to `sf.label` in any `s5FC` model). This is why witness
reuse is structurally easier than minting: no world is created, so the world-assignment `f` is
never extended. -/

/-- The per-call contract the S5 soundness chain consumes: at every call site, `apply` either
agrees with `modalApplyOneS5` outright, or fires a **witness reuse** -- emitting `.linear [sf']`
for a signed formula `sf'` already present on the branch, plus the single edge
`sf.label → sf'.label`. Paired with the per-branch invariant `S5SoundInv`. -/
def S5SoundSpec (apply : RuleApply Atom) : Prop :=
  ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
    apply sf b acc = modalApplyOneS5 sf b acc ∨
    ∃ sf' : SignedFormula (Proposition Atom) WorldIndex,
      sf' ∈ b ∧ apply sf b acc = (RuleResult.linear [sf'], acc.addEdge sf.label sf'.label)

/-- `modalApplyOneS5` satisfies `S5SoundSpec` degenerately: it never reuses, so the left
disjunct always fires. This is what re-derives every original S5 soundness statement below as a
free corollary of its lifted form. -/
lemma modalApplyOneS5_s5SoundSpec : S5SoundSpec (Atom := Atom) modalApplyOneS5 :=
  fun _ _ _ => Or.inl rfl

/-- `modalApplyOneS5w` satisfies `S5SoundSpec`. Outside the two mint shapes it is definitionally
`modalApplyOneS5` (`modalApplyOneS5w_eq_of_not_mint_shape`), as it is at a mint shape with no
available witness. At a mint shape *with* a witness `w'`, the emitted formula `⟨s, φ, w'⟩` is on
the branch by `witnessWorldS5_mem` and its label is `w'`, so the right disjunct fires. -/
lemma modalApplyOneS5w_s5SoundSpec : S5SoundSpec (Atom := Atom) modalApplyOneS5w := by
  intro sf b acc
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
  case pos.diamond =>
    unfold modalApplyOneS5w
    cases hw : witnessWorldS5 b Sign.pos φ with
    | none => exact Or.inl (by simp only [hw])
    | some w' => exact Or.inr ⟨⟨.pos, φ, w'⟩, witnessWorldS5_mem hw, by simp only [hw]⟩
  case neg.box =>
    unfold modalApplyOneS5w
    cases hw : witnessWorldS5 b Sign.neg φ with
    | none => exact Or.inl (by simp only [hw])
    | some w' => exact Or.inr ⟨⟨.neg, φ, w'⟩, witnessWorldS5_mem hw, by simp only [hw]⟩
  all_goals exact Or.inl (modalApplyOneS5w_eq_of_not_mint_shape _ b acc (by simp))

/-- Single-step reachability preservation, lifted over any `apply` satisfying `S5SoundSpec`. At
the "acc unchanged" branch of `modalApplyOneS5_knownWorlds_step` (the universal-propagation arms,
which only ever target *known* worlds, and every ordinary K arm outside the two minting shapes),
every newly known world of the child branch was already known on `b`, so the (unchanged)
reachability witness transfers directly; at the "mint" branch (the two K-minting shapes, disjoint
from the S5-relevant shapes, so untouched by the universal arms), the one fresh world is reached
by extending the popped formula's own (already-known, hence already-reachable) witness by the new
edge. At a **reuse** call the target `sf'.label` is a world already known on `b`, so no new world
appears at all and every witness transfers under `hasEdge_addEdge_mono_FS`. -/
lemma modalStepBranchS5Gen_preserves_accReachableInv
    (apply : RuleApply Atom) (hspec : S5SoundSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc)
    (hInv : accReachableInv b acc) :
    ∀ b' ∈ newBs, accReachableInv b' newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsflabel_known : sf.label ∈ modalKnownWorlds b := (mem_modalKnownWorlds b sf.label).mpr
    ⟨sf, hsfmem, rfl⟩
  rcases hspec sf b acc with heq | ⟨sf', hsf'mem, heq⟩
  swap
  · -- Reuse: the emitted formula is already on `b`, so the child branch knows no new world;
    -- every reachability witness survives the one added edge by monotonicity.
    rw [heq] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, rfl⟩ := hsf
    intro b' hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro w hw
    have hsf'known : sf'.label ∈ modalKnownWorlds b :=
      (mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hsf'mem, rfl⟩
    have hknown' : ∀ x ∈ [sf'], x.label ∈ modalKnownWorlds b := by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact hsf'known
    exact Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _
      (hInv w (modalKnownWorlds_append_subset_of_labels_known hknown' w hw))
  rw [heq] at hsf
  rcases modalApplyOneS5_knownWorlds_step sf b acc hsfmem hknown with
    ⟨hsndeq, hdich⟩ | ⟨hsndeq, hdich⟩
  · -- acc unchanged: every new label of the child branch was already known on `b`.
    rcases hfstc : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | _
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hdich w hw)
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'
      obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
      have hbr_known : ∀ x ∈ br, x.label ∈ modalKnownWorlds b :=
        fun x hx => hdich x (List.mem_flatten.mpr ⟨br, hbrmem, hx⟩)
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hbr_known w hw)
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hdich w hw)
    · rw [hfstc] at hsf; simp at hsf
  · -- mint case: one fresh edge `sf.label → modalNextWorld b` added.
    rcases hfstc : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | _
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      obtain ⟨-, hlabels⟩ := hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      intro w hw
      rw [mem_modalKnownWorlds] at hw
      obtain ⟨sf', hsf', rfl⟩ := hw
      rcases List.mem_append.mp hsf' with hnew | hold
      · -- the fresh world: extend sf.label's (already-known) reachability witness by one hop.
        rw [hlabels sf' hnew]
        exact (Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _ (hInv sf.label
          hsflabel_known)).tail (hasEdge_addEdge_self_FS acc sf.label (modalNextWorld b))
      · exact Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _
          (hInv sf'.label ((mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hold, rfl⟩))
    · rw [hfstc] at hdich; exact hdich.elim
    · rw [hfstc] at hdich; exact hdich.elim
    · rw [hfstc] at hsf; simp at hsf

/-- A `modalStepBranchGen modalApplyOneS5` step preserves `accReachableInv`, given
`accTargetsKnown`. Free corollary of `modalStepBranchS5Gen_preserves_accReachableInv` at the
degenerate spec `modalApplyOneS5_s5SoundSpec`; statement unchanged. -/
lemma modalStepBranchS5_preserves_accReachableInv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneS5 b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc)
    (hInv : accReachableInv b acc) :
    ∀ b' ∈ newBs, accReachableInv b' newAcc :=
  modalStepBranchS5Gen_preserves_accReachableInv modalApplyOneS5 modalApplyOneS5_s5SoundSpec
    b e acc newBs newExps newAcc hstep hknown hInv

/-- A `modalStepBranchGen modalApplyOneS5w` step preserves `accReachableInv`. Free corollary of
`modalStepBranchS5Gen_preserves_accReachableInv` at `modalApplyOneS5w_s5SoundSpec`. -/
lemma modalStepBranchS5w_preserves_accReachableInv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneS5w b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc)
    (hInv : accReachableInv b acc) :
    ∀ b' ∈ newBs, accReachableInv b' newAcc :=
  modalStepBranchS5Gen_preserves_accReachableInv modalApplyOneS5w modalApplyOneS5w_s5SoundSpec
    b e acc newBs newExps newAcc hstep hknown hInv

/-! ### Rule-Level S5 Semantic Soundness -/

omit [Hashable Atom] in
/-- Frame-relativized semantic soundness of `modalApplyOneS5`'s
box-positive output under `s5FC`, given `accReachableInv`. K's own bounded propagation
(`kForms`, at `acc.successorsOf lbl`) is sound via the existing `modalApplyOne_boxPos_sound`
(direct-edge relatedness, `FC` unused); the S5-added universal propagation
(`modalS5BoxAll b φ lbl`, to *every* known world) is sound via `accReachableInv_related_s5`:
`lbl` and any target world `x.label` are both known, hence related in the model regardless of
any direct edge between them. -/
lemma modalS5BoxAll_soundIn
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : s5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf) (hreach : accReachableInv b acc)
    {φ : Proposition Atom} {lbl : WorldIndex}
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS5
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneS5
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have hKeq := modalApplyOne_boxPos_eq
    (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
  have hKsound := modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem
  have hlblknown : lbl ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b lbl).mpr
      ⟨(⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem, rfl⟩
  have hallSat : ∀ x ∈ modalS5BoxAll b φ lbl, sfSat m f x := by
    intro x hx
    obtain ⟨hxeq, hxknown, -⟩ := modalS5BoxAll_mem hx
    have hboxsat : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
    simp only [Satisfies] at hboxsat
    have hrel : m.r (f lbl) (f x.label) :=
      accReachableInv_related_s5 hFC hacc hreach hlblknown hxknown
    rw [hxeq]
    exact sfSat_pos m f φ x.label (hboxsat (f x.label) hrel)
  unfold modalApplyOneS5
  rcases hp : modalApplyOne (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)
      b acc with ⟨kResult, kAcc⟩
  rw [hp] at hKeq hKsound
  simp only at hKeq hKsound
  rcases hKeq with hKeq | ⟨kForms, hKeq⟩ <;> subst hKeq
  · obtain ⟨hsndeq, -⟩ := hKsound
    dsimp only
    split_ifs with hemp
    · exact ⟨hsndeq, trivial⟩
    · exact ⟨hsndeq, hallSat⟩
  · obtain ⟨hsndeq, hKformSat⟩ := hKsound
    dsimp only
    refine ⟨hsndeq, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hKformSat x hx
    · exact hallSat x hx

omit [Hashable Atom] in
/-- Dual of `modalS5BoxAll_soundIn` for the diamond-negative shape. -/
lemma modalS5DiaNegAll_soundIn
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : s5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf) (hreach : accReachableInv b acc)
    {φ : Proposition Atom} {lbl : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS5
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneS5
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have hKeq := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
  have hKsound := modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem
  have hlblknown : lbl ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b lbl).mpr
      ⟨(⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem, rfl⟩
  have hallSat : ∀ x ∈ modalS5DiaNegAll b φ lbl, sfSat m f x := by
    intro x hx
    obtain ⟨hxeq, hxknown, -⟩ := modalS5DiaNegAll_mem hx
    have hdiasat : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
    simp only [Satisfies] at hdiasat
    push Not at hdiasat
    have hrel : m.r (f lbl) (f x.label) :=
      accReachableInv_related_s5 hFC hacc hreach hlblknown hxknown
    rw [hxeq]
    exact sfSat_neg m f φ x.label (hdiasat (f x.label) hrel)
  unfold modalApplyOneS5
  rcases hp : modalApplyOne
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hKeq hKsound
  simp only at hKeq hKsound
  rcases hKeq with hKeq | ⟨kForms, hKeq⟩ <;> subst hKeq
  · obtain ⟨hsndeq, -⟩ := hKsound
    dsimp only
    split_ifs with hemp
    · exact ⟨hsndeq, trivial⟩
    · exact ⟨hsndeq, hallSat⟩
  · obtain ⟨hsndeq, hKformSat⟩ := hKsound
    dsimp only
    refine ⟨hsndeq, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hKformSat x hx
    · exact hallSat x hx

/-! ### The Bespoke S5 Fuel-Induction Assembly

The generic `modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`
cannot be instantiated at `apply := modalApplyOneS5` directly: their
`hBoxPos`/`hDiaNeg` parameters are universally quantified over *all* `(b, acc)` pairs, with no
parameter slot to receive `accReachableInv b acc` -- a fact about *this specific* `(b, acc)`'s
computational history, not derivable from `hacc` alone for an arbitrary pair. The theorems below
are bespoke S5 specializations: the box-positive/diamond-negative branches are replaced by
`modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn` (consuming the threaded
`accReachableInv` witness); every other shape is *identical* to the generic crux's own "not
shape" branch (reachability is irrelevant there -- only the two S5-relevant shapes need it) and
is reused verbatim via `modalApplyOneS5_eq_of_not_boxPos_diaNeg`. -/

/-- The combined per-step invariant the S5 fuel induction threads:
`accFreshInv` (fresh-world confinement, needed by the two K-minting shapes inside the per-step
satisfiability lemma), `accReachableInv` (needed by the two
S5-relevant shapes), and `accTargetsKnown` (needed to preserve `accReachableInv` itself across a
step, via `modalStepBranchS5_preserves_accReachableInv`). Bundled into one `Prop` so
a single `List.Forall₂` threads all three through the outer induction, mirroring how
`modalExpandBranchesGen_closed_unsatIn` threads `accFreshInv` alone. -/
def S5SoundInv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  accFreshInv b acc ∧ accReachableInv b acc ∧ accTargetsKnown b acc

/-- Per-step satisfiability preservation for the S5 frame condition, lifted over any `apply`
satisfying `S5SoundSpec`. Specialization of `modalStepBranchGen_preserves_satIn` to `FC := s5FC`,
threading the extra `accReachableInv` witness the two S5-relevant shapes need. The
box-positive/diamond-negative branches discharge via the landed
`modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn` (consuming `hreach`); every other shape is
byte-identical to the generic crux's own "not shape" branch, ported via
`modalApplyOneS5_eq_of_not_boxPos_diaNeg` in place of the generic `hAgree` parameter.

The **reuse** call handled up front is the only case the unguarded universal rule cannot produce,
and it is the cheapest of all: no world is minted, so the world-assignment `f` is not extended
and the model is carried over verbatim. Both obligations fall out of `sf' ∈ b` -- the re-asserted
formula is already satisfied (`hb sf'`), and the single new edge `sf.label → sf'.label` connects
two *known* worlds, which `accReachableInv_related_s5` relates in any model whose relation is an
equivalence. -/
theorem modalStepBranchS5Gen_preserves_satIn
    (apply : RuleApply Atom) (hspec : S5SoundSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiableIn s5FC b acc)
    (hInv : accFreshInv b acc)
    (hreach : accReachableInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiableIn s5FC b' newAcc := by
  obtain ⟨W, m, f, hFC, hacc, hb⟩ := hsat
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsflabel_known : sf.label ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b sf.label).mpr ⟨sf, hsfmem, rfl⟩
  rcases hspec sf b acc with heq | ⟨sf', hsf'mem, heq⟩
  swap
  · -- Witness reuse: re-assert a formula already on `b` and record one edge between two
    -- already-known worlds. The model is unchanged; `f` is not extended.
    have hsf'known : sf'.label ∈ modalKnownWorlds b :=
      (mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hsf'mem, rfl⟩
    rw [heq] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, rfl⟩ := hsf
    refine ⟨[sf'] ++ b, List.mem_cons_self, W, m, f, hFC, ?_, ?_⟩
    · -- The one new edge relates two known worlds; every old edge survives via `hacc`.
      intro w1 w2 hedge
      rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
      · exact accReachableInv_related_s5 hFC hacc hreach hsflabel_known hsf'known
      · exact hacc w1 w2 hold
    · -- The re-asserted formula is already satisfied, being already on `b`.
      intro sfx hmem
      simp only [List.singleton_append, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hb sfx hsf'mem
      · exact hb sfx hmem
  rw [heq] at hsf
  obtain ⟨sign, formula, lbl⟩ := sf
  have hsf_b := hb ⟨sign, formula, lbl⟩ hsfmem
  by_cases hshape :
      (sign = Sign.pos ∧ ∃ φ, formula = Proposition.box φ) ∨
      (sign = Sign.neg ∧ ∃ φ, formula = Proposition.diamond φ)
  · -- The two propagating shapes: discharge via the landed S5 rule-soundness lemmas.
    rcases hshape with ⟨hs, φ, hform⟩ | ⟨hs, φ, hform⟩
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := modalS5BoxAll_soundIn hFC hacc hb hreach hsfmem
      rcases hres :
          (modalApplyOneS5
            (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := modalS5DiaNegAll_soundIn hFC hacc hb hreach hsfmem
      rcases hres :
          (modalApplyOneS5
            (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
  · -- Every other shape: `modalApplyOneS5` agrees with `modalApplyOne`, port the K arm verbatim.
    have heq : modalApplyOneS5 ⟨sign, formula, lbl⟩ b acc
        = modalApplyOne ⟨sign, formula, lbl⟩ b acc :=
      modalApplyOneS5_eq_of_not_boxPos_diaNeg ⟨sign, formula, lbl⟩ b acc (not_or.mp hshape)
    rw [heq] at hsf
    cases sign with
    | pos =>
      have hpos : Satisfies m (f lbl) formula := hsf_b.1 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp only [Satisfies] at hpos
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, List.find?_cons_of_pos, Option.getD_some,
          ↓reduceIte, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        obtain ⟨hφ, hψ⟩ := hpos
        refine ⟨[⟨.pos, φ, lbl⟩, ⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun _ => hφ, fun h => by simp at h⟩
        · exact ⟨fun _ => hψ, fun h => by simp at h⟩
        · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        cases hpos with
        | inl hφ =>
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hφ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        | inr hψ =>
          refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hψ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [Satisfies] at hpos
            exact fun ha => hpos ha
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hpos
          rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
          · refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
              W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun _ => hpos hφ, fun h => by simp at h⟩
            · exact hb sf' hmem_old
          · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun h => by simp at h, fun _ => hφ⟩
            · exact hb sf' hmem_old
      | box φ => exact absurd (Or.inl ⟨rfl, φ, rfl⟩) hshape
      | diamond φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        simp only [Satisfies] at hpos
        obtain ⟨ww, hwwr, hwwφ⟩ := hpos
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.pos, .diamond φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · refine ⟨fun _ => ?_, fun h => by simp at h⟩
            simp only [witness, f', if_pos rfl]
            exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
    | neg =>
      have hneg : ¬Satisfies m (f lbl) formula := hsf_b.2 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
        · refine ⟨[⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hneg hφ⟩
          · exact hb sf' hmem_old
        · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hφ⟩
          · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨hφ, hψ⟩ := hneg
        refine ⟨[⟨.neg, φ, lbl⟩, ⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun h => by simp at h, fun _ => hφ⟩
        · exact ⟨fun h => by simp at h, fun _ => hψ⟩
        · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hneg
          push Not at hneg
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hneg.1, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          exact ⟨_, List.mem_cons_self,
            negImp_alpha_preserved_gen s5FC hFC hacc hb hneg⟩
      | box φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨ww, hwwr, hwwφ⟩ := hneg
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let newAcc' := acc.addEdge lbl w'
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.neg, .box φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · constructor
            · intro h; simp at h
            · intro _
              simp only [witness, f', if_pos rfl]
              exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
      | diamond φ => exact absurd (Or.inr ⟨rfl, φ, rfl⟩) hshape

/-- Per-step `s5FC`-satisfiability preservation for `modalApplyOneS5`. Free corollary of
`modalStepBranchS5Gen_preserves_satIn` at the degenerate spec `modalApplyOneS5_s5SoundSpec`
(the unguarded universal rule never reuses, so the reuse branch of the lift is vacuous for it);
statement unchanged. -/
theorem modalStepBranchS5_preserves_satIn
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneS5 b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiableIn s5FC b acc)
    (hInv : accFreshInv b acc)
    (hreach : accReachableInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiableIn s5FC b' newAcc :=
  modalStepBranchS5Gen_preserves_satIn modalApplyOneS5 modalApplyOneS5_s5SoundSpec
    b e acc newBs newExps newAcc hstep hsat hInv hreach

/-- Per-step `s5FC`-satisfiability preservation for the witness-reuse rule `modalApplyOneS5w`.
Free corollary of `modalStepBranchS5Gen_preserves_satIn` at `modalApplyOneS5w_s5SoundSpec`. -/
theorem modalStepBranchS5w_preserves_satIn
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneS5w b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiableIn s5FC b acc)
    (hInv : accFreshInv b acc)
    (hreach : accReachableInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiableIn s5FC b' newAcc :=
  modalStepBranchS5Gen_preserves_satIn modalApplyOneS5w modalApplyOneS5w_s5SoundSpec
    b e acc newBs newExps newAcc hstep hsat hInv hreach

/-- The S5 fuel induction, lifted over any `apply` satisfying `S5SoundSpec` (and the per-call
freshness dichotomy `hfresh` that the two already-generic structural preservation lemmas need):
`modalExpandBranchesGen apply` closing implies every branch is unsatisfiable-in-`s5FC`. Threads
the combined invariant `S5SoundInv` via `List.Forall₂`, reusing all three step-preservation
lemmas (`modalStepBranch_preserves_accFreshInv_gen`,
`modalStepBranchS5Gen_preserves_accReachableInv`, `modalStepBranch_preserves_accTargetsKnown_gen`)
plus the per-step satisfiability bridge `modalStepBranchS5Gen_preserves_satIn` above. -/
theorem modalExpandBranchesS5Gen_closed_unsatIn
    (apply : RuleApply Atom) (hspec : S5SoundSpec apply)
    (hfresh : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => S5SoundInv b acc) branches accs →
      modalExpandBranchesGen apply branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiableIn s5FC b acc) branches accs := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs hlength hlength_accs hInv h
    simp only [modalExpandBranchesGen] at h
    split at h
    · simp at h
    · rename_i hfind
      refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩
      intro b a hmem
      have hfn := (List.findSome?_eq_none_iff.mp hfind) _ hmem
      have hcl : isModalClosed b = true := by
        cases h : isModalClosed b with
        | true => rfl
        | false => simp [h] at hfn
      exact modalClosed_unsatIn s5FC b hcl a
  | succ fuel' ih =>
    intro branches expandedSets accs hlength hlength_accs hInv h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        List.Forall₂ (fun b a => S5SoundInv b a) pending pendingAccs →
        List.Forall₂ (fun b a => S5SoundInv b a) done doneAccs →
        modalExpandBranchesGen.processNext apply
          fuel' pending pendingExp pendingAccs done doneExp doneAccs = .closed →
        List.Forall₂ (fun b a => ¬branchSatisfiableIn s5FC b a) pending pendingAccs from
      key branches expandedSets accs [] [] []
        hlength hlength_accs rfl rfl hInv List.Forall₂.nil
        (by simpa [modalExpandBranchesGen] using h)
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ _ _ hInv_pending _ _
      cases hInv_pending
      exact List.Forall₂.nil
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hpendingExpLen hpendingAccsLen hdoneExpLen hdoneAccsLen
        hInv_pending hInv_done hinner
      cases pendingAccs with
      | nil => simp at hpendingAccsLen
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hpendingExpLen
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hpendingExpLen hpendingAccsLen
          cases hInv_pending with
          | cons hInv_bh hInv_rest =>
            have hFresh_bh : accFreshInv bh a := hInv_bh.1
            have hReach_bh : accReachableInv bh a := hInv_bh.2.1
            have hKnown_bh : accTargetsKnown bh a := hInv_bh.2.2
            simp only [modalExpandBranchesGen.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              apply List.Forall₂.cons
              · exact modalClosed_unsatIn s5FC bh hcl a
              · exact ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                    (by simp [hpendingExpLen])
                    (by simp [hpendingAccsLen])
                    (by simp [hdoneExpLen])
                    (by simp [hdoneAccsLen])
                    hInv_rest
                    (List.rel_append hInv_done
                      (List.Forall₂.cons hInv_bh List.Forall₂.nil))
                    hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep_eq : modalStepBranchGen apply bh e a with
              | none => rw [hstep_eq] at hinner; simp at hinner
              | some step =>
                obtain ⟨newBs, newExps, newAcc⟩ := step
                rw [hstep_eq] at hinner
                have hnewExpLen : newExps.length = newBs.length := by
                  unfold modalStepBranchGen at hstep_eq
                  obtain ⟨sf, -, hf⟩ := List.exists_of_findSome?_eq_some hstep_eq
                  rcases h_apply : (apply sf bh a) with ⟨result, _⟩
                  simp only [h_apply] at hf
                  cases result with
                  | notApplicable => simp at hf
                  | _ =>
                    split_ifs at hf
                    simp only [Option.some.injEq, Prod.mk.injEq] at hf
                    obtain ⟨rfl, rfl, -⟩ := hf; simp [List.length_map]
                have hInvNew : List.Forall₂ (fun b a => S5SoundInv b a)
                    newBs (List.replicate newBs.length newAcc) :=
                  forall₂_replicate_right.mpr (fun b' hb' =>
                    ⟨modalStepBranch_preserves_accFreshInv_gen apply
                        hfresh bh e a newBs newExps newAcc hstep_eq
                        hFresh_bh b' hb',
                     modalStepBranchS5Gen_preserves_accReachableInv apply hspec bh e a newBs
                        newExps newAcc hstep_eq hKnown_bh hReach_bh b' hb',
                     modalStepBranch_preserves_accTargetsKnown_gen apply
                        hfresh bh e a newBs newExps newAcc hstep_eq
                        hKnown_bh b' hb'⟩)
                have hInvAll : List.Forall₂ (fun b a => S5SoundInv b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  List.rel_append (List.rel_append hInv_done hInvNew) hInv_rest
                have hunsat_all :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn s5FC b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                    (by simp only [List.length_append]; omega)
                    (by simp only [List.length_append, List.length_replicate]; omega)
                    hInvAll hinner
                have hunsat_newBs_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn s5FC b a)
                    (newBs ++ bt) (List.replicate newBs.length newAcc ++ restAs) := by
                  have h := List.forall₂_drop done.length hunsat_all
                  rw [List.append_assoc done newBs bt, List.drop_left,
                      List.append_assoc doneAccs (List.replicate newBs.length newAcc) restAs,
                      List.drop_left' hdoneAccsLen] at h
                  exact h
                have hunsat_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn s5FC b a)
                    bt restAs := by
                  have h := List.forall₂_drop newBs.length hunsat_newBs_bt
                  rw [List.drop_left,
                      List.drop_left' List.length_replicate] at h
                  exact h
                have hunsat_newBs :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn s5FC b a)
                    newBs (List.replicate newBs.length newAcc) := by
                  have h := List.forall₂_take newBs.length hunsat_newBs_bt
                  rw [List.take_left,
                      List.take_left' List.length_replicate] at h
                  exact h
                have hbh_unsat : ¬branchSatisfiableIn s5FC bh a := by
                  intro hbh_sat
                  obtain ⟨b', hb'_mem, hb'_sat⟩ :=
                    modalStepBranchS5Gen_preserves_satIn apply hspec
                      bh e a newBs newExps newAcc hstep_eq hbh_sat hFresh_bh hReach_bh
                  exact (forall₂_replicate_right.mp hunsat_newBs b' hb'_mem) hb'_sat
                exact List.Forall₂.cons hbh_unsat hunsat_bt

/-- `modalExpandBranchesGen modalApplyOneS5` closing implies every branch is
unsatisfiable-in-`s5FC`. Free corollary of `modalExpandBranchesS5Gen_closed_unsatIn` at the
degenerate spec `modalApplyOneS5_s5SoundSpec`; statement unchanged. -/
theorem modalExpandBranchesS5_closed_unsatIn
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => S5SoundInv b acc) branches accs →
      modalExpandBranchesGen modalApplyOneS5 branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiableIn s5FC b acc) branches accs :=
  modalExpandBranchesS5Gen_closed_unsatIn modalApplyOneS5 modalApplyOneS5_s5SoundSpec
    modalApplyOneS5_fresh_local fuel

/-- `modalExpandBranchesGen modalApplyOneS5w` closing implies every branch is
unsatisfiable-in-`s5FC`. Free corollary of `modalExpandBranchesS5Gen_closed_unsatIn` at
`modalApplyOneS5w_s5SoundSpec` and the landed `modalApplyOneS5w_fresh_local`. -/
theorem modalExpandBranchesS5w_closed_unsatIn
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => S5SoundInv b acc) branches accs →
      modalExpandBranchesGen modalApplyOneS5w branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiableIn s5FC b acc) branches accs :=
  modalExpandBranchesS5Gen_closed_unsatIn modalApplyOneS5w modalApplyOneS5w_s5SoundSpec
    modalApplyOneS5w_fresh_local fuel

/-- **The S5 soundness capstone, lifted over any `apply` satisfying `S5SoundSpec`**: if the
tableau driven by `apply` closes on `F(φ)`, then `φ` is `s5Valid`. Contrapositive over `s5FC`,
mirroring `modalTableauT_sound` (`FrameCompleteness.lean`): feeds
`modalExpandBranchesS5Gen_closed_unsatIn` at the initial configuration
`[[F(φ)@0]] [[]] [Accessibility.empty]`, with the initial `S5SoundInv` witness built from
`accFreshInv_empty` (any branch, empty `acc`), the landed `accReachableInv_initial`, and the
trivial vacuous `accTargetsKnown` for the edgeless empty accessibility relation. -/
theorem modalTableauS5Gen_sound
    (apply : RuleApply Atom) (hspec : S5SoundSpec apply)
    (hfresh : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (φ : Proposition Atom) (h : modalTableauGen apply φ = .closed) :
    s5Valid φ := by
  intro World m hFC w
  by_contra hnotsat
  have hsat : branchSatisfiableIn s5FC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hFC,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hInv0 : S5SoundInv
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] Accessibility.empty :=
    ⟨accFreshInv_empty _, accReachableInv_initial φ,
      fun w w' hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge])⟩
  have hunsat := modalExpandBranchesS5Gen_closed_unsatIn apply hspec hfresh (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons hInv0 List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesGen apply
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-- **The witness-reuse S5 soundness capstone**: if the tableau driven by the witness-reuse rule
`modalApplyOneS5w` closes on `F(φ)`, then `φ` is `s5Valid`. Free corollary of
`modalTableauS5Gen_sound` at `modalApplyOneS5w_s5SoundSpec` and the landed
`modalApplyOneS5w_fresh_local`.

Soundness survives the move from unguarded minting to witness reuse because a reuse edge only
ever connects two worlds *already known* to the branch, and under `s5FC` -- whose relation is an
equivalence -- any two worlds reachable from the common origin `0` are related
(`accReachableInv_related_s5`). Re-basing `modalTableauS5` onto `modalApplyOneS5w` therefore
carries `modalTableauS5_sound` over by definitional unfolding, with no change to its
statement. -/
theorem modalTableauS5w_sound (φ : Proposition Atom)
    (h : modalTableauGen modalApplyOneS5w φ = .closed) :
    s5Valid φ :=
  modalTableauS5Gen_sound modalApplyOneS5w modalApplyOneS5w_s5SoundSpec
    modalApplyOneS5w_fresh_local φ h

/-- `modalTableauS5` is sound: if the S5 tableau closes on `F(φ)`, then `φ` is `s5Valid`.
Statement unchanged across `modalTableauS5`'s re-basing onto the witness-reuse rule
(`S5Simplification.lean`): `modalTableauS5 φ` is now *definitionally* `modalTableauGen
modalApplyOneS5w φ`, which is exactly `modalTableauS5w_sound`'s hypothesis, so this carries over
by unfolding with no change to what it asserts. -/
theorem modalTableauS5_sound (φ : Proposition Atom) (h : modalTableauS5 φ = .closed) :
    s5Valid φ :=
  modalTableauS5w_sound φ h

/-! ### Rule-Level Five/KB5 Semantic Soundness

The root/non-root split lands here: `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`
discharge the root-triggered arm directly via `hacc` on the `modalFiveBoxAll_root_hasEdge`/
`modalFiveDiaNegAll_root_hasEdge` witness (`FiveSimplification.lean`), and the non-root-triggered
arm via the codomain-equivalence discharge `accReachableInv_related_five`. Mirrors
`modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn`. -/

omit [Hashable Atom] in
/-- Frame-relativized semantic soundness of `modalApplyOneFiveProp`'s
box-positive output under `fiveFC`, given `accReachableInv`. K's own bounded propagation
(`kForms`, at `acc.successorsOf lbl`) is sound via the existing `modalApplyOne_boxPos_sound`
(direct-edge relatedness, `FC` unused); the root-aware universal propagation
(`modalFiveBoxAll b acc φ lbl`) splits on whether the trigger `lbl` is the root: at the root, every
emitted target has a genuine recorded edge (`modalFiveBoxAll_root_hasEdge`), discharged directly
via `hacc`; away from the root, both `lbl` and any target world `x.label` are non-root known
worlds, hence related via `accReachableInv_related_five`. -/
lemma modalFiveBoxAll_soundIn
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : fiveFC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf) (hreach : accReachableInv b acc)
    {φ : Proposition Atom} {lbl : WorldIndex}
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneFiveProp
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneFiveProp
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have hKeq := modalApplyOne_boxPos_eq
    (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
  have hKsound := modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem
  have hlblknown : lbl ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b lbl).mpr
      ⟨(⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem, rfl⟩
  have hboxsat : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
  simp only [Satisfies] at hboxsat
  have hallSat : ∀ x ∈ modalFiveBoxAll b acc φ lbl, sfSat m f x := by
    intro x hx
    obtain ⟨hxeq, hxknown, hxne0, -⟩ := modalFiveBoxAll_mem hx
    by_cases hlbl0 : lbl = (0 : WorldIndex)
    · subst hlbl0
      have hedge : acc.hasEdge 0 x.label = true := modalFiveBoxAll_root_hasEdge hx
      have hrel : m.r (f 0) (f x.label) := hacc 0 x.label hedge
      rw [hxeq]
      exact sfSat_pos m f φ x.label (hboxsat (f x.label) hrel)
    · have hrel : m.r (f lbl) (f x.label) :=
        accReachableInv_related_five hFC hacc hreach hlblknown hxknown hlbl0 hxne0
      rw [hxeq]
      exact sfSat_pos m f φ x.label (hboxsat (f x.label) hrel)
  unfold modalApplyOneFiveProp
  rcases hp : modalApplyOne (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)
      b acc with ⟨kResult, kAcc⟩
  rw [hp] at hKeq hKsound
  simp only at hKeq hKsound
  rcases hKeq with hKeq | ⟨kForms, hKeq⟩ <;> subst hKeq
  · obtain ⟨hsndeq, -⟩ := hKsound
    dsimp only
    split_ifs with hemp
    · exact ⟨hsndeq, trivial⟩
    · exact ⟨hsndeq, hallSat⟩
  · obtain ⟨hsndeq, hKformSat⟩ := hKsound
    dsimp only
    refine ⟨hsndeq, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hKformSat x hx
    · exact hallSat x hx

omit [Hashable Atom] in
/-- Dual of `modalFiveBoxAll_soundIn` for the diamond-negative shape. -/
lemma modalFiveDiaNegAll_soundIn
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : fiveFC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf) (hreach : accReachableInv b acc)
    {φ : Proposition Atom} {lbl : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneFiveProp
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneFiveProp
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have hKeq := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
  have hKsound := modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem
  have hlblknown : lbl ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b lbl).mpr
      ⟨(⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem, rfl⟩
  have hdiasat : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
  simp only [Satisfies] at hdiasat
  push Not at hdiasat
  have hallSat : ∀ x ∈ modalFiveDiaNegAll b acc φ lbl, sfSat m f x := by
    intro x hx
    obtain ⟨hxeq, hxknown, hxne0, -⟩ := modalFiveDiaNegAll_mem hx
    by_cases hlbl0 : lbl = (0 : WorldIndex)
    · subst hlbl0
      have hedge : acc.hasEdge 0 x.label = true := modalFiveDiaNegAll_root_hasEdge hx
      have hrel : m.r (f 0) (f x.label) := hacc 0 x.label hedge
      rw [hxeq]
      exact sfSat_neg m f φ x.label (hdiasat (f x.label) hrel)
    · have hrel : m.r (f lbl) (f x.label) :=
        accReachableInv_related_five hFC hacc hreach hlblknown hxknown hlbl0 hxne0
      rw [hxeq]
      exact sfSat_neg m f φ x.label (hdiasat (f x.label) hrel)
  unfold modalApplyOneFiveProp
  rcases hp : modalApplyOne
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hKeq hKsound
  simp only at hKeq hKsound
  rcases hKeq with hKeq | ⟨kForms, hKeq⟩ <;> subst hKeq
  · obtain ⟨hsndeq, -⟩ := hKsound
    dsimp only
    split_ifs with hemp
    · exact ⟨hsndeq, trivial⟩
    · exact ⟨hsndeq, hallSat⟩
  · obtain ⟨hsndeq, hKformSat⟩ := hKsound
    dsimp only
    refine ⟨hsndeq, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hKformSat x hx
    · exact hallSat x hx

/-! ### Corrected-Gate Rule-Level Semantic Soundness

`modalKb5BoxAllUniv_soundIn`/`modalKb5DiaNegAllUniv_soundIn` discharge the corrected-gate rule's
two propagation shapes directly against `kb5FC`, reusing the three-case semantic
family (`reachable_imp_related_kb5`/`accReachableInv_related_kb5`/`accReachableInv_kb5_root_refl`)
for the non-root-target and trigger-is-root cases verbatim, plus one new one-liner
(`reachable_imp_related_kb5_symm`) for the genuinely new fourth case: a non-root trigger firing
the self-target arm, which the retired frozen rule's trigger-identity gate could never reach. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- **The one new semantic case the corrected gate needs**: symmetrized form of
`reachable_imp_related_kb5`, giving the relation *from* a known non-root world *back to* the root
(rather than root-to-world). This is exactly what discharges the corrected rule's self-target arm
when it fires from a non-root trigger `lbl ≠ 0`: `T(□φ)@lbl`'s semantic content
(`∀ w', m.r (f lbl) (f w') → ...`) needs `m.r (f lbl) (f 0)`, not `m.r (f 0) (f lbl)`. -/
lemma reachable_imp_related_kb5_symm
    {acc : Accessibility} {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : kb5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    {w : WorldIndex} (hw0 : w ≠ 0)
    (hreach : Relation.ReflTransGen (fun a c => acc.hasEdge a c) 0 w) :
    m.r (f w) (f 0) := by
  haveI : Std.Symm m.r := hFC.1
  exact Std.Symm.symm _ _ (reachable_imp_related_kb5 hFC hacc hw0 hreach)

omit [Hashable Atom] in
/-- **The corrected-gate KB5 rule's box-positive semantic soundness**, direct analogue of the
retired frozen-rule box-positive soundness lemma against `modalKb5BoxAllUniv`'s trigger-free
dichotomy (`modalKb5BoxAllUniv_mem`). The self-target arm (`x.label = 0`) now splits into two
sub-cases on whether the trigger itself is the root: `lbl = 0` discharges via
`accReachableInv_kb5_root_refl` exactly as the frozen rule did; `lbl ≠ 0` is the genuinely new
case, discharged via `reachable_imp_related_kb5_symm`. -/
lemma modalKb5BoxAllUniv_soundIn
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : kb5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf) (hreach : accReachableInv b acc)
    {φ : Proposition Atom} {lbl : WorldIndex}
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneKb5''Prop
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneKb5''Prop
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have hKeq := modalApplyOne_boxPos_eq
    (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
  have hKsound := modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem
  have hlblknown : lbl ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b lbl).mpr
      ⟨(⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem, rfl⟩
  have hboxsat : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
  simp only [Satisfies] at hboxsat
  have hallSat : ∀ x ∈ modalKb5BoxAllUniv b φ lbl, sfSat m f x := by
    intro x hx
    have hxeq : x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) :=
      modalKb5BoxAllUniv_mem_eq hx
    rcases (modalKb5BoxAllUniv_mem hx).2 with ⟨-, hxknown, hxne0⟩ | ⟨hxeq0, v, hv, hvne⟩
    · by_cases hlbleq : lbl = (0 : WorldIndex)
      · subst hlbleq
        have hrel : m.r (f 0) (f x.label) :=
          reachable_imp_related_kb5 hFC hacc hxne0 (hreach x.label hxknown)
        rw [hxeq]
        exact sfSat_pos m f φ x.label (hboxsat (f x.label) hrel)
      · have hrel : m.r (f lbl) (f x.label) :=
          accReachableInv_related_kb5 hFC hacc hreach hlblknown hxknown hlbleq hxne0
        rw [hxeq]
        exact sfSat_pos m f φ x.label (hboxsat (f x.label) hrel)
    · by_cases hlbleq : lbl = (0 : WorldIndex)
      · subst hlbleq
        have hrefl : m.r (f 0) (f 0) := accReachableInv_kb5_root_refl hFC hacc hreach hv hvne
        have hsat0 : Satisfies m (f 0) φ := hboxsat (f 0) hrefl
        rw [hxeq0]
        exact sfSat_pos m f φ 0 hsat0
      · have hrel0 : m.r (f lbl) (f 0) :=
          reachable_imp_related_kb5_symm hFC hacc hlbleq (hreach lbl hlblknown)
        have hsat0 : Satisfies m (f 0) φ := hboxsat (f 0) hrel0
        rw [hxeq0]
        exact sfSat_pos m f φ 0 hsat0
  unfold modalApplyOneKb5''Prop
  rcases hp : modalApplyOne (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)
      b acc with ⟨kResult, kAcc⟩
  rw [hp] at hKeq hKsound
  simp only at hKeq hKsound
  rcases hKeq with hKeq | ⟨kForms, hKeq⟩ <;> subst hKeq
  · obtain ⟨hsndeq, -⟩ := hKsound
    dsimp only
    split_ifs with hemp
    · exact ⟨hsndeq, trivial⟩
    · exact ⟨hsndeq, hallSat⟩
  · obtain ⟨hsndeq, hKformSat⟩ := hKsound
    dsimp only
    refine ⟨hsndeq, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hKformSat x hx
    · exact hallSat x hx

omit [Hashable Atom] in
/-- Dual of `modalKb5BoxAllUniv_soundIn` for the diamond-negative shape. -/
lemma modalKb5DiaNegAllUniv_soundIn
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : kb5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf) (hreach : accReachableInv b acc)
    {φ : Proposition Atom} {lbl : WorldIndex}
    (hmem : (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneKb5''Prop
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneKb5''Prop
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have hKeq := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
  have hKsound := modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem
  have hlblknown : lbl ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b lbl).mpr
      ⟨(⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem, rfl⟩
  have hdiasat : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
  simp only [Satisfies] at hdiasat
  push Not at hdiasat
  have hallSat : ∀ x ∈ modalKb5DiaNegAllUniv b φ lbl, sfSat m f x := by
    intro x hx
    have hxeq : x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) :=
      modalKb5DiaNegAllUniv_mem_eq hx
    rcases (modalKb5DiaNegAllUniv_mem hx).2 with ⟨-, hxknown, hxne0⟩ | ⟨hxeq0, v, hv, hvne⟩
    · by_cases hlbleq : lbl = (0 : WorldIndex)
      · subst hlbleq
        have hrel : m.r (f 0) (f x.label) :=
          reachable_imp_related_kb5 hFC hacc hxne0 (hreach x.label hxknown)
        rw [hxeq]
        exact sfSat_neg m f φ x.label (hdiasat (f x.label) hrel)
      · have hrel : m.r (f lbl) (f x.label) :=
          accReachableInv_related_kb5 hFC hacc hreach hlblknown hxknown hlbleq hxne0
        rw [hxeq]
        exact sfSat_neg m f φ x.label (hdiasat (f x.label) hrel)
    · by_cases hlbleq : lbl = (0 : WorldIndex)
      · subst hlbleq
        have hrefl : m.r (f 0) (f 0) := accReachableInv_kb5_root_refl hFC hacc hreach hv hvne
        have hsat0 : ¬ Satisfies m (f 0) φ := hdiasat (f 0) hrefl
        rw [hxeq0]
        exact sfSat_neg m f φ 0 hsat0
      · have hrel0 : m.r (f lbl) (f 0) :=
          reachable_imp_related_kb5_symm hFC hacc hlbleq (hreach lbl hlblknown)
        have hsat0 : ¬ Satisfies m (f 0) φ := hdiasat (f 0) hrel0
        rw [hxeq0]
        exact sfSat_neg m f φ 0 hsat0
  unfold modalApplyOneKb5''Prop
  rcases hp : modalApplyOne
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hKeq hKsound
  simp only at hKeq hKsound
  rcases hKeq with hKeq | ⟨kForms, hKeq⟩ <;> subst hKeq
  · obtain ⟨hsndeq, -⟩ := hKsound
    dsimp only
    split_ifs with hemp
    · exact ⟨hsndeq, trivial⟩
    · exact ⟨hsndeq, hallSat⟩
  · obtain ⟨hsndeq, hKformSat⟩ := hKsound
    dsimp only
    refine ⟨hsndeq, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hKformSat x hx
    · exact hallSat x hx

/-- The combined per-step invariant the Five fuel induction threads:
`accFreshInv`, `accReachableInv`, and `accTargetsKnown`. Mirrors `S5SoundInv`. -/
def FiveSoundInv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  accFreshInv b acc ∧ accReachableInv b acc ∧ accTargetsKnown b acc

/-! ### `accReachableInv` Preservation for `modalApplyOneKb5''`

Direct analogue of the retired frozen-rule's `accReachableInv` preservation lemma, with one
addition: since the corrected rule's self-target arm needs `(0 : WorldIndex) ∈ modalKnownWorlds
b` threaded in (`modalApplyOneKb5''Prop_knownWorlds_step`'s `h0`), the conclusion is strengthened
to also propagate `0 ∈ modalKnownWorlds b'` to every child branch `b'` -- trivial by
`modalKnownWorlds_mono_append` at each case, since every child branch is `b` with formulas
prepended (never removed). -/

/-- A `modalStepBranchGen modalApplyOneKb5''` step preserves `accReachableInv` and the "root
always known" invariant, given `accTargetsKnown`. -/
lemma modalStepBranchKb5''_preserves_accReachableInv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneKb5'' b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc)
    (hInv : accReachableInv b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b) :
    ∀ b' ∈ newBs, accReachableInv b' newAcc ∧ (0 : WorldIndex) ∈ modalKnownWorlds b' := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsflabel_known : sf.label ∈ modalKnownWorlds b := (mem_modalKnownWorlds b sf.label).mpr
    ⟨sf, hsfmem, rfl⟩
  rcases modalApplyOneKb5''_agree_or_reuse sf b acc with heq | ⟨sf', hsf'mem, heq⟩
  swap
  · -- Reuse: the emitted formula is already on `b`, so the child branch knows no new world;
    -- every reachability witness survives the one added edge by monotonicity.
    rw [heq] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, rfl⟩ := hsf
    intro b' hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    refine ⟨?_, modalKnownWorlds_mono_append _ b 0 h0⟩
    intro w hw
    have hsf'known : sf'.label ∈ modalKnownWorlds b :=
      (mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hsf'mem, rfl⟩
    have hknown' : ∀ x ∈ [sf'], x.label ∈ modalKnownWorlds b := by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact hsf'known
    exact Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _
      (hInv w (modalKnownWorlds_append_subset_of_labels_known hknown' w hw))
  rw [heq] at hsf
  rcases modalApplyOneKb5''Prop_knownWorlds_step sf b acc hsfmem hknown h0 with
    ⟨hsndeq, hdich⟩ | ⟨hsndeq, hdich⟩
  · -- acc unchanged: every new label of the child branch was already known on `b`.
    rcases hfstc : (modalApplyOneKb5''Prop sf b acc).fst with nf | brs | nf | _
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      refine ⟨?_, modalKnownWorlds_mono_append _ b 0 h0⟩
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hdich w hw)
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'
      obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
      have hbr_known : ∀ x ∈ br, x.label ∈ modalKnownWorlds b :=
        fun x hx => hdich x (List.mem_flatten.mpr ⟨br, hbrmem, hx⟩)
      refine ⟨?_, modalKnownWorlds_mono_append _ b 0 h0⟩
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hbr_known w hw)
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      refine ⟨?_, modalKnownWorlds_mono_append _ b 0 h0⟩
      intro w hw
      exact hInv w (modalKnownWorlds_append_subset_of_labels_known hdich w hw)
    · rw [hfstc] at hsf; simp at hsf
  · -- mint case: one fresh edge `sf.label → modalNextWorld b` added.
    rcases hfstc : (modalApplyOneKb5''Prop sf b acc).fst with nf | brs | nf | _
    · rw [hfstc, hsndeq] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl⟩ := hsf
      rw [hfstc] at hdich
      obtain ⟨-, hlabels⟩ := hdich
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      refine ⟨?_, modalKnownWorlds_mono_append _ b 0 h0⟩
      intro w hw
      rw [mem_modalKnownWorlds] at hw
      obtain ⟨sf', hsf', rfl⟩ := hw
      rcases List.mem_append.mp hsf' with hnew | hold
      · -- the fresh world: extend sf.label's (already-known) reachability witness by one hop.
        rw [hlabels sf' hnew]
        exact (Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _ (hInv sf.label
          hsflabel_known)).tail (hasEdge_addEdge_self_FS acc sf.label (modalNextWorld b))
      · exact Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_FS) _ _
          (hInv sf'.label ((mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hold, rfl⟩))
    · rw [hfstc] at hdich; exact hdich.elim
    · rw [hfstc] at hdich; exact hdich.elim
    · rw [hfstc] at hsf; simp at hsf

/-! ### The Bespoke Five/KB5 Fuel-Induction Assembly

The Five analogue of the S5 bespoke chain above. Since `modalApplyOneFive` is the **only**
shipped Five rule (no separate unguarded-rule stage, unlike S5's `modalApplyOneS5`/
`modalApplyOneS5w` pair), the whole chain is stated directly over `modalApplyOneFive`, with no
`RuleApply`/spec-class abstraction layer: `modalApplyOneFive_agree_or_reuse_ne_root`
(`FiveSimplification.lean`) is the exact per-call dichotomy consumed in place of threading an
`S5SoundSpec`-style hypothesis, mirroring `S5SoundSpec` itself but strengthened with the
root-exclusion fact `accReachableInv_related_five` needs (that `accReachableInv_related_s5`
never needed, `s5FC` being an equivalence). The propagating shapes (box-positive/diamond-negative)
discharge via the landed `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`; every other shape
(including the two K-minting shapes, when `modalApplyOneFive` agrees with `modalApplyOneFiveProp`,
i.e. no reuse fired) is byte-identical to the S5 chain's own "not shape" branch, ported via
`modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg` in place of
`modalApplyOneS5_eq_of_not_boxPos_diaNeg`
-- that branch never inspects `s5FC`/`fiveFC`-specific facts (reflexivity, symmetry, Euclideanness),
only threading the frame-condition witness `hFC` opaquely through the output model, so it carries
over under the literal `s5FC ↦ fiveFC` substitution.

The **reuse** call is handled up front, exactly as S5's witness-reuse case: no world is minted, so
`f` is not extended. Both obligations fall out of `sf' ∈ b` (already satisfied) and the edge
`sf.label → sf'.label`, discharged via `accReachableInv_related_five` at the two root-excluded
endpoints `modalApplyOneFive_agree_or_reuse_ne_root` supplies. -/

theorem modalStepBranchFive_preserves_satIn
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneFive b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiableIn fiveFC b acc)
    (hInv : accFreshInv b acc)
    (hreach : accReachableInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiableIn fiveFC b' newAcc := by
  obtain ⟨W, m, f, hFC, hacc, hb⟩ := hsat
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsflabel_known : sf.label ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b sf.label).mpr ⟨sf, hsfmem, rfl⟩
  rcases modalApplyOneFive_agree_or_reuse_ne_root sf b acc with
    heq | ⟨sf', hsf'mem, hsflabelne, hsf'labelne, heq⟩
  swap
  · -- Witness reuse away from the root: re-assert a formula already on `b` and record one edge
    -- between two already-known, non-root worlds. The model is unchanged; `f` is not extended.
    have hsf'known : sf'.label ∈ modalKnownWorlds b :=
      (mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hsf'mem, rfl⟩
    rw [heq] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, rfl⟩ := hsf
    refine ⟨[sf'] ++ b, List.mem_cons_self, W, m, f, hFC, ?_, ?_⟩
    · -- The one new edge relates two known, non-root worlds; every old edge survives via `hacc`.
      intro w1 w2 hedge
      rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
      · exact accReachableInv_related_five hFC hacc hreach hsflabel_known hsf'known
          hsflabelne hsf'labelne
      · exact hacc w1 w2 hold
    · -- The re-asserted formula is already satisfied, being already on `b`.
      intro sfx hmem
      simp only [List.singleton_append, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hb sfx hsf'mem
      · exact hb sfx hmem
  rw [heq] at hsf
  obtain ⟨sign, formula, lbl⟩ := sf
  have hsf_b := hb ⟨sign, formula, lbl⟩ hsfmem
  by_cases hshape :
      (sign = Sign.pos ∧ ∃ φ, formula = Proposition.box φ) ∨
      (sign = Sign.neg ∧ ∃ φ, formula = Proposition.diamond φ)
  · -- The two propagating shapes: discharge via the landed Five rule-soundness lemmas.
    rcases hshape with ⟨hs, φ, hform⟩ | ⟨hs, φ, hform⟩
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := modalFiveBoxAll_soundIn hFC hacc hb hreach hsfmem
      rcases hres :
          (modalApplyOneFiveProp
            (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := modalFiveDiaNegAll_soundIn hFC hacc hb hreach hsfmem
      rcases hres :
          (modalApplyOneFiveProp
            (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
  · -- Every other shape: `modalApplyOneFiveProp` agrees with `modalApplyOne`, port the K arm
    -- verbatim (this branch never inspects `fiveFC`-specific facts, only threads `hFC` opaquely).
    have heq2 : modalApplyOneFiveProp ⟨sign, formula, lbl⟩ b acc
        = modalApplyOne ⟨sign, formula, lbl⟩ b acc :=
      modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg ⟨sign, formula, lbl⟩ b acc (not_or.mp hshape)
    rw [heq2] at hsf
    cases sign with
    | pos =>
      have hpos : Satisfies m (f lbl) formula := hsf_b.1 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp only [Satisfies] at hpos
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, List.find?_cons_of_pos, Option.getD_some,
          ↓reduceIte, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        obtain ⟨hφ, hψ⟩ := hpos
        refine ⟨[⟨.pos, φ, lbl⟩, ⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun _ => hφ, fun h => by simp at h⟩
        · exact ⟨fun _ => hψ, fun h => by simp at h⟩
        · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        cases hpos with
        | inl hφ =>
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hφ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        | inr hψ =>
          refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hψ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [Satisfies] at hpos
            exact fun ha => hpos ha
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hpos
          rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
          · refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
              W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun _ => hpos hφ, fun h => by simp at h⟩
            · exact hb sf' hmem_old
          · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun h => by simp at h, fun _ => hφ⟩
            · exact hb sf' hmem_old
      | box φ => exact absurd (Or.inl ⟨rfl, φ, rfl⟩) hshape
      | diamond φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        simp only [Satisfies] at hpos
        obtain ⟨ww, hwwr, hwwφ⟩ := hpos
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.pos, .diamond φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · refine ⟨fun _ => ?_, fun h => by simp at h⟩
            simp only [witness, f', if_pos rfl]
            exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
    | neg =>
      have hneg : ¬Satisfies m (f lbl) formula := hsf_b.2 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
        · refine ⟨[⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hneg hφ⟩
          · exact hb sf' hmem_old
        · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hφ⟩
          · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨hφ, hψ⟩ := hneg
        refine ⟨[⟨.neg, φ, lbl⟩, ⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun h => by simp at h, fun _ => hφ⟩
        · exact ⟨fun h => by simp at h, fun _ => hψ⟩
        · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hneg
          push Not at hneg
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hneg.1, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          exact ⟨_, List.mem_cons_self,
            negImp_alpha_preserved_gen fiveFC hFC hacc hb hneg⟩
      | box φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨ww, hwwr, hwwφ⟩ := hneg
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let newAcc' := acc.addEdge lbl w'
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.neg, .box φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · constructor
            · intro h; simp at h
            · intro _
              simp only [witness, f', if_pos rfl]
              exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
      | diamond φ => exact absurd (Or.inr ⟨rfl, φ, rfl⟩) hshape

/-- The Five fuel induction: `modalExpandBranchesGen modalApplyOneFive`
closing implies every branch is unsatisfiable-in-`fiveFC`. Direct, non-generic analogue of
`modalExpandBranchesS5Gen_closed_unsatIn`, threading `FiveSoundInv` via `List.Forall₂` and reusing
`modalStepBranch_preserves_accFreshInv_gen`/`modalStepBranch_preserves_accTargetsKnown_gen` (both
generic, instantiated at `modalApplyOneFive`/`modalApplyOneFive_fresh_local`),
`modalStepBranchFive_preserves_accReachableInv` (non-generic), and the per-step
satisfiability bridge `modalStepBranchFive_preserves_satIn` above. -/
theorem modalExpandBranchesFive_closed_unsatIn
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => FiveSoundInv b acc) branches accs →
      modalExpandBranchesGen modalApplyOneFive branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiableIn fiveFC b acc) branches accs := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs hlength hlength_accs hInv h
    simp only [modalExpandBranchesGen] at h
    split at h
    · simp at h
    · rename_i hfind
      refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩
      intro b a hmem
      have hfn := (List.findSome?_eq_none_iff.mp hfind) _ hmem
      have hcl : isModalClosed b = true := by
        cases h : isModalClosed b with
        | true => rfl
        | false => simp [h] at hfn
      exact modalClosed_unsatIn fiveFC b hcl a
  | succ fuel' ih =>
    intro branches expandedSets accs hlength hlength_accs hInv h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        List.Forall₂ (fun b a => FiveSoundInv b a) pending pendingAccs →
        List.Forall₂ (fun b a => FiveSoundInv b a) done doneAccs →
        modalExpandBranchesGen.processNext modalApplyOneFive
          fuel' pending pendingExp pendingAccs done doneExp doneAccs = .closed →
        List.Forall₂ (fun b a => ¬branchSatisfiableIn fiveFC b a) pending pendingAccs from
      key branches expandedSets accs [] [] []
        hlength hlength_accs rfl rfl hInv List.Forall₂.nil
        (by simpa [modalExpandBranchesGen] using h)
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ _ _ hInv_pending _ _
      cases hInv_pending
      exact List.Forall₂.nil
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hpendingExpLen hpendingAccsLen hdoneExpLen hdoneAccsLen
        hInv_pending hInv_done hinner
      cases pendingAccs with
      | nil => simp at hpendingAccsLen
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hpendingExpLen
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hpendingExpLen hpendingAccsLen
          cases hInv_pending with
          | cons hInv_bh hInv_rest =>
            have hFresh_bh : accFreshInv bh a := hInv_bh.1
            have hReach_bh : accReachableInv bh a := hInv_bh.2.1
            have hKnown_bh : accTargetsKnown bh a := hInv_bh.2.2
            simp only [modalExpandBranchesGen.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              apply List.Forall₂.cons
              · exact modalClosed_unsatIn fiveFC bh hcl a
              · exact ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                    (by simp [hpendingExpLen])
                    (by simp [hpendingAccsLen])
                    (by simp [hdoneExpLen])
                    (by simp [hdoneAccsLen])
                    hInv_rest
                    (List.rel_append hInv_done
                      (List.Forall₂.cons hInv_bh List.Forall₂.nil))
                    hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep_eq : modalStepBranchGen modalApplyOneFive bh e a with
              | none => rw [hstep_eq] at hinner; simp at hinner
              | some step =>
                obtain ⟨newBs, newExps, newAcc⟩ := step
                rw [hstep_eq] at hinner
                have hnewExpLen : newExps.length = newBs.length := by
                  unfold modalStepBranchGen at hstep_eq
                  obtain ⟨sf, -, hf⟩ := List.exists_of_findSome?_eq_some hstep_eq
                  rcases h_apply : (modalApplyOneFive sf bh a) with ⟨result, _⟩
                  simp only [h_apply] at hf
                  cases result with
                  | notApplicable => simp at hf
                  | _ =>
                    split_ifs at hf
                    simp only [Option.some.injEq, Prod.mk.injEq] at hf
                    obtain ⟨rfl, rfl, -⟩ := hf; simp [List.length_map]
                have hInvNew : List.Forall₂ (fun b a => FiveSoundInv b a)
                    newBs (List.replicate newBs.length newAcc) :=
                  forall₂_replicate_right.mpr (fun b' hb' =>
                    ⟨modalStepBranch_preserves_accFreshInv_gen modalApplyOneFive
                        modalApplyOneFive_fresh_local bh e a newBs newExps newAcc hstep_eq
                        hFresh_bh b' hb',
                     modalStepBranchFive_preserves_accReachableInv bh e a newBs
                        newExps newAcc hstep_eq hKnown_bh hReach_bh b' hb',
                     modalStepBranch_preserves_accTargetsKnown_gen modalApplyOneFive
                        modalApplyOneFive_fresh_local bh e a newBs newExps newAcc hstep_eq
                        hKnown_bh b' hb'⟩)
                have hInvAll : List.Forall₂ (fun b a => FiveSoundInv b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  List.rel_append (List.rel_append hInv_done hInvNew) hInv_rest
                have hunsat_all :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn fiveFC b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                    (by simp only [List.length_append]; omega)
                    (by simp only [List.length_append, List.length_replicate]; omega)
                    hInvAll hinner
                have hunsat_newBs_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn fiveFC b a)
                    (newBs ++ bt) (List.replicate newBs.length newAcc ++ restAs) := by
                  have h := List.forall₂_drop done.length hunsat_all
                  rw [List.append_assoc done newBs bt, List.drop_left,
                      List.append_assoc doneAccs (List.replicate newBs.length newAcc) restAs,
                      List.drop_left' hdoneAccsLen] at h
                  exact h
                have hunsat_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn fiveFC b a)
                    bt restAs := by
                  have h := List.forall₂_drop newBs.length hunsat_newBs_bt
                  rw [List.drop_left,
                      List.drop_left' List.length_replicate] at h
                  exact h
                have hunsat_newBs :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn fiveFC b a)
                    newBs (List.replicate newBs.length newAcc) := by
                  have h := List.forall₂_take newBs.length hunsat_newBs_bt
                  rw [List.take_left,
                      List.take_left' List.length_replicate] at h
                  exact h
                have hbh_unsat : ¬branchSatisfiableIn fiveFC bh a := by
                  intro hbh_sat
                  obtain ⟨b', hb'_mem, hb'_sat⟩ :=
                    modalStepBranchFive_preserves_satIn
                      bh e a newBs newExps newAcc hstep_eq hbh_sat hFresh_bh hReach_bh
                  exact (forall₂_replicate_right.mp hunsat_newBs b' hb'_mem) hb'_sat
                exact List.Forall₂.cons hbh_unsat hunsat_bt

/-- **The Five/KB5 soundness capstone**: if the tableau closes on `F(φ)`, then `φ` is
`fiveValid`. Direct, non-generic analogue of `modalTableauS5Gen_sound`: contrapositive over
`fiveFC`, feeding `modalExpandBranchesFive_closed_unsatIn` at the initial configuration
`[[F(φ)@0]] [[]] [Accessibility.empty]`, with the initial `FiveSoundInv` witness built from
`accFreshInv_empty` (any branch, empty `acc`), the landed `accReachableInv_initial`, and the
trivial vacuous `accTargetsKnown` for the edgeless empty accessibility relation. -/
theorem modalTableauFive_sound (φ : Proposition Atom) (h : modalTableauFive φ = .closed) :
    fiveValid φ := by
  intro World m hFC w
  by_contra hnotsat
  have hsat : branchSatisfiableIn fiveFC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hFC,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hInv0 : FiveSoundInv
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] Accessibility.empty :=
    ⟨accFreshInv_empty _, accReachableInv_initial φ,
      fun w w' hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge])⟩
  have hunsat := modalExpandBranchesFive_closed_unsatIn (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons hInv0 List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesGen modalApplyOneFive
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-! ### Corrected-Gate Fuel-Induction Step: `satIn` Preservation

Direct analogue of the retired frozen-rule's `satIn`-preservation lemma, substituting the
corrected-gate rule-soundness lemmas (`modalKb5BoxAllUniv_soundIn`/`modalKb5DiaNegAllUniv_soundIn`)
for their frozen `Full` counterparts. No `h0` ("root known") threading is needed here: this lemma
tracks semantic
(model) satisfiability, and both rule-soundness lemmas it calls already discharge their
self-target arm without any `modalKnownWorlds`-membership side-condition on `0` (see
`modalKb5BoxAllUniv_soundIn`'s docstring). Every other branch (the K-generic shape cases) is a
byte-for-byte port via `modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg`. -/

theorem modalStepBranchKb5''_preserves_satIn
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneKb5'' b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiableIn kb5FC b acc)
    (hInv : accFreshInv b acc)
    (hreach : accReachableInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiableIn kb5FC b' newAcc := by
  obtain ⟨W, m, f, hFC, hacc, hb⟩ := hsat
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsflabel_known : sf.label ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds b sf.label).mpr ⟨sf, hsfmem, rfl⟩
  rcases modalApplyOneKb5''_agree_or_reuse_ne_root sf b acc with
    heq | ⟨sf', hsf'mem, hsflabelne, hsf'labelne, heq⟩
  swap
  · -- Witness reuse away from the root: re-assert a formula already on `b` and record one edge
    -- between two already-known, non-root worlds. The model is unchanged; `f` is not extended.
    have hsf'known : sf'.label ∈ modalKnownWorlds b :=
      (mem_modalKnownWorlds b sf'.label).mpr ⟨sf', hsf'mem, rfl⟩
    rw [heq] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, rfl⟩ := hsf
    refine ⟨[sf'] ++ b, List.mem_cons_self, W, m, f, hFC, ?_, ?_⟩
    · -- The one new edge relates two known, non-root worlds; every old edge survives via `hacc`.
      intro w1 w2 hedge
      rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
      · exact accReachableInv_related_kb5 hFC hacc hreach hsflabel_known hsf'known
          hsflabelne hsf'labelne
      · exact hacc w1 w2 hold
    · -- The re-asserted formula is already satisfied, being already on `b`.
      intro sfx hmem
      simp only [List.singleton_append, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hb sfx hsf'mem
      · exact hb sfx hmem
  rw [heq] at hsf
  obtain ⟨sign, formula, lbl⟩ := sf
  have hsf_b := hb ⟨sign, formula, lbl⟩ hsfmem
  by_cases hshape :
      (sign = Sign.pos ∧ ∃ φ, formula = Proposition.box φ) ∨
      (sign = Sign.neg ∧ ∃ φ, formula = Proposition.diamond φ)
  · -- The two propagating shapes: discharge via the landed KB5 full-cluster rule-soundness lemmas.
    rcases hshape with ⟨hs, φ, hform⟩ | ⟨hs, φ, hform⟩
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := modalKb5BoxAllUniv_soundIn hFC hacc hb hreach hsfmem
      rcases hres :
          (modalApplyOneKb5''Prop
            (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
    · subst hs; subst hform
      obtain ⟨hsndeq, hRRS⟩ := modalKb5DiaNegAllUniv_soundIn hFC hacc hb hreach hsfmem
      rcases hres :
          (modalApplyOneKb5''Prop
            (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc)
          with ⟨result, accOut⟩
      rw [hres] at hsf hRRS hsndeq
      simp only at hRRS hsndeq
      subst hsndeq
      cases result with
      | linear nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | branching brs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
        refine ⟨br ++ b, List.mem_map_of_mem hbrmem, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hbrsat sf' hmem_new
        · exact hb sf' hmem_old
      | persistent nf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append] at hmem'
        rcases hmem' with hmem_new | hmem_old
        · exact hRRS sf' hmem_new
        · exact hb sf' hmem_old
      | notApplicable => simp at hsf
  · -- Every other shape: `modalApplyOneKb5''Prop` agrees with `modalApplyOne`, port the K arm
    -- verbatim (this branch never inspects `kb5FC`-specific facts, only threads `hFC` opaquely).
    have heq2 : modalApplyOneKb5''Prop ⟨sign, formula, lbl⟩ b acc
        = modalApplyOne ⟨sign, formula, lbl⟩ b acc :=
      modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg ⟨sign, formula, lbl⟩ b acc (not_or.mp hshape)
    rw [heq2] at hsf
    cases sign with
    | pos =>
      have hpos : Satisfies m (f lbl) formula := hsf_b.1 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp only [Satisfies] at hpos
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, List.find?_cons_of_pos, Option.getD_some,
          ↓reduceIte, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        obtain ⟨hφ, hψ⟩ := hpos
        refine ⟨[⟨.pos, φ, lbl⟩, ⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun _ => hφ, fun h => by simp at h⟩
        · exact ⟨fun _ => hψ, fun h => by simp at h⟩
        · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hpos
        cases hpos with
        | inl hφ =>
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hφ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        | inr hψ =>
          refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hψ, fun h => by simp at h⟩
          · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [Satisfies] at hpos
            exact fun ha => hpos ha
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hpos
          rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
          · refine ⟨[⟨.pos, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
              W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun _ => hpos hφ, fun h => by simp at h⟩
            · exact hb sf' hmem_old
          · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · exact ⟨fun h => by simp at h, fun _ => hφ⟩
            · exact hb sf' hmem_old
      | box φ => exact absurd (Or.inl ⟨rfl, φ, rfl⟩) hshape
      | diamond φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        simp only [Satisfies] at hpos
        obtain ⟨ww, hwwr, hwwφ⟩ := hpos
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.pos, .diamond φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · refine ⟨fun _ => ?_, fun h => by simp at h⟩
            simp only [witness, f', if_pos rfl]
            exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
    | neg =>
      have hneg : ¬Satisfies m (f lbl) formula := hsf_b.2 rfl
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | and φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        rcases Classical.em (Satisfies m (f lbl) φ) with hφ | hφ
        · refine ⟨[⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_of_mem _ List.mem_cons_self,
            W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hneg hφ⟩
          · exact hb sf' hmem_old
        · refine ⟨[⟨.neg, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun h => by simp at h, fun _ => hφ⟩
          · exact hb sf' hmem_old
      | or φ ψ =>
        simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
          modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
          List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨hφ, hψ⟩ := hneg
        refine ⟨[⟨.neg, φ, lbl⟩, ⟨.neg, ψ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
        intro sf' hmem'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with (rfl | rfl) | hmem_old
        · exact ⟨fun h => by simp at h, fun _ => hφ⟩
        · exact ⟨fun h => by simp at h, fun _ => hψ⟩
        · exact hb sf' hmem_old
      | imp φ ψ =>
        rcases eq_or_ne ψ Proposition.bot with rfl | hne
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          simp only [Satisfies] at hneg
          push Not at hneg
          refine ⟨[⟨.pos, φ, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | hmem_old
          · exact ⟨fun _ => hneg.1, fun h => by simp at h⟩
          · exact hb sf' hmem_old
        · simp only [RuleResult.isApplicable, tryAllPropRules, List.map, applyPropRule, modalAndOf?,
            modalOrOf?, modalImpOf?_imp hne, modalNegOf?, Bool.false_eq_true, not_false_eq_true,
            List.find?_cons_of_neg, List.find?, Option.getD_some, ↓reduceIte, List.cons_append,
            List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
          subst hnewBs hnewAcc'
          exact ⟨_, List.mem_cons_self,
            negImp_alpha_preserved_gen kb5FC hFC hacc hb hneg⟩
      | box φ =>
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc'⟩ := hsf
        subst hnewBs hnewAcc'
        simp only [Satisfies] at hneg
        push Not at hneg
        obtain ⟨ww, hwwr, hwwφ⟩ := hneg
        let w' := modalNextWorld b
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        let newAcc' := acc.addEdge lbl w'
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', hFC, ?_, ?_⟩
        · intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.neg, .box φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · have huw' : u ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).1
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq'
              have hfresh := (hInv u v hedge).2
              rw [heq'] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · constructor
            · intro h; simp at h
            · intro _
              simp only [witness, f', if_pos rfl]
              exact hwwφ
          · simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == lbl) = true
            · rw [if_pos hbsfsign] at hbsfprop
              cases hbf : bsf.formula with
              | diamond ψ' =>
                simp only [hbf] at hbsfprop
                by_cases hinb :
                    (b.any (· == (⟨.neg, ψ', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                      = true
                · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
                · rw [if_neg hinb] at hbsfprop
                  simp only [Option.some.injEq] at hbsfprop
                  subst hbsfprop
                  have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                    exact hbsfsign
                  have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                  rw [hbf, hsign.2] at hdiaNeg
                  simp only [Satisfies] at hdiaNeg
                  push Not at hdiaNeg
                  refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [f', if_pos rfl]
                  exact hdiaNeg ww hwwr
              | _ => simp [hbf] at hbsfprop
            · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
          · have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
      | diamond φ => exact absurd (Or.inr ⟨rfl, φ, rfl⟩) hshape


/-! ### Corrected-Gate Fuel-Induction Assembly

Direct analogue of the retired frozen-rule's fuel induction, with one addition: the threaded
invariant is strengthened from `FiveSoundInv` alone to `Kb5''SoundInv` (`FiveSoundInv` plus the
"root always known" fact `modalApplyOneKb5''Prop_knownWorlds_step`'s `h0` parameter needs), since
the corrected rule's self-target arm can fire from any trigger, not just the root. -/

/-- The combined per-step invariant the corrected-gate KB5 fuel induction threads: `FiveSoundInv`
(`accFreshInv`/`accReachableInv`/`accTargetsKnown`) plus the "root always known" fact every
branch in this tableau satisfies (it starts from the singleton `[F(φ)@0]`, formulas never
removed). Mirrors `FiveSoundInv`, strengthened for the corrected rule's needs. -/
def Kb5''SoundInv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  FiveSoundInv b acc ∧ (0 : WorldIndex) ∈ modalKnownWorlds b

/-- **The corrected-gate KB5 fuel induction**: `modalExpandBranchesGen modalApplyOneKb5''`
closing implies every branch is unsatisfiable-in-`kb5FC`. Direct analogue of the retired
frozen-rule's fuel induction, threading `Kb5''SoundInv` in place of `FiveSoundInv`
and reusing `modalStepBranch_preserves_accFreshInv_gen`/
`modalStepBranch_preserves_accTargetsKnown_gen` (both generic, instantiated at
`modalApplyOneKb5''`/`modalApplyOneKb5''_fresh_local`),
`modalStepBranchKb5''_preserves_accReachableInv` (already landed, bundling the reachability and
root-known preservation together), and the per-step satisfiability bridge
`modalStepBranchKb5''_preserves_satIn` above. -/
theorem modalExpandBranchesKb5''_closed_unsatIn
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => Kb5''SoundInv b acc) branches accs →
      modalExpandBranchesGen modalApplyOneKb5'' branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiableIn kb5FC b acc) branches accs := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs hlength hlength_accs hInv h
    simp only [modalExpandBranchesGen] at h
    split at h
    · simp at h
    · rename_i hfind
      refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩
      intro b a hmem
      have hfn := (List.findSome?_eq_none_iff.mp hfind) _ hmem
      have hcl : isModalClosed b = true := by
        cases h : isModalClosed b with
        | true => rfl
        | false => simp [h] at hfn
      exact modalClosed_unsatIn kb5FC b hcl a
  | succ fuel' ih =>
    intro branches expandedSets accs hlength hlength_accs hInv h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        List.Forall₂ (fun b a => Kb5''SoundInv b a) pending pendingAccs →
        List.Forall₂ (fun b a => Kb5''SoundInv b a) done doneAccs →
        modalExpandBranchesGen.processNext modalApplyOneKb5''
          fuel' pending pendingExp pendingAccs done doneExp doneAccs = .closed →
        List.Forall₂ (fun b a => ¬branchSatisfiableIn kb5FC b a) pending pendingAccs from
      key branches expandedSets accs [] [] []
        hlength hlength_accs rfl rfl hInv List.Forall₂.nil
        (by simpa [modalExpandBranchesGen] using h)
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ _ _ hInv_pending _ _
      cases hInv_pending
      exact List.Forall₂.nil
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hpendingExpLen hpendingAccsLen hdoneExpLen hdoneAccsLen
        hInv_pending hInv_done hinner
      cases pendingAccs with
      | nil => simp at hpendingAccsLen
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hpendingExpLen
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hpendingExpLen hpendingAccsLen
          cases hInv_pending with
          | cons hInv_bh hInv_rest =>
            have hFresh_bh : accFreshInv bh a := hInv_bh.1.1
            have hReach_bh : accReachableInv bh a := hInv_bh.1.2.1
            have hKnown_bh : accTargetsKnown bh a := hInv_bh.1.2.2
            have h0_bh : (0 : WorldIndex) ∈ modalKnownWorlds bh := hInv_bh.2
            simp only [modalExpandBranchesGen.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              apply List.Forall₂.cons
              · exact modalClosed_unsatIn kb5FC bh hcl a
              · exact ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                    (by simp [hpendingExpLen])
                    (by simp [hpendingAccsLen])
                    (by simp [hdoneExpLen])
                    (by simp [hdoneAccsLen])
                    hInv_rest
                    (List.rel_append hInv_done
                      (List.Forall₂.cons hInv_bh List.Forall₂.nil))
                    hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep_eq : modalStepBranchGen modalApplyOneKb5'' bh e a with
              | none => rw [hstep_eq] at hinner; simp at hinner
              | some step =>
                obtain ⟨newBs, newExps, newAcc⟩ := step
                rw [hstep_eq] at hinner
                have hnewExpLen : newExps.length = newBs.length := by
                  unfold modalStepBranchGen at hstep_eq
                  obtain ⟨sf, -, hf⟩ := List.exists_of_findSome?_eq_some hstep_eq
                  rcases h_apply : (modalApplyOneKb5'' sf bh a) with ⟨result, _⟩
                  simp only [h_apply] at hf
                  cases result with
                  | notApplicable => simp at hf
                  | _ =>
                    split_ifs at hf
                    simp only [Option.some.injEq, Prod.mk.injEq] at hf
                    obtain ⟨rfl, rfl, -⟩ := hf; simp [List.length_map]
                have hInvNew : List.Forall₂ (fun b a => Kb5''SoundInv b a)
                    newBs (List.replicate newBs.length newAcc) :=
                  forall₂_replicate_right.mpr (fun b' hb' =>
                    ⟨⟨modalStepBranch_preserves_accFreshInv_gen modalApplyOneKb5''
                          modalApplyOneKb5''_fresh_local bh e a newBs newExps newAcc hstep_eq
                          hFresh_bh b' hb',
                      (modalStepBranchKb5''_preserves_accReachableInv bh e a newBs
                          newExps newAcc hstep_eq hKnown_bh hReach_bh h0_bh b' hb').1,
                      modalStepBranch_preserves_accTargetsKnown_gen modalApplyOneKb5''
                          modalApplyOneKb5''_fresh_local bh e a newBs newExps newAcc hstep_eq
                          hKnown_bh b' hb'⟩,
                     (modalStepBranchKb5''_preserves_accReachableInv bh e a newBs
                        newExps newAcc hstep_eq hKnown_bh hReach_bh h0_bh b' hb').2⟩)
                have hInvAll : List.Forall₂ (fun b a => Kb5''SoundInv b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  List.rel_append (List.rel_append hInv_done hInvNew) hInv_rest
                have hunsat_all :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn kb5FC b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                    (by simp only [List.length_append]; omega)
                    (by simp only [List.length_append, List.length_replicate]; omega)
                    hInvAll hinner
                have hunsat_newBs_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn kb5FC b a)
                    (newBs ++ bt) (List.replicate newBs.length newAcc ++ restAs) := by
                  have h := List.forall₂_drop done.length hunsat_all
                  rw [List.append_assoc done newBs bt, List.drop_left,
                      List.append_assoc doneAccs (List.replicate newBs.length newAcc) restAs,
                      List.drop_left' hdoneAccsLen] at h
                  exact h
                have hunsat_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn kb5FC b a)
                    bt restAs := by
                  have h := List.forall₂_drop newBs.length hunsat_newBs_bt
                  rw [List.drop_left,
                      List.drop_left' List.length_replicate] at h
                  exact h
                have hunsat_newBs :
                    List.Forall₂ (fun b a => ¬branchSatisfiableIn kb5FC b a)
                    newBs (List.replicate newBs.length newAcc) := by
                  have h := List.forall₂_take newBs.length hunsat_newBs_bt
                  rw [List.take_left,
                      List.take_left' List.length_replicate] at h
                  exact h
                have hbh_unsat : ¬branchSatisfiableIn kb5FC bh a := by
                  intro hbh_sat
                  obtain ⟨b', hb'_mem, hb'_sat⟩ :=
                    modalStepBranchKb5''_preserves_satIn
                      bh e a newBs newExps newAcc hstep_eq hbh_sat hFresh_bh hReach_bh
                  exact (forall₂_replicate_right.mp hunsat_newBs b' hb'_mem) hb'_sat
                exact List.Forall₂.cons hbh_unsat hunsat_bt

/-- **The corrected-gate KB5 soundness capstone**: if `modalTableauKb5''` closes on `F(φ)`, then
`φ` is `kb5Valid` -- proved **directly** against `kb5FC`. Direct analogue of the retired
frozen-rule's soundness capstone, feeding `modalExpandBranchesKb5''_closed_unsatIn` at the
initial configuration
`[[F(φ)@0]] [[]] [Accessibility.empty]`, with the initial `Kb5''SoundInv` witness built from
`accFreshInv_empty`, `accReachableInv_initial`, the trivial vacuous `accTargetsKnown` for the
edgeless empty accessibility relation, and the trivial "root known" fact for the singleton seed
branch `[F(φ)@0]` (its only label is `0`). -/
theorem modalTableauKb5''_sound (φ : Proposition Atom) (h : modalTableauKb5'' φ = .closed) :
    kb5Valid φ := by
  intro World m hFC w
  by_contra hnotsat
  have hsat : branchSatisfiableIn kb5FC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hFC,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have h0 : (0 : WorldIndex) ∈ modalKnownWorlds
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] :=
    (mem_modalKnownWorlds _ 0).mpr
      ⟨(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex), List.mem_cons_self, rfl⟩
  have hInv0 : Kb5''SoundInv
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] Accessibility.empty :=
    ⟨⟨accFreshInv_empty _, accReachableInv_initial φ,
      fun w w' hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge])⟩, h0⟩
  have hunsat := modalExpandBranchesKb5''_closed_unsatIn (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons hInv0 List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesGen modalApplyOneKb5''
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-! ## KB5 Soundness via Frame-Class Monotonicity

`modalTableauKb5` (`FiveSimplification.lean`) is definitionally `modalTableauFive` -- the "factor,
not clone" decision recorded in that file's KB5-instantiation module note. Soundness for `kb5Valid`
is therefore not a re-derived fuel-induction chain but a two-line corollary of
`modalTableauFive_sound` composed with the frame-class monotonicity below, mirroring the
S5/Five separation proof's bridging pattern
(`s5FC_imp_fiveFC`/`fiveValid_imp_s5Valid`) one level down the frame-class hierarchy
(`kb5FC ⇒ fiveFC ⇒ trivialFC`, matching `s5FC ⇒ fiveFC`/`s5FC ⇒ kb5FC`'s already-probed shape). -/

/-- `kb5FC` entails `fiveFC` by projection: KB5 frames are Euclidean frames with symmetry added.
Mirrors the separation probe's `s5FC_imp_fiveFC`. -/
theorem kb5FC_imp_fiveFC {World : Type} {r : World → World → Prop} (h : kb5FC r) : fiveFC r := h.2

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Frame-class monotonicity**: `fiveValid φ → kb5Valid φ`. Validity over the larger
(Euclidean) frame class is the stronger requirement, so it descends to the smaller (KB5,
symmetric-and-Euclidean) subclass. Mirrors the separation probe's `fiveValid_imp_s5Valid`. -/
theorem fiveValid_imp_kb5Valid (φ : Proposition Atom) (h : fiveValid φ) : kb5Valid φ :=
  fun World m hFC w => h World m hFC.2 w

/-- **The KB5 soundness capstone**: if the KB5 tableau closes on `F(φ)`, then
`φ` is `kb5Valid`. Since `modalTableauKb5 = modalTableauFive` definitionally
(`FiveSimplification.lean`'s `modalTableauKb5_eq_modalTableauFive`), this is a direct corollary of
`modalTableauFive_sound` composed with `fiveValid_imp_kb5Valid` -- no bespoke fuel-induction
re-derivation needed. See `FiveSimplification.lean`'s KB5-instantiation module note for the full
"factor, don't clone" argument. -/
theorem modalTableauKb5_sound (φ : Proposition Atom) (h : modalTableauKb5 φ = .closed) :
    kb5Valid φ :=
  fiveValid_imp_kb5Valid φ (modalTableauFive_sound φ h)

/-! ## Pinned-Witness Truth Lemma (Route (1), Decision Gate A)

**Route (1)** repairs the S4-keyed loop guard's soundness obligation (the redirect edge
`blockingWorldS4Keyed` licenses, `LoopChecking.lean`) by *pinning* the witness model:
strengthening `branchSatisfiableIn`'s existential witness with an extra conjunct,
`accPinnedBy`, that upper-bounds the witness relation `m.r` over the branch's own label
images by the reflexive-transitive closure of the recorded `acc` edges. This is the
containment `ChagrovZakharyaschev1997` Theorem 5.51 states for its filtration model,
`chunk_0267.md`: *"It should be clear that `S_{n+1} ⊆ R_Grz`"* -- an upper bound on the
generated relation that does **not** claim equality with the ambient relation restricted to
the carrier (the parenthetical immediately following, `chunk_0267.md`-`chunk_0268.md`). It is
also exactly the upper half of the interval theorem `S_min ⊆ S ⊆ S_max` (`chunk_0246.md`
L43-65), whose explicit warning -- *"a relation `S` between `S` and `S̄` may be nontransitive
even if the original `R` is transitive"* -- is why an upper bound on `m.r`, not merely the
edge conjunct's lower bound, is needed at all: three prior soundness routes for this guard died
precisely because the witness model's ambient predecessors of the redirect's source label were
uncontrolled -- a standalone, driver-independent redirect lemma naming only `src` (refuted
below); ancestor-only blocking; the origin-edge revision.

### The standalone redirect lemma was refuted, not merely left unproven

A fourth route was attempted, as a standalone ancestor-redirect decision-gate lemma (since
deleted): the claim that `branchSatisfiableIn s4FC b acc`, `acc.hasEdge a src`, and hypotheses
propagating box-positive/diamond-negative content from `src` to `a` alone
(`hboxback`/`hdianeg`) suffice for `branchSatisfiableIn s4FC b (acc.addEdge src a)`. This is
**not** an open conjecture: it is **false**, witnessed by an explicit three-world countermodel,
and the lemma was deleted rather than left as a standing `sorry`.

- **The statement is false.** Countermodel: `acc = {0→1, 2→1}`, `b = [T(□p)@0, F(p)@2]`, redirect
  `src = 1`, `a = 2`. `hboxback`/`hdianeg` hold vacuously (no box-positive/diamond-negative
  formula at label `1` occurs on `b`). `b` is `s4FC`-satisfiable at `acc`, but not at
  `acc.addEdge 1 2`: the edge conjunct forces `m.r (f 0) (f 1)` and `m.r (f 1) (f 2)`,
  transitivity forces `m.r (f 0) (f 2)`, and `T(□p)@0` then forces `p` at `f 2`, contradicting
  `F(p)@2`.
- **Why it is false.** Transitive closure transmits box-positive payload from *every*
  `acc`-ancestor of `src` (here, `0`, via `2 → 1` and the closure edge `0 → 1 → 2` after the
  redirect) -- not just from `src` itself. A hypothesis set naming only `src` cannot see the
  payload carried by `src`'s own ancestors, so it cannot control what the redirect exposes them
  to.
- **The Massacci citation was a dead end, and additionally a category error here.** Massacci
  (2000) Theorem 8.1 -- stated, never proved in that paper, deferred to refs [7]/[20] -- concerns
  blocking on a **π-completed (saturated)** branch. The deleted lemma dropped saturation entirely
  in pursuit of a driver-independent statement; that is exactly the hypothesis the countermodel
  exploits (`[T(□p)@0, F(p)@2]` is nowhere near saturated). So the citation was never going to
  close this lemma even if Theorem 8.1 had been proved -- the two statements are about different
  things.

The refutation is preserved as an executable regression witness at
`CslibTests/AncestorRedirectRefutation.lean` (`RefuteAncestorRedirect.statement_is_false`), so a
future re-derivation of this obstruction fails the test suite rather than being rediscovered from
scratch. **Route decision**: the standalone lemma was deleted, not restated or retained, because
its statement is false; the soundness obligation it attempted is discharged sorry-free by
`branchSatisfiableIn_s4FC_addEdge_of_blocked` (below `extractModelS4`/`modalTruthLemmaS4`,
`FrameCompleteness.lean`) under a Hintikka-saturation hypothesis, and independently by the
`S4RedirectSoundInv` family (ghost-edge quarantine, `FrameCompleteness.lean`) -- both of which add
the ancestor-visibility content this standalone route lacked.

`accPinnedBy` quantifies only over `modalKnownWorlds b` -- **not** every `WorldIndex` --
because `f : WorldIndex → W` is total: an unrestricted upper bound would force every UNUSED
label to map to a point with no `m.r`-relations at all beyond what `ReflTransGen acc` already
proves between them, which is false in general (nothing prevents the witness model from
relating two unused labels' images however it likes). Restricting to labels that actually
occur on the branch is the same restriction `branchSatisfiableIn`'s own edge conjunct is
silent about, stated the other way around.

A **box-condition** form of the pinning invariant --
`m.r (f w) (f w') → ∀ ψ, T(□ψ)@w ∈ b → (T(□ψ)@w' ∈ b ∧ T(ψ)@w' ∈ b)` -- was considered and
**rejected** as the primitive invariant: it is not monotone in `b`, since the 4-rule only ever
adds `T(□ψ)@w` at *direct* `acc`-edge targets, while `m.r` may relate `f w` to strictly more
label images than `acc`'s recorded edges reach in one step. `accPinnedBy` avoids this by
bounding `m.r` itself (a purely structural fact about the witness relation), leaving the
Hintikka-side box-content transfer to Gate B's saturation hypothesis and the boxed birth
content mechanism, applied separately. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Mechanism 1 of Route (1) (Decision Gate A).** On labels that occur on the branch `b`,
the witness relation `m.r` is no LARGER than the reflexive-transitive closure of the recorded
`acc` edges. Together with `branchSatisfiableIn`'s existing edge conjunct (`acc.hasEdge w w' →
m.r (f w) (f w')`, the matching LOWER bound), this PINS `m.r` on the label image: an "ambient
predecessor of `f src`" among known labels is thereby forced to be an `acc`-ancestor of `src`,
a set the tableau's own 4-rule has already propagated box-positive content to. See the module
comment above for why the quantification is restricted to `modalKnownWorlds b` and why the
box-condition alternative was rejected. -/
def accPinnedBy (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W) : Prop :=
  ∀ w ∈ modalKnownWorlds b, ∀ w' ∈ modalKnownWorlds b,
    m.r (f w) (f w') → Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w'

omit [DecidableEq Atom] [Hashable Atom] in
/-- **`branchSatisfiableIn`, additionally PINNED** by `accPinnedBy`: the witness model is
constrained by an extra conjunct inside the existential, rather than left existentially
arbitrary. Route (1)'s central definitional device -- see the module comment above. -/
def branchSatisfiablePinnedIn (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
    FC m.r ∧
    (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧
    accPinnedBy b acc m f ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula)

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Sub-step 1.1 of Decision Gate A** (lands sorry-free regardless of the gate's overall
verdict): the redirect edge `src → wBlock` extends a pinned witness model's relation, via
`r' := m.r ∨ (m.r · (f src) ∧ m.r (f wBlock) ·)`, preserving the frame condition, the edge
conjunct, and `accPinnedBy` -- the three MECHANICAL conjuncts of `branchSatisfiablePinnedIn`.
`r'` is exactly "add the edge `f src → f wBlock`, then close transitively", the only extension
an `IsTrans`-constrained relation admits; the four-case split on `IsTrans` (old/old, old/new,
new/old, new/new) is the standard closure-preserves-transitivity argument. The `accPinnedBy`
case for a NEW-disjunct pair composes three `ReflTransGen` legs -- `w ⇝ src` (old, lifted by
monotonicity), the single new edge `src → wBlock`, and `wBlock ⇝ w'` (old, lifted) -- using
`hsrc`/`hwB` to invoke the ORIGINAL `accPinnedBy` at `src`/`wBlock` themselves (both already
known worlds). The BRANCH conjunct is deliberately absent from this lemma's conclusion: it is
Gate A's verdict, attempted separately below. -/
lemma branchSatisfiablePinnedIn_redirect_mechanical
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {src wBlock : WorldIndex}
    (h : branchSatisfiablePinnedIn s4FC b acc)
    (hsrc : src ∈ modalKnownWorlds b) (hwB : wBlock ∈ modalKnownWorlds b) :
    ∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W), s4FC m.r ∧
      (∀ w w', (acc.addEdge src wBlock).hasEdge w w' → m.r (f w) (f w')) ∧
      accPinnedBy b (acc.addEdge src wBlock) m f := by
  obtain ⟨W, m, f, ⟨hrefl, htrans⟩, hedges, hpinned, -⟩ := h
  have hmono : ∀ {u v : WorldIndex},
      Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) u v →
      Relation.ReflTransGen (fun a c => (acc.addEdge src wBlock).hasEdge a c = true) u v := by
    intro u v huv
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hlast ih => exact ih.tail (hasEdge_addEdge_mono_FS hlast)
  refine ⟨W, ⟨fun x y => m.r x y ∨ (m.r x (f src) ∧ m.r (f wBlock) y), m.v⟩, f, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact ⟨fun a => Or.inl (hrefl.refl a)⟩
  · refine ⟨?_⟩
    rintro a b c (hab | ⟨ha, hb⟩) (hbc | ⟨hb', hc⟩)
    · exact Or.inl (htrans.trans a b c hab hbc)
    · exact Or.inr ⟨htrans.trans a b (f src) hab hb', hc⟩
    · exact Or.inr ⟨ha, htrans.trans (f wBlock) b c hb hbc⟩
    · exact Or.inr ⟨ha, hc⟩
  · intro w w' hedge
    rcases hasEdge_addEdge_cases hedge with ⟨hw, hw'⟩ | hold
    · rw [hw, hw']
      exact Or.inr ⟨hrefl.refl (f src), hrefl.refl (f wBlock)⟩
    · exact Or.inl (hedges w w' hold)
  · intro w hw w' hw' hmr
    rcases hmr with hold | ⟨ha, hc⟩
    · exact hmono (hpinned w hw w' hw' hold)
    · have hstep : Relation.ReflTransGen
          (fun a c => (acc.addEdge src wBlock).hasEdge a c = true) src wBlock :=
        Relation.ReflTransGen.single (hasEdge_addEdge_self_FS acc src wBlock)
      exact (hmono (hpinned w hw src hsrc ha)).trans
        (hstep.trans (hmono (hpinned wBlock hwB w' hw' hc)))

end Cslib.Logic.Modal.Tableau

end
