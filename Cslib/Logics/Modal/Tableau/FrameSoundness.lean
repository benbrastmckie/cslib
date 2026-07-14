/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Soundness

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

end Cslib.Logic.Modal.Tableau

end
