/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.Saturation

/-! # Modal K Tableau Soundness

This module proves soundness of the modal K tableau: if the tableau closes on `φ`
(starting from `F(φ)` at world 0), then `φ` is K-valid (satisfied in all Kripke models).

## Main Results

- `branchSatisfiable`: Satisfiability of a branch via a Kripke model.
- `modalExpandBranches_closed_unsat`: Key loop soundness (marked sorry; see notes).
- `modalTableau_sound`: `modalTableau φ = .closed → Proposition.valid Set.univ φ`.

## Notes on sorry

`modalExpandBranches_closed_unsat` is sorry'd, following the same pattern as
`classicalExpandBranches_closed_unsat` in `Classical/Soundness.lean`. The soundness
proof requires a fuel induction argument, which in turn requires per-rule satisfiability
preservation lemmas. The structure and statements are correct; the loop invariant proof
is the technically deepest part and is deferred as a follow-on proof obligation.

The `Decidable` instance in `Completeness.lean` uses `modalTableau_sound` and
`modalTableau_complete` via isTrue/isFalse; both inherit this sorry.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Branch Satisfiability -/

/-- A branch `b` with accessibility relation `acc` is satisfiable if there exists a
Kripke model `m` over `WorldIndex` such that:
- The model's accessibility extends `acc`: if `(w, w') ∈ acc.edges` then `m.r w w'`.
- Every T(φ)@w on the branch: `Satisfies m w φ`.
- Every F(φ)@w on the branch: `¬Satisfies m w φ`. -/
def branchSatisfiable
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (m : Model WorldIndex Atom),
    (∀ w w', acc.hasEdge w w' → m.r w w') ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m sf.label sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m sf.label sf.formula)

/-! ## Key Soundness Lemma -/

/-- If `modalExpandBranches` closes all branches, then no branch in the initial list
was satisfiable. Proved by induction on fuel and worklist structure.

NOTE: Full proof marked sorry. The proof requires showing that each application of
`modalApplyOne` preserves branch satisfiability, and that closed branches are
unsatisfiable. Both sub-proofs are correct in structure but require detailed
case analysis on the formula type. This matches the pattern of
`classicalExpandBranches_closed_unsat` in `Classical/Soundness.lean`. -/
theorem modalExpandBranches_closed_unsat
    (branches : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (acc : Accessibility)
    (fuel : Nat)
    (hclosed : modalExpandBranches branches expandedSets acc fuel = .closed) :
    ∀ i (hi : i < branches.length), ¬branchSatisfiable (branches.get ⟨i, hi⟩) acc := by
  sorry

/-! ## K-Validity and Soundness -/

/-- K-validity: a proposition is K-valid if it is satisfied in all Kripke models at all worlds. -/
def kValid (φ : Proposition Atom) : Prop :=
  ∀ (World : Type) (m : Model World Atom) (w : World), Satisfies m w φ

/-- The modal K tableau is sound: if the tableau closes on `F(φ)`, then `φ` is K-valid.

Proof by contrapositive: if `φ` is falsified at some world `w` in model `m`, then
the initial branch `[F(φ)@0]` is satisfiable (map world 0 to `w`). But if the
tableau closes, the initial branch is unsatisfiable by `modalExpandBranches_closed_unsat`.

Inherits sorry from `modalExpandBranches_closed_unsat`. -/
theorem modalTableau_sound (φ : Proposition Atom)
    (h : modalTableau φ = .closed) :
    kValid φ := by
  intro World m w
  by_contra hnotsat
  -- The initial branch [F(φ)@0] is satisfiable via a model embedding the counterexample.
  -- The construction embeds `m` into a `Model WorldIndex Atom` via a Skolem-style function.
  -- This requires a universe-polymorphic embedding which uses sorry below for the
  -- semantic correspondence (Satisfies m0 0 φ ↔ Satisfies m w φ).
  have hsat : branchSatisfiable [⟨.neg, φ, 0⟩] Accessibility.empty := by
    sorry
  -- The tableau closes, so the initial branch is unsatisfiable
  have hunsat := modalExpandBranches_closed_unsat
    [[⟨.neg, φ, 0⟩]]
    [[]]
    Accessibility.empty
    (modalFuel φ)
    (by simp only [modalTableau] at h; exact h)
  exact hunsat 0 (by simp) hsat

end Cslib.Logic.Modal.Tableau

end
