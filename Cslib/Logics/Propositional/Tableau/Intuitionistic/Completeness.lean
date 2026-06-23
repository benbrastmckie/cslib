/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness

/-! # Intuitionistic Tableau Completeness

This module proves completeness of the intuitionistic propositional tableau: if `φ` is
intuitionistically valid, then the tableau closes on `φ`.

## Main Results

- `intExtractModel`: Construct a Kripke model from an open saturated branch.
- `intTruthLemma`: The extracted model satisfies all signed formulas on the branch.
- `intuitionisticTableau_complete`: If `IValid φ`, then `intuitionisticTableau φ = closed`.

## Countermodel Construction

From an open saturated branch `b`, construct a Kripke model as follows:
- **Worlds**: The set of world labels appearing on `b`, ordered by ≤.
- **Valuation**: `v(w, p) = true ↔ T(atom p) is on branch b at world w`.
- **botForces**: Always `False` (intuitionistic semantics).
- **Accessibility**: `w ≤ w'` iff `w ≤ w'` as natural numbers (the creation order).

The model is well-formed because:
1. Upward-closure of valuation follows from the persistence propagation in the expansion.
2. The truth lemma follows by induction on formula structure using the saturation condition.

## Notes on sorry

The truth lemma requires careful induction on formula structure. All proofs are marked sorry.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Countermodel Extraction -/

/-- The valuation extracted from an open saturated branch.

Atom `p` is assigned true at world `w` iff T(atom p) appears at label `w` on the branch. -/
def intExtractValuation (b : IBranch Atom) (w : Nat) (p : Atom) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- The `botForces` predicate for the intuitionistic countermodel: always False. -/
def intBotForces : Nat → Prop := fun _ => False

/-! ## Truth Lemma -/

/-- The truth lemma for the intuitionistic tableau.

If `b` is an open saturated branch (after persistence fixpoint), then the extracted
valuation `intExtractValuation b` satisfies every T(φ) on `b` and falsifies every F(φ) on `b`.

The proof is by induction on `φ`:
- **atom p**: T(p) on branch ↔ `intExtractValuation b w p` by definition.
- **bot**: T(⊥) cannot appear on an open branch (closure would have fired).
- **imp φ ψ**:
  - T(φ → ψ) at w: by saturation, for all w' ≥ w with T(φ) at w',
    T(ψ) is at w' (by the T(imp) rule applied to fixpoint). By IH.
  - F(φ → ψ) at w: by saturation (world-creating rule was applied),
    there is a world w' with T(φ) at w' and F(ψ) at w'. By IH.
- **and**, **or**: Standard truth lemma steps.

NOTE: Full proof marked sorry. -/
lemma intTruthLemma (b : IBranch Atom)
    (hopen : isIntuitionisticallyClosed b = false)
    (hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none) -- Simplified saturation hypothesis
    (φ : Proposition Atom) (w : Nat) :
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) intBotForces w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) intBotForces w φ) := by
  sorry

/-- An open saturated branch from the intuitionistic tableau yields a Kripke countermodel.

If `intuitionisticTableau φ = openBranch b`, then `intExtractValuation b` falsifies `φ`
at world 0 in the intuitionistic Kripke model with worlds ordered by ≤ on Nat. -/
lemma intuitionisticOpenBranch_countermodel (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .openBranch b) :
    ¬ IForces (intExtractValuation b) intBotForces 0 φ := by
  sorry

/-! ## Main Completeness Theorem -/

/-- **Intuitionistic Tableau Completeness**: If `φ` is intuitionistically valid,
then the intuitionistic tableau closes on `φ`.

Proof by contrapositive: if `intuitionisticTableau φ = openBranch b`, then
`intuitionisticOpenBranch_countermodel` gives a Kripke model falsifying `φ`,
contradicting `IValid φ`.

NOTE: Full proof marked sorry. -/
theorem intuitionisticTableau_complete (φ : Proposition Atom)
    (h : IValid φ) : intuitionisticTableau φ = .closed := by
  sorry

end Cslib.Logic.PL

end
