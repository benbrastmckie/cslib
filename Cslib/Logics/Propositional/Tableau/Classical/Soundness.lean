/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Classical.Expansion
public import Cslib.Logics.Propositional.Semantics.Bool

/-! # Classical Tableau Soundness

This module proves soundness of the classical propositional tableau: if the tableau
closes on `φ` (starting from `F(φ)`), then `φ` is a classical tautology.

## Main Results

- `branchConsistent`: Predicate relating a Boolean valuation to a signed branch.
- `classicalBranchSatisfiable`: A branch is satisfiable if a consistent valuation exists.
- `classicalTableau_sound`: If `classicalTableau φ = closed`, then `Tautology φ`.

## Strategy

Soundness follows from two sub-lemmas:
1. Each classical rule preserves branch satisfiability.
2. A classically closed branch is unsatisfiable.

Together these imply: if the tableau closes (all branches are closed), then the initial
branch `[F(φ)]` was unsatisfiable, meaning every valuation satisfies `T(φ)`, i.e., `φ`
is a tautology.

## Notes on sorry

The soundness proof for the `classicalExpandBranches` loop (induction on fuel) requires
significant infrastructure. The key lemmas are stated and their proofs are marked sorry.
The decision procedure in `Classical/DecisionProcedure.lean` uses the existing Boolean
enumeration completeness to give a sorry-free `Decidable (Tautology φ)` instance.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Branch Satisfiability -/

/-- A Boolean valuation is consistent with a signed branch if:
- For every T(φ) on the branch, `BoolEvaluate v φ = true`
- For every F(φ) on the branch, `BoolEvaluate v φ = false` -/
def branchConsistent (v : BoolValuation Atom)
    (b : Branch (Proposition Atom) Unit) : Prop :=
  ∀ sf ∈ b,
    (sf.sign = .pos → BoolEvaluate v sf.formula = true) ∧
    (sf.sign = .neg → BoolEvaluate v sf.formula = false)

/-- A branch is satisfiable if there exists a Boolean valuation consistent with it. -/
def classicalBranchSatisfiable (b : Branch (Proposition Atom) Unit) : Prop :=
  ∃ v : BoolValuation Atom, branchConsistent v b

/-! ## Key Lemmas (with sorry) -/

/-- Each classical rule application preserves branch satisfiability.

If branch `b` is satisfiable and a rule applied to `sf ∈ b` gives sub-branches,
then at least one sub-branch is also satisfiable (for beta-rules) or the single
resulting branch is satisfiable (for alpha-rules).

NOTE: Proof by case analysis on all 8 classical rules and both signs.
Full proof deferred; see sorry annotation. -/
lemma classicalRule_preserves_sat (b : Branch (Proposition Atom) Unit)
    (sf : SignedFormula (Proposition Atom) Unit)
    (hmem : sf ∈ b)
    (hsat : classicalBranchSatisfiable b) :
    match classicalApplyOne sf with
    | .linear newForms =>
      classicalBranchSatisfiable (Branch.extendMany b newForms)
    | .branching branches =>
      ∃ br ∈ branches, classicalBranchSatisfiable (Branch.extendMany b br)
    | .persistent newForms =>
      classicalBranchSatisfiable (Branch.extendMany b newForms)
    | .notApplicable => True := by
  sorry

/-- A classically closed branch is unsatisfiable.

Classical closure holds when T(⊥) is present (which is never satisfiable) or when
T(φ) and F(φ) coexist (which forces `BoolEvaluate v φ = true` and `= false` simultaneously). -/
lemma classically_closed_unsatisfiable (b : Branch (Proposition Atom) Unit)
    (hclosed : isClassicallyClosed b = true) :
    ¬ classicalBranchSatisfiable b := by
  sorry

/-! ## Main Soundness Theorem -/

/-- **Classical Tableau Soundness**: If the classical tableau closes on `φ`,
then `φ` is a classical tautology.

The proof proceeds by contrapositive: if `φ` is not a tautology, there is a Boolean
valuation `v` with `BoolEvaluate v φ = false`. The initial branch `[F(φ)]` is satisfiable
via `v`. By `classicalRule_preserves_sat`, no branch can become unsatisfiable through rule
applications. By `classically_closed_unsatisfiable`, no satisfiable branch can close.
Hence the tableau cannot return `closed`, contradiction.

NOTE: The formal loop induction is marked sorry; the `Decidable` instance in
`DecisionProcedure.lean` uses the existing Boolean enumeration for classical logic. -/
theorem classicalTableau_sound (φ : Proposition Atom)
    (h : classicalTableau φ = .closed) : Tautology φ := by
  sorry

end Cslib.Logic.PL

end
