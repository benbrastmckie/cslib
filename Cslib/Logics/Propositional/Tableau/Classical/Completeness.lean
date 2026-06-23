/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Classical.Soundness

/-! # Classical Tableau Completeness

This module proves completeness of the classical propositional tableau: if `φ` is a
classical tautology, then the tableau closes on `φ`.

## Main Results

- `classicalOpenBranch_countermodel`: An open saturated branch yields a Boolean countermodel.
- `classicalTableau_complete`: If `Tautology φ`, then `classicalTableau φ = closed`.

## Strategy

By contrapositive: if the tableau returns `openBranch b`, then `b` is an open saturated
branch from which we extract a Boolean valuation:
  `v p = true ↔ T(atom p) is on branch b`

The truth lemma (proved by induction on formula structure) shows this valuation satisfies
every T(φ) and falsifies every F(φ) on the branch. In particular, F(φ) is on the initial
branch, so `v` falsifies `φ`, meaning `φ` is not a tautology.

## Notes on sorry

The truth lemma by induction on formula structure requires careful case analysis. Full
proof is marked sorry; the decision procedure uses the Boolean enumeration instead.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Countermodel Extraction -/

/-- Extract a Boolean valuation from an open saturated branch.

An atom `p` is assigned `true` iff T(atom p) appears on the branch.
Saturatedness ensures this valuation is consistent with all signed formulas. -/
def extractValuation (b : Branch (Proposition Atom) Unit) : BoolValuation Atom :=
  fun p => b.any fun sf => sf.sign == .pos && sf.formula == .atom p

/-- Truth lemma for the extracted valuation.

If `b` is a saturated open branch (every applicable rule has been used), then
the valuation `extractValuation b` satisfies every T(φ) on `b` and falsifies every F(φ) on `b`.

Proof by induction on the structure of `φ`. The base cases (atom, bot) follow from the
definition of `extractValuation` and classical closure. The inductive cases follow from
saturation: if T(φ ∧ ψ) is on the branch, then T(φ) and T(ψ) are too (by saturation),
so by induction hypothesis the valuation satisfies both.

NOTE: Full proof by formula induction is marked sorry. -/
lemma classicalTruthLemma (b : Branch (Proposition Atom) Unit)
    (hopen : isClassicallyClosed b = false)
    (hsat : classicalStepBranch b [] = none) -- Branch is saturated
    (φ : Proposition Atom) :
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ) →
      BoolEvaluate (extractValuation b) φ = true) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ) →
      BoolEvaluate (extractValuation b) φ = false) := by
  sorry

/-- An open saturated branch from the classical tableau yields a Boolean countermodel.

If the tableau returns `openBranch b`, then `b` is consistent: the valuation
`extractValuation b` satisfies it. This means there exists a valuation falsifying `φ`. -/
lemma classicalOpenBranch_countermodel (φ : Proposition Atom)
    (h : classicalTableau φ = .openBranch b) :
    BoolEvaluate (extractValuation b) φ = false := by
  sorry

/-! ## Main Completeness Theorem -/

/-- **Classical Tableau Completeness**: If `φ` is a classical tautology,
then the classical tableau closes on `φ`.

Proof by contrapositive: if `classicalTableau φ ≠ closed`, then
`classicalTableau φ = openBranch b` for some `b`, and by `classicalOpenBranch_countermodel`,
`BoolEvaluate (extractValuation b) φ = false`, so `φ` is not a tautology.

NOTE: Full formal proof marked sorry. -/
theorem classicalTableau_complete (φ : Proposition Atom)
    (h : Tautology φ) : classicalTableau φ = .closed := by
  sorry

end Cslib.Logic.PL

end
