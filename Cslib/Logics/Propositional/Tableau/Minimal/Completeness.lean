/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Minimal.Soundness
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness

/-! # Minimal Tableau Completeness

This module proves completeness of the minimal propositional tableau: if `φ` is minimally
valid, then the tableau closes on `φ`.

## Main Results

- `minBranchBotForces`: Defined in `Minimal.Soundness`; see that module.
- `minTruthLemma`: Delegates to the parametric `truthLemma minScheme` from `Scheme.lean`.
- `minimalTableau_complete`: If `MValid φ`, then `minimalTableau φ = closed`.

## Design

This module now delegates to the parametric implementations in `Intuitionistic.Scheme`.
The declarations `minTruthLemma`, `minOpenBranch_countermodel`, and `minimalTableau_complete`
are thin corollaries of their parametric counterparts `truthLemma minScheme`,
`openBranch_countermodel minScheme`, and `tableau_complete minScheme`.

The valuation extracted from an open saturated branch reuses `intExtractValuation` from
`Intuitionistic.Soundness` (available via the transitivity
`Int.Completeness → Int.Scheme → Min.Soundness → Int.Soundness`).

## Countermodel Construction

From an open saturated branch `b`, construct a Kripke model as follows:
- **Worlds**: Natural numbers (Kripke world labels on `b`) with ≤ ordering.
- **Valuation**: `intExtractValuation b` (from `Intuitionistic.Soundness`).
- **botForces**: `minBranchBotForces b` (T(⊥) read from the branch; defined in `Minimal.Soundness`).
- **Accessibility**: `w ≤ w'` as natural numbers.

## Notes on sorry

`minTruthLemma` and `minOpenBranch_countermodel` delegate to `truthLemma minScheme`
and `openBranch_countermodel minScheme` respectively, which carry the deferred sorries in
`Scheme.lean`. The remaining sorry in `minimalTableau_complete` bridges `MValid φ` to the
per-branch forcing hypothesis required by `tableau_complete minScheme`; this is part of the
completeness obligations handed to task 317.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Truth Lemma -/

/-- The truth lemma for the minimal tableau.

Delegates to `truthLemma minScheme`. The parametric sorry in `truthLemma` is the single
deferred completeness obligation for task 317.

If `b` is an open saturated branch, then for every signed formula on `b`, the extracted
model (`intExtractValuation b`, `minBranchBotForces b`) satisfies positive formulas and
falsifies negative formulas. -/
lemma minTruthLemma (b : IBranch Atom)
    (hopen : isMinimallyClosed b = false)
    (hsat : IBranchSaturation Atom b)
    (φ : Proposition Atom) (w : Nat) :
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) (minBranchBotForces b) w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) (minBranchBotForces b) w φ) := by
  exact truthLemma minScheme b hopen hsat φ w

/-! ## Completeness Theorems -/

/-- An open saturated branch from the minimal tableau yields a Kripke countermodel.

Delegates to `openBranch_countermodel minScheme`. The structural sorries in
`openBranch_countermodel` are deferred to task 317.

If `minimalTableau φ = openBranch b`, then `intExtractValuation b` and `minBranchBotForces b`
define a minimal Kripke model that falsifies `φ` at world 0. -/
lemma minOpenBranch_countermodel {b : IBranch Atom} (φ : Proposition Atom)
    (h : minimalTableau φ = .openBranch b) :
    ¬ IForces (intExtractValuation b) (minBranchBotForces b) 0 φ := by
  exact openBranch_countermodel minScheme φ b h

/-- **Minimal Tableau Completeness**: If `φ` is minimally valid, then the minimal
tableau closes on `φ`.

Delegates to `tableau_complete minScheme`. The remaining sorry bridges `MValid φ` to the
per-branch forcing hypothesis `∀ b, IForces (intExtractValuation b) (minBranchBotForces b) 0 φ`
required by `tableau_complete`; this is the core completeness obligation for task 317. -/
theorem minimalTableau_complete (φ : Proposition Atom)
    (h : MValid φ) : minimalTableau φ = .closed := by
  apply tableau_complete minScheme
  intro _b
  -- Bridge: MValid φ → IForces (intExtractValuation b) (minBranchBotForces b) 0 φ
  -- Requires: upward-closure of intExtractValuation b and minBranchBotForces b (task 317)
  sorry

end Cslib.Logic.PL

end
