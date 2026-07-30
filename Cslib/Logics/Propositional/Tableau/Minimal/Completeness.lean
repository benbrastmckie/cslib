/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Minimal.Soundness
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme

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
deferred completeness obligations.

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
deferred completeness obligation.

**Route (a) frame**: takes `edges`/`hfimp` and installs
`intAccessPreorder edges` as the countermodel frame via `letI` (mirrors
`Intuitionistic.Completeness.intTruthLemma`).

If `b` is an open saturated branch, then for every signed formula on `b`, the extracted
model (`intExtractValuation b`, `minBranchBotForces b`) satisfies positive formulas and
falsifies negative formulas. -/
lemma minTruthLemma (b : IBranch Atom) (edges : IEdges)
    (hopen : isMinimallyClosed b = false)
    (hsat : IBranchSaturation Atom b)
    (hfimp : IFimpAccess edges b)
    (φ : Proposition Atom) (w : Nat) :
    letI : Preorder Nat := intAccessPreorder edges
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) (minBranchBotForces b) w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) (minBranchBotForces b) w φ) := by
  exact truthLemma minScheme b edges hopen hsat hfimp φ w

/-! ## Completeness Theorems -/

/-- An open saturated branch from the minimal tableau yields a Kripke countermodel.

Delegates to `openBranch_countermodel minScheme`. The structural sorries in
`openBranch_countermodel` remain deferred.

**Route (a) frame**: mirrors
`Intuitionistic.Completeness.intuitionisticOpenBranch_countermodel`'s existential exposure of
`edges`.

**Statement-shape fix**: the conclusion also carries the upward-closure of
`intExtractValuation b` along `intAccessPreorder edges` (see `Scheme.lean`'s
`openBranch_countermodel` docstring). This is only ONE of `MValid`'s two upward-closure
premises -- `minimalTableau_complete` below still needs `minBranchBotForces b`'s upward-closure
separately.

If `minimalTableau φ = openBranch b`, then `intExtractValuation b` and `minBranchBotForces b`
define a minimal Kripke model that falsifies `φ` at world 0 (over edge-accessibility). -/
lemma minOpenBranch_countermodel {b : IBranch Atom} (φ : Proposition Atom)
    (h : minimalTableau φ = .openBranch b) :
    ∃ edges : IEdges,
      (∀ {w w' : Nat} (p : Atom), @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p) ∧
      ¬ @IForces Atom Nat (intAccessPreorder edges)
        (intExtractValuation b) (minBranchBotForces b) 0 φ := by
  exact openBranch_countermodel minScheme φ b h

/-- **Minimal Tableau Completeness**: If `φ` is minimally valid, then the minimal
tableau closes on `φ`.

Delegates to `tableau_complete minScheme`. **Statement-shape fix**: `tableau_complete`'s
`hvalid` premise now accepts `intExtractValuation b`'s upward-closure as an explicit hypothesis
(mirrors `intuitionisticTableau_complete`'s fix; see `Scheme.lean`'s `openBranch_countermodel`
and `tableau_complete` docstrings for the machine-verified defect this replaces).

`MValid φ` needs TWO upward-closure premises (val AND `botForces`); the supplied `_huc`
discharges only the first. The remaining sorry is deliberately left deferred, re-annotated to
point at the two ACTUAL remaining obligations: (1) `openBranch_countermodel`'s own
upward-closure conjunct is itself still `sorry` in `Scheme.lean`, pending the plan's Phases
7-11; (2) `minBranchBotForces b`'s own upward-closure (a SEPARATE fact, at the `⊥` formula
shape) is not yet established either -- the plan's Phase 13 derives both as one-line
specializations of a single generic persistence corollary once Phases 7-11 land. -/
theorem minimalTableau_complete (φ : Proposition Atom)
    (h : MValid φ) : minimalTableau φ = .closed := by
  apply tableau_complete minScheme
  intro edges _b _huc
  -- Once both (1) `openBranch_countermodel`'s upward-closure conjunct and (2)
  -- `minBranchBotForces b`'s upward-closure are established (plan Phases 7-11, 13), this goal
  -- closes via `exact h Nat (intExtractValuation _b) (minBranchBotForces _b) _huc hbotuc 0`
  -- for the appropriate `hbotuc`. Left `sorry` deliberately for now -- see the docstring above.
  sorry

end Cslib.Logic.PL

end
