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
`Scheme.lean`. The remaining sorry in `minimalTableau_complete` (DP-4) bridges `MValid φ` to the
per-branch forcing hypothesis required by `tableau_complete minScheme`.

**DP-4 is PERMANENTLY DEFERRED — unprovable as stated**, not merely unfinished, and is refuted
**independently** of DP-3: the same machine-verified counterexample
(`CslibTests/BetaSplitRefutation.lean`, `phiRef1 := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr`)
reproduces under `isMinimallyClosed` (`reportMin phiRef1 realFuel` yields the identical violation,
and `minBranchesAgree = true` against the real `minimalTableau`). The mechanism is independent
beta-splits at two augmented-preorder-equivalent worlds joined by a loop-back edge that
`intFImpReuseWitnessAnc?` never re-validates once recorded (`Expansion.lean`). DP-4 is therefore
not collateral damage from DP-3's dependency chain; it fails on its own terms under the minimal
calculus's own closure predicate.

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
discharges only the first. **DP-4 is PERMANENTLY DEFERRED — unprovable as stated**, not
"pending" any future phase, and refuted **independently** of DP-3 (see "Notes on sorry" above:
`reportMin phiRef1 realFuel` and `minBranchesAgree = true` against the real `minimalTableau`).
Two obligations would need to be discharged even setting the refutation aside: (1)
`openBranch_countermodel`'s own upward-closure conjunct, which is DISPOSITION UNDECIDED (an open
decision point) in `Scheme.lean`; (2) `minBranchBotForces b`'s own upward-closure (a SEPARATE
fact, at the `⊥` formula shape), not established. Neither is pursued: the underlying statement
this sorry needs is refuted, so this is a terminal deferral, not an unfinished step. -/
theorem minimalTableau_complete (φ : Proposition Atom)
    (h : MValid φ) : minimalTableau φ = .closed := by
  apply tableau_complete minScheme
  intro edges _b _huc
  -- DP-4 -- PERMANENTLY DEFERRED, unprovable as stated, refuted INDEPENDENTLY of DP-3 under
  -- `isMinimallyClosed` (`CslibTests/BetaSplitRefutation.lean`'s `reportMin phiRef1 realFuel`,
  -- `minBranchesAgree = true` against the real `minimalTableau`). `exact h Nat
  -- (intExtractValuation _b) (minBranchBotForces _b) _huc hbotuc 0` (for the appropriate
  -- `hbotuc`) would type-check once both upward-closure obligations named in the docstring above
  -- are discharged, but the underlying statement is refuted, so this is left `sorry`
  -- deliberately. Not a route failure; no follow-up is scheduled.
  sorry

end Cslib.Logic.PL

end
