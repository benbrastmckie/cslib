/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme

/-! # Intuitionistic Tableau Completeness

This module proves completeness of the intuitionistic propositional tableau: if `φ` is
intuitionistically valid, then the tableau closes on `φ`.

## Main Results

- `intExtractValuation`: Defined in `Intuitionistic.Soundness`; see that module.
- `intTruthLemma`: Delegates to the parametric `truthLemma intScheme` from `Scheme.lean`.
- `intuitionisticTableau_complete`: If `IValid φ`, then `intuitionisticTableau φ = closed`.

## Design

This module now delegates to the parametric implementations in `Intuitionistic.Scheme`.
The declarations `intTruthLemma`, `intuitionisticOpenBranch_countermodel`, and
`intuitionisticTableau_complete` are thin corollaries of their parametric counterparts
`truthLemma intScheme`, `openBranch_countermodel intScheme`, and `tableau_complete intScheme`.

## Countermodel Construction

From an open saturated branch `b`, the countermodel is:
- **Worlds**: Natural numbers (world labels on `b`) with ≤ ordering.
- **Valuation**: `intExtractValuation b` (defined in `Intuitionistic.Soundness`).
- **botForces**: Always `False` (`intScheme.modelBot b = fun _ => False`).
- **Accessibility**: `w ≤ w'` as natural numbers.

## Notes on sorry

`intTruthLemma` and `intuitionisticOpenBranch_countermodel` delegate to `truthLemma intScheme`
and `openBranch_countermodel intScheme` respectively, which carry the deferred sorries in
`Scheme.lean`. The remaining sorry in `intuitionisticTableau_complete` (DP-3) bridges `IValid φ`
to the per-branch forcing hypothesis required by `tableau_complete intScheme`.

**DP-3 is PERMANENTLY DEFERRED — unprovable as stated**, not merely unfinished. It consumes
`openBranch_countermodel`'s upward-closure conjunct (`Scheme.lean`), whose disposition is an
open decision point (see that conjunct's docstring): upward closure of `intExtractValuation b`
along the augmented `intAccessPreorder edges` frame is machine-verified to FAIL at
`phiRef1 := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr` (`CslibTests/BetaSplitRefutation.lean`,
`lake env lean` clean, zero sorries, `branchesAgree = true` against the real
`intuitionisticTableau`). The mechanism is independent beta-splits at two
augmented-preorder-equivalent worlds joined by a loop-back edge that `intFImpReuseWitnessAnc?`
never re-validates once recorded (`Expansion.lean`). DP-3 therefore consumes a premise whose
underlying content is refuted at this witness — it is not a route failure, and is not scheduled
for any follow-up.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Truth Lemma -/

/-- The truth lemma for the intuitionistic tableau.

Delegates to `truthLemma intScheme`. The parametric sorry in `truthLemma` is the single
deferred completeness obligation.

**Route (a) frame**: takes `edges`/`hfimp` and installs
`intAccessPreorder edges` as the countermodel frame via `letI` (Postmortem-5 revision — this
internal corollary MAY expose `edges`; the stable public contract is untouched, see
`intuitionisticTableau_complete` below).

If `b` is an open saturated branch, then the extracted valuation `intExtractValuation b`
satisfies every T(φ) on `b` and falsifies every F(φ) on `b`. -/
lemma intTruthLemma (b : IBranch Atom) (edges : IEdges)
    (hopen : isIntuitionisticallyClosed b = false)
    (hsat : IBranchSaturation Atom b)
    (hfimp : IFimpAccess edges b)
    (φ : Proposition Atom) (w : Nat) :
    letI : Preorder Nat := intAccessPreorder edges
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) intBotForces w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) intBotForces w φ) := by
  exact truthLemma intScheme b edges hopen hsat hfimp φ w

/-- An open saturated branch from the intuitionistic tableau yields a Kripke countermodel.

Delegates to `openBranch_countermodel intScheme`. The structural sorries in
`openBranch_countermodel` (relating `intExpandBranches ... = .openBranch b` to properties
of `b`) are deferred.

**Route (a) frame**: the conclusion existentially exposes the `edges`
the `intAccessPreorder` countermodel frame is installed over (Postmortem-5 revision: this
internal corollary has no live consumer beyond docstrings, so exposing `edges` here does not
touch the stable public contract).

**Statement-shape fix**: the conclusion also carries the upward-closure of
`intExtractValuation b` along `intAccessPreorder edges` (see `openBranch_countermodel`'s
docstring in `Scheme.lean` for why this replaces the old, machine-verified-defective
`hvalid` premise shape).

If `intuitionisticTableau φ = openBranch b`, then `intExtractValuation b` falsifies `φ`
at world 0 in the intuitionistic Kripke model with worlds ordered by edge-accessibility. -/
lemma intuitionisticOpenBranch_countermodel {b : IBranch Atom} (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .openBranch b) :
    ∃ edges : IEdges,
      (∀ {w w' : Nat} (p : Atom), @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p) ∧
      ¬ @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) intBotForces 0 φ
      := by
  exact openBranch_countermodel intScheme φ b h

/-! ## Main Completeness Theorem -/

/-- **Intuitionistic Tableau Completeness**: If `φ` is intuitionistically valid,
then the intuitionistic tableau closes on `φ`.

Delegates to `tableau_complete intScheme`. **Statement-shape fix**: `tableau_complete`'s
`hvalid` premise now accepts the upward-closure of `intExtractValuation b` (along
`intAccessPreorder edges`) as an explicit hypothesis, supplied by `openBranch_countermodel` --
this replaces the OLD, machine-verified-defective shape (`hvalid` unconditionally quantified
over an arbitrary, unconstrained `(edges, b)` pair, refuted by
`CslibTests/HvalidShapeRefutation.lean`: `IValid (p → (q → p))` holds while the old premise's body
is false at a non-upward-closed witness valuation). With the new shape, `IValid φ` instantiates
DIRECTLY: `World := Nat`, `[Preorder Nat] := intAccessPreorder edges`, `val := intExtractValuation
b`, and the supplied upward-closure hypothesis is exactly `IValid`'s own upward-closure premise.

The remaining sorry below is **not** the old unfillable shape -- it is deliberately left
deferred. **DP-3 is PERMANENTLY DEFERRED — unprovable as stated**, not "pending" any future
phase: `openBranch_countermodel`'s own upward-closure conjunct (`Scheme.lean`) is DISPOSITION
UNDECIDED (an open decision point, not a landed fact) and the underlying augmented-frame
positive-formula persistence it would need is REFUTED by a machine-verified counterexample
(`CslibTests/BetaSplitRefutation.lean`, `phiRef1`). Discharging
`IValid φ Nat (intExtractValuation b) huc 0` here would type-check but would only launder a
refuted premise through this file without being any more honest about it; the obligation stays
visibly deferred here (see `Scheme.lean`'s `openBranch_countermodel` docstring for the full
disposition and the counterexample). No follow-up is scheduled: this is a terminal deferral, not
an unfinished step. -/
theorem intuitionisticTableau_complete (φ : Proposition Atom)
    (h : IValid φ) : intuitionisticTableau φ = .closed := by
  apply tableau_complete intScheme
  intro edges _b _huc
  -- DP-3 -- PERMANENTLY DEFERRED, unprovable as stated. `exact h Nat (intExtractValuation _b)
  -- _huc 0` would type-check (Route (a): `_huc` is exactly `IValid`'s upward-closure hypothesis,
  -- instantiated at the augmented frame `intAccessPreorder edges`), but it would consume
  -- `openBranch_countermodel`'s upward-closure conjunct, which is DISPOSITION UNDECIDED and
  -- whose underlying content is refuted at `phiRef1` (`CslibTests/BetaSplitRefutation.lean`,
  -- `branchesAgree = true` against the real `intuitionisticTableau`). Left `sorry` deliberately
  -- -- see the docstring above. Not a route failure; no follow-up is scheduled.
  sorry

end Cslib.Logic.PL

end
