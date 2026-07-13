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
`Scheme.lean`. The remaining sorry in `intuitionisticTableau_complete` bridges `IValid φ` to
the per-branch forcing hypothesis required by `tableau_complete intScheme`; this bridge is
part of the completeness obligations handed to task 317.

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
deferred completeness obligation for task 317.

**Route (a) frame (task 317 phase 1)**: takes `edges`/`hfimp` and installs
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
of `b`) are deferred to task 317.

**Route (a) frame (task 317 phase 1/3)**: the conclusion existentially exposes the `edges`
the `intAccessPreorder` countermodel frame is installed over (Postmortem-5 revision: this
internal corollary has no live consumer beyond docstrings, so exposing `edges` here does not
touch the stable public contract).

If `intuitionisticTableau φ = openBranch b`, then `intExtractValuation b` falsifies `φ`
at world 0 in the intuitionistic Kripke model with worlds ordered by edge-accessibility. -/
lemma intuitionisticOpenBranch_countermodel {b : IBranch Atom} (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .openBranch b) :
    ∃ edges : IEdges,
      ¬ @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) intBotForces 0 φ
      := by
  exact openBranch_countermodel intScheme φ b h

/-! ## Main Completeness Theorem -/

/-- **Intuitionistic Tableau Completeness**: If `φ` is intuitionistically valid,
then the intuitionistic tableau closes on `φ`.

Delegates to `tableau_complete intScheme`. The remaining sorry bridges `IValid φ` to the
per-`edges` forcing hypothesis `∀ edges b, @IForces Atom Nat (intAccessPreorder edges)
(intExtractValuation b) (fun _ => False) 0 φ` required by `tableau_complete` (task 317 phase 4,
Route (a): `edges` is only discovered inside `tableau_complete`'s own proof, from the
open-branch case, so the bridge must accept it as an argument rather than fix one ambient
frame); this bridge is the core completeness obligation for task 317.

Proof strategy: `tableau_complete intScheme φ` takes `∀ edges b, IForces (intExtractValuation
b) (intScheme.modelBot b) 0 φ` at the `intAccessPreorder edges` frame. For the intuitionistic
scheme, `modelBot b = fun _ => False`. This follows from `IValid φ` by instantiating at
`World = Nat`, `[Preorder Nat] := intAccessPreorder edges`, `val = intExtractValuation b`, with
the upward-closure of `intExtractValuation b` ALONG THAT FRAME — the deferred-monotonicity
obligation folded into fuel-sufficiency (task 317 phase 9/10), not yet available. -/
theorem intuitionisticTableau_complete (φ : Proposition Atom)
    (h : IValid φ) : intuitionisticTableau φ = .closed := by
  apply tableau_complete intScheme
  intro edges _b
  -- Task 317 phase 4 (deferred-monotonicity bridge): `h` instantiated at
  -- `intAccessPreorder edges` needs `intExtractValuation _b`'s upward-closure along that
  -- frame, which is not available until the fuel-sufficiency fixpoint (phase 9/10).
  -- The bridge SHAPE (accepting `edges`) is now Route (a)-correct; only this monotonicity
  -- premise remains deferred.
  sorry

end Cslib.Logic.PL

end
