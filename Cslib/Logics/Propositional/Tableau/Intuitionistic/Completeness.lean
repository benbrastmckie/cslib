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

`intTruthLemma` delegates to `truthLemma intScheme`, which is now sorry-free (DP-5 discharged
via an explicit `hpers` positive-persistence hypothesis, threaded through here as `hpers`
above). `intuitionisticOpenBranch_countermodel` delegates to `openBranch_countermodel
intScheme`, which still carries the deferred sorry in `Scheme.lean` (the existential's whole
statement, genuinely open — see that lemma's docstring). The remaining sorry in
`intuitionisticTableau_complete` (DP-3) bridges `IValid φ` to the per-branch forcing hypothesis
required by `tableau_complete intScheme`.

**DP-3 is open — augmented-frame route known-bad, admissible edge space characterised**, not
refuted. It consumes `openBranch_countermodel`'s upward-closure conjunct (`Scheme.lean`); see
that conjunct's docstring for the full disposition: the admissible `edges` are exactly the
subsets of the atom-inclusion preorder `⊑`, none of which need the algorithm's own edge list,
and a pruned witness (computed against the real `intuitionisticTableau`) satisfies both
conjuncts for `phiRef1 := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr`. What IS
machine-verified (`CslibTests/BetaSplitRefutation.lean`, `lake env lean` clean, zero sorries,
`branchesAgree = true`) is that the AUGMENTED `intAccessPreorder edges` frame fails upward
closure at `phiRef1` via independent beta-splits at two augmented-preorder-equivalent worlds
joined by a loop-back edge that `intFImpReuseWitnessAnc?` never re-validates once recorded
(`Expansion.lean`) — a bad witness choice, not a refutation of the conjunct DP-3 consumes. The
general `∀ φ` form of that conjunct remains unproved (the maximal `⊑` frame is not a uniform
witness), so DP-3's remaining obligation is genuinely open, not a small residual.

**Universe pin recorded, not yet built.** Closing DP-3 (once the conjunct above is available)
will also need `h : IValid φ` pinned to `IValid.{_, 0} φ` before it can apply at the `Nat`-frame
countermodel here, the same way `Minimal/DecisionProcedure.lean`'s `mvalid_universe_invariant`
pins `MValid` for DP-4 -- see `intuitionisticTableau_complete`'s docstring below for the
machine-verified detail.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Truth Lemma -/

/-- The truth lemma for the intuitionistic tableau.

Delegates to `truthLemma intScheme`, which is sorry-free (DP-5 discharged via the `hpers`
positive-persistence hypothesis taken above and threaded through). The single deferred
completeness obligation now lives in `openBranch_countermodel` (`Scheme.lean`), not here.

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
    (hpers : ∀ (χ : Proposition Atom) (x y : Nat), isAccessible edges x y = true →
      (⟨.pos, χ, x⟩ : ISF Atom) ∈ b → (⟨.pos, χ, y⟩ : ISF Atom) ∈ b)
    (φ : Proposition Atom) (w : Nat) :
    letI : Preorder Nat := intAccessPreorder edges
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) intBotForces w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) intBotForces w φ) := by
  exact truthLemma intScheme b edges hopen hsat hfimp hpers φ w

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
      (∀ {w w' : Nat}, @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intBotForces w → intBotForces w') ∧
      ¬ @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) intBotForces 0 φ
      := by
  exact openBranch_countermodel intScheme φ b h

/-! ## Main Completeness Theorem -/

/-- **Intuitionistic Tableau Completeness**: If `φ` is intuitionistically valid,
then the intuitionistic tableau closes on `φ`.

Delegates to `tableau_complete intScheme`. **Statement-shape fix**: `tableau_complete`'s
`hvalid` premise now accepts the upward-closure of `intExtractValuation b` (along
`intAccessPreorder edges`) AND the upward-closure of `intBotForces` as explicit hypotheses
(`_huc`, `_hbuc` below), both supplied by `openBranch_countermodel` -- this replaces the OLD,
machine-verified-defective shape (`hvalid` unconditionally quantified over an arbitrary,
unconstrained `(edges, b)` pair, refuted by `CslibTests/HvalidShapeRefutation.lean`:
`IValid (p → (q → p))` holds while the old premise's body is false at a non-upward-closed
witness valuation; the `⊥`-shape analogue is `CslibTests/MvalidBotShapeRefutation.lean`, refuted
for `MValid`/`minScheme` the same way). For `intScheme`, `intBotForces = fun _ => False`, so
`_hbuc` is trivially dischargeable once `_huc` is -- the fix costs nothing extra on the
intuitionistic side.

**Universe pin needed, not yet applied.** With the new shape, `IValid φ` instantiated at
`World := Nat`, `[Preorder Nat] := intAccessPreorder edges`, `val := intExtractValuation b`
would need `IValid.{_, 0} φ`, mirroring the pin `Minimal/DecisionProcedure.lean`'s
`mvalid_universe_invariant` resolves for `MValid`/DP-4: `IValid.{u, v}` quantifies
`World : Type v` while the countermodel frame here is `Nat : Type 0`, so `h`'s own bound
universe parameter cannot be instantiated as stated (`exact h Nat (intExtractValuation _b) _huc
0` does NOT type-check as written -- verified). An earlier version of this docstring claimed
that call would type-check; it does not. Closing DP-3 will need the same `.{_, 0}` pin on `h`'s
type and the same `ULift` transport `mvalid_universe_invariant` already builds for `MValid`, once
someone builds the `IValid` analogue.

The remaining sorry below is **not** the old unfillable shape -- it is deliberately left
deferred. **DP-3 is open — augmented-frame route known-bad, admissible edge space
characterised**, not "pending" any future phase in the old sense, but genuinely unresolved:
`openBranch_countermodel`'s own upward-closure conjunct (`Scheme.lean`) is open, and only the
AUGMENTED-frame route to it is known-bad, refuted by a machine-verified counterexample
(`CslibTests/BetaSplitRefutation.lean`, `phiRef1`). Even setting the universe pin aside,
discharging this site would only launder that still-open conjunct through this file without
being any more honest about it; the obligation stays visibly deferred here (see `Scheme.lean`'s
`openBranch_countermodel` docstring for the full disposition, the admissible-edge-space
characterisation, and the counterexample). The remaining work is a uniform construction of
`edges` from `b` plus a truth lemma over that frame, which -- per that docstring's structural
argument -- is equivalent to proving the tableau procedure complete: genuine open work, not a
small residual, and not attempted here. -/
theorem intuitionisticTableau_complete (φ : Proposition Atom)
    (h : IValid φ) : intuitionisticTableau φ = .closed := by
  apply tableau_complete intScheme
  intro edges _b _huc _hbuc
  -- DP-3 -- open, augmented-frame route known-bad. Even setting aside the universe pin the
  -- docstring above records (`h` would need `IValid.{_, 0} φ` to apply at the `Nat`-frame
  -- countermodel), `_huc`/`_hbuc` at this frame do not genuinely discharge the goal: they would
  -- only launder `openBranch_countermodel`'s upward-closure conjunct through this file, and that
  -- conjunct is open, not refuted (see the docstring above). Left `sorry` deliberately -- see the
  -- docstring above for the full disposition.
  sorry

end Cslib.Logic.PL

end
