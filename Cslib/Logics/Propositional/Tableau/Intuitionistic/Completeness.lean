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
- `intuitionisticTableau_complete`: If `IValid.{_, 0} φ`, then `intuitionisticTableau φ = closed`.
  Sorry-free.

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

This module is now sorry-free. `intTruthLemma` delegates to `truthLemma intScheme`, which is
sorry-free (DP-5 discharged via an explicit `hpers` positive-persistence hypothesis, threaded
through here as `hpers` above). `intuitionisticOpenBranch_countermodel` delegates to
`openBranch_countermodel intScheme`, which is now ALSO sorry-free: the AUGMENTED `augSets`
witness carries `IFimpAccess` and positive persistence simultaneously post-repair, closing the
existential that used to be `Scheme.lean`'s one remaining declaration-level sorry (see that
lemma's docstring for the full disposition). `intuitionisticTableau_complete` (DP-3), which used
to defer its own obligation, now discharges directly from `openBranch_countermodel`'s upward-closure
conjunct via `_huc` -- no laundering, since that conjunct is genuinely proved, not merely assumed.

**DP-3, historical record.** DP-3 used to be open because `openBranch_countermodel`'s
upward-closure conjunct (`Scheme.lean`) was open, with only the AUGMENTED-frame route to it
known-bad (refuted by `CslibTests/BetaSplitRefutation.lean`'s `phiRef1` counterexample: the
pre-repair augmented frame failed upward closure via independent beta-splits at two
augmented-preorder-equivalent worlds joined by a loop-back edge `intFImpReuseWitnessAnc?` never
re-validated once recorded). Re-validating that loop-back containment as the branch grows
(`Expansion.lean`) is what closes the conjunct, giving one frame that carries both `IFimpAccess`
and positive persistence simultaneously -- see `Scheme.lean`'s `openBranch_countermodel`
docstring for the full frame-adequacy table and the three excluded sub-frame constructions.

**Universe pin, now built.** `intuitionisticTableau_complete` is stated at `h : IValid.{_, 0} φ`
so it can apply directly at the `Nat`-frame countermodel here, the same way
`Minimal/Completeness.lean`'s `minimalTableau_complete` pins `MValid.{_, 0}` for DP-4. This
module's own theorem stays pinned; `Intuitionistic/DecisionProcedure.lean`'s
`ivalid_descend` / `ivalid_universe_invariant` (mirroring `Minimal/DecisionProcedure.lean`'s
`mvalid_descend` / `mvalid_universe_invariant`) let the `Decidable`/biconditional instances built
on top of it keep their original, unpinned public statement.

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
positive-persistence hypothesis taken above and threaded through). This module and
`openBranch_countermodel` (`Scheme.lean`) are both sorry-free; no completeness obligation is
deferred anywhere in this dependency chain.

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

Delegates to `openBranch_countermodel intScheme`, which is sorry-free (see `Scheme.lean`'s
docstring for the AUGMENTED-frame proof this lemma inherits).

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

**Universe pin applied.** `intuitionisticTableau_complete` is now stated at `IValid.{_, 0} φ`,
mirroring the pin `Minimal/Completeness.lean`'s `minimalTableau_complete` already carries for
`MValid`/DP-4: `IValid.{u, v}` quantifies `World : Type v` while the countermodel frame here is
built from `Nat : Type 0`, so the theorem's own `h` must be pinned to `v := 0` before
`@h Nat (intAccessPreorder edges) (intExtractValuation _b) _huc 0` type-checks (it now does --
verified by `lake build`). An earlier version of this docstring recorded that the unpinned call
does NOT type-check; that diagnosis stands for the unpinned `IValid φ` shape, and is exactly why
the pin was added here rather than attempted against the old signature.
`Intuitionistic/DecisionProcedure.lean` supplies the `ivalid_descend` / `ivalid_universe_invariant`
bridge (mirroring `mvalid_descend` / `mvalid_universe_invariant`) that lets callers of the
`Decidable`/biconditional instances built on top of this theorem keep an unpinned, universe-generic
public statement despite this theorem's own pin.

**DP-3, now sorry-free.** `openBranch_countermodel`'s upward-closure conjunct (`Scheme.lean`) is
discharged (the AUGMENTED `augSets` witness carries positive persistence post-repair, see that
lemma's docstring), so `_huc` genuinely discharges the goal here rather than laundering an open
obligation through this file -- the prohibition this docstring used to record no longer applies.
`IValid` takes no separate `bot_forces` argument (it is fixed to `fun _ => False`), so `_hbuc` is
simply unused: `intScheme.modelBot` is defeq to `fun _ _ => False`, matching `IValid`'s fixed
`bot_forces` on the nose, with no `modelBot_uc`-style bridge needed on this side. -/
theorem intuitionisticTableau_complete (φ : Proposition Atom)
    (h : IValid.{_, 0} φ) : intuitionisticTableau φ = .closed := by
  apply tableau_complete intScheme
  intro edges _b _huc _hbuc
  exact @h Nat (intAccessPreorder edges) (intExtractValuation _b) _huc 0

end Cslib.Logic.PL

end
