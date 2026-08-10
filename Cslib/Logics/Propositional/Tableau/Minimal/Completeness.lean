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
- `minimalTableau_complete`: If `MValid.{_, 0} φ`, then `minimalTableau φ = closed`. Sorry-free.

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

This module is sorry-free, and so is everything it depends on. `minTruthLemma` delegates to
`truthLemma minScheme`, which is sorry-free (DP-5 discharged via an explicit `hpers`
positive-persistence hypothesis, threaded through here as `hpers` above).
`minOpenBranch_countermodel` delegates to `openBranch_countermodel minScheme`, which is now ALSO
sorry-free (the AUGMENTED `augSets` witness carries `IFimpAccess` and positive persistence
simultaneously post-repair, closing the existential that used to be `Scheme.lean`'s one remaining
declaration-level sorry -- see that lemma's docstring for the full disposition).

`minimalTableau_complete` (DP-4) is **sorry-free**. The old two-obligation framing (a
valuation upward-closure premise plus a separately-tracked `⊥`-shape upward-closure premise) is
retired: `openBranch_countermodel`'s existential now supplies BOTH conjuncts directly, so DP-4
instantiates `MValid.{_, 0} φ` with everything it needs in one call. Mirrors DP-3
(`intuitionisticTableau_complete` in `Intuitionistic/Completeness.lean`), which discharges the
same way via `openBranch_countermodel intScheme`. The `⊥`-shape conjunct costs nothing beyond the
valuation one: both are the SAME `χ`-general raw-edge persistence fact
(`openBranch_rawEdges_upward_closed`/`openBranch_rawEdges_both_upward_closed` in `Scheme.lean`),
instantiated at `χ := .atom p` and `χ := HasBot.bot` respectively.

**Why the old, two-premise `hvalid` shape could not have closed DP-4 as previously stated.**
`CslibTests/MvalidBotShapeRefutation.lean` machine-checks that `tableau_complete`'s `hvalid`
body, quantified over an ARBITRARY unconstrained `(edges, b)` pair with only the valuation
upward-closure premise supplied, is refuted: `φ = ⊥ → ((⊥ → ⊥) → ⊥)` is `MValid`, yet the
`hvalid` body is false at an atom-free witness whose `minBranchBotForces` is not upward closed.
Adding the matching `bot_forces`-upward-closure premise to `hvalid` (and the matching conjunct
to `openBranch_countermodel`) is what makes the goal provable at all — this is the SAME kind of
statement-shape defect `CslibTests/HvalidShapeRefutation.lean` documents for the valuation
conjunct, one conjunct later.

**Universe pin.** `minimalTableau_complete` is stated at `MValid.{_, 0} φ` because the
countermodel frame here is built from `Nat : Type 0`, while `MValid.{u, v}` quantifies
`World : Type v` in general. `Minimal/DecisionProcedure.lean`'s `mvalid_universe_invariant`
proves this pin costs nothing (`MValid` is universe-invariant), so
`instDecidableDerivableMinPropAxiom` there keeps its original, universe-unpinned public
statement despite `minimalTableau_decides`/`instDecidableMValid` now being pinned to `Type 0`
alongside this theorem.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Truth Lemma -/

/-- The truth lemma for the minimal tableau.

Delegates to `truthLemma minScheme`, which is sorry-free (DP-5 discharged via the `hpers`
positive-persistence hypothesis taken above and threaded through). This module and
`openBranch_countermodel` (`Scheme.lean`) are both sorry-free; no completeness obligation is
deferred anywhere in this dependency chain.

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
    (hpers : ∀ (χ : Proposition Atom) (x y : Nat), isAccessible edges x y = true →
      (⟨.pos, χ, x⟩ : ISF Atom) ∈ b → (⟨.pos, χ, y⟩ : ISF Atom) ∈ b)
    (φ : Proposition Atom) (w : Nat) :
    letI : Preorder Nat := intAccessPreorder edges
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) (minBranchBotForces b) w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) (minBranchBotForces b) w φ) := by
  exact truthLemma minScheme b edges hopen hsat hfimp hpers φ w

/-! ## Completeness Theorems -/

/-- An open saturated branch from the minimal tableau yields a Kripke countermodel.

Delegates to `openBranch_countermodel minScheme`, which is sorry-free (see `Scheme.lean`'s
docstring for the AUGMENTED-frame proof this lemma inherits).

**Route (a) frame**: mirrors
`Intuitionistic.Completeness.intuitionisticOpenBranch_countermodel`'s existential exposure of
`edges`.

**Statement-shape fix**: the conclusion carries BOTH of `MValid`'s upward-closure conjuncts --
`intExtractValuation b`'s and `minBranchBotForces b`'s -- along `intAccessPreorder edges` (see
`Scheme.lean`'s `openBranch_countermodel` docstring). `minimalTableau_complete` below needs
nothing further from this lemma: both conjuncts arrive here together.

If `minimalTableau φ = openBranch b`, then `intExtractValuation b` and `minBranchBotForces b`
define a minimal Kripke model that falsifies `φ` at world 0 (over edge-accessibility). -/
lemma minOpenBranch_countermodel {b : IBranch Atom} (φ : Proposition Atom)
    (h : minimalTableau φ = .openBranch b) :
    ∃ edges : IEdges,
      (∀ {w w' : Nat} (p : Atom), @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p) ∧
      (∀ {w w' : Nat}, @LE.le Nat (intAccessPreorder edges).toLE w w' →
        minBranchBotForces b w → minBranchBotForces b w') ∧
      ¬ @IForces Atom Nat (intAccessPreorder edges)
        (intExtractValuation b) (minBranchBotForces b) 0 φ := by
  exact openBranch_countermodel minScheme φ b h

/-- **Minimal Tableau Completeness**: If `φ` is minimally valid (at universe `0`), then the
minimal tableau closes on `φ`. Sorry-free.

Delegates to `tableau_complete minScheme`. **Statement-shape fix**: `tableau_complete`'s
`hvalid` premise now accepts BOTH of `MValid`'s upward-closure conjuncts as explicit hypotheses
(`_huc` for the valuation, `_hbuc` for `minBranchBotForces`; mirrors
`intuitionisticTableau_complete`'s fix; see `Scheme.lean`'s `openBranch_countermodel` and
`tableau_complete` docstrings for the machine-verified defect this replaces, and
`CslibTests/MvalidBotShapeRefutation.lean` for the refutation of the old, `⊥`-conjunct-missing
shape).

This site now rests on exactly one obligation, the same one DP-3 rests on:
`openBranch_countermodel`'s own existential in `Scheme.lean` (`minOpenBranch_countermodel`'s
delegate above), which supplies `edges`, `_huc`, and `_hbuc` together. With both conjuncts in
hand, `MValid.{_, 0} φ` instantiates directly at `World := Nat`,
`[Preorder Nat] := intAccessPreorder edges`, `val := intExtractValuation _b`,
`bot_forces := minBranchBotForces _b` -- no separate `⊥`-shape residual remains. -/
theorem minimalTableau_complete (φ : Proposition Atom)
    (h : MValid.{_, 0} φ) : minimalTableau φ = .closed := by
  apply tableau_complete minScheme
  intro edges _b _huc _hbuc
  exact @h Nat (intAccessPreorder edges) (intExtractValuation _b)
    (minBranchBotForces _b) _huc _hbuc 0

end Cslib.Logic.PL

end
