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

`minTruthLemma` delegates to `truthLemma minScheme`, which is now sorry-free (DP-5 discharged
via an explicit `hpers` positive-persistence hypothesis, threaded through here as `hpers`
above). `minOpenBranch_countermodel` delegates to `openBranch_countermodel minScheme`, which
still carries the deferred sorry in `Scheme.lean` (the existential's whole statement, genuinely
open — see that lemma's docstring). The remaining sorry in `minimalTableau_complete` (DP-4)
bridges `MValid φ` to the per-branch forcing hypothesis required by `tableau_complete
minScheme`.

**DP-4 is open — augmented-frame route known-bad, admissible edge space characterised**, not
refuted, and the earlier claim that it is refuted **independently** of DP-3 is itself retracted:
under `isMinimallyClosed`, the pruned edge set `edges = [(1, 0)]` (computed against the real
`minimalTableau` for `phiRef1 := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr`) discharges BOTH
upward-closure obligations `MValid` needs here — the valuation one and the `⊥` one — and still
falsifies `phiRef1` at world 0 (`minBranchesAgree = true` against the real `minimalTableau`).
That refutes the independent-refutation claim, not the conjunct. What IS machine-verified
(`CslibTests/BetaSplitRefutation.lean`, `reportMin phiRef1 realFuel`) is that the same
augmented-frame mechanism as DP-3 — independent beta-splits at two augmented-preorder-equivalent
worlds joined by a loop-back edge that `intFImpReuseWitnessAnc?` never re-validates once
recorded (`Expansion.lean`) — also fails upward closure under `isMinimallyClosed`. So DP-4 is
NOT collateral damage from DP-3's dependency chain in the old refuted-consequence sense; it
shares DP-3's bad witness choice, and its own upward-closure obligation (`minBranchBotForces b`,
below) is a genuinely separate, still-open residual.

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
positive-persistence hypothesis taken above and threaded through). The single deferred
completeness obligation now lives in `openBranch_countermodel` (`Scheme.lean`), not here.

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
discharges only the first. **DP-4 is open — augmented-frame route known-bad**, not "pending" any
future phase in the old sense, and the earlier claim that it is refuted **independently** of
DP-3 is retracted (see "Notes on sorry" above: `[(1, 0)]` discharges both upward-closure
obligations under `isMinimallyClosed` and still falsifies `phiRef1`, so the independent
refutation does not hold). Two obligations remain genuinely open: (1)
`openBranch_countermodel`'s own upward-closure conjunct in `Scheme.lean`, which is open with the
augmented-frame route known-bad (see that docstring); (2) `minBranchBotForces b`'s own
upward-closure (a SEPARATE fact, at the `⊥` formula shape) — a **named residual**: it holds at
the `[(1, 0)]` witness (computed) but is not established in general. Neither is pursued here. -/
theorem minimalTableau_complete (φ : Proposition Atom)
    (h : MValid φ) : minimalTableau φ = .closed := by
  apply tableau_complete minScheme
  intro edges _b _huc
  -- DP-4 -- open, augmented-frame route known-bad, sharing DP-3's bad witness choice under
  -- `isMinimallyClosed` (`CslibTests/BetaSplitRefutation.lean`'s `reportMin phiRef1 realFuel`,
  -- `minBranchesAgree = true` against the real `minimalTableau`). `exact h Nat
  -- (intExtractValuation _b) (minBranchBotForces _b) _huc hbotuc 0` (for the appropriate
  -- `hbotuc`) would type-check once both upward-closure obligations named in the docstring above
  -- are discharged; both are open, so this is left `sorry` deliberately.
  sorry

end Cslib.Logic.PL

end
