/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.Sign

/-! # Signed Formula Type

This module defines `SignedFormula F L`, the fundamental unit of analytic tableau calculi.
A signed formula combines a `Sign`, a formula of type `F`, and a label of type `L`.

The label type `L` enables label-generic tableau algorithms:
- Classical logic: `L = Unit` (no labeling; all formulas share one implicit world)
- Intuitionistic/minimal logic: `L = Nat` (labels index worlds in a model)
- Modal logic: `L = WorldIndex` (labels index accessibility worlds)

## Main Definitions

- `SignedFormula F L`: A triple of sign, formula, and label.
- `SignedFormula.pos`, `SignedFormula.neg`: Smart constructors.
- `SignedFormula.flip`: Flip the sign, preserving formula and label.
- `SignedFormula.withLabel`: Relabel a signed formula.
- `SignedFormula.isPos`, `SignedFormula.isNeg`: Boolean sign predicates.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-! ## SignedFormula -/

/-- A signed formula: a formula of type `F` paired with a `Sign` and a label of type `L`.

The label enables world-indexed tableau calculi (e.g., intuitionistic, modal). For classical
propositional tableau, use `L = Unit` and pass `()` as the label.

When `F` and `L` both have `DecidableEq`, `BEq`, and `Hashable` instances,
`SignedFormula F L` inherits them via `deriving`. -/
structure SignedFormula (F : Type*) (L : Type*) where
  /-- The sign of this signed formula: positive (T) or negative (F). -/
  sign : Sign
  /-- The formula component. -/
  formula : F
  /-- The label (world index, prefix, etc.) associated with this formula. -/
  label : L
  deriving DecidableEq, BEq, Hashable

namespace SignedFormula

/-- Construct a positively signed formula with the given formula and label. -/
def pos (φ : F) (l : L) : SignedFormula F L := ⟨.pos, φ, l⟩

/-- Construct a negatively signed formula with the given formula and label. -/
def neg (φ : F) (l : L) : SignedFormula F L := ⟨.neg, φ, l⟩

/-- Flip the sign of a signed formula, preserving its formula and label.

Positive becomes negative and vice versa. -/
def flip (sf : SignedFormula F L) : SignedFormula F L :=
  { sf with sign := sf.sign.flip }

/-- Flipping a signed formula twice returns the original. -/
@[simp]
lemma flip_flip (sf : SignedFormula F L) : sf.flip.flip = sf := by
  simp [flip]

/-- Replace the label on a signed formula, preserving sign and formula. -/
def withLabel (sf : SignedFormula F L) (l' : L) : SignedFormula F L :=
  { sf with label := l' }

/-- `true` when the signed formula has a positive sign. -/
def isPos (sf : SignedFormula F L) : Bool := sf.sign.isPos

/-- `true` when the signed formula has a negative sign. -/
def isNeg (sf : SignedFormula F L) : Bool := sf.sign.isNeg

/-- `isPos` and `isNeg` are complementary. -/
@[simp]
lemma isNeg_eq_not_isPos (sf : SignedFormula F L) : sf.isNeg = !sf.isPos := by
  simp [isPos, isNeg, Sign.isNeg_eq_not_isPos]

end SignedFormula

end Cslib.Logic.Tableau

end
