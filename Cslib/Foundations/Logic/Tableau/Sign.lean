/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

/-! # Tableau Sign Type

This module provides the unified two-valued sign type for analytic tableau calculi.

A sign indicates the "truth status" asserted for a formula in a tableau branch.
Positive (T) means the formula is asserted true; negative (F) means it is asserted false.
Signed formulas are the atomic units from which tableau branches are built.

This type unifies the `PropSign` from `Cslib.Foundations.Logic.PropositionalTableau` and the
`Sign` used in the bimodal tableau, both of which are structurally identical two-element types.
This module supersedes both with a single canonical definition.

## Main Definitions

- `Sign`: The two-element sign type with `pos` and `neg` constructors.
- `Sign.flip`: Involution swapping positive and negative signs.
- `Sign.isPos`, `Sign.isNeg`: Boolean predicates for sign testing.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-! ## Sign -/

/-- The two-valued sign used in signed tableau formulas.

A positive sign (T) asserts that the formula holds in the model being constructed;
a negative sign (F) asserts that it fails. Together with a formula and a label, a sign
forms a `SignedFormula`. -/
inductive Sign : Type where
  /-- Positive sign: the formula is asserted true (T). -/
  | pos : Sign
  /-- Negative sign: the formula is asserted false (F). -/
  | neg : Sign
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

namespace Sign

/-- Swap a sign: `pos` becomes `neg` and vice versa.

This operation is its own inverse (`flip_flip`). -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos

/-- Flipping a positive sign gives a negative sign. -/
@[simp]
lemma flip_pos : flip pos = neg := rfl

/-- Flipping a negative sign gives a positive sign. -/
@[simp]
lemma flip_neg : flip neg = pos := rfl

/-- Flipping a sign twice returns to the original. -/
@[simp]
lemma flip_flip (s : Sign) : flip (flip s) = s := by
  cases s <;> rfl

/-- `true` when the sign is positive. -/
def isPos : Sign → Bool
  | pos => true
  | neg => false

/-- `true` when the sign is negative. -/
def isNeg : Sign → Bool
  | pos => false
  | neg => true

/-- `isPos` and `isNeg` are complementary. -/
@[simp]
lemma isNeg_eq_not_isPos (s : Sign) : s.isNeg = !s.isPos := by
  cases s <;> rfl

end Sign

/-- `Sign` satisfies reflexivity for `BEq`: every sign is `BEq`-equal to itself.

This instance follows the bimodal tableau pattern where `ReflBEq` is registered
explicitly to enable `BEq`-based lookup in hash maps. -/
instance : ReflBEq Sign where
  rfl := fun {s} => by cases s <;> decide

/-- `Sign`'s `BEq` instance is lawful: `BEq` agrees with propositional equality. -/
instance : LawfulBEq Sign where
  eq_of_beq {a b} h := by
    cases a <;> cases b
    · rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rfl
  rfl := by intro s; cases s <;> decide

end Cslib.Logic.Tableau

end
