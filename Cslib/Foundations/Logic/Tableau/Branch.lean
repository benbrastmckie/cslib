/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.SignedFormula
public import Cslib.Foundations.Logic.Connectives

/-! # Branch Type

This module defines `Branch F L`, a label-generic type for tableau branches.
A branch is simply a list of signed formulas, with helper operations for the common
patterns arising in tableau algorithms.

## Main Definitions

- `Branch F L`: A list of `SignedFormula F L` values.
- `Branch.empty`: The empty branch.
- `Branch.contains`: Signed formula membership test.
- `Branch.extend`, `Branch.extendMany`: Add signed formulas to a branch.
- `Branch.positives`, `Branch.negatives`: Filter by sign.
- `Branch.hasPosAt`, `Branch.hasNegAt`: Test for a signed formula at a given label.
- `Branch.formulasAt`: All formulas with a given label.
- `Branch.labels`: Collect all distinct labels.
- `Branch.findContradiction`: Find a complementary T(phi)/F(phi) pair at the same label.
- `Branch.hasContradiction`: Boolean wrapper for `findContradiction`.
- `Branch.hasBotPos`: Check for T(bot) at any label (requires `HasBot F`).

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-! ## Branch -/

/-- A tableau branch: a list of signed formulas parameterized over formula type `F`
and label type `L`. -/
abbrev Branch (F : Type*) (L : Type*) := List (SignedFormula F L)

namespace Branch

/-- The empty branch (no signed formulas). -/
def empty : Branch F L := []

/-- Test whether a signed formula is on this branch (using `BEq`). -/
def contains [BEq (SignedFormula F L)] (b : Branch F L) (sf : SignedFormula F L) : Bool :=
  b.any (· == sf)

/-- Add a single signed formula to the front of the branch. -/
def extend (b : Branch F L) (sf : SignedFormula F L) : Branch F L := sf :: b

/-- Add a list of signed formulas to the front of the branch. -/
def extendMany (b : Branch F L) (sfs : List (SignedFormula F L)) : Branch F L := sfs ++ b

/-- All positively signed formulas on the branch. -/
def positives (b : Branch F L) : List (SignedFormula F L) :=
  b.filter (·.isPos)

/-- All negatively signed formulas on the branch. -/
def negatives (b : Branch F L) : List (SignedFormula F L) :=
  b.filter (·.isNeg)

/-- Test whether the branch contains T(phi) at label `l` for the given formula `phi`. -/
def hasPosAt [BEq F] [BEq L] (b : Branch F L) (phi : F) (l : L) : Bool :=
  b.any fun sf => sf.sign == .pos && sf.formula == phi && sf.label == l

/-- Test whether the branch contains F(phi) at label `l` for the given formula `phi`. -/
def hasNegAt [BEq F] [BEq L] (b : Branch F L) (phi : F) (l : L) : Bool :=
  b.any fun sf => sf.sign == .neg && sf.formula == phi && sf.label == l

/-- All formulas (regardless of sign) with label `l`. -/
def formulasAt [BEq L] (b : Branch F L) (l : L) : List F :=
  (b.filter fun sf => sf.label == l).map (·.formula)

/-- Collect all distinct labels that appear on the branch. -/
def labels [BEq L] (b : Branch F L) : List L :=
  b.foldl (fun acc sf => if acc.any (· == sf.label) then acc else sf.label :: acc) []

/-- Search the branch for a complementary pair T(phi)/F(phi) at the same label.
Returns `some (phi, l)` if found, `none` if the branch has no contradiction. -/
def findContradiction [BEq F] [BEq L] (b : Branch F L) : Option (F × L) :=
  b.findSome? fun sf =>
    if sf.isPos then
      if b.any fun sf' => sf'.sign == .neg && sf'.formula == sf.formula && sf'.label == sf.label
      then some (sf.formula, sf.label)
      else none
    else
      none

/-- `true` when the branch contains T(phi) and F(phi) at the same label for some phi. -/
def hasContradiction [BEq F] [BEq L] (b : Branch F L) : Bool :=
  (b.findContradiction).isSome

/-- `true` when the branch contains T(bot) at any label (classical closure condition). -/
def hasBotPos [HasBot F] [BEq F] (b : Branch F L) : Bool :=
  b.any fun sf => sf.isPos && sf.formula == (HasBot.bot : F)

end Branch

end Cslib.Logic.Tableau

end
