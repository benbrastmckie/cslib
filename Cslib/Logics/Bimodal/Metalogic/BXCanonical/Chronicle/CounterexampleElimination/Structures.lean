/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleTypes
public import Cslib.Foundations.Logic.Metalogic.Chronicle.CounterexampleElimination.Structures
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-! # C5/C5' Counterexample Structures and Fresh-Rational Helpers

C5/C5' counterexample structures and the fresh-rational helper lemmas
used by the Burgess chronicle construction.

## Status (task 530, Phase 3a)

The fresh-rational Finset helpers (`exists_rat_gt_finset`/`exists_rat_lt_finset`/
`exists_rat_between_not_in_finset`) are now thin re-exports of
`Cslib.Foundations.Logic.Metalogic.Chronicle.CounterexampleElimination.Structures` (zero
`Formula`/`Chronicle` dependency, identical in both trees).

`C5Counterexample`/`C5'Counterexample` stay logic-local, verbatim: they are `structure`s
indexed by `Chronicle Atom`, referencing the `.f`/`.dom` fields Phase 1 deliberately kept
logic-local (a `toGeneric` bridge broke downstream `rcases`/`simp` proofs). See the generic
module's docstring for the full rationale.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

set_option linter.unusedSimpArgs false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.style.setOption false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Bimodal

/-! ## C5/C5' Counterexample Structures -/

/--
A **C5 counterexample** for a chronicle: a point x and formulas xi, eta such that
xi U eta in f(x) but no witness exists in the current domain.
-/
structure C5Counterexample (χ : Chronicle Atom) where
  /-- The rational point in the chronicle domain witnessing the counterexample. -/
  x : Rat
  x_mem : x ∈ χ.dom
  /-- The guard formula (the body of the Until). -/
  ξ : Formula Atom
  /-- The event formula (the trigger of the Until). -/
  η : Formula Atom
  until_mem : Formula.untl ξ η ∈ χ.f x
  no_witness : ¬∃ y ∈ χ.dom, x < y ∧ η ∈ χ.f y ∧
    ∀ z ∈ χ.dom, x < z → z < y → ξ ∈ χ.f z ∧ Formula.untl ξ η ∈ χ.f z

/--
A **C5' counterexample** (Since direction): a point x and formulas xi, eta such that
xi S eta in f(x) but no backward witness exists.
-/
structure C5'Counterexample (χ : Chronicle Atom) where
  /-- The rational point in the chronicle domain witnessing the counterexample. -/
  x : Rat
  x_mem : x ∈ χ.dom
  /-- The guard formula (the body of the Since). -/
  ξ : Formula Atom
  /-- The event formula (the trigger of the Since). -/
  η : Formula Atom
  since_mem : Formula.snce ξ η ∈ χ.f x
  no_witness : ¬∃ y ∈ χ.dom, y < x ∧ η ∈ χ.f y ∧
    ∀ z ∈ χ.dom, y < z → z < x → ξ ∈ χ.f z ∧ Formula.snce ξ η ∈ χ.f z

/-! ## Helper: Finding Fresh Rationals -/

/--
There exists a rational strictly greater than all elements of a finite set
of rationals. (The rationals are unbounded above.)
-/
theorem exists_rat_gt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, s < q) ∧ q ∉ fs :=
  Cslib.Logic.Metalogic.Chronicle.exists_rat_gt_finset fs

/--
There exists a rational strictly less than all elements of a finite set
of rationals. (The rationals are unbounded below.)
-/
theorem exists_rat_lt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, q < s) ∧ q ∉ fs :=
  Cslib.Logic.Metalogic.Chronicle.exists_rat_lt_finset fs

/--
There exists a rational strictly between x and y that is NOT in a finite set fs.
-/
private theorem exists_rat_between_not_in_finset (fs : Finset Rat) (x y : Rat) (hxy : x < y) :
    ∃ z : Rat, x < z ∧ z < y ∧ z ∉ fs :=
  Cslib.Logic.Metalogic.Chronicle.exists_rat_between_not_in_finset fs x y hxy

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

end
