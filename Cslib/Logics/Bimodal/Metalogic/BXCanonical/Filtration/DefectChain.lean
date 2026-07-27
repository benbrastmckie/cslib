/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image

/-!
# Defect-Discharge Chain Construction

Sigma defect count on BXPoints and defect-discharge infrastructure.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Filtration/DefectChain.lean
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Filtration

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
-- File-wide `open Classical` (not per-declaration) provides the scoped
-- `Classical.propDecidable` instance used by `Finset.filter` below; `set_option ... in`
-- would scope the open to a single command and silently break this instance propagation.
set_option linter.style.openClassical false
open Classical

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Until Defect Count -/

/-- Predicate for an Until-defect: an Until-formula in `Sigma` whose guard does not hold at `w`. -/
def isUntilDefect (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) (f : Formula Atom) : Prop :=
  f ∈ Sigma ∧ f ∈ w.formulas ∧
  ∃ φ ψ : Formula Atom, f = Formula.untl φ ψ ∧ ψ ∉ w.formulas

/-- The number of Until-defects at `w` relative to `Sigma`. -/
noncomputable def sigmaDefectCount (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) : Nat :=
  (Sigma.filter (fun f =>
    f ∈ w.formulas ∧
    ∃ φ ψ : Formula Atom, f = Formula.untl φ ψ ∧ ψ ∉ w.formulas)).card

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem sigma_defect_count_bounded (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) :
    sigmaDefectCount w Sigma ≤ Sigma.card := by
  unfold sigmaDefectCount
  exact Finset.card_filter_le Sigma _

/-! ## Defect Step Properties -/

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem defect_step_F_psi {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_until : Formula.untl φ ψ ∈ w.formulas) :
    Formula.someFuture ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ :=
    DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h_until

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem defect_step_connect {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_until : Formula.untl φ ψ ∈ w.formulas) :
    Formula.allFuture (Formula.somePast (Formula.untl φ ψ)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ :=
    DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl φ ψ)) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h_until

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem defect_step_self_accum {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_until : Formula.untl φ ψ ∈ w.formulas) :
    Formula.untl (Formula.and φ (Formula.untl φ ψ)) ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ :=
    DerivationTree.axiom [] _ (Axiom.self_accum_until φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h_until

/-! ## Since Defect Properties -/

/-- The number of Since-defects at `w` relative to `Sigma`. -/
noncomputable def sigmaSinceDefectCount (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) : Nat :=
  (Sigma.filter (fun f =>
    f ∈ w.formulas ∧
    ∃ φ ψ : Formula Atom, f = Formula.snce φ ψ ∧ ψ ∉ w.formulas)).card

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem since_defect_step_P_psi {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_since : Formula.snce φ ψ ∈ w.formulas) :
    Formula.somePast ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ :=
    DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h_since

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
theorem since_defect_step_connect {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_since : Formula.snce φ ψ ∈ w.formulas) :
    Formula.allPast (Formula.someFuture (Formula.snce φ ψ)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ :=
    DerivationTree.axiom [] _ (Axiom.connect_past (Formula.snce φ ψ)) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h_since

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Filtration
