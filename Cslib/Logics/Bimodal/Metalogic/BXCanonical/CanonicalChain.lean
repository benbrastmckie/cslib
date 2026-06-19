/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Filtration.DefectChain

/-!
# Canonical Chain Infrastructure

MCS-level lemmas for BX axioms and delegation bridges.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/CanonicalChain.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.Filtration

variable {Atom : Type*}

/-! ## BX12 at MCS level: F(ψ) → ⊤ U ψ -/

theorem F_imp_top_until_mcs {w : BXPoint Atom} {ψ : Formula Atom}
    (h : Formula.someFuture ψ ∈ w.formulas) :
    Formula.untl ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)) ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.someFuture ψ).imp
    (Formula.untl ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)) ψ)) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

theorem P_imp_top_since_mcs {w : BXPoint Atom} {ψ : Formula Atom}
    (h : Formula.somePast ψ ∈ w.formulas) :
    Formula.snce ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)) ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.somePast ψ).imp
    (Formula.snce ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)) ψ)) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-! ## BX6 at MCS level: absorption -/

theorem absorb_until_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.untl φ (Formula.and φ (Formula.untl φ ψ)) ∈ w.formulas) :
    Formula.untl φ ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl φ (Formula.and φ (Formula.untl φ ψ))).imp
    (Formula.untl φ ψ)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_until φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

theorem absorb_since_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.snce φ (Formula.and φ (Formula.snce φ ψ)) ∈ w.formulas) :
    Formula.snce φ ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce φ (Formula.and φ (Formula.snce φ ψ))).imp
    (Formula.snce φ ψ)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_since φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-! ## Delegation bridges -/

theorem delegation_until_eventuality
    (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_until : Formula.untl φ ψ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bxLe w v ∧ ψ ∈ v.formulas :=
  bxUntilEventualityResolution w φ ψ h_until h_not_psi

theorem delegation_since_eventuality
    (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_since : Formula.snce φ ψ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bxLe v w ∧ ψ ∈ v.formulas :=
  bxSinceEventualityResolution w φ ψ h_since h_not_psi

end Cslib.Logic.Bimodal.Metalogic.BXCanonical
