/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame

/-!
# Canonical Chain Infrastructure

MCS-level lemmas for BX axioms and delegation bridges.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalChain.lean
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

variable {Atom : Type*}

/-! ## BX12 at MCS level -/

theorem F_imp_top_until_mcs {w : TPoint Atom} {ψ : Formula Atom}
    (h : (𝐅ψ) ∈ w.formulas) :
    (⊤ U ψ) ∈ w.formulas :=
  temporal_implication_property w.is_mcs
    (theoremInMcs w.is_mcs (DerivationTree.axiom [] _ (Axiom.F_until_equiv ψ) trivial)) h

theorem P_imp_top_since_mcs {w : TPoint Atom} {ψ : Formula Atom}
    (h : (𝐏ψ) ∈ w.formulas) :
    (⊤ S ψ) ∈ w.formulas :=
  temporal_implication_property w.is_mcs
    (theoremInMcs w.is_mcs (DerivationTree.axiom [] _ (Axiom.P_since_equiv ψ) trivial)) h

/-! ## BX6 at MCS level -/

theorem absorb_until_mcs {w : TPoint Atom} {φ ψ : Formula Atom}
    (h : (φ U (φ ∧ (φ U ψ))) ∈ w.formulas) :
    (φ U ψ) ∈ w.formulas :=
  temporal_implication_property w.is_mcs
    (theoremInMcs w.is_mcs (DerivationTree.axiom [] _ (Axiom.absorb_until φ ψ) trivial)) h

theorem absorb_since_mcs {w : TPoint Atom} {φ ψ : Formula Atom}
    (h : (φ S (φ ∧ (φ S ψ))) ∈ w.formulas) :
    (φ S ψ) ∈ w.formulas :=
  temporal_implication_property w.is_mcs
    (theoremInMcs w.is_mcs (DerivationTree.axiom [] _ (Axiom.absorb_since φ ψ) trivial)) h

/-! ## Delegation bridges -/

theorem delegation_until_eventuality
    (w : TPoint Atom) (φ ψ : Formula Atom)
    (h_until : (φ U ψ) ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : TPoint Atom, tLe w v ∧ ψ ∈ v.formulas :=
  tUntilEventualityResolution w φ ψ h_until h_not_psi

theorem delegation_since_eventuality
    (w : TPoint Atom) (φ ψ : Formula Atom)
    (h_since : (φ S ψ) ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : TPoint Atom, tLe v w ∧ ψ ∈ v.formulas :=
  tSinceEventualityResolution w φ ψ h_since h_not_psi

end Cslib.Logic.Temporal.Metalogic.Chronicle
