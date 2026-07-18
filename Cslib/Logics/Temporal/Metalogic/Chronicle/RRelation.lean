/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
public import Cslib.Logics.Temporal.Metalogic.WitnessSeed
public import Cslib.Foundations.Logic.Metalogic.Chronicle.RRelation
public import Mathlib.Order.Zorn

/-!
# r-Relation Lemmas (Burgess 1982, Lemmas 2.2-2.5)

Core r-relation infrastructure for the temporal chronicle construction.

## Status (task 530, Phase 2)

The ~38-lemma shared core (deductive-closure infrastructure, r-relation/r3
maximal-extension existence via Zorn, `burgess*_absorption`, `untl/snce_left_mono*`,
seed→`BurgessR3Maximal`, the duality/absurdity lemmas, and the
`burgessR_implies_burgessRSince` pair) is now a thin instance + re-export layer over
`Cslib.Foundations.Logic.Metalogic.Chronicle.RRelation`, instantiated by
`temporalChronicleInterface`. See that module's docstring for the full list and for the
`ChronicleInterface` fields added this phase.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean
* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]
-/

set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic
open Cslib.Logic.Metalogic.Chronicle (ChronicleInterface)

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## BX10/BX5 at MCS Level -/

theorem until_implies_F_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_until : (γ U δ) ∈ A) : (𝐅δ) ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.until_implies_F_in_mcs temporalChronicleInterface h_mcs h_until

theorem until_self_accum_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_until : (γ U δ) ∈ A) :
    Formula.untl (Formula.and γ (Formula.untl γ δ)) δ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.until_self_accum_in_mcs temporalChronicleInterface h_mcs h_until

theorem since_implies_P_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_since : (γ S δ) ∈ A) : (𝐏δ) ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.since_implies_P_in_mcs temporalChronicleInterface h_mcs h_since

/-! ## r-Relation Guard Continues -/

theorem rRelation_guard_continues' {A B : Set (Formula Atom)}
    (h_r : rRelation A B) {γ δ : Formula Atom}
    (h_until : (γ U δ) ∈ A) (h_not_delta : δ ∉ B) :
    γ ∈ B ∧ (γ U δ) ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.rRelation_guard_continues' temporalChronicleInterface h_r h_until h_not_delta

/-! ## Deductive Closure -/

/-- The deductive closure of a set of formulas under Base-frame derivation. -/
noncomputable def deductiveClosure (Sig : Set (Formula Atom)) : Set (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.ciDeductiveClosure temporalChronicleInterface Sig

theorem subset_deductiveClosure (Sig : Set (Formula Atom)) : Sig ⊆ deductiveClosure Sig :=
  Cslib.Logic.Metalogic.Chronicle.subset_deductiveClosure temporalChronicleInterface Sig

theorem deductiveClosure_closed (Sig : Set (Formula Atom)) :
    ∀ (L : List (Formula Atom)) (φ : Formula Atom),
      (∀ ψ ∈ L, ψ ∈ deductiveClosure Sig) → DerivationTree FrameClass.Base L φ → φ ∈ deductiveClosure Sig :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_closed temporalChronicleInterface Sig

theorem deductiveClosure_consistent {Sig : Set (Formula Atom)}
    (h : Temporal.SetConsistent Sig) :
    Temporal.SetConsistent (deductiveClosure Sig) :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_consistent temporalChronicleInterface h

theorem deductiveClosure_is_dcs {Sig : Set (Formula Atom)}
    (h : Temporal.SetConsistent Sig) :
    SetDeductivelyClosed (deductiveClosure Sig) :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_is_dcs temporalChronicleInterface h

theorem deductiveClosure_closed_under_derivation (Sig : Set (Formula Atom)) :
    ClosedUnderDerivation (deductiveClosure Sig) :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_closed_under_derivation temporalChronicleInterface Sig

/-! ## R-Maximal Extension Existence via Zorn -/

theorem chain_finite_subset_in_element {c : Set (Set (Formula Atom))} {T₀ : Set (Formula Atom)}
    (hc_chain : IsChain (· ⊆ ·) c) (hT₀ : T₀ ∈ c)
    (L : List (Formula Atom))
    (hL : ∀ φ ∈ L, φ ∈ ⋃₀ c) :
    ∃ T ∈ c, ∀ φ ∈ L, φ ∈ T :=
  Cslib.Logic.Metalogic.Chronicle.chain_finite_subset_in_element hc_chain hT₀ L hL

theorem rMaximal_extension_exists {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed Sig) (h_r : rRelation A Sig) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ rMaximal A B :=
  Cslib.Logic.Metalogic.Chronicle.rMaximal_extension_exists temporalChronicleInterface h_mcs h_dcs h_r

/-! ## R3-Maximal Extension Existence -/

theorem r3Maximal_extension_exists {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed Sig) (h_r3 : r3Relation A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ R3Maximal A B C :=
  Cslib.Logic.Metalogic.Chronicle.r3Maximal_extension_exists temporalChronicleInterface h_mcs_A h_mcs_C h_dcs h_r3

/-! ## Burgess Absorption (Lemma 2.5) -/

theorem burgessR_absorption {A D C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_D : Temporal.SetMaximalConsistent D)
    (β : Formula Atom) (h_β_D : β ∈ D)
    (h_rAD : burgessR A β D) (h_rDC : burgessR D β C) :
    burgessR A β C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR_absorption temporalChronicleInterface h_mcs_A h_mcs_D β h_β_D h_rAD h_rDC

theorem burgessRSince_absorption {A D C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_D : Temporal.SetMaximalConsistent D)
    (β : Formula Atom) (h_β_D : β ∈ D)
    (h_rAD : burgessRSince A β D) (h_rDC : burgessRSince D β C) :
    burgessRSince A β C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSince_absorption temporalChronicleInterface h_mcs_A h_mcs_D β h_β_D h_rAD h_rDC

theorem burgessRSet_absorption {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_D : Temporal.SetMaximalConsistent D)
    (h_sub_D : B ⊆ D) (h_rAD : burgessRSet A B D) (h_rDC : burgessRSet D B C) :
    burgessRSet A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSet_absorption temporalChronicleInterface h_mcs_A h_mcs_D h_sub_D h_rAD h_rDC

theorem burgessRSetSince_absorption {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_D : Temporal.SetMaximalConsistent D)
    (h_sub_D : B ⊆ D) (h_rAD : burgessRSetSince A B D) (h_rDC : burgessRSetSince D B C) :
    burgessRSetSince A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSetSince_absorption temporalChronicleInterface h_mcs_A h_mcs_D h_sub_D h_rAD h_rDC

theorem burgessR3_absorption {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_D : Temporal.SetMaximalConsistent D)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_sub_D : B ⊆ D) (h_r3_AD : burgessR3 A B D) (h_r3_DC : burgessR3 D B C) :
    burgessR3 A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3_absorption temporalChronicleInterface h_mcs_A h_mcs_D h_mcs_C h_sub_D h_r3_AD h_r3_DC

/-! ## MCS Contrapositive Helper -/

theorem mcs_contrapositive_mem {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M)
    {φ ψ : Formula Atom}
    (h_imp : (φ → ψ) ∈ M) (h_neg_psi : (¬ψ) ∈ M) :
    (¬φ) ∈ M :=
  Cslib.Logic.Metalogic.Chronicle.mcs_contrapositive_mem temporalChronicleInterface h_mcs h_imp h_neg_psi

/-! ## BurgessR3Maximal Existence -/

theorem deductiveClosure_singleton_imp {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B) {δ φ : Formula Atom}
    (h_delta : δ ∈ B) (h_imp : (δ.imp φ) ∈ deductiveClosure B) :
    φ ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_singleton_imp temporalChronicleInterface h_cud h_delta h_imp

theorem dcs_neg_insert_consistent {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    {φ : Formula Atom} (h_not_mem : φ ∉ B) :
    Temporal.SetConsistent ({Formula.neg φ} ∪ B) :=
  Cslib.Logic.Metalogic.Chronicle.dcs_neg_insert_consistent temporalChronicleInterface h_cud h_not_mem

theorem burgessR3Maximal_extension_exists {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    {Sig : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation Sig)
    (h_br3 : burgessR3 A Sig C) :
    ∃ B, Sig ⊆ B ∧ BurgessR3Maximal A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_extension_exists temporalChronicleInterface h_mcs_A h_mcs_C h_cud h_br3

/-! ## Left Monotonicity Helpers (BX2G/BX2H at MCS Level) -/

theorem untl_left_mono_G {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h_G_impl : (β₁.imp β₂).allFuture ∈ A) (hUntl : (β₁ U γ) ∈ A) :
    (β₂ U γ) ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.untl_left_mono_G temporalChronicleInterface h_mcs h_G_impl hUntl

theorem snce_left_mono_H {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h_H_impl : (β₁.imp β₂).allPast ∈ A) (hSnce : (β₁ S γ) ∈ A) :
    (β₂ S γ) ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.snce_left_mono_H temporalChronicleInterface h_mcs h_H_impl hSnce

theorem untl_left_mono_thm {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (hImpl : DerivationTree FrameClass.Base [] (β₁.imp β₂)) (hUntl : (β₁ U γ) ∈ A) :
    (β₂ U γ) ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.untl_left_mono_thm temporalChronicleInterface h_mcs hImpl hUntl

theorem snce_left_mono_thm {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (hImpl : DerivationTree FrameClass.Base [] (β₁.imp β₂)) (hSnce : (β₁ S γ) ∈ A) :
    (β₂ S γ) ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.snce_left_mono_thm temporalChronicleInterface h_mcs hImpl hSnce

/-! ## Duality Helpers for Burgess Lemma 2.3 -/

theorem neg_allPast_neg_to_somePast {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (α : Formula Atom)
    (h : Formula.neg (Formula.allPast (Formula.neg α)) ∈ M) :
    (𝐏α) ∈ M :=
  Cslib.Logic.Metalogic.Chronicle.neg_allPast_neg_to_somePast temporalChronicleInterface h_mcs α h

theorem neg_allFuture_neg_to_someFuture {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (γ : Formula Atom)
    (h : Formula.neg (Formula.allFuture (Formula.neg γ)) ∈ M) :
    (𝐅γ) ∈ M :=
  Cslib.Logic.Metalogic.Chronicle.neg_allFuture_neg_to_someFuture temporalChronicleInterface h_mcs γ h

theorem someFuture_H_neg_G_P_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (α : Formula Atom)
    (h_F : Formula.someFuture (Formula.allPast (Formula.neg α)) ∈ M)
    (h_GP : Formula.allFuture (Formula.somePast α) ∈ M) : False :=
  Cslib.Logic.Metalogic.Chronicle.someFuture_H_neg_G_P_absurd temporalChronicleInterface h_mcs α h_F h_GP

theorem somePast_G_neg_H_F_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (γ : Formula Atom)
    (h_P : Formula.somePast (Formula.allFuture (Formula.neg γ)) ∈ M)
    (h_HF : Formula.allPast (Formula.someFuture γ) ∈ M) : False :=
  Cslib.Logic.Metalogic.Chronicle.somePast_G_neg_H_F_absurd temporalChronicleInterface h_mcs γ h_P h_HF

/-! ## Burgess Lemma 2.3: burgessR <-> burgessRSince -/

theorem burgessR_implies_burgessRSince {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    {β : Formula Atom} (h_burgessR : burgessR A β C) :
    burgessRSince C β A :=
  Cslib.Logic.Metalogic.Chronicle.burgessR_implies_burgessRSince temporalChronicleInterface h_mcs_A h_mcs_C h_burgessR

theorem burgessRSince_implies_burgessR {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    {β : Formula Atom} (h_burgessRSince : burgessRSince C β A) :
    burgessR A β C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSince_implies_burgessR temporalChronicleInterface h_mcs_A h_mcs_C h_burgessRSince

/-! ## Deductive Closure Singleton Propagation -/

/-- If `L` consists entirely of copies of `η` and `L ⊢ φ`, then `[η] ⊢ φ`. -/
noncomputable def derivationFromSingletonList {η φ : Formula Atom} {L : List (Formula Atom)}
    (hL : ∀ ψ ∈ L, ψ = η) (d : DerivationTree FrameClass.Base L φ) :
    DerivationTree FrameClass.Base [η] φ :=
  Cslib.Logic.Metalogic.Chronicle.derivationFromSingletonList temporalChronicleInterface hL d

theorem deductiveClosure_singleton_imp' {η φ : Formula Atom}
    (hφ : φ ∈ deductiveClosure ({η} : Set (Formula Atom))) :
    Nonempty (DerivationTree FrameClass.Base [] (η.imp φ)) :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_singleton_imp' temporalChronicleInterface hφ

theorem burgessR_of_deductiveClosure_singleton {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_burgessR : burgessR A η C) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure ({η} : Set (Formula Atom))) :
    burgessR A φ C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR_of_deductiveClosure_singleton temporalChronicleInterface h_mcs_A h_burgessR φ hφ

theorem burgessRSince_of_deductiveClosure_singleton {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_burgessRSince : burgessRSince C η A) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure ({η} : Set (Formula Atom))) :
    burgessRSince C φ A :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSince_of_deductiveClosure_singleton temporalChronicleInterface h_mcs_C h_burgessRSince φ hφ

/-! ## BurgessR3Maximal Existence from Seed -/

theorem burgessR3Maximal_exists_from_seed (A C : Set (Formula Atom)) (η : Formula Atom)
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_burgessR : burgessR A η C)
    (h_burgessRSince : burgessRSince C η A)
    (h_η_A : η ∈ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_exists_from_seed temporalChronicleInterface A C η h_mcs_A h_mcs_C h_burgessR h_burgessRSince h_η_A

end Cslib.Logic.Temporal.Metalogic.Chronicle
