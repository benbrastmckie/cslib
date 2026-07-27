/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleTypes
public import Cslib.Logics.Bimodal.Metalogic.Bundle.WitnessSeed
public import Cslib.Logics.Bimodal.Theorems.TemporalDerived
public import Cslib.Logics.Bimodal.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Metalogic.Chronicle.RRelation
public import Mathlib.Order.Zorn

/-!
# r-Relation Lemmas (Burgess 1982, Lemmas 2.2-2.3)

This module proves the foundational lemmas about the r-relation
from Burgess 1982 Section 2, adapted for irreflexive (strict) temporal semantics.

## Status

The ~38-lemma shared core (deductive-closure infrastructure, r-relation/r3
maximal-extension existence via Zorn, `burgess*_absorption`, `untl/snce_left_mono*`,
seed→`BurgessR3Maximal`, the duality/absurdity lemmas, and the
`burgessR_implies_burgessRSince` pair) is now a thin instance + re-export layer over
`Cslib.Foundations.Logic.Metalogic.Chronicle.RRelation`, instantiated by
`bimodalChronicleInterface fc`. See that module's docstring for the full list.

Bimodal's own extras stay logic-local, verbatim: the Since-mirrored maximal-extension
variants (`rMaximalSince_extension_exists`, `r3MaximalSince_extension_exists`), the
`BurgessR3Maximal` projection/accessor suite, conjunction-guard machinery
(`untl/snce_conj_guard`, `burgessR_conj`, `burgessRSince_conj`), the c4/c4' hard-case
lemmas, `burgessR3_untl_conj_in_A` (Xu's Lemma 3.2.1), and
`F_mem_of_g_content_sub`/`P_mem_of_g_content_sub`/`burgessR3Maximal_from_g_content_sub`/
`burgessR3Maximal_with_guard` (the latter is a namesake, not the same lemma, as a Temporal
declaration of the same short name -- see the generic module's docstring).

## Adaptation for Open Guard Semantics

Under open guard semantics (t,s), the evaluation point t is NOT in the guard
interval. Key consequences:
- BX9 (until_elim) is REMOVED: `(phi U psi) -> (phi ∨ psi)` is invalid
- until_guard axiom is REMOVED: `(phi U psi) -> phi` is invalid

## References

- Burgess 1982: "Axioms for tense logic II: Time periods", Lemmas 2.2-2.3
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean
-/

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Metalogic.Chronicle (ChronicleInterface)

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## Note on Lemma 2.2 (Until Guard Consistency)

Burgess's Lemma 2.2 states: if `gamma U delta in A` for MCS A, then `{gamma}` is
consistent. This is **FALSE** under strict (irreflexive) Until semantics for gamma = bot;
see the removed `until_disjunction_in_mcs` lemma, withdrawn once discovered to be false
under strict Until semantics.
-/

/-! ## BX10/BX5/Guard-Continues Shared Core -/

theorem until_implies_F_in_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {γ δ : Formula Atom}
    (h_until : Formula.untl γ δ ∈ A) :
    Formula.someFuture δ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.until_implies_F_in_mcs (bimodalChronicleInterface fc) h_mcs h_until

theorem until_self_accum_in_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {γ δ : Formula Atom}
    (h_until : Formula.untl γ δ ∈ A) :
    Formula.untl (Formula.and γ (Formula.untl γ δ)) δ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.until_self_accum_in_mcs (bimodalChronicleInterface fc) h_mcs h_until

theorem since_implies_P_in_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {γ δ : Formula Atom}
    (h_since : Formula.snce γ δ ∈ A) :
    Formula.somePast δ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.since_implies_P_in_mcs (bimodalChronicleInterface fc) h_mcs h_since

theorem rRelation_guard_continues' {A B : Set (Formula Atom)}
    (h_r : rRelation A B) {γ δ : Formula Atom}
    (h_until : Formula.untl γ δ ∈ A) (h_not_delta : δ ∉ B) :
    γ ∈ B ∧ Formula.untl γ δ ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.rRelation_guard_continues' (bimodalChronicleInterface FrameClass.Base) h_r h_until h_not_delta

/-! ## Deductive Closure -/

/-- Deductive closure of a set: the set of all formulas derivable from finite subsets of S. -/
noncomputable def deductiveClosure (fc : FrameClass) (Sig : Set (Formula Atom)) : Set (Formula Atom) :=
  Cslib.Logic.Metalogic.Chronicle.ciDeductiveClosure (bimodalChronicleInterface fc) Sig

theorem subset_deductiveClosure (fc : FrameClass) (Sig : Set (Formula Atom)) :
    Sig ⊆ deductiveClosure fc Sig :=
  Cslib.Logic.Metalogic.Chronicle.subset_deductiveClosure (bimodalChronicleInterface fc) Sig

theorem deductiveClosure_closed (fc : FrameClass) (Sig : Set (Formula Atom)) :
    ∀ (L : List (Formula Atom)) (φ : Formula Atom),
      (∀ ψ ∈ L, ψ ∈ deductiveClosure fc Sig) → DerivationTree fc L φ → φ ∈ deductiveClosure fc Sig :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_closed (bimodalChronicleInterface fc) Sig

theorem deductiveClosure_consistent (fc : FrameClass) {Sig : Set (Formula Atom)} (h : SetConsistent fc Sig) :
    SetConsistent fc (deductiveClosure fc Sig) :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_consistent (bimodalChronicleInterface fc) h

theorem deductiveClosure_is_dcs (fc : FrameClass) {Sig : Set (Formula Atom)} (h : SetConsistent fc Sig) :
    SetDeductivelyClosed fc (deductiveClosure fc Sig) :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_is_dcs (bimodalChronicleInterface fc) h

theorem deductiveClosure_closed_under_derivation (fc : FrameClass) (Sig : Set (Formula Atom)) :
    ClosedUnderDerivation fc (deductiveClosure fc Sig) :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_closed_under_derivation (bimodalChronicleInterface fc) Sig

/-! ## R-Maximal Extension Existence -/

theorem chain_finite_subset_in_element {c : Set (Set (Formula Atom))} {T₀ : Set (Formula Atom)}
    (hc_chain : IsChain (· ⊆ ·) c) (hT₀ : T₀ ∈ c)
    (L : List (Formula Atom))
    (hL : ∀ φ ∈ L, φ ∈ ⋃₀ c) :
    ∃ T ∈ c, ∀ φ ∈ L, φ ∈ T :=
  Cslib.Logic.Metalogic.Chronicle.chain_finite_subset_in_element hc_chain hT₀ L hL

theorem rMaximal_extension_exists (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig) (h_r : rRelation A Sig) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ rMaximal fc A B :=
  Cslib.Logic.Metalogic.Chronicle.rMaximal_extension_exists (bimodalChronicleInterface fc) h_mcs h_dcs h_r

/--
Similarly for Since: R-maximal Since extensions exist. (Bimodal-only: no Temporal
counterpart in this direction is needed downstream.)
-/
theorem rMaximalSince_extension_exists (fc : FrameClass) {A : Set (Formula Atom)}
    (_h_mcs : SetMaximalConsistent fc A)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig)
    (h_r : rRelationSince A Sig) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ rMaximalSince fc A B := by
  have h_S_in : Sig ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ rRelationSince A B} :=
    ⟨Set.Subset.refl _, h_dcs, h_r⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ rRelationSince A B} (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · constructor
        · intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · intro γ δ h_since
        rcases (hc_sub hT₀).2.2 γ δ h_since with h_d | ⟨h_g, h_s⟩
        · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
        · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                         Set.mem_sUnion.mpr ⟨T₀, hT₀, h_s⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r, ?_⟩
  intro C hC_dcs hBC hC_r
  have hC_in : C ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ rRelationSince A B} :=
    ⟨Set.Subset.trans hSB hBC.1, hC_dcs, hC_r⟩
  exact hBC.2 (hB_max hC_in hBC.1)

/-! ## Three-Argument R-Maximal Extension Existence -/

theorem r3Maximal_extension_exists (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig) (h_r3 : r3Relation A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ R3Maximal fc A B C :=
  Cslib.Logic.Metalogic.Chronicle.r3Maximal_extension_exists (bimodalChronicleInterface fc) h_mcs_A h_mcs_C h_dcs h_r3

/--
Mirror: R3-maximal Since extensions exist. (Bimodal-only.)
-/
theorem r3MaximalSince_extension_exists (fc : FrameClass) {A C : Set (Formula Atom)}
    (_h_mcs_A : SetMaximalConsistent fc A) (_h_mcs_C : SetMaximalConsistent fc C)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig) (h_r3 : r3RelationSince A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ R3MaximalSince fc A B C := by
  have h_S_in : Sig ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ r3RelationSince A B C} :=
    ⟨Set.Subset.refl _, h_dcs, h_r3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ r3RelationSince A B C} (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · constructor
        · intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · constructor
        · intro γ δ h_since
          rcases (hc_sub hT₀).2.2.1 γ δ h_since with h_d | ⟨h_g, h_s⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                           Set.mem_sUnion.mpr ⟨T₀, hT₀, h_s⟩⟩
        · intro γ δ h_until
          rcases (hc_sub hT₀).2.2.2 γ δ h_until with h_d | ⟨h_g, h_u⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                           Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r3⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r3, ?_⟩
  intro D hD_dcs hBD hD_r3
  have hD_in : D ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ r3RelationSince A B C} :=
    ⟨Set.Subset.trans hSB hBD.1, hD_dcs, hD_r3⟩
  exact hBD.2 (hB_max hD_in hBD.1)

/--
A deductive closure seed for r3-relation: given rRelation and rRelationSince,
the three-argument version holds automatically. (Bimodal-only convenience.)
-/
theorem r3_seed_from_rRelation {A B C : Set (Formula Atom)}
    (h_r : rRelation A B) (h_rS : rRelationSince C B) : r3Relation A B C :=
  ⟨h_r, h_rS⟩

/-! ## Burgess r-Relation Lemmas -/

theorem burgessR_absorption (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_D : SetMaximalConsistent fc D)
    (β : Formula Atom) (h_β_D : β ∈ D)
    (h_rAD : burgessR A β D) (h_rDC : burgessR D β C) :
    burgessR A β C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR_absorption (bimodalChronicleInterface fc) h_mcs_A h_mcs_D β h_β_D h_rAD h_rDC

theorem burgessRSet_absorption (fc : FrameClass) {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_D : SetMaximalConsistent fc D)
    (h_sub_D : B ⊆ D) (h_rAD : burgessRSet A B D) (h_rDC : burgessRSet D B C) :
    burgessRSet A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSet_absorption (bimodalChronicleInterface fc) h_mcs_A h_mcs_D h_sub_D h_rAD h_rDC

theorem burgessRSince_absorption (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_D : SetMaximalConsistent fc D)
    (β : Formula Atom) (h_β_D : β ∈ D)
    (h_rAD : burgessRSince A β D) (h_rDC : burgessRSince D β C) :
    burgessRSince A β C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSince_absorption (bimodalChronicleInterface fc) h_mcs_A h_mcs_D β h_β_D h_rAD h_rDC

theorem burgessRSetSince_absorption (fc : FrameClass) {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_D : SetMaximalConsistent fc D)
    (h_sub_D : B ⊆ D) (h_rAD : burgessRSetSince A B D) (h_rDC : burgessRSetSince D B C) :
    burgessRSetSince A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSetSince_absorption (bimodalChronicleInterface fc) h_mcs_A h_mcs_D h_sub_D h_rAD h_rDC

theorem burgessR3_absorption (fc : FrameClass) {A D C : Set (Formula Atom)} {B₁ B₂ B₁₂ : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_D : SetMaximalConsistent fc D) (h_mcs_C : SetMaximalConsistent fc C)
    (h_sub_B₁ : B₁₂ ⊆ B₁) (h_sub_D : B₁₂ ⊆ D) (h_sub_B₂ : B₁₂ ⊆ B₂)
    (h_r3_AD : burgessR3 A B₁ D) (h_r3_DC : burgessR3 D B₂ C) :
    burgessR3 A B₁₂ C := by
  constructor
  · have h_rAD : burgessRSet A B₁₂ D := fun β hβ => h_r3_AD.1 β (h_sub_B₁ hβ)
    have h_rDC : burgessRSet D B₁₂ C := fun β hβ => h_r3_DC.1 β (h_sub_B₂ hβ)
    exact burgessRSet_absorption fc h_mcs_A h_mcs_D h_sub_D h_rAD h_rDC
  · have h_rCD : burgessRSetSince C B₁₂ D := fun β hβ => h_r3_DC.2 β (h_sub_B₂ hβ)
    have h_rDA : burgessRSetSince D B₁₂ A := fun β hβ => h_r3_AD.2 β (h_sub_B₁ hβ)
    exact burgessRSetSince_absorption fc h_mcs_C h_mcs_D h_sub_D h_rCD h_rDA

/-! ## MCS Contrapositive Helper -/

theorem mcs_contrapositive_mem (fc : FrameClass) {Sig : Set (Formula Atom)} (h_mcs : SetMaximalConsistent fc Sig)
    {A B : Formula Atom} (hImpl : A.imp B ∈ Sig) (h_negB : B.neg ∈ Sig) : A.neg ∈ Sig :=
  Cslib.Logic.Metalogic.Chronicle.mcs_contrapositive_mem (bimodalChronicleInterface fc) h_mcs hImpl h_negB

/-! ## C4 Hard Case Derivations (Bimodal-only) -/

/--
Key syntactic derivation for the C4 hard case (Burgess Lemma 2.9):
from G(gamma) in A and neg(untl(gamma, delta)) in A, derive G(neg(delta)) in A.
-/
theorem c4_hard_case_G_neg_delta (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {γ δ : Formula Atom}
    (_h_γ : γ ∈ A)
    (h_Gγ : Formula.allFuture γ ∈ A)
    (h_neg_until : (Formula.untl γ δ).neg ∈ A) :
    Formula.allFuture δ.neg ∈ A := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with htop_def
  have h_G_top_gamma : Formula.allFuture (top.imp γ) ∈ A := by
    have h_G_ps := theoremInMcsFc h_mcs
      (DerivationTree.temporal_necessitation _ (DerivationTree.axiom [] _ (Axiom.imp_s γ top) trivial))
    have h_dist := theoremInMcsFc h_mcs
      (liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived (Atom := Atom) γ (top.imp γ)))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_dist h_G_ps) h_Gγ
  have h_ax := theoremInMcsFc h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_until_G top γ δ) trivial)
  have h_mono : (Formula.untl top δ).imp (Formula.untl γ δ) ∈ A :=
    SetMaximalConsistent.implication_property h_mcs h_ax h_G_top_gamma
  have h_neg_top_until := mcs_contrapositive_mem fc h_mcs h_mono h_neg_until
  have h_bx12 := theoremInMcsFc h_mcs
    (DerivationTree.axiom [] _ (Axiom.F_until_equiv δ) trivial)
  have h_neg_F := mcs_contrapositive_mem fc h_mcs h_bx12 h_neg_top_until
  exact neg_someFuture_to_allFuture_neg h_mcs δ h_neg_F

/--
Mirror of `c4_hard_case_G_neg_delta` for the Since direction (C4' hard case):
from H(gamma) in A and neg(snce(gamma, delta)) in A, derive H(neg(delta)) in A.
-/
theorem c4'_hard_case_H_neg_delta (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {γ δ : Formula Atom}
    (_h_γ : γ ∈ A)
    (h_Hγ : Formula.allPast γ ∈ A)
    (h_neg_since : (Formula.snce γ δ).neg ∈ A) :
    Formula.allPast δ.neg ∈ A := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with htop_def
  have h_H_top_gamma : Formula.allPast (top.imp γ) ∈ A := by
    have h_H_ps := theoremInMcsFc h_mcs
      (Cslib.Logic.Bimodal.Theorems.pastNecessitation _
        (DerivationTree.axiom [] _ (Axiom.imp_s γ top) trivial))
    have h_dist := theoremInMcsFc h_mcs
      (Cslib.Logic.Bimodal.Theorems.pastKDist γ (top.imp γ))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_dist h_H_ps) h_Hγ
  have h_ax := theoremInMcsFc h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_since_H top γ δ) trivial)
  have h_mono : (Formula.snce top δ).imp (Formula.snce γ δ) ∈ A :=
    SetMaximalConsistent.implication_property h_mcs h_ax h_H_top_gamma
  have h_neg_top_since := mcs_contrapositive_mem fc h_mcs h_mono h_neg_since
  have h_bx12' := theoremInMcsFc h_mcs
    (DerivationTree.axiom [] _ (Axiom.P_since_equiv δ) trivial)
  have h_neg_P := mcs_contrapositive_mem fc h_mcs h_bx12' h_neg_top_since
  exact neg_somePast_to_allPast_neg h_mcs δ h_neg_P

/-! ## BurgessR3Maximal Existence -/

theorem deductiveClosure_singleton_imp (fc : FrameClass) {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation fc B) {δ φ : Formula Atom}
    (h_delta : δ ∈ B) (h_imp : (δ.imp φ) ∈ deductiveClosure fc B) :
    φ ∈ B :=
  Cslib.Logic.Metalogic.Chronicle.deductiveClosure_singleton_imp (bimodalChronicleInterface fc) h_cud h_delta h_imp

theorem dcs_neg_insert_consistent (fc : FrameClass) {B : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc B)
    {φ : Formula Atom} (h_not_in : φ ∉ B) :
    SetConsistent fc (insert φ.neg B) :=
  Cslib.Logic.Metalogic.Chronicle.dcs_neg_insert_consistent (bimodalChronicleInterface fc) h_dcs.2 h_not_in

/-! ## BurgessR3 Guard Algebra (Bimodal-only) -/

/--
**Guard conjunction for Until**: If untl(β₁, γ) ∈ A and untl(β₂, γ) ∈ A (MCS A),
then untl(β₁∧β₂, γ) ∈ A. Uses BX7 (linear_until), BX2G, BX3 (right_mono_until).
-/
theorem untl_conj_guard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : Formula.untl β₁ γ ∈ A)
    (h2 : Formula.untl β₂ γ ∈ A) :
    Formula.untl (Formula.and β₁ β₂) γ ∈ A := by
  have h_conj : Formula.and (Formula.untl β₁ γ) (Formula.untl β₂ γ) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7 := theoremInMcsFc h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_until β₁ γ β₂ γ) trivial)
  have h_disj := SetMaximalConsistent.implication_property h_mcs h_bx7 h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.untl guard (Formula.and γ γ)
  set D2 := Formula.untl guard (Formula.and γ β₂)
  set D3 := Formula.untl guard (Formula.and β₁ γ)
  set target := Formula.untl guard γ
  have mk_thm : ∀ e : Formula Atom, DerivationTree fc [] (e.imp γ) →
      DerivationTree fc [] ((Formula.untl guard e).imp target) := by
    intro e h_e_imp
    have h_G := DerivationTree.temporal_necessitation _ h_e_imp
    have h_bx3 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3 h_G
  have h_D1_impl := theoremInMcsFc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lceImp γ γ))
  have h_D2_impl := theoremInMcsFc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lceImp γ β₂))
  have h_D3_impl := theoremInMcsFc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.rceImp β₁ γ))
  rcases SetMaximalConsistent.negation_complete h_mcs D3 with h | h
  · exact SetMaximalConsistent.implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := SetMaximalConsistent.implication_property h_mcs h_disj h'
        exact absurd this (SetMaximalConsistent.neg_excludes h_mcs _ h)
    rcases SetMaximalConsistent.negation_complete h_mcs D1 with h' | h'
    · exact SetMaximalConsistent.implication_property h_mcs h_D1_impl h'
    · have h_D2 := SetMaximalConsistent.implication_property h_mcs h_D1_or_D2 h'
      exact SetMaximalConsistent.implication_property h_mcs h_D2_impl h_D2

/--
**Guard conjunction for Since** (mirror of `untl_conj_guard`):
If snce(β₁, γ) ∈ A and snce(β₂, γ) ∈ A (MCS A), then snce(β₁∧β₂, γ) ∈ A.
Uses BX7' (linear_since), BX3' (right_mono_since).
-/
theorem snce_conj_guard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : Formula.snce β₁ γ ∈ A)
    (h2 : Formula.snce β₂ γ ∈ A) :
    Formula.snce (Formula.and β₁ β₂) γ ∈ A := by
  have h_conj : Formula.and (Formula.snce β₁ γ) (Formula.snce β₂ γ) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7' := theoremInMcsFc h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_since β₁ γ β₂ γ) trivial)
  have h_disj := SetMaximalConsistent.implication_property h_mcs h_bx7' h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.snce guard (Formula.and γ γ)
  set D2 := Formula.snce guard (Formula.and γ β₂)
  set D3 := Formula.snce guard (Formula.and β₁ γ)
  set target := Formula.snce guard γ
  have mk_thm : ∀ e : Formula Atom, DerivationTree fc [] (e.imp γ) →
      DerivationTree fc [] ((Formula.snce guard e).imp target) := by
    intro e h_e_imp
    have h_H := Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_e_imp
    have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3' h_H
  have h_D1_impl := theoremInMcsFc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lceImp γ γ))
  have h_D2_impl := theoremInMcsFc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lceImp γ β₂))
  have h_D3_impl := theoremInMcsFc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.rceImp β₁ γ))
  rcases SetMaximalConsistent.negation_complete h_mcs D3 with h | h
  · exact SetMaximalConsistent.implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := SetMaximalConsistent.implication_property h_mcs h_disj h'
        exact absurd this (SetMaximalConsistent.neg_excludes h_mcs _ h)
    rcases SetMaximalConsistent.negation_complete h_mcs D1 with h' | h'
    · exact SetMaximalConsistent.implication_property h_mcs h_D1_impl h'
    · have h_D2 := SetMaximalConsistent.implication_property h_mcs h_D1_or_D2 h'
      exact SetMaximalConsistent.implication_property h_mcs h_D2_impl h_D2

/--
**Set-level guard conjunction for Until (burgessR)**: If `burgessR(A, α, C)` and
`burgessR(A, β, C)`, then `burgessR(A, α∧β, C)`.
-/
theorem burgessR_conj (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {α β : Formula Atom}
    (hα : burgessR A α C) (hβ : burgessR A β C) :
    burgessR A (Formula.and α β) C := by
  intro γ hγ
  exact untl_conj_guard fc h_mcs (hα γ hγ) (hβ γ hγ)

/--
**Set-level guard conjunction for Since (burgessRSince)**: If `burgessRSince(C, α, A)` and
`burgessRSince(C, β, A)`, then `burgessRSince(C, α∧β, A)`.
-/
theorem burgessRSince_conj (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C)
    {α β : Formula Atom}
    (hα : burgessRSince C α A) (hβ : burgessRSince C β A) :
    burgessRSince C (Formula.and α β) A := by
  intro γ hγ
  exact snce_conj_guard fc h_mcs (hα γ hγ) (hβ γ hγ)

/-! ## Left Monotonicity Helpers (BX2G/BX2H at MCS Level) -/

theorem untl_left_mono_G (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h_G_impl : (β₁.imp β₂).allFuture ∈ A) (hUntl : Formula.untl β₁ γ ∈ A) :
    Formula.untl β₂ γ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.untl_left_mono_G (bimodalChronicleInterface fc) h_mcs h_G_impl hUntl

theorem snce_left_mono_H (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h_H_impl : (β₁.imp β₂).allPast ∈ A) (hSnce : Formula.snce β₁ γ ∈ A) :
    Formula.snce β₂ γ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.snce_left_mono_H (bimodalChronicleInterface fc) h_mcs h_H_impl hSnce

theorem untl_left_mono_thm (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (hImpl : DerivationTree fc [] (β₁.imp β₂)) (hUntl : Formula.untl β₁ γ ∈ A) :
    Formula.untl β₂ γ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.untl_left_mono_thm (bimodalChronicleInterface fc) h_mcs hImpl hUntl

theorem snce_left_mono_thm (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (hImpl : DerivationTree fc [] (β₁.imp β₂)) (hSnce : Formula.snce β₁ γ ∈ A) :
    Formula.snce β₂ γ ∈ A :=
  Cslib.Logic.Metalogic.Chronicle.snce_left_mono_thm (bimodalChronicleInterface fc) h_mcs hImpl hSnce

/-! ## Helper: Derivation from Singleton Set Implies Implication Theorem -/

/-- If `L` consists entirely of copies of `η` and `L ⊢ φ`, then `[η] ⊢ φ`. -/
noncomputable def derivationFromSingletonList (fc : FrameClass) {η φ : Formula Atom} {L : List (Formula Atom)}
    (hL : ∀ ψ ∈ L, ψ = η) (d : DerivationTree fc L φ) :
    DerivationTree fc [η] φ :=
  Cslib.Logic.Metalogic.Chronicle.derivationFromSingletonList (bimodalChronicleInterface fc) hL d

theorem burgessR_of_deductiveClosure_singleton (fc : FrameClass) {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_burgessR : burgessR A η C) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure fc ({η} : Set (Formula Atom))) :
    burgessR A φ C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR_of_deductiveClosure_singleton (bimodalChronicleInterface fc) h_mcs_A h_burgessR φ hφ

theorem burgessRSince_of_deductiveClosure_singleton (fc : FrameClass) {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_burgessRSince : burgessRSince C η A) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure fc ({η} : Set (Formula Atom))) :
    burgessRSince C φ A :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSince_of_deductiveClosure_singleton (bimodalChronicleInterface fc) h_mcs_C h_burgessRSince φ hφ

/-! ## BurgessR3Maximal Existence from Seed -/

theorem burgessR3Maximal_extension_exists (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    {Sig : Set (Formula Atom)} (h_cud : ClosedUnderDerivation fc Sig) (h_r3 : burgessR3 A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ ClosedUnderDerivation fc B ∧ BurgessR3Maximal fc A B C := by
  obtain ⟨B, hSB, hB_cud, hB_r3⟩ :=
    Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_extension_exists (bimodalChronicleInterface fc) h_mcs_A h_mcs_C h_cud h_r3
  exact ⟨B, hSB, hB_cud, hB_cud, hB_r3⟩

theorem burgessR3Maximal_exists_from_seed (fc : FrameClass) (A C : Set (Formula Atom)) (η : Formula Atom)
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_burgessR : burgessR A η C)
    (h_burgessRSince : burgessRSince C η A)
    (h_η_A : η ∈ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal fc A B C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_exists_from_seed (bimodalChronicleInterface fc) A C η h_mcs_A h_mcs_C h_burgessR h_burgessRSince h_η_A

/-! ## BurgessR3Maximal Accessor Lemmas (Bimodal-only) -/

theorem BurgessR3Maximal_cud (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    ClosedUnderDerivation fc B := h.1

theorem BurgessR3Maximal_burgessR3 (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    burgessR3 A B C := h.2.1

theorem BurgessR3Maximal_burgessRSet (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    burgessRSet A B C := h.2.1.1

theorem BurgessR3Maximal_burgessRSetSince (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    burgessRSetSince C B A := h.2.1.2

/-! ## BurgessR3 Bridging Lemmas for C4 (Bimodal-only) -/

theorem burgessR3_untl_in {A B C : Set (Formula Atom)}
    (h : burgessR3 A B C) {β : Formula Atom} (hβ : β ∈ B) {γ : Formula Atom} (hγ : γ ∈ C) :
    Formula.untl β γ ∈ A :=
  h.1 β hβ γ hγ

theorem burgessR3_snce_in {A B C : Set (Formula Atom)}
    (h : burgessR3 A B C) {β : Formula Atom} (hβ : β ∈ B) {γ : Formula Atom} (hγ : γ ∈ A) :
    Formula.snce β γ ∈ C :=
  h.2 β hβ γ hγ

theorem burgessR3_gamma_not_in_B (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_r3 : burgessR3 A B C)
    {γ δ : Formula Atom}
    (h_neg_until : (Formula.untl γ δ).neg ∈ A)
    (h_delta : δ ∈ C) :
    γ ∉ B := by
  intro h_gamma
  have h_until := h_r3.1 γ h_gamma δ h_delta
  exact set_consistent_not_both h_mcs_A.1 (Formula.untl γ δ) h_until h_neg_until

theorem burgessR3_gamma_not_in_B_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3 : burgessR3 A B C)
    {γ δ : Formula Atom}
    (h_neg_since : (Formula.snce γ δ).neg ∈ C)
    (h_delta : δ ∈ A) :
    γ ∉ B := by
  intro h_gamma
  have h_since := h_r3.2 γ h_gamma δ h_delta
  exact set_consistent_not_both h_mcs_C.1 (Formula.snce γ δ) h_since h_neg_since

/-! ## Duality Helpers for Burgess Lemma 2.3 -/

theorem neg_allPast_neg_to_somePast (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (α : Formula Atom)
    (h : Formula.neg (Formula.allPast (Formula.neg α)) ∈ M) :
    Formula.somePast α ∈ M :=
  Cslib.Logic.Metalogic.Chronicle.neg_allPast_neg_to_somePast (bimodalChronicleInterface fc) h_mcs α h

theorem neg_allFuture_neg_to_someFuture (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (γ : Formula Atom)
    (h : Formula.neg (Formula.allFuture (Formula.neg γ)) ∈ M) :
    Formula.someFuture γ ∈ M :=
  Cslib.Logic.Metalogic.Chronicle.neg_allFuture_neg_to_someFuture (bimodalChronicleInterface fc) h_mcs γ h

theorem someFuture_H_neg_G_P_absurd (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (α : Formula Atom)
    (h_F : Formula.someFuture (Formula.allPast (Formula.neg α)) ∈ M)
    (h_GP : Formula.allFuture (Formula.somePast α) ∈ M) : False :=
  Cslib.Logic.Metalogic.Chronicle.someFuture_H_neg_G_P_absurd (bimodalChronicleInterface fc) h_mcs α h_F h_GP

theorem somePast_G_neg_H_F_absurd (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (γ : Formula Atom)
    (h_P : Formula.somePast (Formula.allFuture (Formula.neg γ)) ∈ M)
    (h_HF : Formula.allPast (Formula.someFuture γ) ∈ M) : False :=
  Cslib.Logic.Metalogic.Chronicle.somePast_G_neg_H_F_absurd (bimodalChronicleInterface fc) h_mcs γ h_P h_HF

theorem burgessR_implies_burgessRSince (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    {β : Formula Atom} (h_burgessR : burgessR A β C) :
    burgessRSince C β A :=
  Cslib.Logic.Metalogic.Chronicle.burgessR_implies_burgessRSince (bimodalChronicleInterface fc) h_mcs_A h_mcs_C h_burgessR

theorem burgessRSince_implies_burgessR (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    {β : Formula Atom} (h_burgessRSince : burgessRSince C β A) :
    burgessR A β C :=
  Cslib.Logic.Metalogic.Chronicle.burgessRSince_implies_burgessR (bimodalChronicleInterface fc) h_mcs_A h_mcs_C h_burgessRSince

/--
**Corollary**: burgessRSet and burgessRSetSince are equivalent. (Bimodal-only.)
-/
theorem burgessRSet_iff_burgessRSetSince (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C) :
    burgessRSet A B C ↔ burgessRSetSince C B A := by
  constructor
  · intro h_rSet β hβ
    exact burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C (h_rSet β hβ)
  · intro h_rSetSince β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C (h_rSetSince β hβ)

/-! ## Xu's Lemma 3.2.1: B Closure Under Until/Since Formation (Bimodal-only)

Xu 1988, Lemma 3.2.1 (p. 192): if `BurgessR3Maximal(A, B, C)` with A, C MCS, then B is
closed under Until formation with endpoint elements. No Temporal counterpart. -/

theorem burgessR3_untl_conj_in_A (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_dcs_B : SetDeductivelyClosed fc B)
    (h_r3 : burgessR3 A B C)
    {β : Formula Atom} (hβ : β ∈ B) {γ : Formula Atom} (hγ : γ ∈ C)
    (β' : Formula Atom) (hβ' : β' ∈ B) (δ : Formula Atom) (hδ : δ ∈ C) :
    Formula.untl (Formula.and β' (Formula.untl β γ)) δ ∈ A := by
  have hβ'' : Formula.and β β' ∈ B := dcs_conj_closed h_dcs_B hβ hβ'
  have hγ'' : Formula.and γ δ ∈ C := dcs_conj_closed (mcs_is_dcs h_mcs_C) hγ hδ
  have hUntl := h_r3.1 (Formula.and β β') hβ'' (Formula.and γ δ) hγ''
  have h_accum := until_self_accum_in_mcs fc h_mcs_A hUntl
  have h_guard_weak1 : DerivationTree fc [] ((Formula.and β β').imp β) :=
    Cslib.Logic.Bimodal.Theorems.Propositional.lceImp β β'
  have h_untl_step1 := untl_left_mono_thm fc h_mcs_A h_guard_weak1 hUntl
  have h_event_weak1 : DerivationTree fc [] ((Formula.and γ δ).imp γ) :=
    Cslib.Logic.Bimodal.Theorems.Propositional.lceImp γ δ
  have h_G_event_weak1 := DerivationTree.temporal_necessitation _ h_event_weak1
  have h_bx3 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until (Formula.and γ δ) γ β) trivial
  have h_untl_beta_gamma := SetMaximalConsistent.implication_property h_mcs_A
    (theoremInMcsFc h_mcs_A (DerivationTree.modus_ponens [] _ _ h_bx3 h_G_event_weak1))
    h_untl_step1
  have h_untl_inner_weak : DerivationTree fc [] (((Formula.and β β').untl (γ.and δ)).imp (β.untl γ)) := by
    have h_G_gw1 := DerivationTree.temporal_necessitation _ h_guard_weak1
    have h_bx2g := DerivationTree.axiom (fc := fc) [] _ (Axiom.left_mono_until_G (Formula.and β β') β (Formula.and γ δ)) trivial
    have h_step1 : DerivationTree fc [] (((Formula.and β β').untl (γ.and δ)).imp (β.untl (γ.and δ))) :=
      DerivationTree.modus_ponens [] _ _ h_bx2g h_G_gw1
    have h_step2 : DerivationTree fc [] ((β.untl (γ.and δ)).imp (β.untl γ)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_event_weak1
    exact impTrans h_step1 h_step2
  have h_full_guard_weak : DerivationTree fc [] (
    ((Formula.and β β').and ((Formula.and β β').untl (γ.and δ))).imp
    (β'.and (β.untl γ))) := by
    have h_comp1 : DerivationTree fc [] (
      ((Formula.and β β').and ((Formula.and β β').untl (γ.and δ))).imp β') := by
      have h1 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.Propositional.lceImp (Formula.and β β') ((Formula.and β β').untl (γ.and δ))
      have h2 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.Propositional.rceImp β β'
      exact impTrans h1 h2
    have h_comp2 : DerivationTree fc [] (
      ((Formula.and β β').and ((Formula.and β β').untl (γ.and δ))).imp (β.untl γ)) := by
      have h1 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.Propositional.rceImp (Formula.and β β') ((Formula.and β β').untl (γ.and δ))
      exact impTrans h1 h_untl_inner_weak
    exact combineImpConj h_comp1 h_comp2
  have h_weak_guard := untl_left_mono_thm fc h_mcs_A h_full_guard_weak h_accum
  have h_event_weak2 : DerivationTree fc [] ((Formula.and γ δ).imp δ) :=
    Cslib.Logic.Bimodal.Theorems.Propositional.rceImp γ δ
  have h_G_event_weak2 := DerivationTree.temporal_necessitation _ h_event_weak2
  have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until (Formula.and γ δ) δ (β'.and (β.untl γ))) trivial
  exact SetMaximalConsistent.implication_property h_mcs_A
    (theoremInMcsFc h_mcs_A (DerivationTree.modus_ponens [] _ _ h_bx3' h_G_event_weak2))
    h_weak_guard

/-! ## BurgessR3Maximal Existence from gContent Inclusion (Bimodal-only)

When `gContent(A) ⊆ C` (the canonical temporal ordering A ≤ C), we can construct
`BurgessR3Maximal(A, B, C)` using ⊤ as a seed. No Temporal counterpart: Temporal's
same-named `burgessR3Maximal_from_g_content_sub` (in the shared generic module's
re-export list) is an unrelated trivial restatement of `burgessR3Maximal_extension_exists`
-- see the generic module's docstring. -/

/-- F(γ) ∈ A for all γ ∈ C when gContent(A) ⊆ C. -/
theorem F_mem_of_g_content_sub (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_gc : gContent A ⊆ C) (γ : Formula Atom) (h_γ : γ ∈ C) :
    Formula.someFuture γ ∈ A := by
  by_contra h_not_F
  have h_neg_F : (Formula.someFuture γ).neg ∈ A :=
    (SetMaximalConsistent.negation_complete h_mcs_A _).resolve_left h_not_F
  have h_G_neg : Formula.allFuture γ.neg ∈ A :=
    neg_someFuture_to_allFuture_neg h_mcs_A γ h_neg_F
  have h_neg_C : γ.neg ∈ C := h_gc h_G_neg
  exact SetMaximalConsistent.neg_excludes h_mcs_C γ h_neg_C h_γ

/-- P(α) ∈ C for all α ∈ A when gContent(A) ⊆ C. Uses BX4 (connect_future). -/
theorem P_mem_of_g_content_sub (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_gc : gContent A ⊆ C) (α : Formula Atom) (h_α : α ∈ A) :
    Formula.somePast α ∈ C := by
  have h_GP : Formula.allFuture (Formula.somePast α) ∈ A := by
    have h_ax : DerivationTree fc [] (α.imp (Formula.allFuture (Formula.somePast α))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future α) trivial
    exact SetMaximalConsistent.implication_property h_mcs_A
      (theoremInMcsFc h_mcs_A h_ax) h_α
  exact h_gc h_GP

/-- **BurgessR3Maximal existence from gContent inclusion**: Given MCS A, C with
gContent(A) ⊆ C, there exists B with BurgessR3Maximal(A, B, C). -/
theorem burgessR3Maximal_from_g_content_sub (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_gc : gContent A ⊆ C) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal fc A B C := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with top_def
  have h_top_A : top ∈ A :=
    theoremInMcsFc h_mcs_A (identity (Formula.bot : Formula Atom))
  have h_bR : burgessR A top C := by
    intro γ hγ
    have h_F := F_mem_of_g_content_sub fc h_mcs_A h_mcs_C h_gc γ hγ
    have h_bx12 : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.untl top γ)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact SetMaximalConsistent.implication_property h_mcs_A
      (theoremInMcsFc h_mcs_A h_bx12) h_F
  have h_bRS : burgessRSince C top A := by
    intro α hα
    have h_P := P_mem_of_g_content_sub fc h_mcs_A h_gc α hα
    have h_bx12' : DerivationTree fc [] ((Formula.somePast α).imp (Formula.snce top α)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact SetMaximalConsistent.implication_property h_mcs_C
      (theoremInMcsFc h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed fc A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

/-- **BurgessR3Maximal existence with guard membership**: Given MCS A, C with
burgessR(A, η, C) and burgessRSince(C, η, A), there exists B with η ∈ B and
BurgessR3Maximal(A, B, C). (Bimodal-only.) -/
theorem burgessR3Maximal_with_guard (fc : FrameClass) (A C : Set (Formula Atom)) (η : Formula Atom)
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_burgessR : burgessR A η C)
    (h_burgessRSince : burgessRSince C η A) :
    ∃ B : Set (Formula Atom), η ∈ B ∧ BurgessR3Maximal fc A B C := by
  have h_dc_cud : ClosedUnderDerivation fc (deductiveClosure fc ({η} : Set (Formula Atom))) :=
    deductiveClosure_closed_under_derivation fc _
  have h_dc_r3 : burgessR3 A (deductiveClosure fc ({η} : Set (Formula Atom))) C := by
    constructor
    · intro φ hφ
      exact burgessR_of_deductiveClosure_singleton fc h_mcs_A h_burgessR φ hφ
    · intro φ hφ
      exact burgessRSince_of_deductiveClosure_singleton fc h_mcs_C h_burgessRSince φ hφ
  obtain ⟨B, hSB, _, h_B3M⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_mcs_C h_dc_cud h_dc_r3
  have h_η_B : η ∈ B := hSB (subset_deductiveClosure fc ({η} : Set (Formula Atom)) (Set.mem_singleton η))
  exact ⟨B, h_η_B, h_B3M⟩

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
