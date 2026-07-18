/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.Chronicle.Types
public import Mathlib.Order.Zorn

/-! # r-Relation Lemmas — Shared Bimodal/Temporal Core (Burgess 1982, Lemmas 2.2-2.5)

Generic version of the ~38-lemma shared core of `RRelation.lean` (deductive-closure
infrastructure, r-relation/r3 maximal-extension existence via Zorn, `burgess*_absorption`,
`untl/snce_left_mono*`, seed→`BurgessR3Maximal`, the `someFuture`/`somePast` absurdity
lemmas, and the `burgessR_implies_burgessRSince` pair), parameterized by a
`ChronicleInterface F` value (task-530 Phase 2). Both
`Logics/Bimodal/.../Chronicle/RRelation.lean` and
`Logics/Temporal/.../Chronicle/RRelation.lean` instantiate this module and re-export its
declarations under their existing names.

## Divergent lemmas kept per-tree (NOT lifted here)

- Bimodal's Since-mirrored maximal-extension variants (`rMaximalSince_extension_exists`,
  `r3MaximalSince_extension_exists`), the `BurgessR3Maximal` projection/accessor suite,
  conjunction-guard machinery (`untl/snce_conj_guard`, `burgessR_conj`,
  `burgessRSince_conj`), the c4/c4' hard-case lemmas, `burgessR3_untl_conj_in_A`
  (Xu's Lemma 3.2.1), and `F_mem_of_g_content_sub`/`P_mem_of_g_content_sub`/
  `burgessR3Maximal_from_g_content_sub` (this last name coincides with a Temporal lemma of
  the same name, but the two are NOT the same lemma: Temporal's version is a trivial
  restatement of `burgessR3Maximal_extension_exists`, while Bimodal's takes an additional
  `gContent A ⊆ C` hypothesis and constructs its own seed via `Formula.top` — kept
  logic-local in both trees to avoid a false-positive merge).
- Temporal's primed `deductiveClosure_singleton_imp'`/`derivationFromSingletonList`
  variant (Bimodal has no primed counterpart).

## Interface Fields Added for This Phase

Phase 0/1 supplied the formula operators, derivation combinators, and MCS/Burgess
apparatus needed by `ChronicleTypes.lean`. This phase adds the axiom-level Deriv facts
(BX2-BX6, BX10, connect_future/past, enrichment) and the MCS-level duality-bridge facts
(`someFutureAllFutureNegAbsurd`, `negAllPastNegToSomePast`, etc.) that the RRelation layer
needs but `ChronicleTypes` does not. Each new field is *statement-only*: both logics prove
it from their own axiom schemas / duality unfoldings, whichever differs, exactly the
`SetMaximalConsistent`/Burgess-apparatus pattern already used for `theoremInMcs` etc.

## References

* Ported from `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` and
  `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean`.
* Burgess 1982: "Axioms for tense logic II: Time periods", Lemmas 2.2-2.5.
-/

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Metalogic.Chronicle

attribute [local instance] Classical.propDecidable

variable {F : Type*}

/-! ## BX10/BX5 at MCS Level -/

theorem until_implies_F_in_mcs (I : ChronicleInterface F) {A : Set F}
    (h_mcs : CISetMaximalConsistent I A) {γ δ : F}
    (h_until : I.untl γ δ ∈ A) :
    I.someFuture δ ∈ A :=
  cud_modus_ponens I (mcs_is_dcs I h_mcs).2 (cud_contains_theorems I (mcs_is_dcs I h_mcs).2
    (I.untilF γ δ)) h_until

theorem until_self_accum_in_mcs (I : ChronicleInterface F) {A : Set F}
    (h_mcs : CISetMaximalConsistent I A) {γ δ : F}
    (h_until : I.untl γ δ ∈ A) :
    I.untl (I.and γ (I.untl γ δ)) δ ∈ A :=
  cud_modus_ponens I (mcs_is_dcs I h_mcs).2 (cud_contains_theorems I (mcs_is_dcs I h_mcs).2
    (I.selfAccumUntil γ δ)) h_until

theorem since_implies_P_in_mcs (I : ChronicleInterface F) {A : Set F}
    (h_mcs : CISetMaximalConsistent I A) {γ δ : F}
    (h_since : I.snce γ δ ∈ A) :
    I.somePast δ ∈ A :=
  cud_modus_ponens I (mcs_is_dcs I h_mcs).2 (cud_contains_theorems I (mcs_is_dcs I h_mcs).2
    (I.sinceP γ δ)) h_since

/-! ## r-Relation Guard Continues -/

theorem rRelation_guard_continues' (I : ChronicleInterface F) {A B : Set F}
    (h_r : rRelation I A B) {γ δ : F}
    (h_until : I.untl γ δ ∈ A) (h_not_delta : δ ∉ B) :
    γ ∈ B ∧ I.untl γ δ ∈ B := by
  rcases h_r γ δ h_until with h_delta | h_guard
  · exact absurd h_delta h_not_delta
  · exact h_guard

/-! ## Deductive Closure -/

theorem subset_deductiveClosure (I : ChronicleInterface F) (Sig : Set F) :
    Sig ⊆ ciDeductiveClosure I Sig := by
  intro φ hφ
  exact ⟨[φ], fun ψ hψ => by simp at hψ; exact hψ ▸ hφ, ⟨I.assumption (by simp)⟩⟩

theorem deductiveClosure_closed (I : ChronicleInterface F) (Sig : Set F) :
    ∀ (L : List F) (φ : F),
      (∀ ψ ∈ L, ψ ∈ ciDeductiveClosure I Sig) → I.Deriv L φ → φ ∈ ciDeductiveClosure I Sig := by
  intro L
  induction L with
  | nil =>
    intro φ _ d
    exact ⟨[], fun _ h => absurd h List.not_mem_nil, ⟨d⟩⟩
  | cons ψ L' ih =>
    intro φ hL d
    have d_imp := I.deductionTheorem L' ψ φ d
    have hψ := hL ψ (List.mem_cons_self)
    have hL' : ∀ χ ∈ L', χ ∈ ciDeductiveClosure I Sig :=
      fun χ hχ => hL χ (List.mem_cons_of_mem ψ hχ)
    have h_imp := ih (I.imp ψ φ) hL' d_imp
    obtain ⟨M1, hM1_sub, ⟨d1⟩⟩ := h_imp
    obtain ⟨M2, hM2_sub, ⟨d2⟩⟩ := hψ
    refine ⟨M1 ++ M2, fun χ hχ => ?_, ?_⟩
    · rcases List.mem_append.mp hχ with h | h
      · exact hM1_sub χ h
      · exact hM2_sub χ h
    · exact ⟨I.modusPonens (I.weakening M1 (M1 ++ M2) (I.imp ψ φ) d1 (List.subset_append_left M1 M2))
        (I.weakening M2 (M1 ++ M2) ψ d2 (List.subset_append_right M1 M2))⟩

theorem deductiveClosure_consistent (I : ChronicleInterface F) {Sig : Set F}
    (h : CISetConsistent I Sig) :
    CISetConsistent I (ciDeductiveClosure I Sig) := by
  intro L hL ⟨d⟩
  have h_bot : I.bot ∈ ciDeductiveClosure I Sig :=
    deductiveClosure_closed I Sig L I.bot hL d
  obtain ⟨M, hM_sub, ⟨dM⟩⟩ := h_bot
  exact h M hM_sub ⟨dM⟩

theorem deductiveClosure_is_dcs (I : ChronicleInterface F) {Sig : Set F}
    (h : CISetConsistent I Sig) :
    SetDeductivelyClosed I (ciDeductiveClosure I Sig) :=
  ⟨deductiveClosure_consistent I h, deductiveClosure_closed I Sig⟩

theorem deductiveClosure_closed_under_derivation (I : ChronicleInterface F) (Sig : Set F) :
    CIClosedUnderDerivation I (ciDeductiveClosure I Sig) :=
  deductiveClosure_closed I Sig

/-! ## R-Maximal Extension Existence via Zorn -/

/-- The collection of deductively closed supersets of `Sig` that stand in the R-relation to
`A`. -/
def rDCSExtensions (I : ChronicleInterface F) (A Sig : Set F) : Set (Set F) :=
  {B | Sig ⊆ B ∧ SetDeductivelyClosed I B ∧ rRelation I A B}

theorem chain_finite_subset_in_element {c : Set (Set F)} {T₀ : Set F}
    (hc_chain : IsChain (· ⊆ ·) c) (hT₀ : T₀ ∈ c)
    (L : List F)
    (hL : ∀ φ ∈ L, φ ∈ ⋃₀ c) :
    ∃ T ∈ c, ∀ φ ∈ L, φ ∈ T := by
  induction L with
  | nil => exact ⟨T₀, hT₀, fun _ h => absurd h List.not_mem_nil⟩
  | cons a L ih =>
    obtain ⟨Ta, hTa, ha⟩ := Set.mem_sUnion.mp (hL a (List.mem_cons_self))
    obtain ⟨TL, hTL, hLTL⟩ := ih (fun φ hφ => hL φ (List.mem_cons_of_mem a hφ))
    rcases hc_chain.total hTa hTL with h_le | h_le
    · exact ⟨TL, hTL, fun φ hφ => by
        rcases List.mem_cons.mp hφ with rfl | h
        · exact h_le ha
        · exact hLTL φ h⟩
    · exact ⟨Ta, hTa, fun φ hφ => by
        rcases List.mem_cons.mp hφ with rfl | h
        · exact ha
        · exact h_le (hLTL φ h)⟩

theorem rMaximal_extension_exists (I : ChronicleInterface F) {A : Set F}
    (_h_mcs : CISetMaximalConsistent I A)
    {Sig : Set F} (h_dcs : SetDeductivelyClosed I Sig) (h_r : rRelation I A Sig) :
    ∃ B : Set F, Sig ⊆ B ∧ rMaximal I A B := by
  have h_S_in : Sig ∈ rDCSExtensions I A Sig := ⟨Set.Subset.refl _, h_dcs, h_r⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset (rDCSExtensions I A Sig) (by
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
      · intro γ δ h_until
        rcases (hc_sub hT₀).2.2 γ δ h_until with h_d | ⟨h_g, h_u⟩
        · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
        · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩, Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r, ?_⟩
  intro C hC_dcs hBC hC_r
  exact hBC.2 (hB_max ⟨Set.Subset.trans hSB hBC.1, hC_dcs, hC_r⟩ hBC.1)

/-! ## R3-Maximal Extension Existence -/

/-- The collection of deductively closed supersets of `Sig` that stand in the R3-relation
between `A` and `C`. -/
def r3DCSExtensions (I : ChronicleInterface F) (A Sig C : Set F) : Set (Set F) :=
  {B | Sig ⊆ B ∧ SetDeductivelyClosed I B ∧ r3Relation I A B C}

theorem r3Maximal_extension_exists (I : ChronicleInterface F) {A C : Set F}
    (_h_mcs_A : CISetMaximalConsistent I A) (_h_mcs_C : CISetMaximalConsistent I C)
    {Sig : Set F} (h_dcs : SetDeductivelyClosed I Sig) (h_r3 : r3Relation I A Sig C) :
    ∃ B : Set F, Sig ⊆ B ∧ R3Maximal I A B C := by
  have h_S_in : Sig ∈ r3DCSExtensions I A Sig C := ⟨Set.Subset.refl _, h_dcs, h_r3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset (r3DCSExtensions I A Sig C) (by
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
        · intro γ δ h_until
          rcases (hc_sub hT₀).2.2.1 γ δ h_until with h_d | ⟨h_g, h_u⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩, Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩
        · intro γ δ h_since
          rcases (hc_sub hT₀).2.2.2 γ δ h_since with h_d | ⟨h_g, h_s⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩, Set.mem_sUnion.mpr ⟨T₀, hT₀, h_s⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r3⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r3, ?_⟩
  intro D hD_dcs hBD hD_r3
  exact hBD.2 (hB_max ⟨Set.Subset.trans hSB hBD.1, hD_dcs, hD_r3⟩ hBD.1)

/-! ## Burgess Absorption (Lemma 2.5) -/

theorem burgessR_absorption (I : ChronicleInterface F) {A D C : Set F}
    (h_mcs_A : CISetMaximalConsistent I A)
    (h_mcs_D : CISetMaximalConsistent I D)
    (β : F)
    (h_β_D : β ∈ D)
    (h_rAD : ciBurgessR I A β D)
    (h_rDC : ciBurgessR I D β C) :
    ciBurgessR I A β C := by
  intro γ h_γ_C
  have h1 : I.untl β γ ∈ D := h_rDC γ h_γ_C
  have h2 : I.and β (I.untl β γ) ∈ D :=
    dcs_conj_closed I (mcs_is_dcs I h_mcs_D) h_β_D h1
  have h3 : I.untl β (I.and β (I.untl β γ)) ∈ A :=
    h_rAD (I.and β (I.untl β γ)) h2
  exact cud_modus_ponens I (mcs_is_dcs I h_mcs_A).2
    (cud_contains_theorems I (mcs_is_dcs I h_mcs_A).2 (I.absorbUntil β γ)) h3

theorem burgessRSince_absorption (I : ChronicleInterface F) {A D C : Set F}
    (h_mcs_A : CISetMaximalConsistent I A)
    (h_mcs_D : CISetMaximalConsistent I D)
    (β : F)
    (h_β_D : β ∈ D)
    (h_rAD : ciBurgessRSince I A β D)
    (h_rDC : ciBurgessRSince I D β C) :
    ciBurgessRSince I A β C := by
  intro γ h_γ_C
  have h1 : I.snce β γ ∈ D := h_rDC γ h_γ_C
  have h2 : I.and β (I.snce β γ) ∈ D :=
    dcs_conj_closed I (mcs_is_dcs I h_mcs_D) h_β_D h1
  have h3 : I.snce β (I.and β (I.snce β γ)) ∈ A :=
    h_rAD (I.and β (I.snce β γ)) h2
  exact cud_modus_ponens I (mcs_is_dcs I h_mcs_A).2
    (cud_contains_theorems I (mcs_is_dcs I h_mcs_A).2 (I.absorbSince β γ)) h3

theorem burgessRSet_absorption (I : ChronicleInterface F) {A D C : Set F} {B : Set F}
    (h_mcs_A : CISetMaximalConsistent I A)
    (h_mcs_D : CISetMaximalConsistent I D)
    (h_sub_D : B ⊆ D)
    (h_rAD : ciBurgessRSet I A B D)
    (h_rDC : ciBurgessRSet I D B C) :
    ciBurgessRSet I A B C := by
  intro β h_β_B
  exact burgessR_absorption I h_mcs_A h_mcs_D β (h_sub_D h_β_B)
    (h_rAD β h_β_B) (h_rDC β h_β_B)

theorem burgessRSetSince_absorption (I : ChronicleInterface F) {A D C : Set F} {B : Set F}
    (h_mcs_A : CISetMaximalConsistent I A)
    (h_mcs_D : CISetMaximalConsistent I D)
    (h_sub_D : B ⊆ D)
    (h_rAD : ciBurgessRSetSince I A B D)
    (h_rDC : ciBurgessRSetSince I D B C) :
    ciBurgessRSetSince I A B C := by
  intro β h_β_B
  exact burgessRSince_absorption I h_mcs_A h_mcs_D β (h_sub_D h_β_B)
    (h_rAD β h_β_B) (h_rDC β h_β_B)

theorem burgessR3_absorption (I : ChronicleInterface F) {A D C : Set F} {B : Set F}
    (h_mcs_A : CISetMaximalConsistent I A)
    (h_mcs_D : CISetMaximalConsistent I D)
    (h_mcs_C : CISetMaximalConsistent I C)
    (h_sub_D : B ⊆ D)
    (h_r3_AD : ciBurgessR3 I A B D)
    (h_r3_DC : ciBurgessR3 I D B C) :
    ciBurgessR3 I A B C :=
  ⟨burgessRSet_absorption I h_mcs_A h_mcs_D h_sub_D h_r3_AD.1 h_r3_DC.1,
   burgessRSetSince_absorption I h_mcs_C h_mcs_D h_sub_D h_r3_DC.2 h_r3_AD.2⟩

/-! ## MCS Contrapositive Helper -/

theorem mcs_contrapositive_mem (I : ChronicleInterface F) {M : Set F}
    (h_mcs : CISetMaximalConsistent I M)
    {φ ψ : F}
    (h_imp : I.imp φ ψ ∈ M) (h_neg_psi : I.imp ψ I.bot ∈ M) :
    I.imp φ I.bot ∈ M := by
  rcases I.negationComplete h_mcs φ with h_phi | h_negphi
  · exact absurd (cud_modus_ponens I (mcs_is_dcs I h_mcs).2 h_imp h_phi) (I.negExcludes h_mcs h_neg_psi)
  · exact h_negphi

/-! ## BurgessR3Maximal Existence -/

/-- Helper: deductive closure of `{δ} ∪ B` inherits `ClosedUnderDerivation`. -/
theorem deductiveClosure_singleton_imp (I : ChronicleInterface F) {B : Set F}
    (h_cud : CIClosedUnderDerivation I B) {δ φ : F}
    (h_delta : δ ∈ B) (h_imp : I.imp δ φ ∈ ciDeductiveClosure I B) :
    φ ∈ B := by
  obtain ⟨L, hL, ⟨d⟩⟩ := h_imp
  exact h_cud (δ :: L) φ
    (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | h
      · exact h_delta
      · exact hL ψ h)
    (I.modusPonens
      (I.weakening L (δ :: L) (I.imp δ φ) d (fun x hx => List.mem_cons_of_mem δ hx))
      (I.assumption (Γ := δ :: L) (φ := δ) (List.mem_cons_self)))

/-- `dcs_neg_insert_consistent`: if `B` is CUD and `φ ∉ B`, then `{¬φ} ∪ B` is consistent. -/
theorem dcs_neg_insert_consistent (I : ChronicleInterface F) {B : Set F}
    (h_cud : CIClosedUnderDerivation I B)
    {φ : F} (h_not_mem : φ ∉ B) :
    CISetConsistent I ({I.imp φ I.bot} ∪ B) := by
  intro L hL ⟨d⟩
  by_cases h_neg_in : I.imp φ I.bot ∈ L
  · have h_sub_reord : ∀ x, x ∈ L → x ∈ I.imp φ I.bot ::
        L.filter (fun y => decide (y ≠ I.imp φ I.bot)) := by
      intro x hx
      by_cases hxn : x = I.imp φ I.bot
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter]; exact ⟨hx, hxn⟩))
    have d_reord := I.weakening L _ I.bot d h_sub_reord
    have d_negneg := I.deductionTheorem _ (I.imp φ I.bot) I.bot d_reord
    have h_filt_in_B : ∀ ψ ∈ L.filter (fun y => decide (y ≠ I.imp φ I.bot)), ψ ∈ B := by
      intro ψ hψ
      have h_and := List.mem_filter.mp hψ
      have h_ne : ψ ≠ I.imp φ I.bot := by simpa using h_and.2
      have h_mem := hL ψ h_and.1
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
      rcases h_mem with rfl | h
      · exact absurd rfl h_ne
      · exact h
    have h_dne := I.doubleNegation φ
    have d_dne_weak := I.weakening [] (L.filter (fun y => decide (y ≠ I.imp φ I.bot))) _
      h_dne (fun _ h => nomatch h)
    have d_phi := I.modusPonens d_dne_weak d_negneg
    exact h_not_mem (h_cud _ φ h_filt_in_B d_phi)
  · have h_L_in_B : ∀ ψ ∈ L, ψ ∈ B := by
      intro ψ hψ
      have h_mem := hL ψ hψ
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
      rcases h_mem with rfl | h
      · exact absurd hψ h_neg_in
      · exact h
    exact (cud_not_mem_is_sdc I h_cud h_not_mem).1 L h_L_in_B ⟨d⟩

theorem burgessR3Maximal_extension_exists (I : ChronicleInterface F) {A C : Set F}
    (_h_mcs_A : CISetMaximalConsistent I A)
    (_h_mcs_C : CISetMaximalConsistent I C)
    {Sig : Set F}
    (h_cud : CIClosedUnderDerivation I Sig)
    (h_br3 : ciBurgessR3 I A Sig C) :
    ∃ B, Sig ⊆ B ∧ CIBurgessR3Maximal I A B C := by
  have h_S_in : Sig ∈ {B | Sig ⊆ B ∧ CIClosedUnderDerivation I B ∧ ciBurgessR3 I A B C} :=
    ⟨Set.Subset.refl _, h_cud, h_br3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset {B | Sig ⊆ B ∧ CIClosedUnderDerivation I B ∧ ciBurgessR3 I A B C} (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · intro L φ hL d
        obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
        exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1 L φ hLT d⟩
      · constructor
        · intro β hβ γ hγ
          obtain ⟨T, hTc, hβT⟩ := Set.mem_sUnion.mp hβ
          exact (hc_sub hTc).2.2.1 β hβT γ hγ
        · intro β hβ γ hγ
          obtain ⟨T, hTc, hβT⟩ := Set.mem_sUnion.mp hβ
          exact (hc_sub hTc).2.2.2 β hβT γ hγ)
  obtain ⟨hSB, hB_cud, hB_br3⟩ := hB_in
  refine ⟨B, hSB, hB_cud, hB_br3, ?_⟩
  intro D hD_cud hBD hD_br3
  exact hBD.2 (hB_max ⟨Set.Subset.trans hSB hBD.1, hD_cud, hD_br3⟩ hBD.1)

/-! ## Left Monotonicity Helpers (BX2G/BX2H at MCS Level) -/

theorem untl_left_mono_G (I : ChronicleInterface F) {A : Set F}
    (h_mcs : CISetMaximalConsistent I A)
    {β₁ β₂ γ : F}
    (h_G_impl : I.allFuture (I.imp β₁ β₂) ∈ A)
    (hUntl : I.untl β₁ γ ∈ A) :
    I.untl β₂ γ ∈ A := by
  have h_step := cud_modus_ponens I (mcs_is_dcs I h_mcs).2
    (cud_contains_theorems I (mcs_is_dcs I h_mcs).2 (I.leftMonoUntilG β₁ β₂ γ)) h_G_impl
  exact cud_modus_ponens I (mcs_is_dcs I h_mcs).2 h_step hUntl

theorem snce_left_mono_H (I : ChronicleInterface F) {A : Set F}
    (h_mcs : CISetMaximalConsistent I A)
    {β₁ β₂ γ : F}
    (h_H_impl : I.allPast (I.imp β₁ β₂) ∈ A)
    (hSnce : I.snce β₁ γ ∈ A) :
    I.snce β₂ γ ∈ A := by
  have h_step := cud_modus_ponens I (mcs_is_dcs I h_mcs).2
    (cud_contains_theorems I (mcs_is_dcs I h_mcs).2 (I.leftMonoSinceH β₁ β₂ γ)) h_H_impl
  exact cud_modus_ponens I (mcs_is_dcs I h_mcs).2 h_step hSnce

theorem untl_left_mono_thm (I : ChronicleInterface F) {A : Set F}
    (h_mcs : CISetMaximalConsistent I A)
    {β₁ β₂ γ : F}
    (hImpl : I.Deriv [] (I.imp β₁ β₂))
    (hUntl : I.untl β₁ γ ∈ A) :
    I.untl β₂ γ ∈ A := by
  have h_G := cud_contains_theorems I (mcs_is_dcs I h_mcs).2 (I.futureNecessitation _ hImpl)
  exact untl_left_mono_G I h_mcs h_G hUntl

theorem snce_left_mono_thm (I : ChronicleInterface F) {A : Set F}
    (h_mcs : CISetMaximalConsistent I A)
    {β₁ β₂ γ : F}
    (hImpl : I.Deriv [] (I.imp β₁ β₂))
    (hSnce : I.snce β₁ γ ∈ A) :
    I.snce β₂ γ ∈ A := by
  have h_H := cud_contains_theorems I (mcs_is_dcs I h_mcs).2 (I.pastNecessitation _ hImpl)
  exact snce_left_mono_H I h_mcs h_H hSnce

/-! ## Duality Helpers for Burgess Lemma 2.3 -/

theorem neg_allPast_neg_to_somePast (I : ChronicleInterface F) {M : Set F}
    (h_mcs : CISetMaximalConsistent I M) (α : F)
    (h : I.imp (I.allPast (I.imp α I.bot)) I.bot ∈ M) :
    I.somePast α ∈ M :=
  I.negAllPastNegToSomePast h_mcs α h

theorem neg_allFuture_neg_to_someFuture (I : ChronicleInterface F) {M : Set F}
    (h_mcs : CISetMaximalConsistent I M) (γ : F)
    (h : I.imp (I.allFuture (I.imp γ I.bot)) I.bot ∈ M) :
    I.someFuture γ ∈ M :=
  I.negAllFutureNegToSomeFuture h_mcs γ h

theorem someFuture_H_neg_G_P_absurd (I : ChronicleInterface F) {M : Set F}
    (h_mcs : CISetMaximalConsistent I M) (α : F)
    (h_F : I.someFuture (I.allPast (I.imp α I.bot)) ∈ M)
    (h_GP : I.allFuture (I.somePast α) ∈ M) : False :=
  I.someFutureHNegGPAbsurd h_mcs α h_F h_GP

theorem somePast_G_neg_H_F_absurd (I : ChronicleInterface F) {M : Set F}
    (h_mcs : CISetMaximalConsistent I M) (γ : F)
    (h_P : I.somePast (I.allFuture (I.imp γ I.bot)) ∈ M)
    (h_HF : I.allPast (I.someFuture γ) ∈ M) : False :=
  I.somePastGNegHFAbsurd h_mcs γ h_P h_HF

/-! ## Burgess Lemma 2.3: burgessR <-> burgessRSince -/

/-- A generic propositional fact: `⊢ ¬(¬ψ ∧ ψ)`, derived from `lceImp`/`rceImp` via the
`deductionTheorem`/`modusPonens`/`weakening`/`assumption` combinators alone (no classical
axiom needed). Used by both directions of Burgess Lemma 2.3. -/
noncomputable def ciNegAndSelfNeg (I : ChronicleInterface F) (ψ : F) :
    I.Deriv [] (I.imp (I.and (I.imp ψ I.bot) ψ) I.bot) := by
  set X := I.and (I.imp ψ I.bot) ψ with hX
  have h1 : I.Deriv [] (I.imp X (I.imp ψ I.bot)) := I.lceImp (I.imp ψ I.bot) ψ
  have h2 : I.Deriv [] (I.imp X ψ) := I.rceImp (I.imp ψ I.bot) ψ
  have d1 : I.Deriv [X] ψ :=
    I.modusPonens (I.weakening [] [X] (I.imp X ψ) h2 (by simp)) (I.assumption (by simp))
  have d2 : I.Deriv [X] (I.imp ψ I.bot) :=
    I.modusPonens (I.weakening [] [X] (I.imp X (I.imp ψ I.bot)) h1 (by simp)) (I.assumption (by simp))
  exact I.deductionTheorem [] X I.bot (I.modusPonens d2 d1)

theorem burgessR_implies_burgessRSince (I : ChronicleInterface F) {A C : Set F}
    (h_mcs_A : CISetMaximalConsistent I A) (h_mcs_C : CISetMaximalConsistent I C)
    {β : F} (h_burgessR : ciBurgessR I A β C) :
    ciBurgessRSince I C β A := by
  intro α hα
  have h_P : I.somePast α ∈ C := by
    rcases I.negationComplete h_mcs_C (I.allPast (I.imp α I.bot)) with h_H | h_notH
    · have hUntl : I.untl β (I.allPast (I.imp α I.bot)) ∈ A := h_burgessR _ h_H
      have h_F : I.someFuture (I.allPast (I.imp α I.bot)) ∈ A :=
        cud_modus_ponens I (mcs_is_dcs I h_mcs_A).2
          (cud_contains_theorems I (mcs_is_dcs I h_mcs_A).2 (I.untilF β (I.allPast (I.imp α I.bot)))) hUntl
      have h_GP : I.allFuture (I.somePast α) ∈ A :=
        cud_modus_ponens I (mcs_is_dcs I h_mcs_A).2
          (cud_contains_theorems I (mcs_is_dcs I h_mcs_A).2 (I.connectFuture α)) hα
      exact False.elim (someFuture_H_neg_G_P_absurd I h_mcs_A α h_F h_GP)
    · exact neg_allPast_neg_to_somePast I h_mcs_C α h_notH
  by_contra h_not
  have h_neg : I.imp (I.snce β α) I.bot ∈ C := by
    rcases I.negationComplete h_mcs_C (I.snce β α) with h | h
    · exact absurd h h_not
    · exact h
  have hUntl : I.untl β (I.imp (I.snce β α) I.bot) ∈ A := h_burgessR _ h_neg
  have h_conj : I.and α (I.untl β (I.imp (I.snce β α) I.bot)) ∈ A :=
    dcs_conj_closed I (mcs_is_dcs I h_mcs_A) hα hUntl
  have h_enriched : I.untl β (I.and (I.imp (I.snce β α) I.bot) (I.snce β α)) ∈ A :=
    cud_modus_ponens I (mcs_is_dcs I h_mcs_A).2
      (cud_contains_theorems I (mcs_is_dcs I h_mcs_A).2
        (I.enrichmentUntil β (I.imp (I.snce β α) I.bot) α)) h_conj
  have h_F := until_implies_F_in_mcs I h_mcs_A h_enriched
  have h_neg_event := ciNegAndSelfNeg I (I.snce β α)
  have h_G_neg := cud_contains_theorems I (mcs_is_dcs I h_mcs_A).2 (I.futureNecessitation _ h_neg_event)
  exact I.someFutureAllFutureNegAbsurd h_mcs_A _ h_F h_G_neg

theorem burgessRSince_implies_burgessR (I : ChronicleInterface F) {A C : Set F}
    (h_mcs_A : CISetMaximalConsistent I A) (h_mcs_C : CISetMaximalConsistent I C)
    {β : F} (h_burgessRSince : ciBurgessRSince I C β A) :
    ciBurgessR I A β C := by
  intro γ hγ
  have h_F : I.someFuture γ ∈ A := by
    rcases I.negationComplete h_mcs_A (I.allFuture (I.imp γ I.bot)) with h_G | h_notG
    · have hSnce : I.snce β (I.allFuture (I.imp γ I.bot)) ∈ C := h_burgessRSince _ h_G
      have h_P : I.somePast (I.allFuture (I.imp γ I.bot)) ∈ C :=
        cud_modus_ponens I (mcs_is_dcs I h_mcs_C).2
          (cud_contains_theorems I (mcs_is_dcs I h_mcs_C).2 (I.sinceP β (I.allFuture (I.imp γ I.bot)))) hSnce
      have h_HF : I.allPast (I.someFuture γ) ∈ C :=
        cud_modus_ponens I (mcs_is_dcs I h_mcs_C).2
          (cud_contains_theorems I (mcs_is_dcs I h_mcs_C).2 (I.connectPast γ)) hγ
      exact False.elim (somePast_G_neg_H_F_absurd I h_mcs_C γ h_P h_HF)
    · exact neg_allFuture_neg_to_someFuture I h_mcs_A γ h_notG
  by_contra h_not
  have h_neg : I.imp (I.untl β γ) I.bot ∈ A := by
    rcases I.negationComplete h_mcs_A (I.untl β γ) with h | h
    · exact absurd h h_not
    · exact h
  have hSnce : I.snce β (I.imp (I.untl β γ) I.bot) ∈ C := h_burgessRSince _ h_neg
  have h_conj : I.and γ (I.snce β (I.imp (I.untl β γ) I.bot)) ∈ C :=
    dcs_conj_closed I (mcs_is_dcs I h_mcs_C) hγ hSnce
  have h_enriched : I.snce β (I.and (I.imp (I.untl β γ) I.bot) (I.untl β γ)) ∈ C :=
    cud_modus_ponens I (mcs_is_dcs I h_mcs_C).2
      (cud_contains_theorems I (mcs_is_dcs I h_mcs_C).2
        (I.enrichmentSince β (I.imp (I.untl β γ) I.bot) γ)) h_conj
  have h_P' := since_implies_P_in_mcs I h_mcs_C h_enriched
  have h_neg_event := ciNegAndSelfNeg I (I.untl β γ)
  have h_H_neg := cud_contains_theorems I (mcs_is_dcs I h_mcs_C).2 (I.pastNecessitation _ h_neg_event)
  exact I.somePastAllPastNegAbsurd h_mcs_C _ h_P' h_H_neg

/-! ## Deductive Closure Singleton Propagation -/

/-- If `L` consists entirely of copies of `η` and `L ⊢ φ`, then `[η] ⊢ φ`. -/
noncomputable def derivationFromSingletonList (I : ChronicleInterface F) {η φ : F} {L : List F}
    (hL : ∀ ψ ∈ L, ψ = η) (d : I.Deriv L φ) :
    I.Deriv [η] φ :=
  I.weakening L [η] φ d (fun ψ hψ => by rw [hL ψ hψ]; simp)

/-- If `φ ∈ deductiveClosure({η})`, then `⊢ η → φ`. -/
theorem deductiveClosure_singleton_imp' (I : ChronicleInterface F) {η φ : F}
    (hφ : φ ∈ ciDeductiveClosure I ({η} : Set F)) :
    Nonempty (I.Deriv [] (I.imp η φ)) := by
  obtain ⟨L, hL_sub, ⟨d⟩⟩ := hφ
  have hL_eq : ∀ ψ ∈ L, ψ = η := fun ψ hψ => Set.mem_singleton_iff.mp (hL_sub ψ hψ)
  exact ⟨I.deductionTheorem [] η φ (derivationFromSingletonList I hL_eq d)⟩

theorem burgessR_of_deductiveClosure_singleton (I : ChronicleInterface F) {A C : Set F} {η : F}
    (h_mcs_A : CISetMaximalConsistent I A)
    (h_burgessR : ciBurgessR I A η C) (φ : F)
    (hφ : φ ∈ ciDeductiveClosure I ({η} : Set F)) :
    ciBurgessR I A φ C := by
  obtain ⟨d⟩ := deductiveClosure_singleton_imp' I hφ
  intro γ hγ
  exact untl_left_mono_thm I h_mcs_A d (h_burgessR γ hγ)

theorem burgessRSince_of_deductiveClosure_singleton (I : ChronicleInterface F) {A C : Set F} {η : F}
    (h_mcs_C : CISetMaximalConsistent I C)
    (h_burgessRSince : ciBurgessRSince I C η A) (φ : F)
    (hφ : φ ∈ ciDeductiveClosure I ({η} : Set F)) :
    ciBurgessRSince I C φ A := by
  obtain ⟨d⟩ := deductiveClosure_singleton_imp' I hφ
  intro γ hγ
  exact snce_left_mono_thm I h_mcs_C d (h_burgessRSince γ hγ)

/-! ## BurgessR3Maximal Existence from Seed -/

theorem burgessR3Maximal_exists_from_seed (I : ChronicleInterface F) (A C : Set F) (η : F)
    (h_mcs_A : CISetMaximalConsistent I A) (h_mcs_C : CISetMaximalConsistent I C)
    (h_burgessR : ciBurgessR I A η C)
    (h_burgessRSince : ciBurgessRSince I C η A)
    (_h_η_A : η ∈ A) :
    ∃ B : Set F, CIBurgessR3Maximal I A B C := by
  have h_dc_cud : CIClosedUnderDerivation I (ciDeductiveClosure I ({η} : Set F)) :=
    deductiveClosure_closed_under_derivation I _
  have h_dc_r3 : ciBurgessR3 I A (ciDeductiveClosure I ({η} : Set F)) C := by
    constructor
    · intro φ hφ
      exact burgessR_of_deductiveClosure_singleton I h_mcs_A h_burgessR φ hφ
    · intro φ hφ
      exact burgessRSince_of_deductiveClosure_singleton I h_mcs_C h_burgessRSince φ hφ
  obtain ⟨B, _, h_B3M⟩ := burgessR3Maximal_extension_exists I h_mcs_A h_mcs_C h_dc_cud h_dc_r3
  exact ⟨B, h_B3M⟩

end Cslib.Logic.Metalogic.Chronicle
