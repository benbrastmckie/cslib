/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
public import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation
public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-! # C5/C5' Counterexample Structures and Fresh-Rational Helpers

C5/C5' counterexample structures, the fresh-rational helper lemmas,
and BurgessR3Maximal helper lemmas used by the Temporal chronicle construction.
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

set_option linter.unusedSimpArgs false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

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
  until_mem : (ξ U η) ∈ χ.f x
  no_witness : ¬∃ y ∈ χ.dom, x < y ∧ η ∈ χ.f y ∧
    ∀ z ∈ χ.dom, x < z → z < y → ξ ∈ χ.f z ∧ (ξ U η) ∈ χ.f z

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
  since_mem : (ξ S η) ∈ χ.f x
  no_witness : ¬∃ y ∈ χ.dom, y < x ∧ η ∈ χ.f y ∧
    ∀ z ∈ χ.dom, y < z → z < x → ξ ∈ χ.f z ∧ (ξ S η) ∈ χ.f z

/-! ## Helper: Finding Fresh Rationals -/

/--
There exists a rational strictly greater than all elements of a finite set
of rationals. (The rationals are unbounded above.)
-/
theorem exists_rat_gt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, s < q) ∧ q ∉ fs := by
  by_cases h : fs.Nonempty
  · refine ⟨fs.max' h + 1, ?_, ?_⟩
    · intro s hs
      calc s ≤ fs.max' h := Finset.le_max' fs s hs
        _ < fs.max' h + 1 := lt_add_one _
    · intro hmem
      have h1 := Finset.le_max' fs _ hmem
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact ⟨0, fun s hs => absurd hs (by simp), (by simp)⟩

/--
There exists a rational strictly less than all elements of a finite set
of rationals. (The rationals are unbounded below.)
-/
theorem exists_rat_lt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, q < s) ∧ q ∉ fs := by
  by_cases h : fs.Nonempty
  · refine ⟨fs.min' h - 1, ?_, ?_⟩
    · intro s hs
      calc fs.min' h - 1 < fs.min' h := sub_one_lt _
        _ ≤ s := Finset.min'_le fs s hs
    · intro hmem
      have h1 := Finset.min'_le fs _ hmem
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact ⟨0, fun s hs => absurd hs (by simp), (by simp)⟩

/--
There exists a rational strictly between x and y that is NOT in a finite set fs.
-/
private theorem exists_rat_between_not_in_finset (fs : Finset Rat) (x y : Rat) (hxy : x < y) :
    ∃ z : Rat, x < z ∧ z < y ∧ z ∉ fs := by
  set T := fs.filter (fun s => x < s ∧ s < y) with hT_def
  by_cases hT : T.Nonempty
  · set t := T.min' hT with ht_def
    have ht_mem : t ∈ T := Finset.min'_mem T hT
    have ht_prop : x < t ∧ t < y := by
      rw [hT_def] at ht_mem; exact (Finset.mem_filter.mp ht_mem).2
    set z := (x + t) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzt : z < t := by linarith
    have hzy : z < y := lt_trans hzt ht_prop.2
    refine ⟨z, hxz, hzy, ?_⟩
    intro hz_mem
    have hz_in_T : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    have : t ≤ z := Finset.min'_le T z hz_in_T
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    set z := (x + y) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzy : z < y := by linarith
    refine ⟨z, hxz, hzy, ?_⟩
    intro hz_mem
    have : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    rw [hT] at this
    exact absurd this (by simp)

/-! ## BurgessR3Maximal Helper Lemmas -/

/--
**BurgessR3Maximal implies gContent(A) ⊆ C**: If BurgessR3Maximal(A, B, C) holds with
A and C both MCS, then gContent(A) ⊆ C.
-/
theorem BurgessR3Maximal_g_content_sub {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal A B C)
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C) :
    gContent A ⊆ C := by
  intro φ hφ
  change Formula.allFuture φ ∈ A at hφ
  by_contra h_not_C
  have h_neg_C : (¬φ) ∈ C := by
    rcases temporal_negation_complete h_mcs_C φ with h | h
    · exact absurd h h_not_C
    · exact h
  set top := Formula.bot.imp Formula.bot with top_def
  have h_top_B : top ∈ B :=
    cud_contains_theorems h_r3m.1 (identity Formula.bot)
  have hUntl : Formula.untl top φ.neg ∈ A :=
    h_r3m.2.1.1 top h_top_B φ.neg h_neg_C
  have h_F_neg : (𝐅(¬φ)) ∈ A :=
    until_implies_F_in_mcs h_mcs_A hUntl
  have h_dni : DerivationTree FrameClass.Base [] (φ.imp φ.neg.neg) := by
    have h1 : DerivationTree FrameClass.Base [φ.neg, φ] Formula.bot :=
      DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
        (DerivationTree.assumption _ φ.neg (by simp))
        (DerivationTree.assumption _ φ (by simp))
    have h2 : DerivationTree FrameClass.Base [φ] φ.neg.neg :=
      deductionTheorem [φ] φ.neg Formula.bot h1
    exact deductionTheorem [] φ φ.neg.neg h2
  have h_G_dni : DerivationTree FrameClass.Base [] (Formula.allFuture (φ.imp φ.neg.neg)) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_kd := tempKDistDerived φ φ.neg.neg
  have h1 := theoremInMcs h_mcs_A h_G_dni
  have h2 := theoremInMcs h_mcs_A h_kd
  have h3 := temporal_implication_property h_mcs_A h2 h1
  have h_G_nn : Formula.allFuture φ.neg.neg ∈ A :=
    temporal_implication_property h_mcs_A h3 hφ
  exact someFuture_allFuture_neg_absurd h_mcs_A φ.neg h_F_neg h_G_nn

/--
**BurgessR3Maximal implies SetDeductivelyClosed** when some formula is not in B.
-/
theorem BurgessR3Maximal_sdc {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal A B C)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) :
    SetDeductivelyClosed B :=
  cud_not_mem_is_sdc h_r3m.1 h_not_mem

/--
**BurgessR3Maximal excludes ⊥ when B is consistent**.
-/
private theorem BurgessR3Maximal_bot_not_mem {A B C : Set (Formula Atom)}
    (_h_r3m : BurgessR3Maximal A B C)
    (h_cons : Temporal.SetConsistent B) :
    Formula.bot ∉ B := by
  intro h_bot
  exact h_cons [Formula.bot] (fun φ hφ => by simp at hφ; rw [hφ]; exact h_bot)
    ⟨DerivationTree.assumption [Formula.bot] Formula.bot (by simp)⟩

/--
Helper: for adjacent pairs in a chronicle satisfying c2', when inserting a new point
that splits an existing adjacent pair, the old adjacent pairs that don't involve the
split are preserved.
-/
private theorem c2'_preserved_on_old_adjacent {χ χ' : Chronicle Atom}
    (h_c2' : χ.c2')
    (h_f_agrees : ∀ x ∈ χ.dom, χ'.f x = χ.f x)
    (h_g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b)
    (_h_dom_sub : χ.dom ⊆ χ'.dom)
    {a b : Rat}
    (_h_adj' : Adjacent χ'.dom a b)
    (h_a_old : a ∈ χ.dom) (h_b_old : b ∈ χ.dom)
    (h_adj_old : Adjacent χ.dom a b) :
    BurgessR3Maximal (χ'.f a) (χ'.g a b) (χ'.f b) := by
  rw [h_f_agrees a h_a_old, h_g_agrees a b h_a_old h_b_old, h_f_agrees b h_b_old]
  exact h_c2' a b h_adj_old

/--
**BurgessR3Maximal from hContent subset (backward direction)**:
If hContent(C) ⊆ A (i.e., H(φ) ∈ C → φ ∈ A), then ∃ B, BurgessR3Maximal(A, B, C).
-/
private theorem burgessR3Maximal_from_h_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_hc : hContent C ⊆ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal A B C := by
  have h_gc : gContent A ⊆ C :=
    h_content_sub_imp_g_content_sub' h_mcs_A h_mcs_C h_hc
  -- Construct burgessR3 seed using top = ⊥ → ⊥
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with top_def
  have h_top_A : top ∈ A :=
    theoremInMcs h_mcs_A (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_bR : burgessR A top C := by
    intro γ hγ
    -- gContent(A) ⊆ C gives F(γ) ∈ A via connect_past + connect_future
    have h_ax_cp : DerivationTree FrameClass.Base [] (γ.imp (Formula.allPast (Formula.someFuture γ))) :=
      DerivationTree.axiom [] _ (Axiom.connect_past γ) trivial
    have h_HF : Formula.allPast (Formula.someFuture γ) ∈ C :=
      temporal_implication_property h_mcs_C
        (theoremInMcs h_mcs_C h_ax_cp) hγ
    have h_F : (𝐅γ) ∈ A := h_hc h_HF
    have h_bx12 : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).imp (Formula.untl top γ)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact temporal_implication_property h_mcs_A
      (theoremInMcs h_mcs_A h_bx12) h_F
  have h_bRS : burgessRSince C top A := by
    intro α hα
    have h_P : (𝐏α) ∈ C := by
      by_contra h_not_P
      have h_neg_P : (Formula.somePast α).neg ∈ C :=
        (temporal_negation_complete h_mcs_C _).resolve_left h_not_P
      -- Use connect_future: α → G(P(α)), so α ∈ A → P(α) ∈ gContent(A) ⊆ C.
      have h_ax_cf : DerivationTree FrameClass.Base [] (α.imp (Formula.allFuture (Formula.somePast α))) :=
        DerivationTree.axiom [] _ (Axiom.connect_future α) trivial
      have h_GP : Formula.allFuture (Formula.somePast α) ∈ A :=
        temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_ax_cf) hα
      have h_P_in_C : (𝐏α) ∈ C := h_gc h_GP
      exact h_not_P h_P_in_C
    have h_bx12' : DerivationTree FrameClass.Base [] ((Formula.somePast α).imp (Formula.snce top α)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact temporal_implication_property h_mcs_C
      (theoremInMcs h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A


end Cslib.Logic.Temporal.Metalogic.Chronicle

end
