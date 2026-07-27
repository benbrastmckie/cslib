/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
public import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation
public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion
public import Cslib.Foundations.Logic.Metalogic.Chronicle.CounterexampleElimination.Structures
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-! # C5/C5' Counterexample Structures and Fresh-Rational Helpers

C5/C5' counterexample structures, the fresh-rational helper lemmas,
and BurgessR3Maximal helper lemmas used by the Temporal chronicle construction.

## Status (Chronicle Consolidation)

The fresh-rational Finset helpers and the `BurgessR3Maximal_g_content_sub`/`_sdc`/
`_bot_not_mem` MCS-level lemmas are now thin re-exports of
`Cslib.Foundations.Logic.Metalogic.Chronicle.CounterexampleElimination.Structures`.

`C5Counterexample`/`C5'Counterexample` stay logic-local, verbatim (see the generic
module's docstring for the `Chronicle`-locality rationale), as does
`burgessR3Maximal_from_h_content_sub` (forward dependency on a not-yet-made
duality-theorem consolidation decision for the shared Chronicle construction) and
`c2'_preserved_on_old_adjacent`.
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

/-! ## BurgessR3Maximal Helper Lemmas -/

/--
**BurgessR3Maximal implies gContent(A) ⊆ C**: If BurgessR3Maximal(A, B, C) holds with
A and C both MCS, then gContent(A) ⊆ C.
-/
theorem BurgessR3Maximal_g_content_sub {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal A B C)
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C) :
    gContent A ⊆ C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_g_content_sub
    temporalChronicleInterface h_r3m h_mcs_A h_mcs_C

/--
**BurgessR3Maximal implies SetDeductivelyClosed** when some formula is not in B.
-/
theorem BurgessR3Maximal_sdc {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal A B C)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) :
    SetDeductivelyClosed B :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_sdc
    temporalChronicleInterface h_r3m h_not_mem

/--
**BurgessR3Maximal excludes ⊥ when B is consistent**.
-/
private theorem BurgessR3Maximal_bot_not_mem {A B C : Set (Formula Atom)}
    (_h_r3m : BurgessR3Maximal A B C)
    (h_cons : Temporal.SetConsistent B) :
    Formula.bot ∉ B :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_bot_not_mem
    temporalChronicleInterface _h_r3m h_cons

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
