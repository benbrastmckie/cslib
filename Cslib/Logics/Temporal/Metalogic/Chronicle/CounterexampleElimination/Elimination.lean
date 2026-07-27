/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.Structures
public import Mathlib.Logic.Encodable.Basic

/-! # C5 Counterexample Elimination and Potential Counterexample Interface

Lemma 2.10 C5/C5' elimination, potential counterexample interface,
and walk result structures.
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

/-! ## Lemma 2.10: C5 Counterexample Elimination -/

/--
**Lemma 2.10** (C5 Counterexample Elimination): Given a chronicle satisfying C0
and a C5 counterexample (x, xi, eta), extend the chronicle by adding a new point y
with eta in f'(y).
-/
private lemma eliminateC5Counterexample {χ : Chronicle Atom}
    (h_c0 : χ.c0)
    (ce : C5Counterexample χ)
    :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ x ∈ χ.dom, χ'.f x = χ.f x) ∧
      χ'.c0 ∧
      (∃ y ∈ χ'.dom, ce.x < y ∧ ce.η ∈ χ'.f y) ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  obtain ⟨y, hy_gt, hy_notin⟩ := exists_rat_gt_finset χ.dom
  have h_mcs_x := h_c0 ce.x ce.x_mem
  obtain ⟨_B, C, h_C_mcs, h_η_C, _, _, _⟩ :=
    lemma24 h_mcs_x ce.ξ ce.η ce.until_mem
  refine ⟨⟨fun q => if q = y then C else χ.f q, χ.g, insert y χ.dom⟩,
    Finset.subset_insert y χ.dom, ?_, ?_, ?_, Finset.ssubset_insert hy_notin,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  · intro x hx
    have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
    exact if_neg h_ne
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · simp only [ite_true]; exact h_C_mcs
    · have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
      simp only [h_ne, ite_false]; exact h_c0 x hx
  · refine ⟨y, Finset.mem_insert_self y χ.dom, hy_gt ce.x ce.x_mem, ?_⟩
    simp only [ite_true]
    exact h_η_C

/--
**Lemma 2.10'** (C5' Counterexample Elimination): Mirror of Lemma 2.10 for Since.
-/
private lemma eliminateC5'Counterexample {χ : Chronicle Atom}
    (h_c0 : χ.c0)
    (ce : C5'Counterexample χ) :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ x ∈ χ.dom, χ'.f x = χ.f x) ∧
      χ'.c0 ∧
      (∃ y ∈ χ'.dom, y < ce.x ∧ ce.η ∈ χ'.f y) ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  obtain ⟨y, hy_lt, hy_notin⟩ := exists_rat_lt_finset χ.dom
  have h_mcs_x := h_c0 ce.x ce.x_mem
  have h_P_η : Formula.somePast ce.η ∈ χ.f ce.x := by
    have h_ax :
        DerivationTree FrameClass.Base [] ((Formula.snce ce.ξ ce.η).imp (Formula.somePast ce.η)) :=
      DerivationTree.axiom [] _ (Axiom.since_P ce.ξ ce.η) trivial
    exact temporal_implication_property h_mcs_x
      (theoremInMcs h_mcs_x h_ax) ce.since_mem
  have h_seed := past_temporal_witness_seed_consistent (χ.f ce.x) h_mcs_x ce.η h_P_η
  obtain ⟨C, h_sup, h_C_mcs⟩ := temporal_lindenbaum h_seed
  have h_η_C : ce.η ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton _))
  refine ⟨⟨fun q => if q = y then C else χ.f q, χ.g, insert y χ.dom⟩,
    Finset.subset_insert y χ.dom, ?_, ?_, ?_, Finset.ssubset_insert hy_notin,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  · intro x hx
    have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
    exact if_neg h_ne
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · simp only [ite_true]; exact h_C_mcs
    · have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
      simp only [h_ne, ite_false]; exact h_c0 x hx
  · refine ⟨y, Finset.mem_insert_self y χ.dom, hy_lt ce.x ce.x_mem, ?_⟩
    simp only [ite_true]
    exact h_η_C

/-! ## Potential Counterexample Interface -/

/--
The **kind** of a potential counterexample.
-/
inductive PotentialCounterexampleKind : Type where
  | c4_forward    : PotentialCounterexampleKind
  | c4_backward   : PotentialCounterexampleKind
  | c5_forward    : PotentialCounterexampleKind
  | c5_backward   : PotentialCounterexampleKind
  deriving DecidableEq

instance : Fintype PotentialCounterexampleKind where
  elems := {.c4_forward, .c4_backward, .c5_forward, .c5_backward}
  complete := by intro x; cases x <;> simp

instance : Encodable PotentialCounterexampleKind where
  encode
    | .c4_forward => 0
    | .c4_backward => 1
    | .c5_forward => 2
    | .c5_backward => 3
  decode
    | 0 => some .c4_forward
    | 1 => some .c4_backward
    | 2 => some .c5_forward
    | 3 => some .c5_backward
    | _ => none
  encodek := by intro x; cases x <;> simp

/--
A **potential counterexample** encodes a tuple (x, y, xi, eta, kind).
-/
structure PotentialCounterexample where
  /-- The base point of the potential counterexample. -/
  x : Rat
  /-- The witness candidate point (used for C4 counterexamples). -/
  y : Rat
  /-- The guard formula. -/
  ξ : Formula Atom
  /-- The event formula. -/
  η : Formula Atom
  /-- The kind of counterexample (C4 forward/backward or C5 forward/backward). -/
  kind : PotentialCounterexampleKind

/--
Result type for `eliminatePotentialCounterexample`.
-/
structure EliminationResult (χ : Chronicle Atom) (pc : PotentialCounterexample) where
  /-- The extended chronicle produced by the elimination step. -/
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0
  f_agrees : ∀ x ∈ χ.dom, val.f x = χ.f x
  g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → val.g a b = χ.g a b
  c2' : val.c2'
  c5_forward_witness : pc.kind = .c5_forward → pc.x ∈ χ.dom →
    Formula.untl pc.ξ pc.η ∈ χ.f pc.x →
    ∃ y ∈ val.dom, pc.x < y ∧ pc.η ∈ val.f y ∧
      (∀ a b, Adjacent val.dom a b → pc.x ≤ a → b ≤ y → pc.ξ ∈ val.g a b) ∧
      (∀ w ∈ χ.dom, pc.x < w → w < y → pc.ξ ∈ val.f w) ∧
      (y ∉ χ.dom ∨ ∀ u ∈ val.dom, u ∈ χ.dom)
  c5_backward_witness : pc.kind = .c5_backward → pc.x ∈ χ.dom →
    Formula.snce pc.ξ pc.η ∈ χ.f pc.x →
    ∃ y ∈ val.dom, y < pc.x ∧ pc.η ∈ val.f y ∧
      (∀ a b, Adjacent val.dom a b → y ≤ a → b ≤ pc.x → pc.ξ ∈ val.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pc.x → pc.ξ ∈ val.f w) ∧
      (y ∉ χ.dom ∨ ∀ u ∈ val.dom, u ∈ χ.dom)
  c4_forward_witness : pc.kind = .c4_forward → pc.x ∈ χ.dom → pc.y ∈ χ.dom →
    pc.x < pc.y →
    (Formula.untl pc.ξ pc.η).neg ∈ χ.f pc.x →
    pc.η ∈ χ.f pc.y →
    ∃ z ∈ val.dom, pc.x < z ∧ z < pc.y ∧ pc.ξ.neg ∈ val.f z
  c4_backward_witness : pc.kind = .c4_backward → pc.x ∈ χ.dom → pc.y ∈ χ.dom →
    pc.y < pc.x →
    (Formula.snce pc.ξ pc.η).neg ∈ χ.f pc.x →
    pc.η ∈ χ.f pc.y →
    ∃ z ∈ val.dom, pc.y < z ∧ z < pc.x ∧ pc.ξ.neg ∈ val.f z
  g_sub_f_insert : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.f w
  g_sub_g_new : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.g a w ∧ χ.g a b ⊆ val.g w b
  dom_new_unique : ∀ u v, u ∈ val.dom → u ∉ χ.dom → v ∈ val.dom → v ∉ χ.dom → u = v
  c5_forward_resolved_no_new : pc.kind = .c5_forward → pc.x ∈ χ.dom →
    Formula.untl pc.ξ pc.η ∈ χ.f pc.x →
    (∃ y ∈ χ.dom, pc.x < y ∧ pc.η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → pc.x ≤ a → b ≤ y → pc.ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, pc.x < w → w < y → pc.ξ ∈ χ.f w)) →
    ∀ u ∈ val.dom, u ∈ χ.dom
  c5_backward_resolved_no_new : pc.kind = .c5_backward → pc.x ∈ χ.dom →
    Formula.snce pc.ξ pc.η ∈ χ.f pc.x →
    (∃ y ∈ χ.dom, y < pc.x ∧ pc.η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ pc.x → pc.ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pc.x → pc.ξ ∈ χ.f w)) →
    ∀ u ∈ val.dom, u ∈ χ.dom

/-! ## Walk Result Structures -/

/--
Result of the C5 forward recursive walk (Burgess 2.10 induction).
-/
structure C5ForwardWalkResult (χ : Chronicle Atom) (ξ η : Formula Atom) (start : Rat) where
  /-- The extended chronicle produced by the forward walk. -/
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0
  c2' : val.c2'
  f_agrees : ∀ x ∈ χ.dom, val.f x = χ.f x
  g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → val.g a b = χ.g a b
  /-- The new domain point witnessing the Until formula after `start`. -/
  witness : Rat
  witness_mem : witness ∈ val.dom
  witness_gt : start < witness
  witness_event : η ∈ val.f witness
  witness_guard : ∀ a b, Adjacent val.dom a b → start ≤ a → b ≤ witness → ξ ∈ val.g a b
  g_sub_f_insert : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.f w
  g_sub_g_new : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.g a w ∧ χ.g a b ⊆ val.g w b
  dom_new_unique : ∀ u v, u ∈ val.dom → u ∉ χ.dom → v ∈ val.dom → v ∉ χ.dom → u = v
  new_point_after : ∀ w ∈ val.dom, w ∉ χ.dom → start < w
  domain_guard : ∀ w ∈ χ.dom, start < w → w < witness → ξ ∈ val.f w
  witness_not_old : witness ∉ χ.dom

/--
Result of the C5 backward recursive walk (mirror for Since).
-/
structure C5BackwardWalkResult (χ : Chronicle Atom) (ξ η : Formula Atom) (start : Rat) where
  /-- The extended chronicle produced by the backward walk. -/
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0
  c2' : val.c2'
  f_agrees : ∀ x ∈ χ.dom, val.f x = χ.f x
  g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → val.g a b = χ.g a b
  /-- The new domain point witnessing the Since formula before `start`. -/
  witness : Rat
  witness_mem : witness ∈ val.dom
  witness_lt : witness < start
  witness_event : η ∈ val.f witness
  witness_guard : ∀ a b, Adjacent val.dom a b → witness ≤ a → b ≤ start → ξ ∈ val.g a b
  g_sub_f_insert : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.f w
  g_sub_g_new : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.g a w ∧ χ.g a b ⊆ val.g w b
  dom_new_unique : ∀ u v, u ∈ val.dom → u ∉ χ.dom → v ∈ val.dom → v ∉ χ.dom → u = v
  new_point_before : ∀ w ∈ val.dom, w ∉ χ.dom → w < start
  domain_guard : ∀ w ∈ χ.dom, witness < w → w < start → ξ ∈ val.f w
  witness_not_old : witness ∉ χ.dom


end Cslib.Logic.Temporal.Metalogic.Chronicle

end
