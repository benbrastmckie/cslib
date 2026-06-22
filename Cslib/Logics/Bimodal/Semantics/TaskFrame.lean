/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.SetLike

/-!
# TaskFrame - Task Frame Structure for TM Semantics

This module defines task frames, the fundamental semantic structures for bimodal logic TM.

## Main Definitions

- `TaskFrame D`: Structure with world states, times of type `D`, task relation, and constraints
- `TaskFrame.nullity_identity`: Zero duration iff identity
- `TaskFrame.forward_comp`: Forward compositionality (restricted to non-negative durations)
- `TaskFrame.converse`: Temporal symmetry
- `TaskFrame.nullity`: Derived reflexivity theorem

## Main Results

- Example task frames for testing and demonstrations (polymorphic over time type)
- `FiniteTaskFrame`: Frame with finitely many world states
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

/--
Task frame for bimodal logic TM.

A task frame consists of:
- A type of world states
- A type `D` of temporal durations with ordered additive group structure
- A task relation connecting world states via timed tasks
- Nullity identity: zero-duration task iff identity (w = u)
- Forward compositionality: tasks compose for non-negative durations
- Converse: taskRel w d u iff taskRel u (-d) w
-/
structure TaskFrame (D : Type*) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] where
  /-- Type of world states -/
  WorldState : Type
  /-- Task relation: `taskRel w x u` means u is reachable from w by task of duration x -/
  taskRel : WorldState → D → WorldState → Prop
  /-- Zero-duration task relates exactly identical states. -/
  nullity_identity : ∀ w u, taskRel w 0 u ↔ w = u
  /-- Forward compositionality: tasks compose for non-negative durations. -/
  forward_comp : ∀ w u v x y, 0 ≤ x → 0 ≤ y → taskRel w x u → taskRel u y v → taskRel w (x + y) v
  /-- Converse: task relation is symmetric under duration negation. -/
  converse : ∀ w d u, taskRel w d u ↔ taskRel u (-d) w

namespace TaskFrame

variable {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/--
Derived nullity: zero-duration task is reflexive.
-/
theorem nullity (F : TaskFrame D) (w : F.WorldState) : F.taskRel w 0 w :=
  F.nullity_identity w w |>.mpr rfl

/--
Derived backward compositionality: tasks compose in the backward direction.
-/
theorem backward_comp (F : TaskFrame D) (w u v : F.WorldState) (x y : D)
    (hx : x ≤ 0) (hy : y ≤ 0)
    (h1 : F.taskRel w x u) (h2 : F.taskRel u y v) :
    F.taskRel w (x + y) v := by
  have h1' : F.taskRel u (-x) w := F.converse w x u |>.mp h1
  have h2' : F.taskRel v (-y) u := F.converse u y v |>.mp h2
  have hx' : 0 ≤ -x := neg_nonneg.mpr hx
  have hy' : 0 ≤ -y := neg_nonneg.mpr hy
  have h3 : F.taskRel v ((-y) + (-x)) w := F.forward_comp v u w (-y) (-x) hy' hx' h2' h1'
  have h4 : -y + -x = -(x + y) := by simp [neg_add_rev, add_comm]
  rw [h4] at h3
  exact F.converse w (x + y) v |>.mpr h3

/--
Simple unit-based task frame for testing.
-/
def trivialFrame {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] : TaskFrame D where
  WorldState := Unit
  taskRel := fun _ _ _ => True
  nullity_identity := fun _ _ => ⟨fun _ => Subsingleton.elim _ _, fun _ => trivial⟩
  forward_comp := fun _ _ _ _ _ _ _ _ _ => trivial
  converse := fun _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩

/--
Identity task frame: task relation is identity.
-/
def identityFrame (W : Type) {D : Type*} [AddCommGroup D]
    [LinearOrder D] [IsOrderedAddMonoid D] : TaskFrame D where
  WorldState := W
  taskRel := fun w x u => w = u ∧ x = 0
  nullity_identity := fun w u => by
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, rfl⟩
  forward_comp := by
    intros w u v x y _ _ hwu huv
    obtain ⟨h1, h2⟩ := hwu
    obtain ⟨h3, h4⟩ := huv
    subst h1 h3
    simp [h2, h4]
  converse := fun w d u => by
    constructor
    · intro ⟨h1, h2⟩
      subst h1 h2
      simp
    · intro ⟨h1, h2⟩
      constructor
      · exact h1.symm
      · exact neg_eq_zero.mp h2

/--
Natural number based task frame.
-/
def natFrame {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] : TaskFrame D where
  WorldState := Nat
  taskRel := fun w d u => d ≠ 0 ∨ w = u
  nullity_identity := fun w u => by
    constructor
    · intro h
      cases h with
      | inl h => exact absurd rfl h
      | inr h => exact h
    · intro h
      right; exact h
  forward_comp := fun w u v x y hx hy h1 h2 => by
    cases h1 with
    | inl hxne =>
      left
      intro heq
      have hy_eq : y = -x := (neg_eq_of_add_eq_zero_right heq).symm
      have h1 : 0 ≤ -x := hy_eq ▸ hy
      have h2 : x ≤ 0 := neg_nonneg.mp h1
      have h3 : x = 0 := le_antisymm h2 hx
      exact hxne h3
    | inr hw =>
      cases h2 with
      | inl hyne =>
        left
        intro heq
        have hx_eq : x = -y := (neg_eq_of_add_eq_zero_left heq).symm
        have h1 : 0 ≤ -y := hx_eq ▸ hx
        have h2 : y ≤ 0 := neg_nonneg.mp h1
        have h3 : y = 0 := le_antisymm h2 hy
        exact hyne h3
      | inr hu => right; exact hw.trans hu
  converse := fun w d u => by
    constructor
    · intro h
      cases h with
      | inl hd => left; simp [hd]
      | inr heq => right; exact heq.symm
    · intro h
      cases h with
      | inl hnd => left; exact neg_ne_zero.mp hnd
      | inr heq => right; exact heq.symm

end TaskFrame

/--
A task frame with finitely many world states.
-/
structure FiniteTaskFrame (D : Type*) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    extends TaskFrame D where
  /-- Proof that the set of world states is finite -/
  finite_world : Finite WorldState

namespace FiniteTaskFrame

variable {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/--
Coercion from a finite task frame to its underlying task frame.
-/
instance : Coe (FiniteTaskFrame D) (TaskFrame D) where
  coe F := F.toTaskFrame

end FiniteTaskFrame

end Cslib.Logic.Bimodal
