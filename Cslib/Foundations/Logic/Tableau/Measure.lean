/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Shared Tableau Termination Measure Arithmetic

This module collects the logic-agnostic pure-`Nat`/`List` arithmetic shared by base-3 damped
worklist termination measures across different tableau calculi (e.g. the classical propositional
tableau and the modal K tableau finite-model-property termination argument). None of the
declarations here reference any specific logic's syntax, rules, or branch representation.

## Main Definitions

- `geomCap`: The exact geometric-sum capacity `Σ_{i=0}^{k} Sf^i`, used to bound the number of
  worlds/nodes a bounded-branching, bounded-depth tree can spawn.

## Main Results

- `sum_map_le_length_mul`: A summed bounded image is bounded by the list length times the bound.
- `geomCap_add_one_le_pow`, `geomCap_zero_le_pow`, `geomCap_le_pow`: `geomCap` is bounded by a
  power of the branching factor.
- `geomCap_mul_eq_succ_sub_one`: The defining recursion of `geomCap`, restated multiplicatively.
- `pow3_two_add_one_le`, `pow3_add_one_le`: Base-3 strict-decrease arithmetic facts used to show
  a single tableau expansion step strictly decreases a base-3 damped worklist measure.
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-- Helper: if every image element of `f` on `l` is bounded by `c`, the summed image is
bounded by `l.length * c`. Self-contained (avoids hunting for the exact Mathlib name). -/
lemma sum_map_le_length_mul {α : Type*} (l : List α) (f : α → Nat) (c : Nat)
    (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : f x ≤ c := h x (by simp)
    have hxs : (xs.map f).sum ≤ xs.length * c := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have heq : (xs.length + 1) * c = xs.length * c + c := by ring
    omega

/-! ## Geometric Capacity -/

/-- The exact geometric-sum capacity: `geomCap Sf k = Σ_{i=0}^{k} Sf^i`, the maximum size of
a tree with branching factor `≤ Sf` and depth `≤ k` (root included). Defined recursively
(`1` plus `Sf` copies of the one-shallower capacity) rather than via `Finset.sum` to keep the
per-step potential-drop arithmetic (`geomCap_succ`) a definitional unfold. -/
def geomCap (Sf : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + Sf * geomCap Sf k

@[simp] lemma geomCap_zero (Sf : Nat) : geomCap Sf 0 = 1 := rfl

lemma geomCap_succ (Sf k : Nat) :
    geomCap Sf (k + 1) = 1 + Sf * geomCap Sf k := rfl

/-- For branching factor `Sf ≥ 2`, the capacity stays strictly below `Sf ^ (k+1)` (with room
`≥ 1`, stated additively to avoid `Nat` truncated-subtraction pitfalls): the exact geometric
sum `Σ_{i≤k} Sf^i` satisfies `Σ + 1 ≤ Sf^{k+1}` once the branching factor is `≥ 2`. -/
lemma geomCap_add_one_le_pow {Sf : Nat} (hSf : 2 ≤ Sf) :
    ∀ k, geomCap Sf k + 1 ≤ Sf ^ (k + 1)
  | 0 => by simp only [geomCap_zero, Nat.zero_add, pow_one]; omega
  | k + 1 => by
    have ih := geomCap_add_one_le_pow hSf k
    have hmul : Sf * (geomCap Sf k + 1) ≤ Sf * Sf ^ (k + 1) :=
      Nat.mul_le_mul_left Sf ih
    have heq : Sf * Sf ^ (k + 1) = Sf ^ (k + 2) := by ring
    have hexpand : Sf * (geomCap Sf k + 1) = Sf * geomCap Sf k + Sf := by ring
    have hkey : Sf * geomCap Sf k + Sf ≤ Sf ^ (k + 2) := by
      rw [← heq, ← hexpand]; exact hmul
    have hsucc : geomCap Sf (k + 1) + 1 = Sf * geomCap Sf k + 2 := by
      rw [geomCap_succ]; ring
    have hgoal : k + 1 + 1 = k + 2 := rfl
    rw [hsucc, hgoal]
    omega

/-- Degenerate branching factor `Sf ≤ 1` forces capacity `1` regardless of `k` when `k = 0`
(the only case this lemma is ever invoked with, since `Sf = 1` forces depth `0` in the calling
context's structural argument). -/
lemma geomCap_zero_le_pow {Sf : Nat} (hSf : 1 ≤ Sf) : geomCap Sf 0 ≤ Sf ^ 1 := by
  simp only [geomCap_zero, pow_one]; omega

/-- Unconditional capacity bound: `geomCap Sf k ≤ Sf ^ (k+1)`, for any `Sf ≥ 1` with
`Sf = 1 → k = 0` (the only shape that ever arises in the calling contexts). -/
lemma geomCap_le_pow {Sf k : Nat} (hSf : 1 ≤ Sf) (hdeg : Sf = 1 → k = 0) :
    geomCap Sf k ≤ Sf ^ (k + 1) := by
  rcases Nat.lt_or_ge Sf 2 with hlt | hge
  · have hSf1 : Sf = 1 := by omega
    subst hSf1
    have hk0 : k = 0 := hdeg rfl
    subst hk0
    simpa using geomCap_zero_le_pow (Sf := 1) (le_refl 1)
  · have := geomCap_add_one_le_pow hge k
    omega

/-- The key arithmetic identity closing a mint-step potential-drop computation (the `rank ≥ 2`
sub-case, and — via `geomCap_zero`, `Sf * 1 = Sf * geomCap Sf 0 = geomCap Sf 1 - 1` — also
usable as the base case): `Sf * geomCap Sf k = geomCap Sf (k+1) - 1`, an immediate unfold of
`geomCap`'s defining recursion. -/
lemma geomCap_mul_eq_succ_sub_one (Sf k : Nat) :
    Sf * geomCap Sf k = geomCap Sf (k + 1) - 1 := by
  rw [geomCap_succ]; omega

/-! ## Base-3 Strict-Decrease Arithmetic -/

/-- Base-3 decrease for a BETA (branching) step: two children of `R`-value `≤ C - 1` plus the
saved unit. -/
lemma pow3_two_add_one_le {a0 a1 C : Nat} (hC : 1 ≤ C) (h0 : a0 ≤ C - 1)
    (h1 : a1 ≤ C - 1) :
    3 ^ a0 + 3 ^ a1 + 1 ≤ 3 ^ C := by
  have h0' : 3 ^ a0 ≤ 3 ^ (C - 1) := Nat.pow_le_pow_right (by omega) h0
  have h1' : 3 ^ a1 ≤ 3 ^ (C - 1) := Nat.pow_le_pow_right (by omega) h1
  have hone : 1 ≤ 3 ^ (C - 1) := Nat.one_le_pow _ _ (by omega)
  rw [show C = C - 1 + 1 from (Nat.sub_add_cancel hC).symm, pow_succ]
  omega

/-- Base-3 decrease for an ALPHA/persistent step: one child of `R`-value `≤ C - 1` plus the
saved unit. -/
lemma pow3_add_one_le {a0 C : Nat} (hC : 1 ≤ C) (h0 : a0 ≤ C - 1) :
    3 ^ a0 + 1 ≤ 3 ^ C := by
  have h0' : 3 ^ a0 ≤ 3 ^ (C - 1) := Nat.pow_le_pow_right (by omega) h0
  have hone : 1 ≤ 3 ^ (C - 1) := Nat.one_le_pow _ _ (by omega)
  rw [show C = C - 1 + 1 from (Nat.sub_add_cancel hC).symm, pow_succ]
  omega

end Cslib.Logic.Tableau

end
