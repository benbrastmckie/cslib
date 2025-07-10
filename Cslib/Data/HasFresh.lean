/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.SuccPred.Basic

universe u

/-- A type `α` has a computable `fresh` function if it is always possible, for any finite set of `α`, to compute a fresh element not in the set. -/
class HasFresh (α : Type u) where
  /-- Given a finite set, returns an element not in the set. -/
  fresh : Finset α → α
  /-- Proof that `fresh` returns a fresh element for its input set. -/
  fresh_notMem (s : Finset α) : fresh s ∉ s

/-- `ℕ` has a computable fresh function. -/
instance instHasFreshNat : HasFresh ℕ where
  -- We could also use Nat.find here.
  fresh s :=
    match s.max with
    | ⊥ => 0
    | some n => n.succ
  fresh_notMem s := by
    cases h : s.max
    case bot =>
      simp [Finset.max] at h
      simp
      exact h 0
    case coe n =>
      simp
      have h' : s.max < ↑(n + 1) := by simp_all only [WithBot.coe_lt_coe, Nat.lt_add_one]
      apply Finset.notMem_of_max_lt_coe h'
