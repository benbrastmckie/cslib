/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rel

/-! # λ-calculus

The untyped λ-calculus.

WIP.

-/

universe u

variable {Var : Type u}

namespace LambdaCalculus

/-- Syntax of terms. -/
inductive Term {Var : Type u} : Type u where
| var (x : Var)
| abs (x : Var) (m : @Term Var)
| app (m n : @Term Var)
deriving DecidableEq

/-- Free variables. -/
def Term.fv [DecidableEq Var] (m : @Term Var) : Finset Var :=
  match m with
  | var x => {x}
  | abs x m => m.fv.erase x
  | app m n => m.fv ∪ n.fv

/-- Bound variables. -/
def Term.bv [DecidableEq Var] (m : @Term Var) : Finset Var :=
  match m with
  | var _ => ∅
  | abs x m => m.bv ∪ {x} -- Could also be `insert x m.bv`
  | app m n => m.bv ∪ n.bv

/-- Variable names (free and bound) in a term. -/
def Term.vars [DecidableEq Var] (m : @Term Var) : Finset Var :=
  m.fv ∪ m.bv

/-- Capture-avoiding substitution, as an inference system. -/
inductive Term.Subst [DecidableEq Var] : @Term Var → Var → @Term Var → @Term Var → Prop where
| varHit : (var x).Subst x r r
| varMiss : x ≠ y → (var y).Subst x r (var y)
| absShadow : (abs x m).Subst x r (abs x m)
| absIn : x ≠ y → y ∉ r.fv → m.Subst x r m' → (abs y m).Subst x r (abs y m')
| app : m.Subst x r m' → n.Subst x r n' → (app m n).Subst x r (app m' n')

-- WIP: functional version of Subst
-- def Term.subst [DecidableEq Var] (m : @Term Var) (x : Var) (r : @Term Var) : @Term Var :=
--   match m with
--   | var y => if y = x then r else var y
--   | abs y m' =>
--     if y = x then
--       abs y m'
--     else if y ∉ r.fv then
--       abs y (m.subst x r)
--     else
--       let z := (abs y m').freshVar
--       abs z ((m.subst y (var z)).subst x r)
--   | app m1 m2 => app (m1.subst x r) (m2.subst x r)

/-
TODO: Would be nice to have a (syntax-agnostic) class for what a Substitution is, with the expected
notation m[x := n]. Then show that Term.subst is an instance. See `Substitution`.
-/

/-- Contexts. -/
inductive Context {Var : Type u} : Type u where
| hole
| abs (x : Var) (c : @Context Var)
| appL (c : @Context Var) (m : @Term Var)
| appR (m : @Term Var) (c : @Context Var)
deriving DecidableEq

/-- Replaces the hole in a `Context` with a `Term`. -/
def Context.fill (c : @Context Var) (m : @Term Var) : @Term Var :=
  match c with
  | hole => m
  | abs x c => Term.abs x (c.fill m)
  | appL c n => Term.app (c.fill m) n
  | appR n c => Term.app n (c.fill m)

/-- Any `Term` can be obtained by filling a `Context` with a variable. This proves that `Context`
completely captures the syntax of terms. -/
theorem Context.complete (m : @Term Var) :
  ∃ (c : @Context Var) (x : Var), m = (c.fill (Term.var x)) := by
  induction m
  case var x =>
    exists hole
    simp [fill]
  case abs x n ih =>
    obtain ⟨c', y, ih⟩ := ih
    exists Context.abs x c'
    exists y
    simp [ih, fill]
  case app n1 n2 ih1 ih2 =>
    obtain ⟨c1, x1, ih1⟩ := ih1
    exists Context.appL c1 n2
    exists x1
    simp [ih1, fill]

open Term

/-- α-equivalence. WIP. -/
inductive AlphaEquiv [DecidableEq Var] : Rel (@Term Var) (@Term Var) where
-- The α-axiom
| ax {m : @Term Var} {x y : Var} : y ∉ m.fv → m.Subst x (var y) m' → AlphaEquiv (abs x m) (abs y m')
-- Equivalence relation rules
| refl : AlphaEquiv m m
| symm : AlphaEquiv m n → AlphaEquiv n m -- TODO: This might be provable as a theorem.
| trans : AlphaEquiv m1 m2 → AlphaEquiv m2 m3 → AlphaEquiv m1 m3
-- Context closure
| ctx {c : @Context Var} {m n : @Term Var} : AlphaEquiv m n → AlphaEquiv (c.fill m) (c.fill n)

/- Notation for α-equivalence.

TODO: make this a class, we want to use the same notation for different languages. -/
-- notation m:max " =α " n:max => AlphaEquiv m n

end LambdaCalculus
