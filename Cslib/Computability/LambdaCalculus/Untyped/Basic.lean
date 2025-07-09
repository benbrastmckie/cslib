/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Data.Finset.Basic

/-! # λ-calculus

The untyped λ-calculus.

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

end LambdaCalculus
