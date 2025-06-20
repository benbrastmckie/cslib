/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

variable (Name : Type u) (Constant : Type v)

namespace CCS

inductive Act : Type u where
| name (a : Name)
| coname (a : Name)
| τ
deriving DecidableEq

inductive Process : Type (max u v) where
| nil
| pre (μ : Act Name) (p : Process)
| par (p q : Process)
| choice (p q : Process)
| res (a : Name) (p : Process)
| const (c : Constant)
deriving DecidableEq

def Act.co (μ : Act Name) : Act Name :=
  match μ with
  | name a => coname a
  | coname a => name a
  | τ => τ

theorem Act.co.involution (μ : Act Name) : μ.co.co = μ := by
  cases μ <;> simp only [Act.co]

end CCS
