/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-- Class for substitution relations. -/
class Substitution (α : Type u) (β : Type v) where
  /-- Substitution function. Replaces `x` in `t` with `t'`. -/
  subst (t : α) (x : β) (t' : α) : α

notation t:max "[" x ":=" t' "]" => Substitution.subst t x t'
