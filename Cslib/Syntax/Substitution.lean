/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-- Class for substitution relations. WIP. -/
class Substitution where
  subst : α → β → γ

notation t:max "[" x ":=" t' "]" => Substitution.subst t x t'
