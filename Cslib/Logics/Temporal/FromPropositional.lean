/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Temporal.Syntax.Formula

/-! # Propositional to Temporal Embedding

This module defines the structural embedding from propositional logic into temporal logic.
The embedding maps each propositional primitive constructor to the corresponding temporal
constructor, establishing Propositional as a sub-logic of Temporal.

## Main Definitions

- `PL.Proposition.toTemporal`: Propositional → Temporal (maps atom/bot/imp)
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula into temporal logic.

The `and` and `or` cases use Lukasiewicz encoding into `{atom, bot, imp, untl, snce}`:
- `A ∧ B` maps to `¬(A → ¬B)` = `(A → (B → ⊥)) → ⊥`
- `A ∨ B` maps to `¬A → B` = `(A → ⊥) → B` -/
def PL.Proposition.toTemporal : PL.Proposition Atom → Temporal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.toTemporal) (φ₂.toTemporal)
  | .and φ₁ φ₂ => .imp (.imp φ₁.toTemporal (.imp φ₂.toTemporal .bot)) .bot
  | .or φ₁ φ₂ => .imp (.imp φ₁.toTemporal .bot) φ₂.toTemporal

/-- Coercion from propositional to temporal formulas. -/
instance instCoePLToTemporal : Coe (PL.Proposition Atom) (Temporal.Formula Atom) where
  coe := PL.Proposition.toTemporal

/-- Embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toTemporal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toTemporal = Temporal.Formula.atom p := rfl

/-- Embedding preserves bot. -/
@[simp]
theorem PL.Proposition.toTemporal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toTemporal = Temporal.Formula.bot := rfl

/-- Embedding preserves imp. -/
@[simp]
theorem PL.Proposition.toTemporal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toTemporal = Temporal.Formula.imp φ₁.toTemporal φ₂.toTemporal := rfl

/-- Embedding preserves and (Lukasiewicz encoding). -/
@[simp]
theorem PL.Proposition.toTemporal_and (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.and φ₁ φ₂).toTemporal =
    .imp (.imp φ₁.toTemporal (.imp φ₂.toTemporal .bot)) .bot := rfl

/-- Embedding preserves or (Lukasiewicz encoding). -/
@[simp]
theorem PL.Proposition.toTemporal_or (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.or φ₁ φ₂).toTemporal =
    .imp (.imp φ₁.toTemporal .bot) φ₂.toTemporal := rfl

/-- Embedding preserves neg. -/
theorem PL.Proposition.toTemporal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toTemporal = Temporal.Formula.neg φ.toTemporal := rfl

end Cslib.Logic
