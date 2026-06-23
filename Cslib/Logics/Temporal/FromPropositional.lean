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

- `PL.Proposition.toTemporal`: Propositional → Temporal (maps atom/bot/imp/and/or)

## Encoding Rationale

`PL.Proposition` has five primitive constructors `{atom, bot, imp, and, or}`, while
`Temporal.Formula` has only `{atom, bot, imp, untl, snce}`. The `and`/`or` cases must
therefore be encoded using a formula built from the available temporal connectives. The
Lukasiewicz encodings `and φ ψ := ¬(φ → ¬ψ)` and `or φ ψ := ¬φ → ψ` are classically
sound and are used here because this embedding targets classical temporal logic (BX).

Note: This differs from the propositional level, where `and`/`or` are native constructors
with `HasAnd`/`HasOr` instances. The embedding necessarily uses Lukasiewicz because
`Temporal.Formula` lacks native `and`/`or` constructors.

## Limitations

**Classical scope only.** The Lukasiewicz encodings `¬(φ → ¬ψ)` for `∧` and `¬φ → ψ` for `∨`
are classically valid but not intuitionistically valid. This embedding is therefore sound for
classical temporal logics (e.g., BX) but **not** for intuitionistic temporal logics. If CSLib
adds intuitionistic temporal logic in the future, a separate embedding respecting the native
`and`/`or` constructors will be required.
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula into temporal logic.

The `atom`, `bot`, and `imp` cases map to the corresponding `Temporal.Formula` constructors.
The `and` and `or` cases use the Lukasiewicz encoding into `{atom, bot, imp, untl, snce}`
because `Temporal.Formula` has no native `and`/`or` constructors:
- `A ∧ B` maps to `¬(A → ¬B)` = `(A → (B → ⊥)) → ⊥`
- `A ∨ B` maps to `¬A → B` = `(A → ⊥) → B`

These encodings are classically equivalent to `∧` and `∨` but not intuitionistically
([Wajsberg1938], [McKinsey1939]); this embedding therefore targets classical temporal logic. -/
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
@[simp, scoped grind =]
theorem PL.Proposition.toTemporal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toTemporal = Temporal.Formula.atom p := rfl

/-- Embedding preserves bot. -/
@[simp, scoped grind =]
theorem PL.Proposition.toTemporal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toTemporal = Temporal.Formula.bot := rfl

/-- Embedding preserves imp. -/
@[simp, scoped grind =]
theorem PL.Proposition.toTemporal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toTemporal = Temporal.Formula.imp φ₁.toTemporal φ₂.toTemporal := rfl

/-- Embedding preserves and (Lukasiewicz encoding). -/
@[simp, scoped grind =]
theorem PL.Proposition.toTemporal_and (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.and φ₁ φ₂).toTemporal =
    .imp (.imp φ₁.toTemporal (.imp φ₂.toTemporal .bot)) .bot := rfl

/-- Embedding preserves or (Lukasiewicz encoding). -/
@[simp, scoped grind =]
theorem PL.Proposition.toTemporal_or (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.or φ₁ φ₂).toTemporal =
    .imp (.imp φ₁.toTemporal .bot) φ₂.toTemporal := rfl

/-- Embedding preserves neg. -/
theorem PL.Proposition.toTemporal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toTemporal = Temporal.Formula.neg φ.toTemporal := rfl

end Cslib.Logic
