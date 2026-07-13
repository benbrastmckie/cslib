/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Bimodal.Syntax.Formula

/-! # Modal to Bimodal Embedding

This module defines the structural embedding from modal logic formulas into bimodal logic formulas.
The embedding maps each modal primitive constructor to the corresponding bimodal constructor.

## Main Definitions

- `Modal.Proposition.toBimodal`: Modal → Bimodal (structural recursion on 4 constructors)
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a modal formula into bimodal logic.

`Modal.Proposition` has native `and`/`or`/`diamond` constructors (task 441), while
`Bimodal.Formula` still encodes them as derived Łukasiewicz `abbrev`s (`Formula.and`/`.or`/
`.diamond`, `Formula.lean`); the embedding maps native Modal connectives to the corresponding
Bimodal `abbrev`. -/
def Modal.Proposition.toBimodal : Modal.Proposition Atom → Bimodal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.toBimodal) (φ₂.toBimodal)
  | .and φ₁ φ₂ => .and (φ₁.toBimodal) (φ₂.toBimodal)
  | .or φ₁ φ₂ => .or (φ₁.toBimodal) (φ₂.toBimodal)
  | .box φ => .box (φ.toBimodal)
  | .diamond φ => .diamond (φ.toBimodal)

/-- Coercion from modal to bimodal formulas. -/
instance instCoeModalToBimodal : Coe (Modal.Proposition Atom) (Bimodal.Formula Atom) where
  coe := Modal.Proposition.toBimodal

/-- Embedding preserves atom. -/
@[simp]
theorem Modal.Proposition.toBimodal_atom (p : Atom) :
    (Modal.Proposition.atom p : Modal.Proposition Atom).toBimodal = Bimodal.Formula.atom p := rfl

/-- Embedding preserves bot. -/
@[simp]
theorem Modal.Proposition.toBimodal_bot :
    (Modal.Proposition.bot : Modal.Proposition Atom).toBimodal = Bimodal.Formula.bot := rfl

/-- Embedding preserves imp. -/
@[simp]
theorem Modal.Proposition.toBimodal_imp (φ₁ φ₂ : Modal.Proposition Atom) :
    (Modal.Proposition.imp φ₁ φ₂).toBimodal =
      Bimodal.Formula.imp φ₁.toBimodal φ₂.toBimodal := rfl

/-- Embedding preserves and. -/
@[simp]
theorem Modal.Proposition.toBimodal_and (φ₁ φ₂ : Modal.Proposition Atom) :
    (Modal.Proposition.and φ₁ φ₂).toBimodal =
      Bimodal.Formula.and φ₁.toBimodal φ₂.toBimodal := rfl

/-- Embedding preserves or. -/
@[simp]
theorem Modal.Proposition.toBimodal_or (φ₁ φ₂ : Modal.Proposition Atom) :
    (Modal.Proposition.or φ₁ φ₂).toBimodal =
      Bimodal.Formula.or φ₁.toBimodal φ₂.toBimodal := rfl

/-- Embedding preserves box. -/
@[simp]
theorem Modal.Proposition.toBimodal_box (φ : Modal.Proposition Atom) :
    (Modal.Proposition.box φ).toBimodal = Bimodal.Formula.box φ.toBimodal := rfl

/-- Embedding preserves neg. -/
theorem Modal.Proposition.toBimodal_neg (φ : Modal.Proposition Atom) :
    (Modal.Proposition.neg φ).toBimodal = Bimodal.Formula.neg φ.toBimodal := rfl

/-- Embedding preserves diamond. -/
theorem Modal.Proposition.toBimodal_diamond (φ : Modal.Proposition Atom) :
    (Modal.Proposition.diamond φ).toBimodal = Bimodal.Formula.diamond φ.toBimodal := rfl

end Cslib.Logic
