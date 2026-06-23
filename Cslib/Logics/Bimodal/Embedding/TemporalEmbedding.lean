/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Syntax.Formula
public import Cslib.Logics.Bimodal.Syntax.Formula

/-! # Temporal to Bimodal Embedding

This module defines the structural embedding from temporal logic formulas into bimodal logic
formulas. The embedding maps each temporal primitive constructor to the corresponding bimodal
constructor.

## Main Definitions

- `Temporal.Formula.toBimodal`: Temporal → Bimodal (structural recursion on 5 constructors)
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a temporal formula into bimodal logic. -/
def Temporal.Formula.toBimodal : Temporal.Formula Atom → Bimodal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.toBimodal) (φ₂.toBimodal)
  | .untl φ₂ φ₁ => .untl (φ₂.toBimodal) (φ₁.toBimodal)
  | .snce φ₂ φ₁ => .snce (φ₂.toBimodal) (φ₁.toBimodal)

/-- Coercion from temporal to bimodal formulas. -/
instance instCoeTemporalToBimodal : Coe (Temporal.Formula Atom) (Bimodal.Formula Atom) where
  coe := Temporal.Formula.toBimodal

/-- Embedding preserves atom. -/
@[simp, scoped grind =]
theorem Temporal.Formula.toBimodal_atom (p : Atom) :
    (Temporal.Formula.atom p : Temporal.Formula Atom).toBimodal = Bimodal.Formula.atom p := rfl

/-- Embedding preserves bot. -/
@[simp, scoped grind =]
theorem Temporal.Formula.toBimodal_bot :
    (Temporal.Formula.bot : Temporal.Formula Atom).toBimodal = Bimodal.Formula.bot := rfl

/-- Embedding preserves imp. -/
@[simp, scoped grind =]
theorem Temporal.Formula.toBimodal_imp (φ₁ φ₂ : Temporal.Formula Atom) :
    (Temporal.Formula.imp φ₁ φ₂).toBimodal =
      Bimodal.Formula.imp φ₁.toBimodal φ₂.toBimodal := rfl

/-- Embedding preserves untl. -/
@[simp, scoped grind =]
theorem Temporal.Formula.toBimodal_untl (φ₁ φ₂ : Temporal.Formula Atom) :
    (Temporal.Formula.untl φ₂ φ₁).toBimodal =
      Bimodal.Formula.untl φ₂.toBimodal φ₁.toBimodal := rfl

/-- Embedding preserves snce. -/
@[simp, scoped grind =]
theorem Temporal.Formula.toBimodal_snce (φ₁ φ₂ : Temporal.Formula Atom) :
    (Temporal.Formula.snce φ₂ φ₁).toBimodal =
      Bimodal.Formula.snce φ₂.toBimodal φ₁.toBimodal := rfl

/-- Embedding preserves neg. -/
theorem Temporal.Formula.toBimodal_neg (φ : Temporal.Formula Atom) :
    (Temporal.Formula.neg φ).toBimodal = Bimodal.Formula.neg φ.toBimodal := rfl

end Cslib.Logic
