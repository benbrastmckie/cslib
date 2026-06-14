/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Temporal.FromPropositional
public import Cslib.Logics.Bimodal.Embedding.ModalEmbedding
public import Cslib.Logics.Bimodal.Embedding.TemporalEmbedding

/-! # Propositional to Bimodal Embedding

This module defines the direct structural embedding from propositional logic formulas into
bimodal logic formulas, and proves that the embedding diamond commutes: going through
Modal is the same as going through Temporal.

The PL-to-Modal and PL-to-Temporal embeddings are imported from `Modal.FromPropositional`
and `Temporal.FromPropositional` respectively.

## Main Definitions

- `PL.Proposition.toBimodal`: Propositional → Bimodal (maps atom/bot/imp/and/or)

## Main Results

- `PL.Proposition.toModal_toBimodal`: PL → Modal → Bimodal = PL → Bimodal
- `PL.Proposition.toTemporal_toBimodal`: PL → Temporal → Bimodal = PL → Bimodal
- `PL.Proposition.embedding_commutes`: both composite paths agree

## Encoding Rationale

`PL.Proposition` has five primitive constructors `{atom, bot, imp, and, or}`, while
`Bimodal.Formula` has only `{atom, bot, imp, box, untl, snce}`. The `and`/`or` cases
must therefore be encoded using a formula built from the available bimodal connectives.
The Lukasiewicz encodings (`and φ ψ := ¬(φ → ¬ψ)`, `or φ ψ := ¬φ → ψ`) are used here
for consistency with the Modal and Temporal embeddings, and because this embedding targets
classical bimodal logic. These encodings are classically equivalent to `∧`/`∨` but not
intuitionistically ([Wajsberg1938], [McKinsey1939]).
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula directly into bimodal logic.

The `atom`, `bot`, and `imp` cases map to the corresponding `Bimodal.Formula` constructors.
The `and` and `or` cases use the Lukasiewicz encoding because `Bimodal.Formula` lacks
native `and`/`or` constructors (its primitives are `{atom, bot, imp, box, untl, snce}`):
- `A ∧ B` maps to `¬(A → ¬B)` = `(A → (B → ⊥)) → ⊥`
- `A ∨ B` maps to `¬A → B` = `(A → ⊥) → B`

This is consistent with the `toModal` and `toTemporal` embeddings, which use the same
Lukasiewicz encoding for the same reason. The diamond commutativity theorems below confirm
all three paths agree. -/
def PL.Proposition.toBimodal : PL.Proposition Atom → Bimodal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp φ₁.toBimodal φ₂.toBimodal
  | .and φ₁ φ₂ => .imp (.imp φ₁.toBimodal (.imp φ₂.toBimodal .bot)) .bot
  | .or φ₁ φ₂ => .imp (.imp φ₁.toBimodal .bot) φ₂.toBimodal

/-- Coercion from propositional to bimodal formulas. -/
instance instCoePLToBimodal : Coe (PL.Proposition Atom) (Bimodal.Formula Atom) where
  coe := PL.Proposition.toBimodal

/-- Direct embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toBimodal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toBimodal = Bimodal.Formula.atom p := rfl

/-- Direct embedding preserves bot. -/
@[simp]
theorem PL.Proposition.toBimodal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toBimodal = Bimodal.Formula.bot := rfl

/-- Direct embedding preserves imp. -/
@[simp]
theorem PL.Proposition.toBimodal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toBimodal =
      Bimodal.Formula.imp φ₁.toBimodal φ₂.toBimodal := rfl

/-- Direct embedding preserves and (Lukasiewicz encoding). -/
@[simp]
theorem PL.Proposition.toBimodal_and (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.and φ₁ φ₂).toBimodal =
      .imp (.imp φ₁.toBimodal (.imp φ₂.toBimodal .bot)) .bot := rfl

/-- Direct embedding preserves or (Lukasiewicz encoding). -/
@[simp]
theorem PL.Proposition.toBimodal_or (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.or φ₁ φ₂).toBimodal =
      .imp (.imp φ₁.toBimodal .bot) φ₂.toBimodal := rfl

/-- Direct embedding preserves neg. -/
@[simp]
theorem PL.Proposition.toBimodal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toBimodal = Bimodal.Formula.neg φ.toBimodal := rfl

/-- The diagram PL → Modal → Bimodal commutes with the direct path PL → Bimodal. -/
@[simp]
theorem PL.Proposition.toModal_toBimodal (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*]

/-- The diagram PL → Temporal → Bimodal commutes with the direct path PL → Bimodal. -/
@[simp]
theorem PL.Proposition.toTemporal_toBimodal (φ : PL.Proposition Atom) :
    φ.toTemporal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*]

/-- The embedding diamond commutes:
    going through Modal is the same as going through Temporal. -/
theorem PL.Proposition.embedding_commutes (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toTemporal.toBimodal := by
  simp

end Cslib.Logic
