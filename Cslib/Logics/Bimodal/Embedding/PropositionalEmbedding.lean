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
bimodal logic formulas, instantiating the shared `PropositionalEmbedding` skeleton from
`Cslib.Logics.Propositional.Embedding`, and proves that the embedding diamond commutes.

## Main Definitions

- `PL.Proposition.toBimodal`: Propositional → Bimodal (thin wrapper over `PL.Proposition.embed`)

## Main Results

- `PL.Proposition.toModal_toBimodal`: PL → Modal → Bimodal = PL → Bimodal
- `PL.Proposition.toTemporal_toBimodal`: PL → Temporal → Bimodal = PL → Bimodal
- `PL.Proposition.embedding_commutes`: both composite paths agree

See `Cslib.Logics.Propositional.Embedding` for the shared typeclass, the `embed` skeleton,
and the classical-scope limitation note (Łukasiewicz / [Wajsberg1938] / [McKinsey1939]).
The `and`/`or` Łukasiewicz encodings are the same as those used in `toModal` and `toTemporal`,
which is why all three commuting-diamond lemmas close by `induction φ <;> simp [*]`.
-/

@[expose] public section

namespace Cslib.Logic

/-- `Bimodal.Formula` instance for `PropositionalEmbedding`:
atoms map to `Bimodal.Formula.atom`. -/
instance instPropositionalEmbeddingBimodal :
    PropositionalEmbedding Atom (Bimodal.Formula Atom) where
  atomEmbed := Bimodal.Formula.atom

/-- Embed a propositional formula directly into bimodal logic.

Thin wrapper over `PL.Proposition.embed` using the `Bimodal.Formula` instance of
`PropositionalEmbedding`. The `and`/`or` cases use the Łukasiewicz encoding via
`{bot, imp}` — the same encoding as `toModal` and `toTemporal`, which is why the
commuting-diamond lemmas below close by `induction φ <;> simp [*]`.
(Classical scope only; see `Cslib.Logics.Propositional.Embedding`.) -/
def PL.Proposition.toBimodal (φ : PL.Proposition Atom) : Bimodal.Formula Atom := φ.embed

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
