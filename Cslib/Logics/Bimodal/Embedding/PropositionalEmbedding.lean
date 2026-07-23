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
which is why all three commuting-diamond lemmas close by
`induction φ <;> simp [*, HasImp.imp, HasBot.bot] <;> tauto` (the explicit `HasImp.imp`/
`HasBot.bot` unfolds are needed once `toModal`/`toTemporal`/`toBimodal` are simp-normalized to
the typeclass-generic `embed`, so the retained per-target `_and`/`_or` restatements can still
match against the underlying concrete constructors).
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
commuting-diamond lemmas below close by
`induction φ <;> simp [*, HasImp.imp, HasBot.bot] <;> tauto`.
(Classical scope only; see `Cslib.Logics.Propositional.Embedding`.) -/
def PL.Proposition.toBimodal (φ : PL.Proposition Atom) : Bimodal.Formula Atom := φ.embed

/-- Coercion from propositional to bimodal formulas. -/
instance instCoePLToBimodal : Coe (PL.Proposition Atom) (Bimodal.Formula Atom) where
  coe := PL.Proposition.toBimodal

/-- `toBimodal` unfolds to the generic `embed` skeleton. Reaches
`embed_atom`/`embed_bot`/`embed_imp` via simp, so the `_atom`/`_bot`/`_imp` restatements are
foldable into the generic lemmas. -/
@[simp]
theorem PL.Proposition.toBimodal_eq_embed (φ : PL.Proposition Atom) :
    φ.toBimodal = φ.embed := rfl

/-- Direct embedding preserves and (Lukasiewicz encoding).

Not tagged `@[simp]`: since `toBimodal_eq_embed` is `@[simp]`, this lemma's LHS is no longer in
simp-normal form (it simplifies further via `toBimodal_eq_embed` + the generic `embed_and`),
which `simpNF` correctly flags as a dead/redundant simp lemma. -/
theorem PL.Proposition.toBimodal_and (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.and φ₁ φ₂).toBimodal =
      .imp (.imp φ₁.toBimodal (.imp φ₂.toBimodal .bot)) .bot := rfl

/-- Direct embedding preserves or (Lukasiewicz encoding). See `toBimodal_and` for why this is not
tagged `@[simp]`. -/
theorem PL.Proposition.toBimodal_or (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.or φ₁ φ₂).toBimodal =
      .imp (.imp φ₁.toBimodal .bot) φ₂.toBimodal := rfl

/-- Direct embedding preserves neg. -/
theorem PL.Proposition.toBimodal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toBimodal = Bimodal.Formula.neg φ.toBimodal := rfl

/-- The diagram PL → Modal → Bimodal commutes with the direct path PL → Bimodal.

Not tagged `@[simp]`: its LHS `φ.toModal.toBimodal` is no longer in simp-normal form once
`toModal_eq_embed` is `@[simp]` (`simpNF` flags it as dead/redundant). -/
theorem PL.Proposition.toModal_toBimodal (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*, HasImp.imp, HasBot.bot] <;> tauto

/-- The diagram PL → Temporal → Bimodal commutes with the direct path PL → Bimodal. See
`toModal_toBimodal` for why this is not tagged `@[simp]`. -/
theorem PL.Proposition.toTemporal_toBimodal (φ : PL.Proposition Atom) :
    φ.toTemporal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*, HasImp.imp, HasBot.bot] <;> tauto

/-- The embedding diamond commutes:
    going through Modal is the same as going through Temporal. -/
theorem PL.Proposition.embedding_commutes (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toTemporal.toBimodal := by
  induction φ <;> simp [*, HasImp.imp, HasBot.bot] <;> tauto

end Cslib.Logic
