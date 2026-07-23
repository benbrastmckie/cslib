/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Embedding
public import Cslib.Logics.Temporal.Syntax.Formula

/-! # Propositional to Temporal Embedding

This module defines the structural embedding from propositional logic into temporal logic,
instantiating the shared `PropositionalEmbedding` skeleton from
`Cslib.Logics.Propositional.Embedding`.

## Main Definitions

- `PL.Proposition.toTemporal`: Propositional → Temporal (thin wrapper over `PL.Proposition.embed`)

See `Cslib.Logics.Propositional.Embedding` for the shared typeclass, the `embed` skeleton,
and the classical-scope limitation note (Łukasiewicz / [Wajsberg1938] / [McKinsey1939]).
-/

@[expose] public section

namespace Cslib.Logic

/-- `Temporal.Formula` instance for `PropositionalEmbedding`:
atoms map to `Temporal.Formula.atom`. -/
instance instPropositionalEmbeddingTemporal :
    PropositionalEmbedding Atom (Temporal.Formula Atom) where
  atomEmbed := Temporal.Formula.atom

/-- Embed a propositional formula into temporal logic.

Thin wrapper over `PL.Proposition.embed` using the `Temporal.Formula` instance of
`PropositionalEmbedding`. The `and`/`or` cases use the Łukasiewicz encoding via
`{bot, imp}` (classical scope only; see `Cslib.Logics.Propositional.Embedding`). -/
def PL.Proposition.toTemporal (φ : PL.Proposition Atom) : Temporal.Formula Atom := φ.embed

/-- Coercion from propositional to temporal formulas. -/
instance instCoePLToTemporal : Coe (PL.Proposition Atom) (Temporal.Formula Atom) where
  coe := PL.Proposition.toTemporal

/-- `toTemporal` unfolds to the generic `embed` skeleton. Reaches
`embed_atom`/`embed_bot`/`embed_imp` via simp, so the `_atom`/`_bot`/`_imp` restatements are
foldable into the generic lemmas. -/
@[simp, scoped grind =]
theorem PL.Proposition.toTemporal_eq_embed (φ : PL.Proposition Atom) :
    φ.toTemporal = φ.embed := rfl

/-- Embedding preserves and (Lukasiewicz encoding).

Not tagged `@[simp]`: since `toTemporal_eq_embed` is `@[simp]`, this lemma's LHS is no longer in
simp-normal form (it simplifies further via `toTemporal_eq_embed` + the generic `embed_and`),
which `simpNF` correctly flags as a dead/redundant simp lemma. `grind` is retained since it is a
separate automation mechanism unaffected by simp normal-form. -/
@[scoped grind =]
theorem PL.Proposition.toTemporal_and (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.and φ₁ φ₂).toTemporal =
    .imp (.imp φ₁.toTemporal (.imp φ₂.toTemporal .bot)) .bot := rfl

/-- Embedding preserves or (Lukasiewicz encoding). See `toTemporal_and` for why this is not
tagged `@[simp]`. -/
@[scoped grind =]
theorem PL.Proposition.toTemporal_or (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.or φ₁ φ₂).toTemporal =
    .imp (.imp φ₁.toTemporal .bot) φ₂.toTemporal := rfl

/-- Embedding preserves neg. -/
theorem PL.Proposition.toTemporal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toTemporal = Temporal.Formula.neg φ.toTemporal := rfl

end Cslib.Logic
