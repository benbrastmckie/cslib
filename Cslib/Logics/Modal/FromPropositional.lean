/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Embedding
public import Cslib.Logics.Propositional.Semantics.Bool
public import Cslib.Logics.Modal.Basic

/-! # Propositional to Modal Embedding

This module defines the structural embedding from propositional logic into modal logic,
instantiating the shared `PropositionalEmbedding` skeleton from
`Cslib.Logics.Propositional.Embedding`.

## Main Definitions

- `PL.Proposition.toModal`: Propositional → Modal (thin wrapper over `PL.Proposition.embed`)

See `Cslib.Logics.Propositional.Embedding` for the shared typeclass, the `embed` skeleton,
and the classical-scope limitation note (Łukasiewicz / [Wajsberg1938] / [McKinsey1939]).
-/

@[expose] public section

namespace Cslib.Logic

/-- `Modal.Proposition` instance for `PropositionalEmbedding`:
atoms map to `Modal.Proposition.atom`. -/
instance instPropositionalEmbeddingModal :
    PropositionalEmbedding Atom (Modal.Proposition Atom) where
  atomEmbed := Modal.Proposition.atom

/-- Embed a propositional formula into modal logic.

Thin wrapper over `PL.Proposition.embed` using the `Modal.Proposition` instance of
`PropositionalEmbedding`. The `and`/`or` cases use the Łukasiewicz encoding via
`{bot, imp}` (classical scope only; see `Cslib.Logics.Propositional.Embedding`). -/
def PL.Proposition.toModal (φ : PL.Proposition Atom) : Modal.Proposition Atom := φ.embed

/-- Coercion from propositional to modal formulas. -/
instance instCoePLToModal : Coe (PL.Proposition Atom) (Modal.Proposition Atom) where
  coe := PL.Proposition.toModal

/-- `toModal` unfolds to the generic `embed` skeleton. Reaches `embed_atom`/`embed_bot`/`embed_imp`
via simp, so the `_atom`/`_bot`/`_imp` restatements are foldable into the generic lemmas. -/
@[simp]
theorem PL.Proposition.toModal_eq_embed (φ : PL.Proposition Atom) :
    φ.toModal = φ.embed := rfl

/-- Embedding preserves and (Lukasiewicz encoding).

The RHS is stated in the *raw* nested `imp`/`bot` shape (not the native `Modal.Proposition.and`
constructor): the shared `PL.Proposition.embed` skeleton
(`Cslib.Logics.Propositional.Embedding`) is classical-scope only and always emits the
Łukasiewicz encoding for `and`/`or`, regardless of whether the target type has a native `and`.
See the module-level docstring there for the encoding rationale.

Not tagged `@[simp]`: since `toModal_eq_embed` is `@[simp]`, this lemma's LHS is no longer in
simp-normal form (it simplifies further via `toModal_eq_embed` + the generic `embed_and`), which
`simpNF` correctly flags as a dead/redundant simp lemma. The statement is retained as a plain
theorem (used by name in `modal_satisfies_toModal_iff_evaluate` below via `simp only`). -/
theorem PL.Proposition.toModal_and (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.and φ₁ φ₂).toModal =
      .imp (.imp φ₁.toModal (.imp φ₂.toModal .bot)) .bot := rfl

/-- Embedding preserves or (Lukasiewicz encoding).

See `PL.Proposition.toModal_and` for why the RHS is the raw nested shape rather than the
native `Modal.Proposition.or` constructor, and for why this is not tagged `@[simp]`. -/
theorem PL.Proposition.toModal_or (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.or φ₁ φ₂).toModal = .imp (.imp φ₁.toModal .bot) φ₂.toModal := rfl

/-- Embedding preserves neg. -/
theorem PL.Proposition.toModal_neg (φ : PL.Proposition Atom) :
    (PL.Proposition.neg φ).toModal = Modal.Proposition.neg φ.toModal := rfl

/-! ## Semantic Coherence

The `toModal` embedding preserves semantic meaning: modal satisfaction of `φ.toModal` at a
world `w` in model `m` coincides with propositional evaluation of `φ` under the valuation
`m.v w`. Since `toModal` never introduces `box`, the accessibility relation plays no role. -/

/-- Bridge lemma: modal satisfaction of `φ.toModal` equals propositional
evaluation under `m.v w`. -/
theorem modal_satisfies_toModal_iff_evaluate
    {World : Type*} {Atom : Type*}
    (m : Modal.Model World Atom) (w : World)
    (φ : PL.Proposition Atom) :
    Modal.Satisfies m w φ.toModal ↔ PL.Evaluate (m.v w) φ := by
  induction φ with
  | atom p => rfl
  | bot => rfl
  | imp φ ψ ih1 ih2 =>
    simp only [PL.Proposition.toModal_eq_embed, PL.Proposition.embed_imp, PL.Evaluate]
    exact ⟨fun h he => ih2.mp (h (ih1.mpr he)),
           fun h hm => ih2.mpr (h (ih1.mp hm))⟩
  | and φ ψ ih1 ih2 =>
    simp only [PL.Proposition.toModal_and, PL.Evaluate]
    constructor
    · intro h
      simp only [Modal.Satisfies] at h
      constructor
      · by_contra hna; exact h (fun ha _ => hna (ih1.mp ha))
      · by_contra hnb; exact h (fun _ hb => hnb (ih2.mp hb))
    · intro ⟨ha, hb⟩
      simp only [Modal.Satisfies]
      intro h; exact h (ih1.mpr ha) (ih2.mpr hb)
  | or φ ψ ih1 ih2 =>
    simp only [PL.Proposition.toModal_or, PL.Evaluate]
    constructor
    · intro h
      simp only [Modal.Satisfies] at h
      by_cases ha : PL.Evaluate (m.v w) φ
      · exact Or.inl ha
      · exact Or.inr (ih2.mp (h (fun hma => ha (ih1.mp hma))))
    · intro h
      simp only [Modal.Satisfies]
      intro hna
      cases h with
      | inl ha => exact absurd (ih1.mpr ha) hna
      | inr hb => exact ih2.mpr hb

/-- Forward direction: every propositional tautology is modally valid under `toModal`. -/
theorem tautology_toModal_valid {Atom : Type*}
    {φ : PL.Proposition Atom} (h : PL.Tautology φ)
    {World : Type*} (m : Modal.Model World Atom) (w : World) :
    Modal.Satisfies m w φ.toModal :=
  (modal_satisfies_toModal_iff_evaluate m w φ).mpr (h (m.v w))

/-- Backward direction: if `φ.toModal` is modally valid over all models, then `φ` is a tautology. -/
theorem toModal_valid_implies_tautology {Atom : Type*}
    {φ : PL.Proposition Atom}
    (h : ∀ (World : Type) (m : Modal.Model World Atom) (w : World),
      Modal.Satisfies m w φ.toModal) :
    PL.Tautology φ := by
  intro v
  let m : Modal.Model Unit Atom := ⟨fun _ _ => False, fun _ => v⟩
  exact (modal_satisfies_toModal_iff_evaluate m () φ).mp (h Unit m ())

/-- Full coherence: `φ` is a propositional tautology iff `φ.toModal` is modally valid. -/
theorem tautology_iff_toModal_valid {Atom : Type*}
    {φ : PL.Proposition Atom} :
    PL.Tautology φ ↔
    (∀ (World : Type) (m : Modal.Model World Atom) (w : World),
      Modal.Satisfies m w φ.toModal) :=
  ⟨fun h _ m w => tautology_toModal_valid h m w, toModal_valid_implies_tautology⟩

end Cslib.Logic
