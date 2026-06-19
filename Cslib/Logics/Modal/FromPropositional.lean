/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.Semantics.Bool
public import Cslib.Logics.Modal.Basic

/-! # Propositional to Modal Embedding

This module defines the structural embedding from propositional logic into modal logic.
The embedding maps each propositional primitive constructor to the corresponding modal
constructor, establishing Propositional as a sub-logic of Modal.

## Main Definitions

- `PL.Proposition.toModal`: Propositional → Modal (maps atom/bot/imp/and/or)

## Encoding Rationale

`PL.Proposition` has five primitive constructors `{atom, bot, imp, and, or}`, while
`Modal.Proposition` has only `{atom, bot, imp, box}`. The `and`/`or` cases must therefore
be encoded using a formula built from the available modal connectives. The Lukasiewicz
encodings `and φ ψ := ¬(φ → ¬ψ)` and `or φ ψ := ¬φ → ψ` are classically sound and
are used here because this embedding targets classical modal logic.

Note: This differs from the propositional level, where `and`/`or` are native constructors
with `HasAnd`/`HasOr` instances. The embedding necessarily uses Lukasiewicz because
`Modal.Proposition` lacks native `and`/`or` constructors.
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula into modal logic.

The `atom`, `bot`, and `imp` cases map to the corresponding `Modal.Proposition` constructors.
The `and` and `or` cases use the Lukasiewicz encoding into `{atom, bot, imp, box}` because
`Modal.Proposition` has no native `and`/`or` constructors:
- `A ∧ B` maps to `¬(A → ¬B)` = `(A → (B → ⊥)) → ⊥`
- `A ∨ B` maps to `¬A → B` = `(A → ⊥) → B`

These encodings are classically equivalent to `∧` and `∨` but not intuitionistically
([Wajsberg1938], [McKinsey1939]); this embedding therefore targets classical modal logic. -/
def PL.Proposition.toModal : PL.Proposition Atom → Modal.Proposition Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.toModal) (φ₂.toModal)
  | .and φ₁ φ₂ => φ₁.toModal.and φ₂.toModal
  | .or φ₁ φ₂ => φ₁.toModal.or φ₂.toModal

/-- Coercion from propositional to modal formulas. -/
instance instCoePLToModal : Coe (PL.Proposition Atom) (Modal.Proposition Atom) where
  coe := PL.Proposition.toModal

/-- Embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toModal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toModal = Modal.Proposition.atom p := rfl

/-- Embedding preserves bot. -/
@[simp]
theorem PL.Proposition.toModal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toModal = Modal.Proposition.bot := rfl

/-- Embedding preserves imp. -/
@[simp]
theorem PL.Proposition.toModal_imp (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.imp φ₁ φ₂).toModal = Modal.Proposition.imp φ₁.toModal φ₂.toModal := rfl

/-- Embedding preserves and (Lukasiewicz encoding). -/
@[simp]
theorem PL.Proposition.toModal_and (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.and φ₁ φ₂).toModal = φ₁.toModal.and φ₂.toModal := rfl

/-- Embedding preserves or (Lukasiewicz encoding). -/
@[simp]
theorem PL.Proposition.toModal_or (φ₁ φ₂ : PL.Proposition Atom) :
    (PL.Proposition.or φ₁ φ₂).toModal = φ₁.toModal.or φ₂.toModal := rfl

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
    simp only [PL.Proposition.toModal, Modal.Satisfies, PL.Evaluate]
    exact ⟨fun h he => ih2.mp (h (ih1.mpr he)),
           fun h hm => ih2.mpr (h (ih1.mp hm))⟩
  | and φ ψ ih1 ih2 =>
    simp only [PL.Proposition.toModal, PL.Evaluate]
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
    simp only [PL.Proposition.toModal, PL.Evaluate]
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
