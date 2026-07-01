/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Semantics.Model

/-! # Temporal Satisfaction Relation

This module defines the recursive satisfaction relation `Satisfies` for temporal
logic formulas evaluated in a `TemporalModel` on a linear order.

## Pnueli Convention (Guard, Event)

The `untl` and `snce` operators follow the Pnueli convention where the first
argument is the GUARD (holds at all intermediate points) and the second is the
EVENT (holds at the witness point):

- `untl ψ φ` at `t`: there exists `s > t` such that `φ` holds at `s` (event)
  and `ψ` holds at all `r` strictly between `t` and `s` (guard).
- `snce ψ φ` at `t`: there exists `s < t` such that `φ` holds at `s` (event)
  and `ψ` holds at all `r` strictly between `s` and `t` (guard).

This matches `Cslib.Logics.LTL` and the `Formula.someFuture` definition
(`someFuture φ = untl ⊤ φ`, where ⊤ is the trivial guard and φ is the event).

`allFuture` and `allPast` are now primitive constructors (task 180) with direct
structural satisfaction clauses:
- `allFuture φ` at `t`: `∀ s, t < s → Satisfies M s φ`
- `allPast φ` at `t`: `∀ s, s < t → Satisfies M s φ`

## Main Definitions

- `Temporal.Satisfies`: Recursive truth evaluation for all formula constructors.

## Main Results

- `bot_false`, `atom_iff`, `imp_iff`, `untl_iff`, `snce_iff`: Constructor lemmas.
- `allFuture_iff`, `allPast_iff`: Universal temporal operator characterizations (now definitional).
- `neg_iff`, `top_true`: Derived connective lemmas.
- `someFuture_iff`, `somePast_iff`: Existential temporal operator characterizations.
- `sat_allFuture_iff_neg_someFuture_neg`, `sat_allPast_iff_neg_somePast_neg`: Semantic
  bridge lemmas recovering the classical equivalences `𝐆φ ↔ ¬𝐅¬φ`, `𝐇φ ↔ ¬𝐏¬φ`.
-/

@[expose] public section

namespace Cslib.Logic.Temporal

variable {D : Type*} [LinearOrder D] {Atom : Type*}

/-- Truth of a temporal formula at a time point in a model.

The evaluation is defined recursively on formula structure:
- Atoms: true iff the valuation assigns true at this time.
- Bot (⊥): always false.
- Implication: standard material conditional.
- Until U(ψ,φ): ∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ψ(r).  (ψ=GUARD, φ=EVENT)
- Since S(ψ,φ): ∃ s < t, φ(s) ∧ ∀ r ∈ (s,t), ψ(r).  (ψ=GUARD, φ=EVENT)
- AllFuture G(φ): ∀ s > t, φ(s).  (primitive constructor, task 180)
- AllPast H(φ): ∀ s < t, φ(s).  (primitive constructor, task 180)
-/
def Satisfies (M : TemporalModel D Atom) (t : D) : Formula Atom → Prop
  | .atom p => M.valuation t p
  | .bot => False
  | .imp φ ψ => Satisfies M t φ → Satisfies M t ψ
  | .untl ψ φ =>
    ∃ s, t < s ∧ Satisfies M s φ ∧
      ∀ r, t < r → r < s → Satisfies M r ψ
  | .snce ψ φ =>
    ∃ s, s < t ∧ Satisfies M s φ ∧
      ∀ r, s < r → r < t → Satisfies M r ψ
  | .allFuture φ => ∀ s, t < s → Satisfies M s φ
  | .allPast φ => ∀ s, s < t → Satisfies M s φ

namespace Satisfies

/-! ## Constructor Lemmas -/

/-- Bot (⊥) is false everywhere. -/
theorem bot_false (M : TemporalModel D Atom) (t : D) :
    ¬ Satisfies M t .bot :=
  id

/-- Truth of an atom is determined by the valuation. -/
@[simp]
theorem atom_iff (M : TemporalModel D Atom) (t : D) (p : Atom) :
    Satisfies M t (.atom p) ↔ M.valuation t p :=
  Iff.rfl

/-- Truth of implication is material conditional. -/
@[simp]
theorem imp_iff (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (.imp φ ψ) ↔
      (Satisfies M t φ → Satisfies M t ψ) :=
  Iff.rfl

/-- Characterization of Until: ∃ s > t with event φ at s and guard ψ between. -/
@[simp]
theorem untl_iff (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (.untl ψ φ) ↔
      ∃ s, t < s ∧ Satisfies M s φ ∧
        ∀ r, t < r → r < s → Satisfies M r ψ :=
  Iff.rfl

/-- Characterization of Since: ∃ s < t with event φ at s and guard ψ between. -/
@[simp]
theorem snce_iff (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (.snce ψ φ) ↔
      ∃ s, s < t ∧ Satisfies M s φ ∧
        ∀ r, s < r → r < t → Satisfies M r ψ :=
  Iff.rfl

/-! ## Derived Connective Lemmas -/

/-- Negation: ¬φ holds iff φ does not hold. -/
theorem neg_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (¬φ) ↔ ¬ Satisfies M t φ := by
  change (Satisfies M t (.imp φ .bot)) ↔ ¬ Satisfies M t φ
  simp only [Satisfies]

/-- Top (⊤) is true everywhere. -/
theorem top_true (M : TemporalModel D Atom) (t : D) :
    Satisfies M t Formula.top := by
  intro h
  exact h

/-! ## Temporal Operator Lemmas -/

/-- Some future (F φ): there exists a future time where φ holds. -/
theorem someFuture_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐅φ) ↔
      ∃ s, t < s ∧ Satisfies M s φ := by
  simp only [Satisfies]
  constructor
  · rintro ⟨s, hlt, hevent, _⟩
    exact ⟨s, hlt, hevent⟩
  · rintro ⟨s, hlt, hs⟩
    exact ⟨s, hlt, hs, fun _ _ _ h => h⟩

/-- Some past (P φ): there exists a past time where φ holds. -/
theorem somePast_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐏φ) ↔
      ∃ s, s < t ∧ Satisfies M s φ := by
  simp only [Satisfies]
  constructor
  · rintro ⟨s, hlt, hevent, _⟩
    exact ⟨s, hlt, hevent⟩
  · rintro ⟨s, hlt, hs⟩
    exact ⟨s, hlt, hs, fun _ _ _ h => h⟩

/-- All future (G φ): φ holds at all future times.

With `allFuture` as a primitive constructor (task 180), this is definitional. -/
@[simp]
theorem allFuture_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐆φ) ↔
      ∀ s, t < s → Satisfies M s φ :=
  Iff.rfl

/-- All past (H φ): φ holds at all past times.

With `allPast` as a primitive constructor (task 180), this is definitional. -/
@[simp]
theorem allPast_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐇φ) ↔
      ∀ s, s < t → Satisfies M s φ :=
  Iff.rfl

/-! ## Semantic Bridge Lemmas

With `allFuture`/`allPast` as primitive constructors (task 180), the classical
equivalences `𝐆φ ↔ ¬𝐅¬φ` and `𝐇φ ↔ ¬𝐏¬φ` are no longer definitional (they were a
`defeq` abbreviation before this promotion). They remain semantically valid (classical
logic on `Prop` justifies the quantifier-negation swap), so we record them here as
theorems. These are the semantic-level counterparts of the `ProofSystem` bridge axioms
(`Axioms.lean`) and are consumed by the TruthLemma reduction (P7). -/

/-- Semantic bridge: primitive `𝐆φ` is equivalent to the classical `¬𝐅¬φ`.
Proved via classical negation of the `someFuture` witness (not a `defeq`, since
`allFuture` is now primitive). -/
theorem sat_allFuture_iff_neg_someFuture_neg (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐆φ) ↔ Satisfies M t (¬𝐅¬φ) := by
  rw [allFuture_iff, neg_iff, someFuture_iff]
  constructor
  · rintro h ⟨s, hlt, hs⟩
    exact (neg_iff M s φ).mp hs (h s hlt)
  · intro h s hlt
    by_contra hφ
    exact h ⟨s, hlt, (neg_iff M s φ).mpr hφ⟩

/-- Semantic bridge: primitive `𝐇φ` is equivalent to the classical `¬𝐏¬φ`.
Past dual of `sat_allFuture_iff_neg_someFuture_neg`. -/
theorem sat_allPast_iff_neg_somePast_neg (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐇φ) ↔ Satisfies M t (¬𝐏¬φ) := by
  rw [allPast_iff, neg_iff, somePast_iff]
  constructor
  · rintro h ⟨s, hlt, hs⟩
    exact (neg_iff M s φ).mp hs (h s hlt)
  · intro h s hlt
    by_contra hφ
    exact h ⟨s, hlt, (neg_iff M s φ).mpr hφ⟩

end Satisfies

end Cslib.Logic.Temporal
