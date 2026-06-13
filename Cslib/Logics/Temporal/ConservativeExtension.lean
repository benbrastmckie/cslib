/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.FromPropositional
public import Cslib.Logics.Temporal.Semantics.Satisfies
public import Cslib.Logics.Temporal.Metalogic.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness
public import Cslib.Logics.Propositional.Semantics.Basic
public import Mathlib.Algebra.Order.Ring.Int

/-! # Temporal BX as a Conservative Extension of Classical Propositional Logic

This module proves that Temporal BX is a conservative extension of CPL: any propositional
formula `φ` that is derivable in BX (as `φ.toTemporal`) is already derivable in CPL.

## Main Theorems

- `temporal_satisfies_toTemporal_iff_evaluate`: Semantic bridge between Temporal satisfaction
  of propositional translations and PL evaluation.
- `temporal_conservative_extension`: BX is a conservative extension of CPL.

## References

* Standard conservativity result for temporal logics over their propositional fragment.
-/

@[expose] public section

namespace Cslib.Logic

open Temporal Cslib.Logic.Temporal PL

/-- **Semantic Bridge Lemma**: Temporal satisfaction of `φ.toTemporal` at any point `t` in
any temporal model `M` is equivalent to propositional evaluation of `φ` under the valuation
`M.valuation t`.

Proof: Structural induction on `φ`. The `and`/`or` cases follow by classical logic since
`toTemporal` encodes these using the Lukasiewicz convention. -/
theorem temporal_satisfies_toTemporal_iff_evaluate
    {D : Type*} [LinearOrder D] {Atom : Type*}
    (M : TemporalModel D Atom) (t : D)
    (φ : PL.Proposition Atom) :
    Satisfies M t φ.toTemporal ↔ PL.Evaluate (M.valuation t) φ := by
  induction φ with
  | atom p => rfl
  | bot => rfl
  | imp φ ψ ih1 ih2 =>
    simp only [PL.Proposition.toTemporal, PL.Evaluate, Satisfies]
    exact ⟨fun h he => ih2.mp (h (ih1.mpr he)),
           fun h hm => ih2.mpr (h (ih1.mp hm))⟩
  | and φ ψ ih1 ih2 =>
    -- toTemporal: A ∧ B ↦ (A → B → ⊥) → ⊥  (Lukasiewicz encoding)
    simp only [PL.Proposition.toTemporal, PL.Evaluate, Satisfies]
    constructor
    · intro h
      constructor
      · by_contra hna; exact h (fun ha _ => hna (ih1.mp ha))
      · by_contra hnb; exact h (fun _ hb => hnb (ih2.mp hb))
    · intro ⟨ha, hb⟩ h
      exact h (ih1.mpr ha) (ih2.mpr hb)
  | or φ ψ ih1 ih2 =>
    -- toTemporal: A ∨ B ↦ (A → ⊥) → B  (Lukasiewicz encoding)
    simp only [PL.Proposition.toTemporal, PL.Evaluate, Satisfies]
    constructor
    · intro h
      by_cases ha : PL.Evaluate (M.valuation t) φ
      · exact Or.inl ha
      · exact Or.inr (ih2.mp (h (fun hma => ha (ih1.mp hma))))
    · intro h hna
      cases h with
      | inl ha => exact absurd (ih1.mpr ha) hna
      | inr hb => exact ih2.mpr hb

/-- **Temporal BX Conservative Extension over CPL**:

If the temporal translation `φ.toTemporal` is BX-derivable, then `φ` is CPL-derivable.

Proof: BX soundness (on `ℤ` as a linear order with no max/min) gives temporal satisfaction
of `φ.toTemporal`; the semantic bridge gives tautologyhood of `φ`; CPL completeness gives
derivability. -/
theorem temporal_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Temporal.ThDerivable φ.toTemporal) :
    Derivable PropositionalAxiom φ := by
  apply prop_completeness
  intro v
  -- Construct a constant temporal model on ℤ with valuation v
  let M : TemporalModel ℤ Atom := TemporalModel.constant v
  -- Use soundness of BX on ℤ (which is a strict linear order with no max/min)
  have hsat : Satisfies M (0 : ℤ) φ.toTemporal := soundness_thderivable h M 0
  -- Apply the semantic bridge lemma
  exact (temporal_satisfies_toTemporal_iff_evaluate M 0 φ).mp hsat

end Cslib.Logic

end
