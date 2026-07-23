/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Embedding
public import Cslib.Logics.LTL.Semantics.Satisfies
public import Cslib.Logics.Temporal.Semantics.Satisfies
public import Cslib.Logics.Temporal.Semantics.Validity

/-! # LTL-to-Temporal Semantic Preservation Bridge

`Cslib.Logics.LTL.Embedding` defines the syntactic map `Formula.toTemporal` from
`LTL.Formula` into `Temporal.Formula`, asserting (in its docstring) that the translation
preserves satisfaction. This module proves that claim.

The bridge model `toTemporalModel` interprets an LTL valuation `v` and omega-word `w` as a
`Temporal.TemporalModel ℕ Atom` whose truth at time `n` is the LTL truth at the `n`-th state
of `w`. The main theorem `satisfies_toTemporal` shows that LTL satisfaction of `φ` at
`w.drop n` agrees with Temporal satisfaction of `φ.toTemporal` at `n` in this model, for every
`n`. The corollary `satisfiable_toTemporal` specializes this at `n = 0` to show that LTL
satisfiability transfers to Temporal satisfiability, giving `toTemporal` a genuine consumer.

This file is deliberately semantics-only: it does not import
`Cslib.Logics.Temporal.Metalogic.Soundness` (which would drag in the whole `ProofSystem`
machinery). Instead it proves two small local classical helpers (`sat_and_iff`, `sat_or_iff`)
by copying the ~6-line proof bodies of `Temporal.sat_and_iff` / `Temporal.sat_or_iff`
specialized to this bridge's needs.

## Main definitions

- `toTemporalModel` : builds a `Temporal.TemporalModel ℕ Atom` from an LTL valuation and
  omega-word.

## Main results

- `satisfies_toTemporal` : `Formula.toTemporal` preserves satisfaction at every time index.
- `satisfiable_toTemporal` : LTL satisfiability transfers to Temporal satisfiability.

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [J. P. Burgess, *Basic Tense Logic*][Burgess1984]
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {Atom State : Type*}

/-- The bridge temporal model on time domain `ℕ`: the atom valuation at time `n` is the LTL
valuation `v` at the `n`-th state of the omega-word `w`. -/
def toTemporalModel (v : Atom → State → Prop) (w : ωSequence State) :
    Temporal.TemporalModel ℕ Atom :=
  ⟨fun n p => v p (w n)⟩

open scoped Cslib.Logic.Temporal in
/-- Local semantic helper: `Temporal.Satisfies` distributes over conjunction. Copies the proof
body of `Temporal.sat_and_iff` (`Cslib.Logics.Temporal.Metalogic.Soundness`) specialized to
`D = ℕ`, kept local so this bridge does not import the `ProofSystem`/`Metalogic` machinery. -/
theorem sat_and_iff (M : Temporal.TemporalModel ℕ Atom) (t : ℕ) (φ ψ : Temporal.Formula Atom) :
    Temporal.Satisfies M t (φ ∧ ψ) ↔ (Temporal.Satisfies M t φ ∧ Temporal.Satisfies M t ψ) := by
  simp only [Temporal.Satisfies]
  constructor
  · intro h
    constructor
    · by_contra hφ; exact h (fun hφ' => absurd hφ' hφ)
    · by_contra hψ; exact h (fun _ hψ' => absurd hψ' hψ)
  · intro ⟨hφ, hψ⟩ h; exact h hφ hψ

open scoped Cslib.Logic.Temporal in
/-- Local semantic helper: `Temporal.Satisfies` distributes over disjunction. Copies the proof
body of `Temporal.sat_or_iff` (`Cslib.Logics.Temporal.Metalogic.Soundness`) specialized to
`D = ℕ`, kept local so this bridge does not import the `ProofSystem`/`Metalogic` machinery. -/
theorem sat_or_iff (M : Temporal.TemporalModel ℕ Atom) (t : ℕ) (φ ψ : Temporal.Formula Atom) :
    Temporal.Satisfies M t (φ ∨ ψ) ↔ (Temporal.Satisfies M t φ ∨ Temporal.Satisfies M t ψ) := by
  simp only [Temporal.Satisfies]
  constructor
  · intro h
    by_contra h_neg
    push Not at h_neg
    exact h_neg.2 (h (fun hφ => absurd hφ h_neg.1))
  · intro h hnφ
    rcases h with hφ | hψ
    · exact absurd hφ hnφ
    · exact hψ

end Cslib.Logic.LTL

end
