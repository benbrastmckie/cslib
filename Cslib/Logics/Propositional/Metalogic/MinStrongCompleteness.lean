/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.MinSoundness
public import Cslib.Logics.Propositional.Metalogic.MinCompleteness

/-! # Strong Completeness for Minimal Propositional Logic

This module proves strong soundness and strong completeness for minimal propositional logic
via the canonical Kripke model construction. Strong completeness states that if `φ` is a
minimal semantic consequence of a set `Γ`, then `φ` is set-derivable from `Γ`.

## Main Results

- `min_strong_soundness`: `SetDerivable MinPropAxiom Γ φ → MSemanticEntails Γ φ`
- `min_strong_completeness`: `MSemanticEntails Γ φ → SetDerivable MinPropAxiom Γ φ`
- `min_strong_completeness_iff`: `MSemanticEntails Γ φ ↔ SetDerivable MinPropAxiom Γ φ`
- `min_compactness`: If every finite `L ⊆ Γ` is minimally satisfiable, then `Γ` is.

## Strategy

Soundness is direct: unfold `SetDerivable` to get a witness list `L ⊆ Γ`, apply `min_soundness`
(which handles derivation trees) to get forcing of `φ` at any world where `Γ` is satisfied.

Completeness is by contraposition via the canonical model. If `φ` is not set-derivable from `Γ`,
then `φ ∉ minDeductiveClosure(Γ)`. By `min_prime_exclusion`, extend to a prime MinTheory `T`
containing `Γ` but excluding `φ`. The canonical Kripke world built from `T` satisfies all of `Γ`
but not `φ`, witnessing failure of `MSemanticEntails Γ φ`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
* Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Strong Soundness -/

/-- **Strong Soundness for Minimal Logic**:
If `φ` is set-derivable from `Γ` using `MinPropAxiom`, then `φ` is a minimal
Kripke semantic consequence of `Γ`. -/
theorem min_strong_soundness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : SetDerivable MinPropAxiom Γ φ) : MSemanticEntails Γ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  intro World _ val bot_forces v_uc bf_uc w h_sat
  exact min_soundness d val bot_forces v_uc bf_uc w
    (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## Helper: SetDerivable and minDeductiveClosure -/

/-- `φ ∈ minDeductiveClosure(Γ)` iff `φ` is set-derivable from `Γ`. -/
theorem minDeductiveClosure_iff_SetDerivable
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    φ ∈ minDeductiveClosure Γ ↔ SetDerivable MinPropAxiom Γ φ := Iff.rfl

/-! ## Strong Completeness -/

/-- **Strong Completeness for Minimal Logic**:
If `φ` is a minimal Kripke semantic consequence of `Γ`, then `φ` is set-derivable
from `Γ` using `MinPropAxiom`.

Proof by contrapositive: assume `φ` is not set-derivable from `Γ`. Then
`φ ∉ minDeductiveClosure(Γ)`, which is a MinTheory. By `min_prime_exclusion`,
extend to a prime MinTheory `T ⊇ Γ` with `φ ∉ T`. The canonical Kripke world
from `T` satisfies all of `Γ` (since `Γ ⊆ T` and the truth lemma) but not `φ`. -/
theorem min_strong_completeness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : MSemanticEntails Γ φ) : SetDerivable MinPropAxiom Γ φ := by
  by_contra h_not
  -- φ ∉ minDeductiveClosure(Γ) (same as ¬SetDerivable by minDeductiveClosure_iff)
  have h_not_mem : φ ∉ minDeductiveClosure Γ :=
    minDeductiveClosure_iff_SetDerivable.not.mpr h_not
  -- minDeductiveClosure(Γ) is a MinTheory
  have h_theory : MinTheory (minDeductiveClosure Γ) :=
    minDeductiveClosure_is_theory Γ
  -- Extend to a prime MinTheory T ⊇ minDeductiveClosure(Γ) with φ ∉ T
  obtain ⟨T_set, hT_sup, hT_prime, hT_excl⟩ :=
    min_prime_exclusion h_theory h_not_mem
  -- Build the canonical world W₀ from T
  let W₀ : MinCanonicalWorld Atom := ⟨T_set, hT_prime⟩
  -- φ is not forced at W₀ (by min_truth_lemma and hT_excl)
  have h_not_forced : ¬ IForces minCanonicalVal minBotForces W₀ φ := by
    intro h_f
    exact hT_excl ((min_truth_lemma W₀ φ).mp h_f)
  -- All members of Γ are forced at W₀
  -- Since Γ ⊆ minDeductiveClosure(Γ) ⊆ T, all of Γ is in T
  have h_gamma_sub_T : ∀ ψ ∈ Γ, ψ ∈ T_set := by
    intro ψ hψ
    exact hT_sup (min_subset_deductive_closure Γ hψ)
  have h_gamma_forced : ∀ ψ ∈ Γ, IForces minCanonicalVal minBotForces W₀ ψ := by
    intro ψ hψ
    exact (min_truth_lemma W₀ ψ).mpr (h_gamma_sub_T ψ hψ)
  -- Instantiate MSemanticEntails to get φ forced at W₀
  have h_forced : IForces minCanonicalVal minBotForces W₀ φ :=
    h (MinCanonicalWorld Atom) minCanonicalVal minBotForces
      (fun {_ _} p hw hv => minCanonicalVal_upward_closed p hw hv)
      (fun {_ _} hw hbf => minBotForces_upward_closed hw hbf)
      W₀ h_gamma_forced
  exact h_not_forced h_forced

/-! ## Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for Minimal Logic**:
`φ` is a minimal Kripke semantic consequence of `Γ` iff `φ` is set-derivable from `Γ`. -/
theorem min_strong_completeness_iff {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    MSemanticEntails Γ φ ↔ SetDerivable MinPropAxiom Γ φ :=
  ⟨min_strong_completeness, min_strong_soundness⟩

/-! ## Compactness Corollary -/

/-- **Compactness for Minimal Kripke Semantics**:
If `φ` is a minimal Kripke semantic consequence of `Γ`, then there exists a finite
list `L ⊆ Γ` such that `φ` is a minimal Kripke semantic consequence of `L`.

This is the semantic compactness property: Kripke entailment is compact for
minimal logic, following directly from strong completeness + the finitary
nature of `SetDerivable`.

Proof: by strong completeness, `MSemanticEntails Γ φ → SetDerivable MinPropAxiom Γ φ`,
which gives a finite list `L ⊆ Γ`. Strong soundness then gives
`SetDerivable MinPropAxiom L φ → MSemanticEntails {ψ | ψ ∈ L} φ`. -/
theorem min_compactness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : MSemanticEntails Γ φ) :
    ∃ L : List (PL.Proposition Atom),
      (∀ x ∈ L, x ∈ Γ) ∧
      MSemanticEntails {ψ | ψ ∈ L} φ := by
  -- By strong completeness, get a finite witness list L ⊆ Γ with L ⊢ φ
  obtain ⟨L, hL_sub, hL_deriv⟩ := min_strong_completeness h
  -- L witnesses the finite subset; by strong soundness, L-derivability gives L-entailment
  refine ⟨L, hL_sub, ?_⟩
  apply min_strong_soundness
  exact ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩

/-! ## Weak Completeness Corollary -/

/-- **Weak Completeness for Minimal Propositional Logic**:
If `φ` is minimally valid (forced at every world of every minimal Kripke model),
then `φ` is derivable from the empty context using `MinPropAxiom`.

This is a corollary of `min_strong_completeness`: a minimally valid formula
is a minimal semantic consequence of the empty set, so strong completeness
gives set-derivability from `∅`, and `SetDerivable_empty_iff` converts this to
ordinary derivability. -/
theorem min_completeness {φ : PL.Proposition Atom}
    (h_valid : MValid.{u, u} φ) : Derivable MinPropAxiom φ :=
  SetDerivable_empty_iff.mp
    (min_strong_completeness (MSemanticEntails_of_MValid h_valid ∅))

/-- **Soundness and Completeness for Minimal Logic**:
`φ` is minimally valid iff `φ` is derivable from the empty context
using `MinPropAxiom`.

This is a corollary of `min_strong_completeness_iff` obtained by instantiating at
`Γ = ∅` and using `SetDerivable_empty_iff`. -/
theorem min_soundness_completeness {φ : PL.Proposition Atom} :
    MValid.{u, u} φ ↔ Derivable MinPropAxiom φ :=
  ⟨min_completeness, min_soundness_derivable⟩

end Cslib.Logic.PL
