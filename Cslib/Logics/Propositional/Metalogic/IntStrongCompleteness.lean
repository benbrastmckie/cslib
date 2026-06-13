/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.IntCompleteness

/-! # Strong Completeness for Intuitionistic Propositional Logic

This module proves strong soundness and strong completeness for intuitionistic propositional
logic via the canonical Kripke model construction. Strong completeness states that if `φ` is
an intuitionistic Kripke semantic consequence of `Γ`, then `φ` is set-derivable from `Γ`.

## Main Results

- `int_strong_soundness`: `SetDerivable IntPropAxiom Γ φ → ISemanticEntails Γ φ`
- `int_strong_completeness`: `ISemanticEntails Γ φ → SetDerivable IntPropAxiom Γ φ`
- `int_strong_completeness_iff`: `ISemanticEntails Γ φ ↔ SetDerivable IntPropAxiom Γ φ`
- `int_compactness`: If `φ` is an intuitionistic consequence of `Γ`, there is a finite `L ⊆ Γ`
  with the same property.

## Strategy

Soundness: unfold `SetDerivable` to get a witness list `L ⊆ Γ`, apply `int_soundness`.

Completeness: by contrapositive. If `φ` is not set-derivable from `Γ`, we show it's not an
intuitionistic consequence either.

Case split on `PropSetConsistent IntPropAxiom (intDeductiveClosure Γ)`:
- **Inconsistent**: `⊥ ∈ intDeductiveClosure Γ`, so `⊥` is set-derivable from `Γ`. By EFQ
  (`IntPropAxiom` includes `.efq`), `φ` is also set-derivable from `Γ`. Contradiction.
- **Consistent**: `intDeductiveClosure Γ` is an `IntDCCS` with `φ ∉ intDeductiveClosure Γ`
  (since φ is not set-derivable). By `int_prime_exclusion`, get a prime IntDCCS `T ⊇ Γ`
  excluding `φ`. The canonical world from `T` satisfies all of `Γ` but not `φ`.

## References

* CZ Theorem 2.43
* Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Strong Soundness -/

/-- **Strong Soundness for Intuitionistic Logic**:
If `φ` is set-derivable from `Γ` using `IntPropAxiom`, then `φ` is an intuitionistic
Kripke semantic consequence of `Γ`. -/
theorem int_strong_soundness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : SetDerivable IntPropAxiom Γ φ) : ISemanticEntails Γ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  intro World _ val v_uc w h_sat
  exact int_soundness d val v_uc w
    (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## Helper: SetDerivable and intDeductiveClosure -/

/-- `φ ∈ intDeductiveClosure(Γ)` iff `φ` is set-derivable from `Γ`. -/
theorem intDeductiveClosure_iff_SetDerivable
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    φ ∈ intDeductiveClosure Γ ↔ SetDerivable IntPropAxiom Γ φ := Iff.rfl

/-! ## EFQ Helper -/

/-- If `⊥` is set-derivable from `Γ` using `IntPropAxiom`, then any `φ` is set-derivable
from `Γ` (by EFQ). -/
theorem SetDerivable_efq_int {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h_bot : SetDerivable IntPropAxiom Γ (⊥ : PL.Proposition Atom)) :
    SetDerivable IntPropAxiom Γ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h_bot
  obtain ⟨d_bot⟩ := hL_deriv
  -- Build L ⊢ φ using EFQ: ⊢ ⊥ → φ, then MP
  let efq : DerivationTree IntPropAxiom (Atom := Atom) L (Proposition.bot.imp φ) :=
    .weakening [] L _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h)
  exact ⟨L, hL_sub, ⟨.modus_ponens L (Proposition.bot) φ efq d_bot⟩⟩

/-! ## Strong Completeness -/

/-- **Strong Completeness for Intuitionistic Logic**:
If `φ` is an intuitionistic Kripke semantic consequence of `Γ`, then `φ` is set-derivable
from `Γ` using `IntPropAxiom`.

Proof by contrapositive via canonical model, with an EFQ case split. -/
theorem int_strong_completeness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : ISemanticEntails Γ φ) : SetDerivable IntPropAxiom Γ φ := by
  by_contra h_not
  -- φ ∉ intDeductiveClosure(Γ)
  have h_not_mem : φ ∉ intDeductiveClosure Γ :=
    intDeductiveClosure_iff_SetDerivable.not.mpr h_not
  -- Case split on consistency of intDeductiveClosure(Γ)
  by_cases h_cons : PropSetConsistent IntPropAxiom (intDeductiveClosure Γ)
  · -- Consistent case: intDeductiveClosure(Γ) is an IntDCCS
    have h_dccs : IntDCCS (intDeductiveClosure Γ) :=
      ⟨h_cons, fun L φ' hL hd => intDeductiveClosure_dccs_closed Γ L φ' hL hd⟩
    -- By int_prime_exclusion, get a prime IntDCCS T ⊇ intDeductiveClosure(Γ) with φ ∉ T
    obtain ⟨T_set, hT_sup, hT_prime, hT_excl⟩ :=
      int_prime_exclusion h_dccs h_not_mem
    -- Build the canonical world W₀ from T
    let W₀ : IntCanonicalWorld Atom := ⟨T_set, hT_prime⟩
    -- φ is not forced at W₀
    have h_not_forced : ¬ IForces intCanonicalVal (fun _ => False) W₀ φ := by
      intro h_f
      exact hT_excl ((int_truth_lemma W₀ φ).mp h_f)
    -- All members of Γ are in T (since Γ ⊆ intDeductiveClosure(Γ) ⊆ T)
    have h_gamma_sub_T : ∀ ψ ∈ Γ, ψ ∈ T_set := by
      intro ψ hψ
      exact hT_sup (int_subset_deductive_closure Γ hψ)
    -- All members of Γ are forced at W₀
    have h_gamma_forced : ∀ ψ ∈ Γ, IForces intCanonicalVal (fun _ => False) W₀ ψ := by
      intro ψ hψ
      exact (int_truth_lemma W₀ ψ).mpr (h_gamma_sub_T ψ hψ)
    -- Instantiate ISemanticEntails
    have h_forced : IForces intCanonicalVal (fun _ => False) W₀ φ :=
      h (IntCanonicalWorld Atom) intCanonicalVal
        (fun {_ _} p hw hv => intCanonicalVal_upward_closed p hw hv)
        W₀ h_gamma_forced
    exact h_not_forced h_forced
  · -- Inconsistent case: ⊥ is set-derivable from Γ
    -- The inconsistency means some finite list from intDeductiveClosure(Γ) derives ⊥
    simp only [PropSetConsistent, Metalogic.SetConsistent, Metalogic.Consistent,
      not_forall, not_not] at h_cons
    obtain ⟨L_inc, hL_inc_sub, hL_inc_bot⟩ := h_cons
    -- Each element of L_inc is in intDeductiveClosure(Γ), i.e., set-derivable from Γ
    -- So ⊥ is set-derivable from Γ
    have h_bot_sd : SetDerivable IntPropAxiom Γ (⊥ : PL.Proposition Atom) :=
      int_deriv_from_closure_to_S L_inc (fun x hx => hL_inc_sub x hx) _ hL_inc_bot
    -- By EFQ, φ is set-derivable from Γ -- contradiction
    exact h_not (SetDerivable_efq_int h_bot_sd)

/-! ## Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for Intuitionistic Logic**:
`φ` is an intuitionistic Kripke semantic consequence of `Γ` iff `φ` is set-derivable from `Γ`. -/
theorem int_strong_completeness_iff {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    ISemanticEntails Γ φ ↔ SetDerivable IntPropAxiom Γ φ :=
  ⟨int_strong_completeness, int_strong_soundness⟩

/-! ## Compactness Corollary -/

/-- **Compactness for Intuitionistic Kripke Semantics**:
If `φ` is an intuitionistic Kripke semantic consequence of `Γ`, there is a finite
list `L ⊆ Γ` such that `φ` is an intuitionistic Kripke semantic consequence of `L`.

Proof: strong completeness gives a finite derivation witness from `Γ`; strong soundness
lifts it back to semantic entailment over just the finite list. -/
theorem int_compactness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : ISemanticEntails Γ φ) :
    ∃ L : List (PL.Proposition Atom),
      (∀ x ∈ L, x ∈ Γ) ∧
      ISemanticEntails {ψ | ψ ∈ L} φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := int_strong_completeness h
  exact ⟨L, hL_sub, int_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩⟩

end Cslib.Logic.PL
