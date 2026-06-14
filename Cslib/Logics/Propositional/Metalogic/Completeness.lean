/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.Metalogic.MCS

/-! # Canonical Model Infrastructure for Classical Propositional Logic

This module provides the canonical model (MCS) construction used in the completeness
proof for classical propositional logic. The main completeness theorems are derived
as corollaries of the strong completeness results in `StrongCompleteness.lean`.

## Main Results

- `canonicalValuation`: The canonical valuation from a maximally consistent set.
- `prop_truth_lemma`: `Evaluate (canonicalValuation S) φ ↔ φ ∈ S` for MCS `S`.

See `Cslib.Logics.Propositional.Metalogic.StrongCompleteness` for:
- `prop_completeness`: `Tautology φ → Derivable PropositionalAxiom φ`
- `prop_completeness_iff_tautology`: `Tautology φ ↔ Derivable PropositionalAxiom φ`

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- modal K completeness
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Canonical Valuation -/

/-- The canonical valuation from a maximally consistent set.

For MCS `S`, the atom `p` is true iff `Proposition.atom p ∈ S`. -/
def canonicalValuation (S : Set (PL.Proposition Atom)) :
    Valuation Atom :=
  fun p => Proposition.atom p ∈ S

/-! ## Truth Lemma: Per-Connective Helpers -/

/-- **Truth Lemma (atom)**: `Evaluate v (atom p) ↔ atom p ∈ S`. Trivial since
the canonical valuation is defined as `fun p => atom p ∈ S`. -/
theorem prop_truth_lemma_atom
    {S : Set (PL.Proposition Atom)}
    (_h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (p : Atom) :
    Evaluate (canonicalValuation S) (.atom p) ↔ (.atom p) ∈ S :=
  Iff.rfl

/-- **Truth Lemma (bot)**: `Evaluate v ⊥ ↔ ⊥ ∈ S`. The forward direction
is vacuously true (⊥ never evaluates to true); the backward direction uses
`prop_mcs_bot_not_mem`. -/
theorem prop_truth_lemma_bot
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S) :
    Evaluate (canonicalValuation S) .bot ↔ (.bot : PL.Proposition Atom) ∈ S := by
  constructor
  · intro h; exact absurd h id
  · intro h; exact absurd h (prop_mcs_bot_not_mem h_mcs)

/-- **Truth Lemma (and)**: Given IH for φ and ψ, prove
`Evaluate v (φ ∧ ψ) ↔ (φ ∧ ψ) ∈ S`. -/
theorem prop_truth_lemma_and
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (φ ψ : PL.Proposition Atom)
    (ih_φ : Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
    (ih_ψ : Evaluate (canonicalValuation S) ψ ↔ ψ ∈ S) :
    Evaluate (canonicalValuation S) (φ.and ψ) ↔ (φ.and ψ) ∈ S := by
  constructor
  · -- Forward: Evaluate v (φ ∧ ψ) → (φ ∧ ψ) ∈ S
    intro ⟨hφ, hψ⟩
    have h_phi_S := ih_φ.mp hφ
    have h_psi_S := ih_ψ.mp hψ
    apply prop_closed_under_derivation prop_h_implyK prop_h_implyS h_mcs
      (L := [φ, ψ])
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        cases hx with
        | inl h => exact h ▸ h_phi_S
        | inr h => exact h ▸ h_psi_S)
    show (propDerivationSystem PropositionalAxiom).Deriv _ _
    unfold propDerivationSystem Deriv
    exact ⟨.modus_ponens _ _ _
      (.modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.andI φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons])))
      (.assumption _ _ (by simp [List.mem_cons]))⟩
  · -- Backward: (φ ∧ ψ) ∈ S → Evaluate v (φ ∧ ψ)
    intro h_mem
    constructor
    · apply ih_φ.mpr
      apply prop_closed_under_derivation prop_h_implyK prop_h_implyS h_mcs
        (L := [φ.and ψ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.andE1 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩
    · apply ih_ψ.mpr
      apply prop_closed_under_derivation prop_h_implyK prop_h_implyS h_mcs
        (L := [φ.and ψ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.andE2 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩

/-- **Truth Lemma (or)**: Given IH for φ and ψ, prove
`Evaluate v (φ ∨ ψ) ↔ (φ ∨ ψ) ∈ S`. -/
theorem prop_truth_lemma_or
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (φ ψ : PL.Proposition Atom)
    (ih_φ : Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
    (ih_ψ : Evaluate (canonicalValuation S) ψ ↔ ψ ∈ S) :
    Evaluate (canonicalValuation S) (φ.or ψ) ↔ (φ.or ψ) ∈ S := by
  constructor
  · -- Forward: Evaluate v (φ ∨ ψ) → (φ ∨ ψ) ∈ S
    intro h_or
    rcases h_or with hφ | hψ
    · have h_phi_S := ih_φ.mp hφ
      apply prop_closed_under_derivation prop_h_implyK prop_h_implyS h_mcs
        (L := [φ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_phi_S)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.orI1 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩
    · have h_psi_S := ih_ψ.mp hψ
      apply prop_closed_under_derivation prop_h_implyK prop_h_implyS h_mcs
        (L := [ψ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_psi_S)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.orI2 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩
  · -- Backward: (φ ∨ ψ) ∈ S → Evaluate v (φ ∨ ψ)
    intro h_mem
    -- Use negation_complete: either φ ∈ S or ¬φ ∈ S
    rcases prop_negation_complete prop_h_implyK prop_h_implyS h_mcs φ with hφ | hnφ
    · exact Or.inl (ih_φ.mpr hφ)
    · rcases prop_negation_complete prop_h_implyK prop_h_implyS h_mcs ψ with hψ | hnψ
      · exact Or.inr (ih_ψ.mpr hψ)
      · -- Both ¬φ ∈ S and ¬ψ ∈ S; derive ⊥ using orE
        exfalso
        apply prop_mcs_bot_not_mem h_mcs
        -- orE: (φ → ⊥) → ((ψ → ⊥) → ((φ ∨ ψ) → ⊥))
        apply prop_closed_under_derivation prop_h_implyK prop_h_implyS h_mcs
          (L := [φ.imp .bot, ψ.imp .bot, φ.or ψ])
          (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            cases hx with
            | inl h => exact h ▸ hnφ
            | inr h =>
              cases h with
              | inl h => exact h ▸ hnψ
              | inr h => exact h ▸ h_mem)
        show (propDerivationSystem PropositionalAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        -- [¬φ, ¬ψ, φ ∨ ψ] ⊢ ⊥ via orE axiom + three modus ponens
        exact ⟨.modus_ponens _ _ _
          (.modus_ponens _ _ _
            (.modus_ponens _ _ _
              (.weakening [] _ _
                (.ax [] _ (.orE φ ψ .bot))
                (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons])))
            (.assumption _ _ (by simp [List.mem_cons])))
          (.assumption _ _ (by simp [List.mem_cons]))⟩

/-- **Truth Lemma (imp)**: Given IH for φ and ψ, prove
`Evaluate v (φ → ψ) ↔ (φ → ψ) ∈ S`. -/
theorem prop_truth_lemma_imp
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (φ ψ : PL.Proposition Atom)
    (ih_φ : Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
    (ih_ψ : Evaluate (canonicalValuation S) ψ ↔ ψ ∈ S) :
    Evaluate (canonicalValuation S) (φ.imp ψ) ↔ (φ.imp ψ) ∈ S := by
  constructor
  · -- Forward: Evaluate v (φ → ψ) → (φ → ψ) ∈ S
    intro h_sat
    rcases prop_negation_complete prop_h_implyK prop_h_implyS
      h_mcs (φ → ψ) with h | h
    · exact h
    · exfalso
      -- h : neg (φ.imp ψ) ∈ S
      -- Derive φ ∈ S from neg (φ.imp ψ) ∈ S
      have h_phi_S : φ ∈ S := by
        apply prop_closed_under_derivation
          prop_h_implyK prop_h_implyS h_mcs
          (L := [(φ.imp ψ).imp .bot])
          (fun x hx => by
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hx
            exact hx ▸ h)
        show (propDerivationSystem
          PropositionalAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        -- [(φ→ψ), (φ→ψ)→⊥] ⊢ ⊥
        have d_bot' :
            DerivationTree PropositionalAxiom
            [φ.imp ψ, (φ.imp ψ).imp .bot]
            Proposition.bot :=
          .modus_ponens _ (φ.imp ψ) .bot
            (.assumption _ _
              (by simp [List.mem_cons]))
            (.assumption _ _
              (by simp [List.mem_cons]))
        -- [(φ→ψ), (φ→ψ)→⊥] ⊢ φ (via EFQ)
        have d_efq' :
            DerivationTree PropositionalAxiom
            [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
          .modus_ponens _ .bot φ
            (.weakening [] _ _
              (.ax [] _ (.efq φ))
              (fun _ h => nomatch h))
            d_bot'
        -- deduction: [(φ→ψ)→⊥] ⊢ (φ→ψ) → φ
        have d_dt := deductionTheorem
          prop_h_implyK prop_h_implyS
          [(φ.imp ψ).imp .bot] (φ.imp ψ) φ
          d_efq'
        -- Peirce: [(φ→ψ)→⊥] ⊢ ((φ→ψ)→φ) → φ
        have d_peirce' :
            DerivationTree PropositionalAxiom
            [(φ.imp ψ).imp .bot]
            (((φ.imp ψ).imp φ).imp φ) :=
          .weakening [] _ _
            (.ax [] _ (.peirce φ ψ))
            (fun _ h => nomatch h)
        -- MP: [(φ→ψ)→⊥] ⊢ φ
        exact ⟨.modus_ponens _ _ _
          d_peirce' d_dt⟩
      -- By IH backward, Evaluate v φ
      have h_sat_phi := ih_φ.mpr h_phi_S
      -- By assumption, Evaluate v ψ
      have h_psi_S := ih_ψ.mp (h_sat h_sat_phi)
      -- Derive ¬ψ ∈ S from neg (φ → ψ) ∈ S
      have h_neg_psi_S :
          (¬ψ) ∈ S := by
        apply prop_closed_under_derivation
          prop_h_implyK prop_h_implyS h_mcs
          (L := [(φ.imp ψ).imp .bot])
          (fun x hx => by
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hx
            exact hx ▸ h)
        show (propDerivationSystem
          PropositionalAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        -- [ψ, (φ→ψ)→⊥] ⊢ φ→ψ via implyK
        have d_imp :
            DerivationTree PropositionalAxiom
            [ψ, (φ.imp ψ).imp .bot]
            (φ.imp ψ) :=
          .modus_ponens _ ψ (φ.imp ψ)
            (.weakening [] _ _
              (.ax [] _ (.implyK ψ φ))
              (fun _ h => nomatch h))
            (.assumption _ _
              (by simp [List.mem_cons]))
        -- [ψ, (φ→ψ)→⊥] ⊢ ⊥
        have d_bot'' :
            DerivationTree PropositionalAxiom
            [ψ, (φ.imp ψ).imp .bot]
            Proposition.bot :=
          .modus_ponens _ (φ.imp ψ) .bot
            (.assumption _ _
              (by simp [List.mem_cons]))
            d_imp
        -- deduction: [(φ→ψ)→⊥] ⊢ ψ → ⊥
        exact ⟨deductionTheorem
          prop_h_implyK prop_h_implyS
          [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
      -- Contradiction: ψ ∈ S and ¬ψ ∈ S
      exact prop_mcs_bot_not_mem h_mcs
        (prop_implication_property
          prop_h_implyK prop_h_implyS h_mcs
          h_neg_psi_S h_psi_S)
  · -- Backward: (φ → ψ) ∈ S → Evaluate v φ → Evaluate v ψ
    intro h_mem h_sat_phi
    exact ih_ψ.mpr
      (prop_implication_property
        prop_h_implyK prop_h_implyS h_mcs h_mem
        (ih_φ.mp h_sat_phi))

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For an MCS `S` and its canonical valuation `v`,
`Evaluate v φ ↔ φ ∈ S`.

Proof by structural recursion on `φ`, dispatching to per-connective helpers:
`prop_truth_lemma_atom`, `prop_truth_lemma_bot`, `prop_truth_lemma_and`,
`prop_truth_lemma_or`, `prop_truth_lemma_imp`. -/
theorem prop_truth_lemma
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S) :
    (φ : PL.Proposition Atom) →
    (Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
  | .atom p => prop_truth_lemma_atom h_mcs p
  | .bot => prop_truth_lemma_bot h_mcs
  | .and φ ψ =>
    prop_truth_lemma_and h_mcs φ ψ
      (prop_truth_lemma h_mcs φ) (prop_truth_lemma h_mcs ψ)
  | .or φ ψ =>
    prop_truth_lemma_or h_mcs φ ψ
      (prop_truth_lemma h_mcs φ) (prop_truth_lemma h_mcs ψ)
  | .imp φ ψ =>
    prop_truth_lemma_imp h_mcs φ ψ
      (prop_truth_lemma h_mcs φ) (prop_truth_lemma h_mcs ψ)

end Cslib.Logic.PL
