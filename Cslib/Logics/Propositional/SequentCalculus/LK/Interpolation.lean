/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
public import Cslib.Logics.Propositional.Subformula

/-! # Craig Interpolation for LK via Maehara's Method

We prove Craig interpolation for the classical propositional sequent calculus LK via
Maehara's method: a structural induction over a cut-free proof.

## Main Results

- `maeharaCore`: For any cut-free LK proof of `Γ ⊢ₛ Δ` and any *cover* partition
  `Γ = Γ₁ ∪ Γ₂`, `Δ = Δ₁ ∪ Δ₂`, there exists an interpolant `I` such that
  `Γ₁ ⊢ₛ insert I Δ₁`, `insert I Γ₂ ⊢ₛ Δ₂`, and
  `I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars`.

## Design Notes

- Follows the `(d, hcf) + induction d with` pattern from `SubformulaProperty.lean:90`,
  which avoids the Finset-quotient index problem when inducting on a cut-free subtype.
- The `cut` case is vacuous since `CutFree` is `False` for `cut` steps.
- Partition overlap is allowed (cover semantics: `Γ₁ ∪ Γ₂ = Γ`, not disjoint).
- The invariant is `Nonempty (LKProof …)` to keep the whole proof in `Prop`.
- All cases, including the hard ones (`ax`, `andR`, `orL`, `impL`, `impR`), are proved below.

## References

* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition LKSequent

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Maehara Core Lemma -/

set_option maxHeartbeats 1600000 in
-- Two-premise cases (andR, orL, impL, impR) require up to ~400k each; 1600000 covers the full induction.
/-- **Maehara core**: For any cut-free LK proof `d` of `seq` and any cover partition
`Γ₁ ∪ Γ₂ = seq.ant`, `Δ₁ ∪ Δ₂ = seq.suc`, there exists an interpolant `I` satisfying:
1. `I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars` (variable constraint),
2. `Γ₁ ⊢ₛ insert I Δ₁` (left half-derivation), and
3. `insert I Γ₂ ⊢ₛ Δ₂` (right half-derivation).

The `cut` case is vacuous since `CutFree d` is `False` for cut steps. The remaining cases
(`ax`, `andR`, `orL`, `impL`, `impR`) are the hard cases, each proved below. -/
private lemma maeharaCore {seq : LKSequent Atom} (d : LKProof seq) (hcf : CutFree d) :
    ∀ Γ₁ Γ₂ Δ₁ Δ₂ : Finset (Proposition Atom),
      seq.ant = Γ₁ ∪ Γ₂ → seq.suc = Δ₁ ∪ Δ₂ →
      ∃ I : Proposition Atom,
        I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars ∧
        Nonempty (LKProof (Γ₁ ⊢ₛ insert I Δ₁)) ∧
        Nonempty (LKProof (insert I Γ₂ ⊢ₛ Δ₂)) := by
  induction d with
  | cut _ _ _ =>
    -- The cut case is vacuous: CutFree is False for cut steps.
    exact absurd hcf id
  | botL Γ Δ hbot =>
    -- Conclusion: Γ ⊢ₛ Δ where ⊥ ∈ Γ = Γ₁ ∪ Γ₂.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    -- hant : (Γ ⊢ₛ Δ).ant = Γ₁ ∪ Γ₂, which is definitionally Γ = Γ₁ ∪ Γ₂.
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    rw [hant'] at hbot
    rcases Finset.mem_union.mp hbot with hbot₁ | hbot₂
    · -- ⊥ ∈ Γ₁: choose I = ⊥; derive both halves by botL.
      refine ⟨⊥, ?_, ?_, ?_⟩
      · simp only [vars_bot, Finset.empty_subset]
      · exact ⟨LKProof.botL Γ₁ (insert ⊥ Δ₁) hbot₁⟩
      · exact ⟨LKProof.botL (insert ⊥ Γ₂) Δ₂ (Finset.mem_insert_self ⊥ Γ₂)⟩
    · -- ⊥ ∈ Γ₂: choose I = ⊤ = ⊥ → ⊥; left by impR∘botL, right by weakL∘botL.
      refine ⟨⊤, ?_, ?_, ?_⟩
      · simp only [vars_top, Finset.empty_subset]
      · -- Γ₁ ⊢ₛ insert ⊤ Δ₁ via impR applied to botL on insert ⊥ Γ₁ ⊢ₛ insert ⊥ (insert ⊤ Δ₁).
        exact ⟨LKProof.impR ⊥ ⊥ (Finset.mem_insert_self ⊤ Δ₁)
          (LKProof.botL (insert ⊥ Γ₁) (insert ⊥ (insert ⊤ Δ₁))
            (Finset.mem_insert_self ⊥ Γ₁))⟩
      · -- insert ⊤ Γ₂ ⊢ₛ Δ₂ via weakL applied to botL on Γ₂ ⊢ₛ Δ₂.
        exact ⟨LKProof.weakL ⊤ (LKProof.botL Γ₂ Δ₂ hbot₂)⟩
  | @weakL Γ Δ A d' ih =>
    -- Conclusion: insert A Γ ⊢ₛ Δ; premise: Γ ⊢ₛ Δ.
    -- Apply IH to d' with cover (Γ ∩ Γ₁) ∪ (Γ ∩ Γ₂) = Γ (uses Γ ⊆ insert A Γ = Γ₁ ∪ Γ₂).
    -- Then weaken both half-derivations via mono.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    -- Establish the cover for the premise antecedent Γ.
    have hcover : (Γ ∩ Γ₁) ∪ (Γ ∩ Γ₂) = Γ := by
      rw [← Finset.inter_union_distrib_left, ← hant]
      exact Finset.inter_eq_left.mpr (Finset.subset_insert A Γ)
    obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
      ih hcf (Γ ∩ Γ₁) (Γ ∩ Γ₂) Δ₁ Δ₂ hcover.symm hsuc
    -- Compute subset inclusions.
    have hΓ₁_sub : Γ ∩ Γ₁ ⊆ Γ₁ := Finset.inter_subset_right
    have hΓ₂_sub : Γ ∩ Γ₂ ⊆ Γ₂ := Finset.inter_subset_right
    -- Weaken the left and right half-derivations.
    have h_left' : LKProof (Γ₁ ⊢ₛ insert I Δ₁) :=
      d_left.mono hΓ₁_sub (Finset.Subset.refl _)
    have h_right' : LKProof (insert I Γ₂ ⊢ₛ Δ₂) :=
      d_right.mono (Finset.insert_subset_insert I hΓ₂_sub) (Finset.Subset.refl _)
    -- Establish the vars bound by transitivity and monotonicity.
    refine ⟨I, ?_, ⟨h_left'⟩, ⟨h_right'⟩⟩
    refine Finset.subset_inter ?_ ?_
    · calc I.vars ⊆ ((Γ ∩ Γ₁) ∪ Δ₁).vars ∩ _ := h_vars
           _ ⊆ (Γ ∩ Γ₁ ∪ Δ₁).vars := Finset.inter_subset_left
           _ ⊆ (Γ₁ ∪ Δ₁).vars := by
               simp only [Finset.vars_union]
               exact Finset.union_subset_union_left (Finset.vars_mono hΓ₁_sub)
    · calc I.vars ⊆ _ ∩ ((Γ ∩ Γ₂) ∪ Δ₂).vars := h_vars
           _ ⊆ (Γ ∩ Γ₂ ∪ Δ₂).vars := Finset.inter_subset_right
           _ ⊆ (Γ₂ ∪ Δ₂).vars := by
               simp only [Finset.vars_union]
               exact Finset.union_subset_union_left (Finset.vars_mono hΓ₂_sub)
  | @weakR Γ Δ A d' ih =>
    -- Conclusion: Γ ⊢ₛ insert A Δ; premise: Γ ⊢ₛ Δ.
    -- Dual of weakL: apply IH with reduced succedent cover.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    have hcover : (Δ ∩ Δ₁) ∪ (Δ ∩ Δ₂) = Δ := by
      rw [← Finset.inter_union_distrib_left, ← hsuc]
      exact Finset.inter_eq_left.mpr (Finset.subset_insert A Δ)
    obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
      ih hcf Γ₁ Γ₂ (Δ ∩ Δ₁) (Δ ∩ Δ₂) hant hcover.symm
    have hΔ₁_sub : Δ ∩ Δ₁ ⊆ Δ₁ := Finset.inter_subset_right
    have hΔ₂_sub : Δ ∩ Δ₂ ⊆ Δ₂ := Finset.inter_subset_right
    have h_left' : LKProof (Γ₁ ⊢ₛ insert I Δ₁) :=
      d_left.mono (Finset.Subset.refl _) (Finset.insert_subset_insert I hΔ₁_sub)
    have h_right' : LKProof (insert I Γ₂ ⊢ₛ Δ₂) :=
      d_right.mono (Finset.Subset.refl _) hΔ₂_sub
    refine ⟨I, ?_, ⟨h_left'⟩, ⟨h_right'⟩⟩
    refine Finset.subset_inter ?_ ?_
    · calc I.vars ⊆ (Γ₁ ∪ (Δ ∩ Δ₁)).vars ∩ _ := h_vars
           _ ⊆ (Γ₁ ∪ Δ ∩ Δ₁).vars := Finset.inter_subset_left
           _ ⊆ (Γ₁ ∪ Δ₁).vars := by
               simp only [Finset.vars_union]
               exact Finset.union_subset_union_right (Finset.vars_mono hΔ₁_sub)
    · calc I.vars ⊆ _ ∩ (Γ₂ ∪ (Δ ∩ Δ₂)).vars := h_vars
           _ ⊆ (Γ₂ ∪ Δ ∩ Δ₂).vars := Finset.inter_subset_right
           _ ⊆ (Γ₂ ∪ Δ₂).vars := by
               simp only [Finset.vars_union]
               exact Finset.union_subset_union_right (Finset.vars_mono hΔ₂_sub)
  | @andL Γ Δ A B hAB d' ih =>
    -- Conclusion: Γ ⊢ₛ Δ where A∧B ∈ Γ = Γ₁ ∪ Γ₂; premise: insert A (insert B Γ) ⊢ₛ Δ.
    -- Side-split on A∧B ∈ Γ₁ or A∧B ∈ Γ₂; place A,B on that side; reapply andL.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    -- hant : (Γ ⊢ₛ Δ).ant = Γ₁ ∪ Γ₂, definitionally Γ = Γ₁ ∪ Γ₂.
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    rw [hant'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A∧B ∈ Γ₁: IH with Γ₁' = insert A (insert B Γ₁), Γ₂' = Γ₂.
      -- d' : LKProof (insert A (insert B Γ) ⊢ₛ Δ); cover: insert A (insert B Γ) = Γ₁' ∪ Γ₂'.
      have hcover : insert A (insert B Γ) = insert A (insert B Γ₁) ∪ Γ₂ := by
        rw [hant']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf (insert A (insert B Γ₁)) Γ₂ Δ₁ Δ₂ hcover hsuc
      -- Compute vars bound: (insert A (insert B Γ₁)).vars ⊆ Γ₁.vars.
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁
        simp only [vars_and] at this; exact this
      have hΓ₁_vars : (insert A (insert B Γ₁)).vars ⊆ Γ₁.vars := by
        simp only [Finset.vars_insert]
        exact Finset.union_subset (Finset.subset_union_left.trans hAB_vars)
          (Finset.union_subset (Finset.subset_union_right.trans hAB_vars) (Finset.Subset.refl _))
      -- Derive the final interpolant.
      refine ⟨I, ?_, ?_, ⟨d_right⟩⟩
      · refine Finset.subset_inter ?_ (h_vars.trans Finset.inter_subset_right)
        calc I.vars ⊆ (insert A (insert B Γ₁) ∪ Δ₁).vars ∩ _ := h_vars
             _ ⊆ (insert A (insert B Γ₁) ∪ Δ₁).vars := Finset.inter_subset_left
             _ ⊆ (Γ₁ ∪ Δ₁).vars := by
                 simp only [Finset.vars_union]
                 exact Finset.union_subset_union_left hΓ₁_vars
      · -- Apply andL to the left half-derivation.
        exact ⟨LKProof.andL A B hAB₁ d_left⟩
    · -- A∧B ∈ Γ₂: IH with Γ₁' = Γ₁, Γ₂' = insert A (insert B Γ₂).
      have hcover : insert A (insert B Γ) = Γ₁ ∪ insert A (insert B Γ₂) := by
        rw [hant']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf Γ₁ (insert A (insert B Γ₂)) Δ₁ Δ₂ hcover hsuc
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂
        simp only [vars_and] at this; exact this
      have hΓ₂_vars : (insert A (insert B Γ₂)).vars ⊆ Γ₂.vars := by
        simp only [Finset.vars_insert]
        exact Finset.union_subset (Finset.subset_union_left.trans hAB_vars)
          (Finset.union_subset (Finset.subset_union_right.trans hAB_vars) (Finset.Subset.refl _))
      refine ⟨I, ?_, ⟨d_left⟩, ?_⟩
      · refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
        calc I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (insert A (insert B Γ₂) ∪ Δ₂).vars := h_vars
             _ ⊆ (insert A (insert B Γ₂) ∪ Δ₂).vars := Finset.inter_subset_right
             _ ⊆ (Γ₂ ∪ Δ₂).vars := by
                 simp only [Finset.vars_union]
                 exact Finset.union_subset_union_left hΓ₂_vars
      · -- d_right : LKProof (insert I (insert A (insert B Γ₂)) ⊢ₛ Δ₂); need antecedent permuted.
        have hperm : insert I (insert A (insert B Γ₂)) ⊆ insert A (insert B (insert I Γ₂)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.andL A B (Finset.mem_insert_of_mem hAB₂)
                  (d_right.mono hperm (Finset.Subset.refl _))⟩
  | @orR Γ Δ A B hAB d' ih =>
    -- Conclusion: Γ ⊢ₛ Δ where A∨B ∈ Δ = Δ₁ ∪ Δ₂; premise: Γ ⊢ₛ insert A (insert B Δ).
    -- Side-split on A∨B ∈ Δ₁ or A∨B ∈ Δ₂; place A,B on that side; reapply orR.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    -- hsuc : (Γ ⊢ₛ Δ).suc = Δ₁ ∪ Δ₂, definitionally Δ = Δ₁ ∪ Δ₂.
    have hsuc' : Δ = Δ₁ ∪ Δ₂ := hsuc
    rw [hsuc'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A∨B ∈ Δ₁: IH with Δ₁' = insert A (insert B Δ₁), Δ₂' = Δ₂.
      -- d' : LKProof (Γ ⊢ₛ insert A (insert B Δ)); cover: insert A (insert B Δ) = Δ₁' ∪ Δ₂'.
      have hcover : insert A (insert B Δ) = insert A (insert B Δ₁) ∪ Δ₂ := by
        rw [hsuc']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf Γ₁ Γ₂ (insert A (insert B Δ₁)) Δ₂ hant hcover
      have hAB_vars : A.vars ∪ B.vars ⊆ Δ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁
        simp only [vars_or] at this; exact this
      have hΔ₁_vars : (insert A (insert B Δ₁)).vars ⊆ Δ₁.vars := by
        simp only [Finset.vars_insert]
        exact Finset.union_subset (Finset.subset_union_left.trans hAB_vars)
          (Finset.union_subset (Finset.subset_union_right.trans hAB_vars) (Finset.Subset.refl _))
      -- Reconstruct: IH gives LKProof (Γ₁ ⊢ₛ insert I (insert A (insert B Δ₁))).
      -- Apply orR: need LKProof (Γ₁ ⊢ₛ insert A (insert B (insert I Δ₁))).
      -- These sets are equal; use mono with Finset.subset_iff.
      have hperm : insert I (insert A (insert B Δ₁)) ⊆ insert A (insert B (insert I Δ₁)) := by
        intro x; simp only [Finset.mem_insert]; tauto
      refine ⟨I, ?_, ?_, ⟨d_right⟩⟩
      · refine Finset.subset_inter ?_ (h_vars.trans Finset.inter_subset_right)
        calc I.vars ⊆ (Γ₁ ∪ insert A (insert B Δ₁)).vars ∩ _ := h_vars
             _ ⊆ (Γ₁ ∪ insert A (insert B Δ₁)).vars := Finset.inter_subset_left
             _ ⊆ (Γ₁ ∪ Δ₁).vars := by
                 simp only [Finset.vars_union]
                 exact Finset.union_subset_union_right hΔ₁_vars
      · exact ⟨LKProof.orR A B (Finset.mem_insert_of_mem hAB₁)
                 (d_left.mono (Finset.Subset.refl _) hperm)⟩
    · -- A∨B ∈ Δ₂: IH with Δ₁' = Δ₁, Δ₂' = insert A (insert B Δ₂).
      have hcover : insert A (insert B Δ) = Δ₁ ∪ insert A (insert B Δ₂) := by
        rw [hsuc']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf Γ₁ Γ₂ Δ₁ (insert A (insert B Δ₂)) hant hcover
      have hAB_vars : A.vars ∪ B.vars ⊆ Δ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂
        simp only [vars_or] at this; exact this
      have hΔ₂_vars : (insert A (insert B Δ₂)).vars ⊆ Δ₂.vars := by
        simp only [Finset.vars_insert]
        exact Finset.union_subset (Finset.subset_union_left.trans hAB_vars)
          (Finset.union_subset (Finset.subset_union_right.trans hAB_vars) (Finset.Subset.refl _))
      refine ⟨I, ?_, ⟨d_left⟩, ?_⟩
      · refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
        calc I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ insert A (insert B Δ₂)).vars := h_vars
             _ ⊆ (Γ₂ ∪ insert A (insert B Δ₂)).vars := Finset.inter_subset_right
             _ ⊆ (Γ₂ ∪ Δ₂).vars := by
                 simp only [Finset.vars_union]
                 exact Finset.union_subset_union_right hΔ₂_vars
      · -- d_right : LKProof (insert I Γ₂ ⊢ₛ insert A (insert B Δ₂)); apply orR directly.
        exact ⟨LKProof.orR A B hAB₂ d_right⟩
  | ax A Γ Δ hL hR =>
    -- Four-way case split on (A ∈ Γ₁ ∨ A ∈ Γ₂) × (A ∈ Δ₁ ∨ A ∈ Δ₂).
    -- Interpolants: (Γ₁,Δ₁)→⊥, (Γ₁,Δ₂)→A, (Γ₂,Δ₁)→¬A, (Γ₂,Δ₂)→⊤.
    intro Γ₁ Γ₂ Δ₁ Δ₂ _hant _hsuc
    have hant' : Γ = Γ₁ ∪ Γ₂ := _hant
    have hsuc' : Δ = Δ₁ ∪ Δ₂ := _hsuc
    rw [hant'] at hL
    rw [hsuc'] at hR
    rcases Finset.mem_union.mp hL with hL₁ | hL₂ <;>
    rcases Finset.mem_union.mp hR with hR₁ | hR₂
    · -- (A ∈ Γ₁, A ∈ Δ₁): I = ⊥; vars ∅; left by ax; right by botL.
      exact ⟨⊥, by simp [vars_bot],
        ⟨LKProof.ax A Γ₁ (insert ⊥ Δ₁) hL₁ (Finset.mem_insert_of_mem hR₁)⟩,
        ⟨LKProof.botL (insert ⊥ Γ₂) Δ₂ (Finset.mem_insert_self ⊥ Γ₂)⟩⟩
    · -- (A ∈ Γ₁, A ∈ Δ₂): I = A; left by ax; right by ax.
      refine ⟨A, ?_,
        ⟨LKProof.ax A Γ₁ (insert A Δ₁) hL₁ (Finset.mem_insert_self A Δ₁)⟩,
        ⟨LKProof.ax A (insert A Γ₂) Δ₂ (Finset.mem_insert_self A Γ₂) hR₂⟩⟩
      simp only [Finset.vars_union]
      exact Finset.subset_inter
        ((Finset.vars_subset_of_mem hL₁).trans Finset.subset_union_left)
        ((Finset.vars_subset_of_mem hR₂).trans Finset.subset_union_right)
    · -- (A ∈ Γ₂, A ∈ Δ₁): I = ¬A; left by impR; right by impL.
      refine ⟨¬A, ?_,
        ⟨LKProof.impR A ⊥ (Finset.mem_insert_self (¬A) Δ₁)
          (LKProof.ax A (insert A Γ₁) (insert ⊥ (insert (¬A) Δ₁))
            (Finset.mem_insert_self A Γ₁)
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hR₁)))⟩,
        ⟨LKProof.impL A ⊥ (Finset.mem_insert_self (¬A) Γ₂)
          (LKProof.ax A (insert (¬A) Γ₂) (insert A Δ₂)
            (Finset.mem_insert_of_mem hL₂) (Finset.mem_insert_self A Δ₂))
          (LKProof.botL (insert ⊥ (insert (¬A) Γ₂)) Δ₂
            (Finset.mem_insert_self ⊥ (insert (¬A) Γ₂)))⟩⟩
      simp only [vars_neg, Finset.vars_union]
      exact Finset.subset_inter
        ((Finset.vars_subset_of_mem hR₁).trans Finset.subset_union_right)
        ((Finset.vars_subset_of_mem hL₂).trans Finset.subset_union_left)
    · -- (A ∈ Γ₂, A ∈ Δ₂): I = ⊤; vars ∅; left by impR∘botL; right by ax.
      exact ⟨⊤, by simp [vars_top],
        ⟨LKProof.impR ⊥ ⊥ (Finset.mem_insert_self ⊤ Δ₁)
          (LKProof.botL (insert ⊥ Γ₁) (insert ⊥ (insert ⊤ Δ₁))
            (Finset.mem_insert_self ⊥ Γ₁))⟩,
        ⟨LKProof.ax A (insert ⊤ Γ₂) Δ₂
          (Finset.mem_insert_of_mem hL₂) hR₂⟩⟩
  | @andR Γ Δ A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ₛ Δ where A∧B ∈ Δ = Δ₁ ∪ Δ₂; two premises:
    --   d₁ : Γ ⊢ₛ insert A Δ,  d₂ : Γ ⊢ₛ insert B Δ.
    -- CutFree: hcf.1 : CutFree d₁, hcf.2 : CutFree d₂.
    -- Side-split on A∧B ∈ Δ₁ or A∧B ∈ Δ₂; combine I₁ ∨ I₂ resp. I₁ ∧ I₂.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    have hsuc' : Δ = Δ₁ ∪ Δ₂ := hsuc
    rw [hsuc'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A∧B ∈ Δ₁: interpolant I = I₁ ∨ I₂.
      -- Place A on Δ₁ side for d₁, B on Δ₁ side for d₂; combine left with andR+orR, right with orL.
      have hAB_vars : A.vars ∪ B.vars ⊆ Δ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁; simp only [vars_and] at this; exact this
      have hA_vars : A.vars ⊆ Δ₁.vars := Finset.subset_union_left.trans hAB_vars
      have hB_vars : B.vars ⊆ Δ₁.vars := Finset.subset_union_right.trans hAB_vars
      have hcover₁ : insert A Δ = insert A Δ₁ ∪ Δ₂ := by
        rw [hsuc']; exact (Finset.insert_union A Δ₁ Δ₂).symm
      have hcover₂ : insert B Δ = insert B Δ₁ ∪ Δ₂ := by
        rw [hsuc']; exact (Finset.insert_union B Δ₁ Δ₂).symm
      obtain ⟨hcf₁, hcf₂⟩ := hcf
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ Γ₁ Γ₂ (insert A Δ₁) Δ₂ hant' hcover₁
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ Γ₁ Γ₂ (insert B Δ₁) Δ₂ hant' hcover₂
      refine ⟨I₁ ∨ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∨I₂).vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars
        simp only [vars_or]
        refine Finset.subset_inter ?_ ?_
        · apply Finset.union_subset
          · have h₁L : I₁.vars ⊆ (Γ₁ ∪ insert A Δ₁).vars :=
              h_vars₁.trans Finset.inter_subset_left
            have h_A_drop : (Γ₁ ∪ insert A Δ₁).vars ⊆ (Γ₁ ∪ Δ₁).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset Finset.subset_union_left
                (Finset.union_subset (hA_vars.trans Finset.subset_union_right)
                  Finset.subset_union_right)
            exact h₁L.trans h_A_drop
          · have h₂L : I₂.vars ⊆ (Γ₁ ∪ insert B Δ₁).vars :=
              h_vars₂.trans Finset.inter_subset_left
            have h_B_drop : (Γ₁ ∪ insert B Δ₁).vars ⊆ (Γ₁ ∪ Δ₁).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset Finset.subset_union_left
                (Finset.union_subset (hB_vars.trans Finset.subset_union_right)
                  Finset.subset_union_right)
            exact h₂L.trans h_B_drop
        · apply Finset.union_subset
          · exact h_vars₁.trans Finset.inter_subset_right
          · exact h_vars₂.trans Finset.inter_subset_right
      · -- Left half: Γ₁ ⊢ₛ insert (I₁∨I₂) Δ₁.
        -- Use andR A B; each premise (insert A / insert B) comes from orR I₁ I₂ + mono.
        have hAB₁' : (A ∧ B) ∈ insert (I₁ ∨ I₂) Δ₁ := Finset.mem_insert_of_mem hAB₁
        -- Γ₁ ⊢ₛ insert A (insert (I₁∨I₂) Δ₁) via orR I₁ I₂.
        have hperm_A : insert I₁ (insert A Δ₁) ⊆
            insert I₁ (insert I₂ (insert A (insert (I₁ ∨ I₂) Δ₁))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have d_left₁' : LKProof (Γ₁ ⊢ₛ insert A (insert (I₁ ∨ I₂) Δ₁)) :=
          LKProof.orR I₁ I₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            (d_left₁.mono (Finset.Subset.refl _) hperm_A)
        -- Γ₁ ⊢ₛ insert B (insert (I₁∨I₂) Δ₁) via orR I₁ I₂.
        have hperm_B : insert I₂ (insert B Δ₁) ⊆
            insert I₁ (insert I₂ (insert B (insert (I₁ ∨ I₂) Δ₁))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have d_left₂' : LKProof (Γ₁ ⊢ₛ insert B (insert (I₁ ∨ I₂) Δ₁)) :=
          LKProof.orR I₁ I₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            (d_left₂.mono (Finset.Subset.refl _) hperm_B)
        exact ⟨LKProof.andR A B hAB₁' d_left₁' d_left₂'⟩
      · -- Right half: insert (I₁∨I₂) Γ₂ ⊢ₛ Δ₂ via orL I₁ I₂.
        have hperm_I₁ : insert I₁ Γ₂ ⊆ insert I₁ (insert (I₁ ∨ I₂) Γ₂) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm_I₂ : insert I₂ Γ₂ ⊆ insert I₂ (insert (I₁ ∨ I₂) Γ₂) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.orL I₁ I₂ (Finset.mem_insert_self _ _)
          (d_right₁.mono hperm_I₁ (Finset.Subset.refl _))
          (d_right₂.mono hperm_I₂ (Finset.Subset.refl _))⟩
    · -- A∧B ∈ Δ₂: interpolant I = I₁ ∧ I₂.
      -- Place A on Δ₂ side for d₁, B on Δ₂ side for d₂;
      -- left with andR I₁ I₂; right with andL+andR A B.
      have hAB_vars₂ : A.vars ∪ B.vars ⊆ Δ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂; simp only [vars_and] at this; exact this
      have hA_vars₂ : A.vars ⊆ Δ₂.vars := Finset.subset_union_left.trans hAB_vars₂
      have hB_vars₂ : B.vars ⊆ Δ₂.vars := Finset.subset_union_right.trans hAB_vars₂
      have hcover₁' : insert A Δ = Δ₁ ∪ insert A Δ₂ := by
        rw [hsuc']; exact (Finset.union_insert A Δ₁ Δ₂).symm
      have hcover₂' : insert B Δ = Δ₁ ∪ insert B Δ₂ := by
        rw [hsuc']; exact (Finset.union_insert B Δ₁ Δ₂).symm
      obtain ⟨hcf₁, hcf₂⟩ := hcf
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ Γ₁ Γ₂ Δ₁ (insert A Δ₂) hant' hcover₁'
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ Γ₁ Γ₂ Δ₁ (insert B Δ₂) hant' hcover₂'
      refine ⟨I₁ ∧ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∧I₂).vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars
        simp only [vars_and]
        refine Finset.subset_inter ?_ ?_
        · apply Finset.union_subset
          · exact h_vars₁.trans Finset.inter_subset_left
          · exact h_vars₂.trans Finset.inter_subset_left
        · apply Finset.union_subset
          · have h₁R : I₁.vars ⊆ (Γ₂ ∪ insert A Δ₂).vars :=
              h_vars₁.trans Finset.inter_subset_right
            have h_A_drop₂ : (Γ₂ ∪ insert A Δ₂).vars ⊆ (Γ₂ ∪ Δ₂).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset Finset.subset_union_left
                (Finset.union_subset (hA_vars₂.trans Finset.subset_union_right)
                  Finset.subset_union_right)
            exact h₁R.trans h_A_drop₂
          · have h₂R : I₂.vars ⊆ (Γ₂ ∪ insert B Δ₂).vars :=
              h_vars₂.trans Finset.inter_subset_right
            have h_B_drop₂ : (Γ₂ ∪ insert B Δ₂).vars ⊆ (Γ₂ ∪ Δ₂).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset Finset.subset_union_left
                (Finset.union_subset (hB_vars₂.trans Finset.subset_union_right)
                  Finset.subset_union_right)
            exact h₂R.trans h_B_drop₂
      · -- Left half: Γ₁ ⊢ₛ insert (I₁∧I₂) Δ₁ via andR I₁ I₂ + mono.
        -- d_left₁ : Γ₁ ⊢ₛ insert I₁ Δ₁; d_left₂ : Γ₁ ⊢ₛ insert I₂ Δ₁.
        have hweaken₁ : insert I₁ Δ₁ ⊆ insert I₁ (insert (I₁ ∧ I₂) Δ₁) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hweaken₂ : insert I₂ Δ₁ ⊆ insert I₂ (insert (I₁ ∧ I₂) Δ₁) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.andR I₁ I₂ (Finset.mem_insert_self _ _)
          (d_left₁.mono (Finset.Subset.refl _) hweaken₁)
          (d_left₂.mono (Finset.Subset.refl _) hweaken₂)⟩
      · -- Right half: insert (I₁∧I₂) Γ₂ ⊢ₛ Δ₂.
        -- Use andL I₁ I₂ to decompose I₁∧I₂ in antecedent, then andR A B for the goal.
        -- d_right₁ : insert I₁ Γ₂ ⊢ₛ insert A Δ₂; d_right₂ : insert I₂ Γ₂ ⊢ₛ insert B Δ₂.
        have hperm₁_ant : insert I₁ Γ₂ ⊆ insert I₁ (insert I₂ (insert (I₁ ∧ I₂) Γ₂)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm₂_ant : insert I₂ Γ₂ ⊆ insert I₁ (insert I₂ (insert (I₁ ∧ I₂) Γ₂)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
          (LKProof.andR A B hAB₂
            (d_right₁.mono hperm₁_ant (Finset.Subset.refl _))
            (d_right₂.mono hperm₂_ant (Finset.Subset.refl _)))⟩
  | @orL Γ Δ A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ₛ Δ where A∨B ∈ Γ = Γ₁ ∪ Γ₂; two premises:
    --   d₁ : insert A Γ ⊢ₛ Δ,  d₂ : insert B Γ ⊢ₛ Δ.
    -- CutFree: hcf.1 : CutFree d₁, hcf.2 : CutFree d₂.
    -- Side-split on A∨B ∈ Γ₁ or A∨B ∈ Γ₂; combine I₁ ∨ I₂ resp. I₁ ∧ I₂.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    have hsuc' : Δ = Δ₁ ∪ Δ₂ := hsuc
    rw [hant'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A∨B ∈ Γ₁: interpolant I = I₁ ∨ I₂.
      -- Place A on Γ₁ side for d₁, B on Γ₁ side for d₂; combine left with orL+orR, right with orL.
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁; simp only [vars_or] at this; exact this
      have hA_vars : A.vars ⊆ Γ₁.vars := Finset.subset_union_left.trans hAB_vars
      have hB_vars : B.vars ⊆ Γ₁.vars := Finset.subset_union_right.trans hAB_vars
      have hcover₁ : insert A Γ = insert A Γ₁ ∪ Γ₂ := by
        rw [hant']; exact (Finset.insert_union A Γ₁ Γ₂).symm
      have hcover₂ : insert B Γ = insert B Γ₁ ∪ Γ₂ := by
        rw [hant']; exact (Finset.insert_union B Γ₁ Γ₂).symm
      obtain ⟨hcf₁, hcf₂⟩ := hcf
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ (insert A Γ₁) Γ₂ Δ₁ Δ₂ hcover₁ hsuc'
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ (insert B Γ₁) Γ₂ Δ₁ Δ₂ hcover₂ hsuc'
      refine ⟨I₁ ∨ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∨I₂).vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars
        simp only [vars_or]
        refine Finset.subset_inter ?_ ?_
        · apply Finset.union_subset
          · have h₁L : I₁.vars ⊆ (insert A Γ₁ ∪ Δ₁).vars :=
              h_vars₁.trans Finset.inter_subset_left
            have h_A_drop : (insert A Γ₁ ∪ Δ₁).vars ⊆ (Γ₁ ∪ Δ₁).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset
                (Finset.union_subset (hA_vars.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₁L.trans h_A_drop
          · have h₂L : I₂.vars ⊆ (insert B Γ₁ ∪ Δ₁).vars :=
              h_vars₂.trans Finset.inter_subset_left
            have h_B_drop : (insert B Γ₁ ∪ Δ₁).vars ⊆ (Γ₁ ∪ Δ₁).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset
                (Finset.union_subset (hB_vars.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₂L.trans h_B_drop
        · apply Finset.union_subset
          · exact h_vars₁.trans Finset.inter_subset_right
          · exact h_vars₂.trans Finset.inter_subset_right
      · -- Left half: Γ₁ ⊢ₛ insert (I₁∨I₂) Δ₁.
        -- Use orL A B; each premise (insert A / insert B) comes from orR I₁ I₂ + mono.
        have hperm_A : insert I₁ Δ₁ ⊆ insert I₁ (insert I₂ (insert (I₁ ∨ I₂) Δ₁)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have d_left₁' : LKProof (insert A Γ₁ ⊢ₛ insert (I₁ ∨ I₂) Δ₁) :=
          LKProof.orR I₁ I₂ (Finset.mem_insert_self _ _)
            (d_left₁.mono (Finset.Subset.refl _) hperm_A)
        have hperm_B : insert I₂ Δ₁ ⊆ insert I₁ (insert I₂ (insert (I₁ ∨ I₂) Δ₁)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have d_left₂' : LKProof (insert B Γ₁ ⊢ₛ insert (I₁ ∨ I₂) Δ₁) :=
          LKProof.orR I₁ I₂ (Finset.mem_insert_self _ _)
            (d_left₂.mono (Finset.Subset.refl _) hperm_B)
        exact ⟨LKProof.orL A B hAB₁ d_left₁' d_left₂'⟩
      · -- Right half: insert (I₁∨I₂) Γ₂ ⊢ₛ Δ₂ via orL I₁ I₂.
        have hperm_I₁ : insert I₁ Γ₂ ⊆ insert I₁ (insert (I₁ ∨ I₂) Γ₂) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm_I₂ : insert I₂ Γ₂ ⊆ insert I₂ (insert (I₁ ∨ I₂) Γ₂) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.orL I₁ I₂ (Finset.mem_insert_self _ _)
          (d_right₁.mono hperm_I₁ (Finset.Subset.refl _))
          (d_right₂.mono hperm_I₂ (Finset.Subset.refl _))⟩
    · -- A∨B ∈ Γ₂: interpolant I = I₁ ∧ I₂.
      -- Place A on Γ₂ side for d₁, B on Γ₂ side for d₂;
      -- combine left with andR I₁ I₂; right with andL+orL A B.
      have hAB_vars₂ : A.vars ∪ B.vars ⊆ Γ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂; simp only [vars_or] at this; exact this
      have hA_vars₂ : A.vars ⊆ Γ₂.vars := Finset.subset_union_left.trans hAB_vars₂
      have hB_vars₂ : B.vars ⊆ Γ₂.vars := Finset.subset_union_right.trans hAB_vars₂
      have hcover₁' : insert A Γ = Γ₁ ∪ insert A Γ₂ := by
        rw [hant']; exact (Finset.union_insert A Γ₁ Γ₂).symm
      have hcover₂' : insert B Γ = Γ₁ ∪ insert B Γ₂ := by
        rw [hant']; exact (Finset.union_insert B Γ₁ Γ₂).symm
      obtain ⟨hcf₁, hcf₂⟩ := hcf
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ Γ₁ (insert A Γ₂) Δ₁ Δ₂ hcover₁' hsuc'
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ Γ₁ (insert B Γ₂) Δ₁ Δ₂ hcover₂' hsuc'
      refine ⟨I₁ ∧ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∧I₂).vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars
        simp only [vars_and]
        refine Finset.subset_inter ?_ ?_
        · apply Finset.union_subset
          · exact h_vars₁.trans Finset.inter_subset_left
          · exact h_vars₂.trans Finset.inter_subset_left
        · apply Finset.union_subset
          · have h₁R : I₁.vars ⊆ (insert A Γ₂ ∪ Δ₂).vars :=
              h_vars₁.trans Finset.inter_subset_right
            have h_A_drop₂ : (insert A Γ₂ ∪ Δ₂).vars ⊆ (Γ₂ ∪ Δ₂).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset
                (Finset.union_subset (hA_vars₂.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₁R.trans h_A_drop₂
          · have h₂R : I₂.vars ⊆ (insert B Γ₂ ∪ Δ₂).vars :=
              h_vars₂.trans Finset.inter_subset_right
            have h_B_drop₂ : (insert B Γ₂ ∪ Δ₂).vars ⊆ (Γ₂ ∪ Δ₂).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset
                (Finset.union_subset (hB_vars₂.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₂R.trans h_B_drop₂
      · -- Left half: Γ₁ ⊢ₛ insert (I₁∧I₂) Δ₁ via andR I₁ I₂ + mono.
        -- d_left₁ : Γ₁ ⊢ₛ insert I₁ Δ₁; d_left₂ : Γ₁ ⊢ₛ insert I₂ Δ₁.
        have hweaken₁ : insert I₁ Δ₁ ⊆ insert I₁ (insert (I₁ ∧ I₂) Δ₁) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hweaken₂ : insert I₂ Δ₁ ⊆ insert I₂ (insert (I₁ ∧ I₂) Δ₁) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.andR I₁ I₂ (Finset.mem_insert_self _ _)
          (d_left₁.mono (Finset.Subset.refl _) hweaken₁)
          (d_left₂.mono (Finset.Subset.refl _) hweaken₂)⟩
      · -- Right half: insert (I₁∧I₂) Γ₂ ⊢ₛ Δ₂.
        -- Use andL I₁ I₂ to decompose I₁∧I₂ in antecedent, then orL A B for the goal.
        -- d_right₁ : insert I₁ (insert A Γ₂) ⊢ₛ Δ₂; d_right₂ : insert I₂ (insert B Γ₂) ⊢ₛ Δ₂.
        have hperm₁_ant : insert I₁ (insert A Γ₂) ⊆
            insert A (insert I₁ (insert I₂ (insert (I₁ ∧ I₂) Γ₂))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm₂_ant : insert I₂ (insert B Γ₂) ⊆
            insert B (insert I₁ (insert I₂ (insert (I₁ ∧ I₂) Γ₂))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
          (LKProof.orL A B
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem hAB₂)))
            (d_right₁.mono hperm₁_ant (Finset.Subset.refl _))
            (d_right₂.mono hperm₂_ant (Finset.Subset.refl _)))⟩
  | @impL Γ Δ A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ₛ Δ where (A→B) ∈ Γ = Γ₁ ∪ Γ₂; two asymmetric premises:
    --   d₁ : Γ ⊢ₛ insert A Δ  (A added to succedent)
    --   d₂ : insert B Γ ⊢ₛ Δ  (B added to antecedent)
    -- Side-split on (A→B) ∈ Γ₁ or (A→B) ∈ Γ₂; combine I₁∨I₂ resp. I₁∧I₂.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    have hsuc' : Δ = Δ₁ ∪ Δ₂ := hsuc
    obtain ⟨hcf₁, hcf₂⟩ := hcf
    rw [hant'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- (A→B) ∈ Γ₁: interpolant I = I₁ ∨ I₂.
      -- Place A on Δ₁ side for d₁, B on Γ₁ side for d₂; combine via orR and orL.
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁; simp only [vars_imp] at this; exact this
      have hA_vars : A.vars ⊆ Γ₁.vars := Finset.subset_union_left.trans hAB_vars
      have hB_vars : B.vars ⊆ Γ₁.vars := Finset.subset_union_right.trans hAB_vars
      have hcover_suc₁ : insert A Δ = insert A Δ₁ ∪ Δ₂ := by
        rw [hsuc']; exact (Finset.insert_union A Δ₁ Δ₂).symm
      have hcover_ant₂ : insert B Γ = insert B Γ₁ ∪ Γ₂ := by
        rw [hant']; exact (Finset.insert_union B Γ₁ Γ₂).symm
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ Γ₁ Γ₂ (insert A Δ₁) Δ₂ hant' hcover_suc₁
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ (insert B Γ₁) Γ₂ Δ₁ Δ₂ hcover_ant₂ hsuc'
      -- d_left₁ : Γ₁ ⊢ₛ insert I₁ (insert A Δ₁)
      -- d_right₁ : insert I₁ Γ₂ ⊢ₛ Δ₂
      -- d_left₂ : insert B Γ₁ ⊢ₛ insert I₂ Δ₁
      -- d_right₂ : insert I₂ Γ₂ ⊢ₛ Δ₂
      refine ⟨I₁ ∨ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∨I₂).vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars
        simp only [vars_or]
        refine Finset.subset_inter ?_ ?_
        · apply Finset.union_subset
          · have h₁L : I₁.vars ⊆ (Γ₁ ∪ insert A Δ₁).vars :=
              h_vars₁.trans Finset.inter_subset_left
            have h_A_drop : (Γ₁ ∪ insert A Δ₁).vars ⊆ (Γ₁ ∪ Δ₁).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset Finset.subset_union_left
                (Finset.union_subset (hA_vars.trans Finset.subset_union_left)
                  Finset.subset_union_right)
            exact h₁L.trans h_A_drop
          · have h₂L : I₂.vars ⊆ (insert B Γ₁ ∪ Δ₁).vars :=
              h_vars₂.trans Finset.inter_subset_left
            have h_B_drop : (insert B Γ₁ ∪ Δ₁).vars ⊆ (Γ₁ ∪ Δ₁).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset
                (Finset.union_subset (hB_vars.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₂L.trans h_B_drop
        · apply Finset.union_subset
          · exact h_vars₁.trans Finset.inter_subset_right
          · exact h_vars₂.trans Finset.inter_subset_right
      · -- Left half: Γ₁ ⊢ₛ insert (I₁∨I₂) Δ₁.
        -- Apply impL A B hAB₁ with both prems built via orR.
        --   left prem: Γ₁ ⊢ₛ insert A (insert (I₁∨I₂) Δ₁)  via orR from d_left₁
        --   right prem: insert B Γ₁ ⊢ₛ insert (I₁∨I₂) Δ₁   via orR from d_left₂
        have hperm_lprem : insert I₁ (insert A Δ₁) ⊆
            insert I₁ (insert I₂ (insert A (insert (I₁ ∨ I₂) Δ₁))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm_rprem : insert I₂ Δ₁ ⊆
            insert I₁ (insert I₂ (insert (I₁ ∨ I₂) Δ₁)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.impL A B hAB₁
          (LKProof.orR I₁ I₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            (d_left₁.mono (Finset.Subset.refl _) hperm_lprem))
          (LKProof.orR I₁ I₂ (Finset.mem_insert_self _ _)
            (d_left₂.mono (Finset.Subset.refl _) hperm_rprem))⟩
      · -- Right half: insert (I₁∨I₂) Γ₂ ⊢ₛ Δ₂ via orL I₁ I₂.
        -- d_right₁ : insert I₁ Γ₂ ⊢ₛ Δ₂; d_right₂ : insert I₂ Γ₂ ⊢ₛ Δ₂.
        have hperm_I₁ : insert I₁ Γ₂ ⊆ insert I₁ (insert (I₁ ∨ I₂) Γ₂) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm_I₂ : insert I₂ Γ₂ ⊆ insert I₂ (insert (I₁ ∨ I₂) Γ₂) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.orL I₁ I₂ (Finset.mem_insert_self _ _)
          (d_right₁.mono hperm_I₁ (Finset.Subset.refl _))
          (d_right₂.mono hperm_I₂ (Finset.Subset.refl _))⟩
    · -- (A→B) ∈ Γ₂: interpolant I = I₁ ∧ I₂.
      -- Place A on Δ₂ side for d₁, B on Γ₂ side for d₂; combine via andR and andL+impL.
      have hAB_vars₂ : A.vars ∪ B.vars ⊆ Γ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂; simp only [vars_imp] at this; exact this
      have hA_vars₂ : A.vars ⊆ Γ₂.vars := Finset.subset_union_left.trans hAB_vars₂
      have hB_vars₂ : B.vars ⊆ Γ₂.vars := Finset.subset_union_right.trans hAB_vars₂
      have hcover_suc₁' : insert A Δ = Δ₁ ∪ insert A Δ₂ := by
        rw [hsuc']; exact (Finset.union_insert A Δ₁ Δ₂).symm
      have hcover_ant₂' : insert B Γ = Γ₁ ∪ insert B Γ₂ := by
        rw [hant']; exact (Finset.union_insert B Γ₁ Γ₂).symm
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ Γ₁ Γ₂ Δ₁ (insert A Δ₂) hant' hcover_suc₁'
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ Γ₁ (insert B Γ₂) Δ₁ Δ₂ hcover_ant₂' hsuc'
      -- d_left₁ : Γ₁ ⊢ₛ insert I₁ Δ₁
      -- d_right₁ : insert I₁ Γ₂ ⊢ₛ insert A Δ₂
      -- d_left₂ : Γ₁ ⊢ₛ insert I₂ Δ₁
      -- d_right₂ : insert I₂ (insert B Γ₂) ⊢ₛ Δ₂
      refine ⟨I₁ ∧ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∧I₂).vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars
        simp only [vars_and]
        refine Finset.subset_inter ?_ ?_
        · apply Finset.union_subset
          · exact h_vars₁.trans Finset.inter_subset_left
          · exact h_vars₂.trans Finset.inter_subset_left
        · apply Finset.union_subset
          · have h₁R : I₁.vars ⊆ (Γ₂ ∪ insert A Δ₂).vars :=
              h_vars₁.trans Finset.inter_subset_right
            have h_A_drop₂ : (Γ₂ ∪ insert A Δ₂).vars ⊆ (Γ₂ ∪ Δ₂).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset Finset.subset_union_left
                (Finset.union_subset (hA_vars₂.trans Finset.subset_union_left)
                  Finset.subset_union_right)
            exact h₁R.trans h_A_drop₂
          · have h₂R : I₂.vars ⊆ (insert B Γ₂ ∪ Δ₂).vars :=
              h_vars₂.trans Finset.inter_subset_right
            have h_B_drop₂ : (insert B Γ₂ ∪ Δ₂).vars ⊆ (Γ₂ ∪ Δ₂).vars := by
              simp only [Finset.vars_union, Finset.vars_insert]
              exact Finset.union_subset
                (Finset.union_subset (hB_vars₂.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₂R.trans h_B_drop₂
      · -- Left half: Γ₁ ⊢ₛ insert (I₁∧I₂) Δ₁ via andR I₁ I₂.
        -- d_left₁ : Γ₁ ⊢ₛ insert I₁ Δ₁; d_left₂ : Γ₁ ⊢ₛ insert I₂ Δ₁.
        have hweaken₁ : insert I₁ Δ₁ ⊆ insert I₁ (insert (I₁ ∧ I₂) Δ₁) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hweaken₂ : insert I₂ Δ₁ ⊆ insert I₂ (insert (I₁ ∧ I₂) Δ₁) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.andR I₁ I₂ (Finset.mem_insert_self _ _)
          (d_left₁.mono (Finset.Subset.refl _) hweaken₁)
          (d_left₂.mono (Finset.Subset.refl _) hweaken₂)⟩
      · -- Right half: insert (I₁∧I₂) Γ₂ ⊢ₛ Δ₂.
        -- Apply impL A B (A→B ∈ insert (I₁∧I₂) Γ₂):
        --   left prem: insert (I₁∧I₂) Γ₂ ⊢ₛ insert A Δ₂  via andL from d_right₁
        --   right prem: insert B (insert (I₁∧I₂) Γ₂) ⊢ₛ Δ₂ via andL from d_right₂
        have hperm_r1 : insert I₁ Γ₂ ⊆
            insert I₁ (insert I₂ (insert (I₁ ∧ I₂) Γ₂)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm_r2 : insert I₂ (insert B Γ₂) ⊆
            insert I₁ (insert I₂ (insert B (insert (I₁ ∧ I₂) Γ₂))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨LKProof.impL A B (Finset.mem_insert_of_mem hAB₂)
          (LKProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
            (d_right₁.mono hperm_r1 (Finset.Subset.refl _)))
          (LKProof.andL I₁ I₂
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            (d_right₂.mono hperm_r2 (Finset.Subset.refl _)))⟩
  | @impR Γ Δ A B hAB d' ih =>
    -- Conclusion: Γ ⊢ₛ Δ where A→B ∈ Δ = Δ₁ ∪ Δ₂; premise: insert A Γ ⊢ₛ insert B Δ.
    -- Side-split on A→B ∈ Δ₁ or A→B ∈ Δ₂; place A on the antecedent and B on the
    -- succedent of the chosen half; reuse the IH interpolant I; reapply impR.
    intro Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    have hsuc' : Δ = Δ₁ ∪ Δ₂ := hsuc
    rw [hsuc'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A→B ∈ Δ₁: IH with Γ₁' = insert A Γ₁, Δ₁' = insert B Δ₁; interpolant I goes left.
      -- d' : insert A Γ ⊢ₛ insert B Δ; cover ant = insert A Γ₁ ∪ Γ₂, suc = insert B Δ₁ ∪ Δ₂.
      have hcover_ant : insert A Γ = insert A Γ₁ ∪ Γ₂ := by
        rw [hant']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      have hcover_suc : insert B Δ = insert B Δ₁ ∪ Δ₂ := by
        rw [hsuc']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf (insert A Γ₁) Γ₂ (insert B Δ₁) Δ₂ hcover_ant hcover_suc
      -- vars bound: A.vars ∪ B.vars ⊆ Δ₁.vars since A→B ∈ Δ₁.
      have hAB_vars : A.vars ∪ B.vars ⊆ Δ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁; simp only [vars_imp] at this; exact this
      -- Permute succedent: insert I (insert B Δ₁) ⊆ insert B (insert I Δ₁).
      have hperm : insert I (insert B Δ₁) ⊆ insert B (insert I Δ₁) := by
        intro x; simp only [Finset.mem_insert]; tauto
      refine ⟨I, ?_, ?_, ⟨d_right⟩⟩
      · -- vars: I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars.
        refine Finset.subset_inter ?_ (h_vars.trans Finset.inter_subset_right)
        calc I.vars ⊆ (insert A Γ₁ ∪ insert B Δ₁).vars ∩ _ := h_vars
             _ ⊆ (insert A Γ₁ ∪ insert B Δ₁).vars := Finset.inter_subset_left
             _ ⊆ (Γ₁ ∪ Δ₁).vars := by
                 have hA : A.vars ⊆ Δ₁.vars := Finset.subset_union_left.trans hAB_vars
                 have hB : B.vars ⊆ Δ₁.vars := Finset.subset_union_right.trans hAB_vars
                 simp only [Finset.vars_union, Finset.vars_insert]
                 exact Finset.union_subset
                   (Finset.union_subset (hA.trans Finset.subset_union_right)
                     Finset.subset_union_left)
                   (Finset.union_subset (hB.trans Finset.subset_union_right)
                     Finset.subset_union_right)
      · -- Left half: d_left : insert A Γ₁ ⊢ₛ insert I (insert B Δ₁).
        -- Permute suc to insert B (insert I Δ₁); apply impR to get Γ₁ ⊢ₛ insert I Δ₁.
        exact ⟨LKProof.impR A B (Finset.mem_insert_of_mem hAB₁)
                 (d_left.mono (Finset.Subset.refl _) hperm)⟩
    · -- A→B ∈ Δ₂: IH with Γ₂' = insert A Γ₂, Δ₂' = insert B Δ₂; interpolant I goes right.
      have hcover_ant : insert A Γ = Γ₁ ∪ insert A Γ₂ := by
        rw [hant']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      have hcover_suc : insert B Δ = Δ₁ ∪ insert B Δ₂ := by
        rw [hsuc']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf Γ₁ (insert A Γ₂) Δ₁ (insert B Δ₂) hcover_ant hcover_suc
      -- vars bound: A.vars ∪ B.vars ⊆ Δ₂.vars since A→B ∈ Δ₂.
      have hAB_vars : A.vars ∪ B.vars ⊆ Δ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂; simp only [vars_imp] at this; exact this
      -- Permute antecedent: insert I (insert A Γ₂) ⊆ insert A (insert I Γ₂).
      have hperm : insert I (insert A Γ₂) ⊆ insert A (insert I Γ₂) := by
        intro x; simp only [Finset.mem_insert]; tauto
      refine ⟨I, ?_, ⟨d_left⟩, ?_⟩
      · -- vars: I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars.
        refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
        calc I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (insert A Γ₂ ∪ insert B Δ₂).vars := h_vars
             _ ⊆ (insert A Γ₂ ∪ insert B Δ₂).vars := Finset.inter_subset_right
             _ ⊆ (Γ₂ ∪ Δ₂).vars := by
                 have hA : A.vars ⊆ Δ₂.vars := Finset.subset_union_left.trans hAB_vars
                 have hB : B.vars ⊆ Δ₂.vars := Finset.subset_union_right.trans hAB_vars
                 simp only [Finset.vars_union, Finset.vars_insert]
                 exact Finset.union_subset
                   (Finset.union_subset (hA.trans Finset.subset_union_right)
                     Finset.subset_union_left)
                   (Finset.union_subset (hB.trans Finset.subset_union_right)
                     Finset.subset_union_right)
      · -- Right half: d_right : insert I (insert A Γ₂) ⊢ₛ insert B Δ₂.
        -- Permute ant to insert A (insert I Γ₂); apply impR (A→B ∈ Δ₂) to get insert I Γ₂ ⊢ₛ Δ₂.
        exact ⟨LKProof.impR A B hAB₂ (d_right.mono hperm (Finset.Subset.refl _))⟩

/-! ## General Split Interpolation (Public) -/

/-- **LK split interpolation**: the general-partition form of Craig interpolation, publicly
exposed. For any cut-free LK proof (bundled as `CutFreeLKProof seq`) and any cover partition
`Γ₁ ∪ Γ₂ = seq.ant`, `Δ₁ ∪ Δ₂ = seq.suc`, there exists an interpolant `I` satisfying:
1. `I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars` (variable constraint),
2. `Γ₁ ⊢ₛ insert I Δ₁` (left half-derivation), and
3. `insert I Γ₂ ⊢ₛ Δ₂` (right half-derivation).

This is a thin public wrapper around `maeharaCore` (which stays `private`, since un-privatising
it would expose an internal induction shape as API). `LKProof.interpolation` below remains the
empty-context implication specialisation of this general-partition form. -/
theorem LKProof.splitInterpolation {seq : LKSequent Atom} (d : CutFreeLKProof seq)
    (Γ₁ Γ₂ Δ₁ Δ₂ : Finset (Proposition Atom))
    (hant : seq.ant = Γ₁ ∪ Γ₂) (hsuc : seq.suc = Δ₁ ∪ Δ₂) :
    ∃ I : Proposition Atom,
      I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars ∧
      Nonempty (LKProof (Γ₁ ⊢ₛ insert I Δ₁)) ∧
      Nonempty (LKProof (insert I Γ₂ ⊢ₛ Δ₂)) :=
  maeharaCore d.1 d.2 Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc

/-! ## LK Craig Interpolation Corollary -/

/-- **LK Craig Interpolation** (corollary): From any LK proof of `∅ ⊢ₛ {A → B}`, there exists
an interpolant `I` such that:
1. `I.vars ⊆ A.vars ∩ B.vars` (variable constraint),
2. `∅ ⊢ₛ {A → I}` (left half-implication), and
3. `∅ ⊢ₛ {I → B}` (right half-implication).

Uses `maeharaCore` with the cover partition `Γ₁ = {A}`, `Γ₂ = ∅`, `Δ₁ = ∅`, `Δ₂ = {B}`,
applied to a cut-free proof of `{A} ⊢ₛ {B}` extracted from `d` via `cutElim`.

Reference: [TroelstraSchwichtenberg2000] §4; [NegriVonPlato2001] §3.3. -/
private lemma lkCraigInterpolation {A B : Proposition Atom}
    (d : LKProof ((∅ : Finset (Proposition Atom)) ⊢ₛ insert (A → B) ∅)) :
    ∃ I : Proposition Atom,
      I.vars ⊆ A.vars ∩ B.vars ∧
      Nonempty (LKProof ((∅ : Finset (Proposition Atom)) ⊢ₛ insert (A → I) ∅)) ∧
      Nonempty (LKProof ((∅ : Finset (Proposition Atom)) ⊢ₛ insert (I → B) ∅)) := by
  -- Build a (cut-using) proof of {A} ⊢ₛ {B} from d via cut on A→B and impL.
  have d_AB : LKProof (insert A ∅ ⊢ₛ insert B ∅) :=
    LKProof.cut (A → B)
      -- left prem: {A} ⊢ₛ {A→B, B} via weakening d to the larger contexts
      (d.mono (Finset.empty_subset _)
        (Finset.insert_subset_insert (A → B) (Finset.empty_subset _)))
      -- right prem: {A, A→B} ⊢ₛ {B} via impL A B
      (LKProof.impL A B (Finset.mem_insert_self _ _)
        -- {A, A→B} ⊢ₛ {A, B} via ax A
        (LKProof.ax A (insert (A → B) (insert A ∅)) (insert A (insert B ∅))
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          (Finset.mem_insert_self _ _))
        -- {B, A, A→B} ⊢ₛ {B} via ax B
        (LKProof.ax B (insert B (insert (A → B) (insert A ∅))) (insert B ∅)
          (Finset.mem_insert_self _ _)
          (Finset.mem_insert_self _ _)))
  -- Apply cut elimination to get a cut-free proof of {A} ⊢ₛ {B}.
  obtain ⟨cfp⟩ := d_AB.cutElim
  -- Apply maeharaCore with Γ₁ = {A}, Γ₂ = ∅, Δ₁ = ∅, Δ₂ = {B}.
  obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
    maeharaCore cfp.1 cfp.2 (insert A ∅) ∅ ∅ (insert B ∅)
      (Finset.union_empty _).symm
      (Finset.empty_union _).symm
  -- Simplify the variable bound: (insert A ∅ ∪ ∅).vars ∩ (∅ ∪ insert B ∅).vars = A.vars ∩ B.vars.
  simp only [Finset.vars_insert, Finset.vars_empty,
    Finset.union_empty, Finset.empty_union] at h_vars
  refine ⟨I, h_vars, ?_, ?_⟩
  · -- ∅ ⊢ₛ {A → I} via impR applied to d_left : {A} ⊢ₛ {I}.
    -- Weaken succedent of d_left to insert I (insert (A → I) ∅), then apply impR.
    exact ⟨LKProof.impR A I (Finset.mem_insert_self _ _)
      (d_left.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert I (Finset.empty_subset _)))⟩
  · -- ∅ ⊢ₛ {I → B} via impR applied to d_right : {I} ⊢ₛ {B}.
    -- Weaken succedent of d_right to insert B (insert (I → B) ∅), then apply impR.
    exact ⟨LKProof.impR I B (Finset.mem_insert_self _ _)
      (d_right.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert B (Finset.empty_subset _)))⟩

/-- **LK Craig Interpolation**: For any LK proof of `∅ ⊢ₛ {A → B}`, there exists an
interpolant `I` with `I.vars ⊆ A.vars ∩ B.vars`, `∅ ⊢ₛ {A → I}`, and `∅ ⊢ₛ {I → B}`.

Follows from `maeharaCore` (Maehara's method) applied via `LKProof.cutElim`
(Gentzen's Hauptsatz).

Reference: [TroelstraSchwichtenberg2000] Theorem 4.1.6; [NegriVonPlato2001] Theorem 3.3.3. -/
theorem LKProof.interpolation {A B : Proposition Atom}
    (d : LKProof ((∅ : Finset (Proposition Atom)) ⊢ₛ insert (A → B) ∅)) :
    ∃ I : Proposition Atom,
      I.vars ⊆ A.vars ∩ B.vars ∧
      Nonempty (LKProof ((∅ : Finset (Proposition Atom)) ⊢ₛ insert (A → I) ∅)) ∧
      Nonempty (LKProof ((∅ : Finset (Proposition Atom)) ⊢ₛ insert (I → B) ∅)) :=
  lkCraigInterpolation d

end Cslib.Logic.PL

end
