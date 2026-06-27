/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
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
- Hard cases (`ax`, `andR`, `orL`, `impL`, `impR`) are deferred to Phase 3.

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

/-- **Maehara core**: For any cut-free LK proof `d` of `seq` and any cover partition
`Γ₁ ∪ Γ₂ = seq.ant`, `Δ₁ ∪ Δ₂ = seq.suc`, there exists an interpolant `I` satisfying:
1. `I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars` (variable constraint),
2. `Γ₁ ⊢ₛ insert I Δ₁` (left half-derivation), and
3. `insert I Γ₂ ⊢ₛ Δ₂` (right half-derivation).

The `cut` case is vacuous since `CutFree d` is `False` for cut steps. The hard cases
(`ax`, `andR`, `orL`, `impL`, `impR`) are marked as deferred to Phase 3. -/
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
    -- PHASE 3: ax leaf table — four sub-cases by (A ∈ Γ₁?, A ∈ Δ₁?).
    -- Deferred to Phase 3 (highest-risk case, requires ⊥/⊤/A/¬A interpolant selection).
    intro Γ₁ Γ₂ Δ₁ Δ₂ _hant _hsuc
    sorry
  | andR A B hAB d₁ d₂ ih₁ ih₂ =>
    -- PHASE 3: two-premise case; obtain I₁, I₂ from each premise; combine via ∨ or ∧.
    intro Γ₁ Γ₂ Δ₁ Δ₂ _hant _hsuc
    sorry
  | orL A B hAB d₁ d₂ ih₁ ih₂ =>
    -- PHASE 3: two-premise case dual to andR.
    intro Γ₁ Γ₂ Δ₁ Δ₂ _hant _hsuc
    sorry
  | impL A B hAB d₁ d₂ ih₁ ih₂ =>
    -- PHASE 3: two-premise case; most intricate.
    intro Γ₁ Γ₂ Δ₁ Δ₂ _hant _hsuc
    sorry
  | impR A B hAB d' ih =>
    -- PHASE 3: one-premise case; reuse I; reapply impR; verify vars bound.
    intro Γ₁ Γ₂ Δ₁ Δ₂ _hant _hsuc
    sorry

end Cslib.Logic.PL

end
