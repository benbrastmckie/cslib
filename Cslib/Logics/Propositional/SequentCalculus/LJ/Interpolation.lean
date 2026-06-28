/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.Subformula

/-! # Craig Interpolation for LJ via Maehara's Method

We prove Craig interpolation for the intuitionistic propositional sequent calculus LJ via
Maehara's method: a structural induction over a cut-free proof.

## Main Results

- `ljMaeharaCore`: For any cut-free LJ proof of `Γ ⊢ C` and any cover partition
  `Γ = Γ₁ ∪ Γ₂`, there exists an interpolant `I` such that
  `Γ₁ ⊢ I`, `insert I Γ₂ ⊢ C`, and
  `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`.

## Design Notes

- LJ uses single-conclusion sequents `Γ ⊢ C`; only the antecedent is partitioned.
- The right rules `orR1`, `orR2`, `andR`, `impR` act on the unsplit succedent; the
  interpolant is threaded (possibly combined for `andR`) without a side-split.
- The `cut` case is vacuous since `LJCutFree` is `False` for cut steps.
- The hard two-premise cases `orL` and `impL` are held as `sorry` checkpoints for Phase C2.
- Follows the `(d, hcf) + induction d with` pattern from `SubformulaProperty.lean`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Maehara Core Lemma for LJ -/

/-- **Maehara core for LJ**: For any cut-free LJ proof `d` of `seq` and any cover partition
`Γ₁ ∪ Γ₂ = seq.1` of the antecedent, there exists an interpolant `I` satisfying:
1. `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars` (variable constraint),
2. `Γ₁ ⊢ I` (left half-derivation), and
3. `insert I Γ₂ ⊢ seq.2` (right half-derivation).

Unlike the LK version, only the antecedent is partitioned (single-conclusion sequents).
The right rules `orR1`, `orR2`, `andR`, `impR` thread the interpolant through unchanged
(or combine for `andR`). The `cut` case is vacuous. The hard two-premise cases `orL` and
`impL` are deferred to Phase C2. -/
private lemma ljMaeharaCore {seq : @Sequent Atom} (d : LJProof seq) (hcf : LJCutFree d) :
    ∀ Γ₁ Γ₂ : Finset (Proposition Atom),
      seq.1 = Γ₁ ∪ Γ₂ →
      ∃ I : Proposition Atom,
        I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars ∧
        Nonempty (LJProof (Γ₁ ⊢ I)) ∧
        Nonempty (LJProof (insert I Γ₂ ⊢ seq.2)) := by
  induction d with
  | cut A _ _ =>
    -- The cut case is vacuous: LJCutFree is False for cut steps.
    exact absurd hcf id
  | ax A Γ hA =>
    -- Conclusion: Γ ⊢ A where A ∈ Γ = Γ₁ ∪ Γ₂.
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    rw [hant'] at hA
    rcases Finset.mem_union.mp hA with hA₁ | hA₂
    · -- A ∈ Γ₁: choose I = A; left by ax; right by ax with self-insert.
      refine ⟨A, ?_, ⟨LJProof.ax A Γ₁ hA₁⟩,
                     ⟨LJProof.ax A (insert A Γ₂) (Finset.mem_insert_self A Γ₂)⟩⟩
      refine Finset.subset_inter (Finset.vars_subset_of_mem hA₁) ?_
      simp only [Finset.vars_union, Finset.vars_singleton]
      exact Finset.subset_union_right
    · -- A ∈ Γ₂: choose I = ⊤; left by impR∘botL; right by ax.
      refine ⟨⊤, ?_,
        ⟨LJProof.impR ⊥ ⊥
          (LJProof.botL (insert ⊥ Γ₁) ⊥ (Finset.mem_insert_self ⊥ Γ₁))⟩,
        ⟨LJProof.ax A (insert ⊤ Γ₂) (Finset.mem_insert_of_mem hA₂)⟩⟩
      simp only [vars_top, Finset.empty_subset]
  | botL Γ C hbot =>
    -- Conclusion: Γ ⊢ C where ⊥ ∈ Γ = Γ₁ ∪ Γ₂.
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    rw [hant'] at hbot
    rcases Finset.mem_union.mp hbot with hbot₁ | hbot₂
    · -- ⊥ ∈ Γ₁: choose I = ⊥; left by botL; right by botL with self-insert.
      refine ⟨⊥, ?_,
        ⟨LJProof.botL Γ₁ ⊥ hbot₁⟩,
        ⟨LJProof.botL (insert ⊥ Γ₂) C (Finset.mem_insert_self ⊥ Γ₂)⟩⟩
      simp only [vars_bot, Finset.empty_subset]
    · -- ⊥ ∈ Γ₂: choose I = ⊤; left by impR∘botL; right by weakL∘botL.
      refine ⟨⊤, ?_,
        ⟨LJProof.impR ⊥ ⊥
          (LJProof.botL (insert ⊥ Γ₁) ⊥ (Finset.mem_insert_self ⊥ Γ₁))⟩,
        ⟨LJProof.weakL ⊤ (LJProof.botL Γ₂ C hbot₂)⟩⟩
      simp only [vars_top, Finset.empty_subset]
  | @weakL Γ C A d' ih =>
    -- Conclusion: insert A Γ ⊢ C; premise: Γ ⊢ C.
    -- Apply IH to d' with cover (Γ ∩ Γ₁) ∪ (Γ ∩ Γ₂) = Γ; then weaken both halves.
    intro Γ₁ Γ₂ hant
    have hcover : (Γ ∩ Γ₁) ∪ (Γ ∩ Γ₂) = Γ := by
      rw [← Finset.inter_union_distrib_left, ← hant]
      exact Finset.inter_eq_left.mpr (Finset.subset_insert A Γ)
    obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
      ih hcf (Γ ∩ Γ₁) (Γ ∩ Γ₂) hcover.symm
    have hΓ₁_sub : Γ ∩ Γ₁ ⊆ Γ₁ := Finset.inter_subset_right
    have hΓ₂_sub : Γ ∩ Γ₂ ⊆ Γ₂ := Finset.inter_subset_right
    have h_left' : LJProof (Γ₁ ⊢ I) := d_left.mono hΓ₁_sub
    have h_right' : LJProof (insert I Γ₂ ⊢ C) :=
      d_right.mono (Finset.insert_subset_insert I hΓ₂_sub)
    refine ⟨I, ?_, ⟨h_left'⟩, ⟨h_right'⟩⟩
    refine Finset.subset_inter ?_ ?_
    · calc I.vars ⊆ (Γ ∩ Γ₁).vars ∩ _ := h_vars
           _ ⊆ (Γ ∩ Γ₁).vars := Finset.inter_subset_left
           _ ⊆ Γ₁.vars := Finset.vars_mono hΓ₁_sub
    · calc I.vars ⊆ _ ∩ ((Γ ∩ Γ₂) ∪ {C}).vars := h_vars
           _ ⊆ ((Γ ∩ Γ₂) ∪ {C}).vars := Finset.inter_subset_right
           _ ⊆ (Γ₂ ∪ {C}).vars := by
               simp only [Finset.vars_union]
               exact Finset.union_subset_union_left (Finset.vars_mono hΓ₂_sub)
  | @andL Γ C A B hAB d' ih =>
    -- Conclusion: Γ ⊢ C where A∧B ∈ Γ = Γ₁ ∪ Γ₂; premise: insert A (insert B Γ) ⊢ C.
    -- Side-split on A∧B ∈ Γ₁ or Γ₂; place A,B on that side; reapply andL.
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    rw [hant'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A∧B ∈ Γ₁: IH with Γ₁' = insert A (insert B Γ₁), Γ₂' = Γ₂.
      have hcover : insert A (insert B Γ) = insert A (insert B Γ₁) ∪ Γ₂ := by
        rw [hant']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf (insert A (insert B Γ₁)) Γ₂ hcover
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁
        simp only [vars_and] at this; exact this
      have hΓ₁_vars : (insert A (insert B Γ₁)).vars ⊆ Γ₁.vars := by
        simp only [Finset.vars_insert]
        exact Finset.union_subset (Finset.subset_union_left.trans hAB_vars)
          (Finset.union_subset (Finset.subset_union_right.trans hAB_vars)
            (Finset.Subset.refl _))
      refine ⟨I, ?_, ?_, ⟨d_right⟩⟩
      · refine Finset.subset_inter ?_ (h_vars.trans Finset.inter_subset_right)
        calc I.vars ⊆ (insert A (insert B Γ₁)).vars ∩ _ := h_vars
             _ ⊆ (insert A (insert B Γ₁)).vars := Finset.inter_subset_left
             _ ⊆ Γ₁.vars := hΓ₁_vars
      · exact ⟨LJProof.andL A B hAB₁ d_left⟩
    · -- A∧B ∈ Γ₂: IH with Γ₁' = Γ₁, Γ₂' = insert A (insert B Γ₂).
      have hcover : insert A (insert B Γ) = Γ₁ ∪ insert A (insert B Γ₂) := by
        rw [hant']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
        ih hcf Γ₁ (insert A (insert B Γ₂)) hcover
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂
        simp only [vars_and] at this; exact this
      have hΓ₂_vars : (insert A (insert B Γ₂)).vars ⊆ Γ₂.vars := by
        simp only [Finset.vars_insert]
        exact Finset.union_subset (Finset.subset_union_left.trans hAB_vars)
          (Finset.union_subset (Finset.subset_union_right.trans hAB_vars)
            (Finset.Subset.refl _))
      have hperm : insert I (insert A (insert B Γ₂)) ⊆
                   insert A (insert B (insert I Γ₂)) := by
        intro x; simp only [Finset.mem_insert]; tauto
      refine ⟨I, ?_, ⟨d_left⟩, ?_⟩
      · refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
        calc I.vars ⊆ _ ∩ (insert A (insert B Γ₂) ∪ {C}).vars := h_vars
             _ ⊆ (insert A (insert B Γ₂) ∪ {C}).vars := Finset.inter_subset_right
             _ ⊆ (Γ₂ ∪ {C}).vars := by
                 simp only [Finset.vars_union]
                 exact Finset.union_subset_union_left hΓ₂_vars
      · exact ⟨LJProof.andL A B (Finset.mem_insert_of_mem hAB₂)
                 (d_right.mono hperm)⟩
  | @andR Γ A B d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ A ∧ B; premises: Γ ⊢ A and Γ ⊢ B (same antecedent).
    -- Apply IH to each premise with the same partition; combine interpolants as I₁ ∧ I₂.
    intro Γ₁ Γ₂ hant
    obtain ⟨I₁, h_I₁, ⟨d_left1⟩, ⟨d_right1⟩⟩ := ih₁ hcf.1 Γ₁ Γ₂ hant
    obtain ⟨I₂, h_I₂, ⟨d_left2⟩, ⟨d_right2⟩⟩ := ih₂ hcf.2 Γ₁ Γ₂ hant
    -- Left: Γ₁ ⊢ I₁ ∧ I₂ by andR.
    -- Right: insert (I₁ ∧ I₂) Γ₂ ⊢ A ∧ B via andL to extract I₁ (resp. I₂) then andR.
    have h_A : LJProof (insert (I₁ ∧ I₂) Γ₂ ⊢ A) :=
      LJProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
        (d_right1.mono (by intro x; simp only [Finset.mem_insert]; tauto))
    have h_B : LJProof (insert (I₁ ∧ I₂) Γ₂ ⊢ B) :=
      LJProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
        (d_right2.mono (by intro x; simp only [Finset.mem_insert]; tauto))
    refine ⟨I₁ ∧ I₂, ?_, ⟨LJProof.andR I₁ I₂ d_left1 d_left2⟩,
                         ⟨LJProof.andR A B h_A h_B⟩⟩
    have hA_sub : (Γ₂ ∪ {A}).vars ⊆ (Γ₂ ∪ {A ∧ B}).vars := by
      simp only [Finset.vars_union, Finset.vars_singleton, vars_and]
      exact Finset.union_subset_union_right Finset.subset_union_left
    have hB_sub : (Γ₂ ∪ {B}).vars ⊆ (Γ₂ ∪ {A ∧ B}).vars := by
      simp only [Finset.vars_union, Finset.vars_singleton, vars_and]
      exact Finset.union_subset_union_right Finset.subset_union_right
    refine Finset.subset_inter ?_ ?_
    · calc (I₁ ∧ I₂).vars = I₁.vars ∪ I₂.vars := vars_and I₁ I₂
           _ ⊆ Γ₁.vars := Finset.union_subset
               (h_I₁.trans Finset.inter_subset_left)
               (h_I₂.trans Finset.inter_subset_left)
    · calc (I₁ ∧ I₂).vars = I₁.vars ∪ I₂.vars := vars_and I₁ I₂
           _ ⊆ (Γ₂ ∪ {A ∧ B}).vars := Finset.union_subset
               ((h_I₁.trans Finset.inter_subset_right).trans hA_sub)
               ((h_I₂.trans Finset.inter_subset_right).trans hB_sub)
  | @orL Γ C A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Phase C2: two-premise case; deferred.
    intro Γ₁ Γ₂ _hant
    sorry -- Phase C2
  | orR1 A B d' ih =>
    -- Conclusion: Γ ⊢ A ∨ B; premise: Γ ⊢ A.
    -- Pass-through: use interpolant I from premise IH; wrap right derivation with orR1.
    intro Γ₁ Γ₂ hant
    obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ := ih hcf Γ₁ Γ₂ hant
    refine ⟨I, ?_, ⟨d_left⟩, ⟨LJProof.orR1 A B d_right⟩⟩
    refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
    calc I.vars ⊆ _ ∩ (Γ₂ ∪ {A}).vars := h_vars
         _ ⊆ (Γ₂ ∪ {A}).vars := Finset.inter_subset_right
         _ ⊆ (Γ₂ ∪ {A ∨ B}).vars := by
             simp only [Finset.vars_union, Finset.vars_singleton, vars_or]
             exact Finset.union_subset_union_right Finset.subset_union_left
  | orR2 A B d' ih =>
    -- Conclusion: Γ ⊢ A ∨ B; premise: Γ ⊢ B.
    -- Pass-through: use interpolant I from premise IH; wrap right derivation with orR2.
    intro Γ₁ Γ₂ hant
    obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ := ih hcf Γ₁ Γ₂ hant
    refine ⟨I, ?_, ⟨d_left⟩, ⟨LJProof.orR2 A B d_right⟩⟩
    refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
    calc I.vars ⊆ _ ∩ (Γ₂ ∪ {B}).vars := h_vars
         _ ⊆ (Γ₂ ∪ {B}).vars := Finset.inter_subset_right
         _ ⊆ (Γ₂ ∪ {A ∨ B}).vars := by
             simp only [Finset.vars_union, Finset.vars_singleton, vars_or]
             exact Finset.union_subset_union_right Finset.subset_union_right
  | @impL Γ C A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Phase C2: two-premise case; deferred.
    intro Γ₁ Γ₂ _hant
    sorry -- Phase C2
  | @impR Γ A B d' ih =>
    -- Conclusion: Γ ⊢ A → B; premise: insert A Γ ⊢ B.
    -- Place A on the Γ₂ side: partition insert A Γ = Γ₁ ∪ insert A Γ₂.
    -- IH gives I with Γ₁ ⊢ I and insert I (insert A Γ₂) ⊢ B; wrap right with impR.
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    have hcover : insert A Γ = Γ₁ ∪ insert A Γ₂ := by
      rw [hant']; ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
    obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
      ih hcf Γ₁ (insert A Γ₂) hcover
    -- d_right : LJProof (insert I (insert A Γ₂) ⊢ B)
    -- Need: LJProof (insert I Γ₂ ⊢ A → B)
    -- Commutativity insert I (insert A Γ₂) ≅ insert A (insert I Γ₂), then impR.
    have hcomm : insert I (insert A Γ₂) ⊆ insert A (insert I Γ₂) := by
      intro x; simp only [Finset.mem_insert]; tauto
    refine ⟨I, ?_, ⟨d_left⟩, ⟨LJProof.impR A B (d_right.mono hcomm)⟩⟩
    -- Vars: I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {A → B}).vars
    -- h_vars: I.vars ⊆ Γ₁.vars ∩ (insert A Γ₂ ∪ {B}).vars
    -- Note: (insert A Γ₂ ∪ {B}).vars = Γ₂.vars ∪ A.vars ∪ B.vars
    --       (Γ₂ ∪ {A → B}).vars    = Γ₂.vars ∪ A.vars ∪ B.vars
    refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
    calc I.vars ⊆ _ ∩ (insert A Γ₂ ∪ {B}).vars := h_vars
         _ ⊆ (insert A Γ₂ ∪ {B}).vars := Finset.inter_subset_right
         _ ⊆ (Γ₂ ∪ {A → B}).vars := by
             simp only [Finset.vars_union, Finset.vars_insert, Finset.vars_singleton,
                        show (A → B).vars = A.vars ∪ B.vars from rfl]
             -- Goal: A.vars ∪ Γ₂.vars ∪ B.vars ⊆ Γ₂.vars ∪ (A.vars ∪ B.vars)
             exact Finset.union_subset
               (Finset.union_subset
                 (Finset.subset_union_left.trans Finset.subset_union_right)
                 Finset.subset_union_left)
               (Finset.subset_union_right.trans Finset.subset_union_right)

end Cslib.Logic.PL

end
