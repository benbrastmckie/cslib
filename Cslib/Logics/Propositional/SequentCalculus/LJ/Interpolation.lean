/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.Subformula

/-! # Craig Interpolation via Maehara's Method, Generic over the Theory `T`

We prove Craig interpolation, generic over the theory `T`, via Maehara's method: a structural
induction over a cut-free `SeqProof T` proof. `LJProof.interpolation` (at `IPL`) and
`LM/Interpolation.lean`'s instantiation (at `MPL`) specialise the generic results here.

## Main Results

- `seqProofMaeharaCore`: For any cut-free `SeqProof T` proof of `Γ ⊢ C` and any cover partition
  `Γ = Γ₁ ∪ Γ₂`, there exists an interpolant `I` such that
  `Γ₁ ⊢ I`, `insert I Γ₂ ⊢ C`, and
  `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`.

## Design Notes

- `SeqProof` uses single-conclusion sequents `Γ ⊢ C`; only the antecedent is partitioned.
- The right rules `orR1`, `orR2`, `andR`, `impR` act on the unsplit succedent; the
  interpolant is threaded (possibly combined for `andR`) without a side-split.
- The `cut` case is vacuous since `SeqProof.CutFree` is `False` for cut steps.
- The `orL` two-premise case is proved by side-splitting `A∨B ∈ Γ₁` or `Γ₂`, combining
  interpolants `I₁∨I₂` resp. `I₁∧I₂`. The `impL` case uses `J→K` (resp. `J∧K`) when
  `A→B ∈ Γ₁` (resp. `A→B ∈ Γ₂`), carrying the implication into the interpolant.
- Follows the `(d, hcf) + induction d with` pattern from `SubformulaProperty.lean`.
- The `ax` case's "`A ∈ Γ₂`" branch and the `botL` case's "`⊥ ∈ Γ₂`" branch both need a proof of
  `Γ₁ ⊢ ⊤` (i.e. `Γ₁ ⊢ ⊥ → ⊥`). This is derivable by `impR` then `ax` alone -- `⊥` is literally
  in `insert ⊥ Γ₁` -- so it needs no `[IsIntuitionistic T]` instance, unlike the IPL-specific
  precedent this generalises, which used `botL` for the same fact. The `botL` case's own
  reconstruction (producing the original conclusion `C` from `⊥ ∈ Γ`) genuinely needs the gated
  rule; it extracts the locally-bound instance carried by the matched `botL` constructor via
  `letI`, following `SeqProof.mono`'s idiom (`LJ/Basic.lean:184-186`).

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

set_option maxHeartbeats 800000 in
-- The orL and impL two-premise cases each require ~100k heartbeats. Since `LJProof`/
-- `LJCutFree`/`mono` are re-exports of the generic `SeqProof T` operations (after the MPL/IPL
-- unification), whnf/unfolding overhead accumulates across the full induction; 800k covers it
-- with margin.
/-- **Maehara core**, generic over the theory `T`: for any cut-free `SeqProof T` proof `d` of
`seq` and any cover partition `Γ₁ ∪ Γ₂ = seq.1` of the antecedent, there exists an interpolant
`I` satisfying:
1. `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars` (variable constraint),
2. `Γ₁ ⊢ I` (left half-derivation), and
3. `insert I Γ₂ ⊢ seq.2` (right half-derivation).

Unlike the LK version, only the antecedent is partitioned (single-conclusion sequents).
The right rules `orR1`, `orR2`, `andR`, `impR` thread the interpolant through unchanged
(or combine for `andR`). The `cut` case is vacuous. -/
private lemma seqProofMaeharaCore {T : Theory Atom} {seq : @Sequent Atom}
    (d : SeqProof T seq) (hcf : SeqProof.CutFree d) :
    ∀ Γ₁ Γ₂ : Finset (Proposition Atom),
      seq.1 = Γ₁ ∪ Γ₂ →
      ∃ I : Proposition Atom,
        I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars ∧
        Nonempty (SeqProof T (Γ₁ ⊢ I)) ∧
        Nonempty (SeqProof T (insert I Γ₂ ⊢ seq.2)) := by
  induction d with
  | cut A _ _ =>
    -- The cut case is vacuous: SeqProof.CutFree is False for cut steps.
    exact absurd hcf id
  | ax A Γ hA =>
    -- Conclusion: Γ ⊢ A where A ∈ Γ = Γ₁ ∪ Γ₂.
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    rw [hant'] at hA
    rcases Finset.mem_union.mp hA with hA₁ | hA₂
    · -- A ∈ Γ₁: choose I = A; left by ax; right by ax with self-insert.
      refine ⟨A, ?_, ⟨SeqProof.ax A Γ₁ hA₁⟩,
                     ⟨SeqProof.ax A (insert A Γ₂) (Finset.mem_insert_self A Γ₂)⟩⟩
      refine Finset.subset_inter (Finset.vars_subset_of_mem hA₁) ?_
      simp only [Finset.vars_union, Finset.vars_singleton]
      exact Finset.subset_union_right
    · -- A ∈ Γ₂: choose I = ⊤; left by impR∘ax (⊥ → ⊥ needs no ex falso); right by ax.
      refine ⟨⊤, ?_,
        ⟨SeqProof.impR ⊥ ⊥
          (SeqProof.ax ⊥ (insert ⊥ Γ₁) (Finset.mem_insert_self ⊥ Γ₁))⟩,
        ⟨SeqProof.ax A (insert ⊤ Γ₂) (Finset.mem_insert_of_mem hA₂)⟩⟩
      simp only [vars_top, Finset.empty_subset]
  | @botL Γ C inst hbot =>
    -- Conclusion: Γ ⊢ C where ⊥ ∈ Γ = Γ₁ ∪ Γ₂. `inst : IsIntuitionistic T` is the instance
    -- carried by this node of `d` itself; `letI` exposes it for the genuine ex falso
    -- reconstruction below (producing the arbitrary conclusion `C`).
    letI := inst
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    rw [hant'] at hbot
    rcases Finset.mem_union.mp hbot with hbot₁ | hbot₂
    · -- ⊥ ∈ Γ₁: choose I = ⊥; left by ax; right by botL with self-insert (arbitrary conclusion C).
      refine ⟨⊥, ?_,
        ⟨SeqProof.ax ⊥ Γ₁ hbot₁⟩,
        ⟨SeqProof.botL (insert ⊥ Γ₂) C (Finset.mem_insert_self ⊥ Γ₂)⟩⟩
      simp only [vars_bot, Finset.empty_subset]
    · -- ⊥ ∈ Γ₂: choose I = ⊤; left by impR∘ax; right by weakL∘botL (arbitrary conclusion C).
      refine ⟨⊤, ?_,
        ⟨SeqProof.impR ⊥ ⊥
          (SeqProof.ax ⊥ (insert ⊥ Γ₁) (Finset.mem_insert_self ⊥ Γ₁))⟩,
        ⟨SeqProof.weakL ⊤ (SeqProof.botL Γ₂ C hbot₂)⟩⟩
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
    have h_left' : SeqProof T (Γ₁ ⊢ I) := d_left.mono hΓ₁_sub
    have h_right' : SeqProof T (insert I Γ₂ ⊢ C) :=
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
      · exact ⟨SeqProof.andL A B hAB₁ d_left⟩
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
      · exact ⟨SeqProof.andL A B (Finset.mem_insert_of_mem hAB₂)
                 (d_right.mono hperm)⟩
  | @andR Γ A B d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ A ∧ B; premises: Γ ⊢ A and Γ ⊢ B (same antecedent).
    -- Apply IH to each premise with the same partition; combine interpolants as I₁ ∧ I₂.
    intro Γ₁ Γ₂ hant
    obtain ⟨I₁, h_I₁, ⟨d_left1⟩, ⟨d_right1⟩⟩ := ih₁ hcf.1 Γ₁ Γ₂ hant
    obtain ⟨I₂, h_I₂, ⟨d_left2⟩, ⟨d_right2⟩⟩ := ih₂ hcf.2 Γ₁ Γ₂ hant
    -- Left: Γ₁ ⊢ I₁ ∧ I₂ by andR.
    -- Right: insert (I₁ ∧ I₂) Γ₂ ⊢ A ∧ B via andL to extract I₁ (resp. I₂) then andR.
    have h_A : SeqProof T (insert (I₁ ∧ I₂) Γ₂ ⊢ A) :=
      SeqProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
        (d_right1.mono (by intro x; simp only [Finset.mem_insert]; tauto))
    have h_B : SeqProof T (insert (I₁ ∧ I₂) Γ₂ ⊢ B) :=
      SeqProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
        (d_right2.mono (by intro x; simp only [Finset.mem_insert]; tauto))
    refine ⟨I₁ ∧ I₂, ?_, ⟨SeqProof.andR I₁ I₂ d_left1 d_left2⟩,
                         ⟨SeqProof.andR A B h_A h_B⟩⟩
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
    -- Conclusion: Γ ⊢ C where A∨B ∈ Γ = Γ₁ ∪ Γ₂; two premises:
    --   d₁ : insert A Γ ⊢ C,  d₂ : insert B Γ ⊢ C.
    -- Side-split on A∨B ∈ Γ₁ or A∨B ∈ Γ₂; combine I₁∨I₂ resp. I₁∧I₂.
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    obtain ⟨hcf₁, hcf₂⟩ := hcf
    rw [hant'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A∨B ∈ Γ₁: interpolant I = I₁ ∨ I₂.
      -- Place A on Γ₁ side for d₁, B on Γ₁ side for d₂;
      -- combine left via orL+orR, right via orL.
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁; simp only [vars_or] at this; exact this
      have hA_vars : A.vars ⊆ Γ₁.vars := Finset.subset_union_left.trans hAB_vars
      have hB_vars : B.vars ⊆ Γ₁.vars := Finset.subset_union_right.trans hAB_vars
      have hcover₁ : insert A Γ = insert A Γ₁ ∪ Γ₂ := by
        rw [hant']; exact (Finset.insert_union A Γ₁ Γ₂).symm
      have hcover₂ : insert B Γ = insert B Γ₁ ∪ Γ₂ := by
        rw [hant']; exact (Finset.insert_union B Γ₁ Γ₂).symm
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ (insert A Γ₁) Γ₂ hcover₁
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ (insert B Γ₁) Γ₂ hcover₂
      refine ⟨I₁ ∨ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∨I₂).vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars
        simp only [vars_or]
        refine Finset.subset_inter ?_ ?_
        · apply Finset.union_subset
          · have h₁L := h_vars₁.trans Finset.inter_subset_left
            have h_A_drop : (insert A Γ₁).vars ⊆ Γ₁.vars := by
              simp only [Finset.vars_insert]
              exact Finset.union_subset hA_vars (Finset.Subset.refl _)
            exact h₁L.trans h_A_drop
          · have h₂L := h_vars₂.trans Finset.inter_subset_left
            have h_B_drop : (insert B Γ₁).vars ⊆ Γ₁.vars := by
              simp only [Finset.vars_insert]
              exact Finset.union_subset hB_vars (Finset.Subset.refl _)
            exact h₂L.trans h_B_drop
        · exact Finset.union_subset (h_vars₁.trans Finset.inter_subset_right)
                                    (h_vars₂.trans Finset.inter_subset_right)
      · -- Left: LJProof (Γ₁, I₁ ∨ I₂) via orL A B hAB₁ with orR1 and orR2 branches.
        exact ⟨SeqProof.orL A B hAB₁
          (SeqProof.orR1 I₁ I₂ d_left₁)
          (SeqProof.orR2 I₁ I₂ d_left₂)⟩
      · -- Right: LJProof (insert (I₁∨I₂) Γ₂, C) via orL I₁ I₂ with weakened halves.
        have hperm_I₁ : insert I₁ Γ₂ ⊆ insert I₁ (insert (I₁ ∨ I₂) Γ₂) :=
          Finset.insert_subset_insert I₁ (Finset.subset_insert _ _)
        have hperm_I₂ : insert I₂ Γ₂ ⊆ insert I₂ (insert (I₁ ∨ I₂) Γ₂) :=
          Finset.insert_subset_insert I₂ (Finset.subset_insert _ _)
        exact ⟨SeqProof.orL I₁ I₂ (Finset.mem_insert_self _ _)
          (d_right₁.mono hperm_I₁)
          (d_right₂.mono hperm_I₂)⟩
    · -- A∨B ∈ Γ₂: interpolant I = I₁ ∧ I₂.
      -- Place A on Γ₂ side for d₁, B on Γ₂ side for d₂;
      -- combine left via andR, right via andL+orL.
      have hAB_vars₂ : A.vars ∪ B.vars ⊆ Γ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂; simp only [vars_or] at this; exact this
      have hA_vars₂ : A.vars ⊆ Γ₂.vars := Finset.subset_union_left.trans hAB_vars₂
      have hB_vars₂ : B.vars ⊆ Γ₂.vars := Finset.subset_union_right.trans hAB_vars₂
      have hcover₁' : insert A Γ = Γ₁ ∪ insert A Γ₂ := by
        rw [hant']; exact (Finset.union_insert A Γ₁ Γ₂).symm
      have hcover₂' : insert B Γ = Γ₁ ∪ insert B Γ₂ := by
        rw [hant']; exact (Finset.union_insert B Γ₁ Γ₂).symm
      obtain ⟨I₁, h_vars₁, ⟨d_left₁⟩, ⟨d_right₁⟩⟩ :=
        ih₁ hcf₁ Γ₁ (insert A Γ₂) hcover₁'
      obtain ⟨I₂, h_vars₂, ⟨d_left₂⟩, ⟨d_right₂⟩⟩ :=
        ih₂ hcf₂ Γ₁ (insert B Γ₂) hcover₂'
      refine ⟨I₁ ∧ I₂, ?_, ?_, ?_⟩
      · -- vars: (I₁∧I₂).vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars
        simp only [vars_and]
        refine Finset.subset_inter ?_ ?_
        · exact Finset.union_subset (h_vars₁.trans Finset.inter_subset_left)
                                    (h_vars₂.trans Finset.inter_subset_left)
        · apply Finset.union_subset
          · have h₁R := h_vars₁.trans Finset.inter_subset_right
            have h_A_drop₂ : (insert A Γ₂ ∪ {C}).vars ⊆ (Γ₂ ∪ {C}).vars := by
              simp only [Finset.vars_union, Finset.vars_insert, Finset.vars_singleton]
              exact Finset.union_subset
                (Finset.union_subset (hA_vars₂.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₁R.trans h_A_drop₂
          · have h₂R := h_vars₂.trans Finset.inter_subset_right
            have h_B_drop₂ : (insert B Γ₂ ∪ {C}).vars ⊆ (Γ₂ ∪ {C}).vars := by
              simp only [Finset.vars_union, Finset.vars_insert, Finset.vars_singleton]
              exact Finset.union_subset
                (Finset.union_subset (hB_vars₂.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact h₂R.trans h_B_drop₂
      · -- Left: LJProof (Γ₁, I₁ ∧ I₂) via andR I₁ I₂.
        exact ⟨SeqProof.andR I₁ I₂ d_left₁ d_left₂⟩
      · -- Right: LJProof (insert (I₁∧I₂) Γ₂, C) via andL I₁ I₂ then orL A B.
        -- d_right₁ : LJProof (insert I₁ (insert A Γ₂), C)
        -- d_right₂ : LJProof (insert I₂ (insert B Γ₂), C)
        -- Use andL to expose I₁,I₂; then orL A B with A∨B ∈ Γ₂.
        have hperm₁_ant : insert I₁ (insert A Γ₂) ⊆
            insert A (insert I₁ (insert I₂ (insert (I₁ ∧ I₂) Γ₂))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm₂_ant : insert I₂ (insert B Γ₂) ⊆
            insert B (insert I₁ (insert I₂ (insert (I₁ ∧ I₂) Γ₂))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨SeqProof.andL I₁ I₂ (Finset.mem_insert_self _ _)
          (SeqProof.orL A B
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem hAB₂)))
            (d_right₁.mono hperm₁_ant)
            (d_right₂.mono hperm₂_ant))⟩
  | orR1 A B d' ih =>
    -- Conclusion: Γ ⊢ A ∨ B; premise: Γ ⊢ A.
    -- Pass-through: use interpolant I from premise IH; wrap right derivation with orR1.
    intro Γ₁ Γ₂ hant
    obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ := ih hcf Γ₁ Γ₂ hant
    refine ⟨I, ?_, ⟨d_left⟩, ⟨SeqProof.orR1 A B d_right⟩⟩
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
    refine ⟨I, ?_, ⟨d_left⟩, ⟨SeqProof.orR2 A B d_right⟩⟩
    refine Finset.subset_inter (h_vars.trans Finset.inter_subset_left) ?_
    calc I.vars ⊆ _ ∩ (Γ₂ ∪ {B}).vars := h_vars
         _ ⊆ (Γ₂ ∪ {B}).vars := Finset.inter_subset_right
         _ ⊆ (Γ₂ ∪ {A ∨ B}).vars := by
             simp only [Finset.vars_union, Finset.vars_singleton, vars_or]
             exact Finset.union_subset_union_right Finset.subset_union_right
  | @impL Γ C A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ C where A→B ∈ Γ = Γ₁ ∪ Γ₂; premises:
    --   d₁ : Γ ⊢ A,  d₂ : insert B Γ ⊢ C.
    -- Side-split on A→B ∈ Γ₁ (interpolant J→K) or A→B ∈ Γ₂ (interpolant J∧K).
    intro Γ₁ Γ₂ hant
    have hant' : Γ = Γ₁ ∪ Γ₂ := hant
    obtain ⟨hcf₁, hcf₂⟩ := hcf
    rw [hant'] at hAB
    rcases Finset.mem_union.mp hAB with hAB₁ | hAB₂
    · -- A→B ∈ Γ₁: interpolant I = J → K.
      -- ih₁ with swapped partition (Δ₁=Γ₂, Δ₂=Γ₁); ih₂ with (Δ₁=insert B Γ₁, Δ₂=Γ₂).
      have hAB_vars : A.vars ∪ B.vars ⊆ Γ₁.vars := by
        have := Finset.vars_subset_of_mem hAB₁
        simp only [show (A → B).vars = A.vars ∪ B.vars from rfl] at this; exact this
      have hA_vars₁ : A.vars ⊆ Γ₁.vars := Finset.subset_union_left.trans hAB_vars
      have hB_vars₁ : B.vars ⊆ Γ₁.vars := Finset.subset_union_right.trans hAB_vars
      have hcover_ih₁ : Γ = Γ₂ ∪ Γ₁ := by rw [hant']; exact Finset.union_comm Γ₁ Γ₂
      have hcover_ih₂ : insert B Γ = insert B Γ₁ ∪ Γ₂ := by
        rw [hant']; exact (Finset.insert_union B Γ₁ Γ₂).symm
      obtain ⟨J, h_varsJ, ⟨d_leftJ⟩, ⟨d_rightJ⟩⟩ :=
        ih₁ hcf₁ Γ₂ Γ₁ hcover_ih₁
      -- d_leftJ  : Γ₂ ⊢ J,  d_rightJ : insert J Γ₁ ⊢ A
      obtain ⟨K, h_varsK, ⟨d_leftK⟩, ⟨d_rightK⟩⟩ :=
        ih₂ hcf₂ (insert B Γ₁) Γ₂ hcover_ih₂
      -- d_leftK  : insert B Γ₁ ⊢ K,  d_rightK : insert K Γ₂ ⊢ C
      refine ⟨J → K, ?_, ?_, ?_⟩
      · -- vars: (J→K).vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars
        simp only [show (J → K).vars = J.vars ∪ K.vars from rfl]
        refine Finset.subset_inter ?_ ?_
        · -- J.vars ∪ K.vars ⊆ Γ₁.vars
          apply Finset.union_subset
          · -- J.vars ⊆ Γ₁.vars via (Γ₁ ∪ {A}).vars ⊆ Γ₁.vars, since A.vars ⊆ Γ₁.vars
            have hJR := h_varsJ.trans Finset.inter_subset_right
            have h_GA_drop : (Γ₁ ∪ {A}).vars ⊆ Γ₁.vars := by
              simp only [Finset.vars_union, Finset.vars_singleton]
              exact Finset.union_subset (Finset.Subset.refl _) hA_vars₁
            exact hJR.trans h_GA_drop
          · -- K.vars ⊆ Γ₁.vars via (insert B Γ₁).vars ⊆ Γ₁.vars, since B.vars ⊆ Γ₁.vars
            have hKL := h_varsK.trans Finset.inter_subset_left
            have h_BG₁_drop : (insert B Γ₁).vars ⊆ Γ₁.vars := by
              simp only [Finset.vars_insert]
              exact Finset.union_subset hB_vars₁ (Finset.Subset.refl _)
            exact hKL.trans h_BG₁_drop
        · -- J.vars ∪ K.vars ⊆ (Γ₂ ∪ {C}).vars
          apply Finset.union_subset
          · -- J.vars ⊆ Γ₂.vars ⊆ (Γ₂ ∪ {C}).vars
            exact (h_varsJ.trans Finset.inter_subset_left).trans
                  (Finset.vars_mono Finset.subset_union_left)
          · -- K.vars ⊆ (Γ₂ ∪ {C}).vars directly
            exact h_varsK.trans Finset.inter_subset_right
      · -- Left: Γ₁ ⊢ J → K
        -- impR J K then impL A B with A→B ∈ insert J Γ₁; left = d_rightJ; right = d_leftK mono.
        have hperm_K : insert B Γ₁ ⊆ insert B (insert J Γ₁) :=
          Finset.insert_subset_insert B (Finset.subset_insert J Γ₁)
        exact ⟨SeqProof.impR J K
          (SeqProof.impL A B (Finset.mem_insert_of_mem hAB₁)
            d_rightJ
            (d_leftK.mono hperm_K))⟩
      · -- Right: insert (J → K) Γ₂ ⊢ C
        -- impL J K with principal J→K ∈ insert (J→K) Γ₂;
        -- left from d_leftJ mono, right from d_rightK mono.
        have hperm_J₂ : Γ₂ ⊆ insert (J → K) Γ₂ := Finset.subset_insert _ _
        have hperm_K₂ : insert K Γ₂ ⊆ insert K (insert (J → K) Γ₂) :=
          Finset.insert_subset_insert K (Finset.subset_insert _ _)
        exact ⟨SeqProof.impL J K (Finset.mem_insert_self _ _)
          (d_leftJ.mono hperm_J₂)
          (d_rightK.mono hperm_K₂)⟩
    · -- A→B ∈ Γ₂: interpolant I = J ∧ K.
      -- ih₁ with partition (Δ₁=Γ₁, Δ₂=Γ₂); ih₂ with (Δ₁=Γ₁, Δ₂=insert B Γ₂).
      have hAB_vars₂ : A.vars ∪ B.vars ⊆ Γ₂.vars := by
        have := Finset.vars_subset_of_mem hAB₂
        simp only [show (A → B).vars = A.vars ∪ B.vars from rfl] at this; exact this
      have hA_vars₂ : A.vars ⊆ Γ₂.vars := Finset.subset_union_left.trans hAB_vars₂
      have hB_vars₂ : B.vars ⊆ Γ₂.vars := Finset.subset_union_right.trans hAB_vars₂
      have hcover_ih₂ : insert B Γ = Γ₁ ∪ insert B Γ₂ := by
        rw [hant']; exact (Finset.union_insert B Γ₁ Γ₂).symm
      obtain ⟨J, h_varsJ, ⟨d_leftJ⟩, ⟨d_rightJ⟩⟩ :=
        ih₁ hcf₁ Γ₁ Γ₂ hant'
      -- d_leftJ  : Γ₁ ⊢ J,  d_rightJ : insert J Γ₂ ⊢ A
      obtain ⟨K, h_varsK, ⟨d_leftK⟩, ⟨d_rightK⟩⟩ :=
        ih₂ hcf₂ Γ₁ (insert B Γ₂) hcover_ih₂
      -- d_leftK  : Γ₁ ⊢ K,  d_rightK : insert K (insert B Γ₂) ⊢ C
      refine ⟨J ∧ K, ?_, ?_, ?_⟩
      · -- vars: (J∧K).vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars
        simp only [vars_and]
        refine Finset.subset_inter ?_ ?_
        · -- J.vars ∪ K.vars ⊆ Γ₁.vars
          exact Finset.union_subset (h_varsJ.trans Finset.inter_subset_left)
                                    (h_varsK.trans Finset.inter_subset_left)
        · -- J.vars ∪ K.vars ⊆ (Γ₂ ∪ {C}).vars
          apply Finset.union_subset
          · -- J.vars ⊆ (Γ₂ ∪ {A}).vars ⊆ (Γ₂ ∪ {C}).vars, since A.vars ⊆ Γ₂.vars
            have hJR := h_varsJ.trans Finset.inter_subset_right
            have h_A_drop : (Γ₂ ∪ {A}).vars ⊆ (Γ₂ ∪ {C}).vars := by
              simp only [Finset.vars_union, Finset.vars_singleton]
              exact Finset.union_subset Finset.subset_union_left
                                        (hA_vars₂.trans Finset.subset_union_left)
            exact hJR.trans h_A_drop
          · -- K.vars ⊆ (insert B Γ₂ ∪ {C}).vars ⊆ (Γ₂ ∪ {C}).vars, since B.vars ⊆ Γ₂.vars
            have hKR := h_varsK.trans Finset.inter_subset_right
            have h_B_drop : (insert B Γ₂ ∪ {C}).vars ⊆ (Γ₂ ∪ {C}).vars := by
              simp only [Finset.vars_union, Finset.vars_insert, Finset.vars_singleton]
              exact Finset.union_subset
                (Finset.union_subset (hB_vars₂.trans Finset.subset_union_left)
                  Finset.subset_union_left)
                Finset.subset_union_right
            exact hKR.trans h_B_drop
      · -- Left: Γ₁ ⊢ J ∧ K
        exact ⟨SeqProof.andR J K d_leftJ d_leftK⟩
      · -- Right: insert (J ∧ K) Γ₂ ⊢ C
        -- andL J K exposes J,K in Σ = insert J (insert K (insert (J∧K) Γ₂));
        -- then impL A B with A→B ∈ Σ; left = d_rightJ mono; right = d_rightK mono.
        have hperm_J_ant : insert J Γ₂ ⊆ insert J (insert K (insert (J ∧ K) Γ₂)) := by
          intro x; simp only [Finset.mem_insert]; tauto
        have hperm_K_ant : insert K (insert B Γ₂) ⊆
            insert B (insert J (insert K (insert (J ∧ K) Γ₂))) := by
          intro x; simp only [Finset.mem_insert]; tauto
        exact ⟨SeqProof.andL J K (Finset.mem_insert_self _ _)
          (SeqProof.impL A B
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem hAB₂)))
            (d_rightJ.mono hperm_J_ant)
            (d_rightK.mono hperm_K_ant))⟩
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
    refine ⟨I, ?_, ⟨d_left⟩, ⟨SeqProof.impR A B (d_right.mono hcomm)⟩⟩
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

/-! ## General Split Interpolation (Public) -/

/-- **Split interpolation**, generic over the theory `T`: the general-partition form of Craig
interpolation, publicly exposed. For any cut-free `SeqProof T` proof (bundled as
`CutFreeSeqProof T seq`) and any cover partition `Γ₁ ∪ Γ₂ = seq.1` of the antecedent, there
exists an interpolant `I` satisfying:
1. `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars` (variable constraint),
2. `Γ₁ ⊢ I` (left half-derivation), and
3. `insert I Γ₂ ⊢ seq.2` (right half-derivation).

Unlike the LK version, only the antecedent is partitioned (single-conclusion sequents); the
core takes `Γ₁ Γ₂` only, not the four-way LK split, so this wrapper's signature does not mirror
`LKProof.splitInterpolation`'s uniformly.

This is a thin public wrapper around `seqProofMaeharaCore` (which stays `private`, since
un-privatising it would expose an internal induction shape as API). `LJProof.splitInterpolation`
below (at `IPL`) and `LM/Interpolation.lean`'s instantiation (at `MPL`) specialise this. -/
theorem CutFreeSeqProof.splitInterpolation {T : Theory Atom} {seq : @Sequent Atom}
    (d : CutFreeSeqProof T seq)
    (Γ₁ Γ₂ : Finset (Proposition Atom)) (hant : seq.1 = Γ₁ ∪ Γ₂) :
    ∃ I : Proposition Atom,
      I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars ∧
      Nonempty (SeqProof T (Γ₁ ⊢ I)) ∧
      Nonempty (SeqProof T (insert I Γ₂ ⊢ seq.2)) :=
  seqProofMaeharaCore d.1 d.2 Γ₁ Γ₂ hant

/-- Split interpolation for LJ. Re-export of `CutFreeSeqProof.splitInterpolation` at `IPL`,
preserving the exact current signature. -/
theorem LJProof.splitInterpolation {seq : @Sequent Atom} (d : CutFreeLJProof seq)
    (Γ₁ Γ₂ : Finset (Proposition Atom)) (hant : seq.1 = Γ₁ ∪ Γ₂) :
    ∃ I : Proposition Atom,
      I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars ∧
      Nonempty (LJProof (Γ₁ ⊢ I)) ∧
      Nonempty (LJProof (insert I Γ₂ ⊢ seq.2)) :=
  CutFreeSeqProof.splitInterpolation d Γ₁ Γ₂ hant

/-! ## Cut Elimination, Local to This File (Generic over `T`) -/

/-- Cut-free provability, generic over the theory `T`, local to this file. `LJProof.cutElim`
(`LJ/CutElimination.lean`) proves the same fact directly at `IPL`; this generic copy mirrors
`SeqProof.cutElim` (`LM/CutElimination.lean`) and `seqProofCutElim`
(`LJ/SubformulaProperty.lean`) so that `seqProofCraigInterpolation` below does not need to
depend on the `IPL`-specific proof. The `botL` case extracts the locally-bound instance carried
by the matched `botL` constructor via `letI`, following `SeqProof.mono`'s idiom
(`LJ/Basic.lean:184-186`). -/
private lemma seqProofCutElim {T : Theory Atom} {seq : @Sequent Atom} (d : SeqProof T seq) :
    Nonempty (CutFreeSeqProof T seq) := by
  induction d with
  | ax A Γ hA => exact ⟨⟨.ax A Γ hA, trivial⟩⟩
  | @botL Γ C inst hbot =>
      letI := inst
      exact ⟨⟨.botL Γ C hbot, trivial⟩⟩
  | andL A B hAB _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.andL A B hAB d', hd'⟩⟩
  | andR A B _ _ ih₁ ih₂ =>
      obtain ⟨⟨d₁', hd₁'⟩⟩ := ih₁
      obtain ⟨⟨d₂', hd₂'⟩⟩ := ih₂
      exact ⟨⟨.andR A B d₁' d₂', ⟨hd₁', hd₂'⟩⟩⟩
  | orL A B hAB _ _ ih₁ ih₂ =>
      obtain ⟨⟨d₁', hd₁'⟩⟩ := ih₁
      obtain ⟨⟨d₂', hd₂'⟩⟩ := ih₂
      exact ⟨⟨.orL A B hAB d₁' d₂', ⟨hd₁', hd₂'⟩⟩⟩
  | orR1 A B _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.orR1 A B d', hd'⟩⟩
  | orR2 A B _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.orR2 A B d', hd'⟩⟩
  | impL A B hAB _ _ ih₁ ih₂ =>
      obtain ⟨⟨d₁', hd₁'⟩⟩ := ih₁
      obtain ⟨⟨d₂', hd₂'⟩⟩ := ih₂
      exact ⟨⟨.impL A B hAB d₁' d₂', ⟨hd₁', hd₂'⟩⟩⟩
  | impR A B _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.impR A B d', hd'⟩⟩
  | weakL A _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.weakL A d', hd'⟩⟩
  | cut A _ _ ih₁ ih₂ =>
      obtain ⟨d₁'⟩ := ih₁
      obtain ⟨d₂'⟩ := ih₂
      exact ⟨ljCutAdmissibility A _ _ d₁' d₂'⟩

/-! ## Craig Interpolation Corollary, Generic over `T` -/

/-- **Craig Interpolation** (corollary), generic over the theory `T`: from any `SeqProof T`
proof of `∅ ⊢ A → B`, there exists an interpolant `I` such that:
1. `I.vars ⊆ A.vars ∩ B.vars` (variable constraint),
2. `∅ ⊢ A → I` (left half-implication), and
3. `∅ ⊢ I → B` (right half-implication).

Uses `seqProofMaeharaCore` with the cover partition `Γ₁ = {A}`, `Γ₂ = ∅`,
applied to a cut-free proof of `{A} ⊢ B` extracted from `d` via the file-local `seqProofCutElim`.
Public (unlike the file-local helpers above) so that `LM/Interpolation.lean` can instantiate it
at `MPL`, mirroring `SeqProof.subformula_property` (`LJ/SubformulaProperty.lean`).

Reference: [TroelstraSchwichtenberg2000] §4; [NegriVonPlato2001] §3.3. -/
theorem SeqProof.interpolation {T : Theory Atom} {A B : Proposition Atom}
    (d : SeqProof T ((∅ : Finset (Proposition Atom)) ⊢ A → B)) :
    ∃ I : Proposition Atom,
      I.vars ⊆ A.vars ∩ B.vars ∧
      Nonempty (SeqProof T ((∅ : Finset (Proposition Atom)) ⊢ A → I)) ∧
      Nonempty (SeqProof T ((∅ : Finset (Proposition Atom)) ⊢ I → B)) := by
  -- Build a (cut-using) proof of {A} ⊢ B from d via cut on A → B and impL.
  have d_AB : SeqProof T (insert A (∅ : Finset (Proposition Atom)) ⊢ B) :=
    SeqProof.cut (A → B)
      -- left prem: {A} ⊢ A → B via mono (∅ ⊆ {A})
      (d.mono (Finset.empty_subset _))
      -- right prem: {A → B, A} ⊢ B via impL A B
      (SeqProof.impL A B (Finset.mem_insert_self _ _)
        -- {A → B, A} ⊢ A via ax A
        (SeqProof.ax A _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        -- {B, A → B, A} ⊢ B via ax B
        (SeqProof.ax B _ (Finset.mem_insert_self _ _)))
  -- Apply cut elimination to get a cut-free proof of {A} ⊢ B.
  obtain ⟨cfp⟩ := seqProofCutElim d_AB
  -- Apply seqProofMaeharaCore with Γ₁ = {A}, Γ₂ = ∅.
  obtain ⟨I, h_vars, ⟨d_left⟩, ⟨d_right⟩⟩ :=
    seqProofMaeharaCore cfp.1 cfp.2 (insert A ∅) ∅
      (Finset.union_empty _).symm
  -- Simplify the variable bound: (insert A ∅).vars ∩ (∅ ∪ {B}).vars = A.vars ∩ B.vars.
  simp only [Finset.vars_insert, Finset.vars_empty, Finset.vars_singleton,
    Finset.union_empty, Finset.empty_union] at h_vars
  refine ⟨I, h_vars, ?_, ?_⟩
  · -- ∅ ⊢ A → I via impR applied to d_left : {A} ⊢ I.
    exact ⟨SeqProof.impR A I d_left⟩
  · -- ∅ ⊢ I → B via impR applied to d_right : {I} ⊢ B.
    exact ⟨SeqProof.impR I B d_right⟩

/-- **LJ Craig Interpolation**: For any LJ proof of `∅ ⊢ A → B`, there exists an
interpolant `I` with `I.vars ⊆ A.vars ∩ B.vars`, `∅ ⊢ A → I`, and `∅ ⊢ I → B`.

Follows from `seqProofMaeharaCore` (Maehara's method) applied via the generic
`seqProofCutElim` (Gentzen's Hauptsatz). Re-export of `SeqProof.interpolation` at `IPL`,
preserving the exact current signature.

Reference: [TroelstraSchwichtenberg2000] Theorem 4.1.6; [NegriVonPlato2001] Theorem 3.3.3. -/
theorem LJProof.interpolation {A B : Proposition Atom}
    (d : LJProof ((∅ : Finset (Proposition Atom)) ⊢ A → B)) :
    ∃ I : Proposition Atom,
      I.vars ⊆ A.vars ∩ B.vars ∧
      Nonempty (LJProof ((∅ : Finset (Proposition Atom)) ⊢ A → I)) ∧
      Nonempty (LJProof ((∅ : Finset (Proposition Atom)) ⊢ I → B)) :=
  SeqProof.interpolation d

end Cslib.Logic.PL

end
