/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LK.Basic

/-! # Soundness of LK for Classical Propositional Logic

Every LK-derivable sequent is semantically valid: if `LKProof (Γ ⊢ₛ Δ)` holds then
every valuation satisfying all formulas in `Γ` satisfies at least one formula in `Δ`.

## Main Results

- `LKProof.sound`: Soundness by structural induction on `LKProof`.
- `lk_sound`: If `Γ ⊢ₛ Δ` is LK-derivable then it is semantically valid.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition LKSequent

variable {Atom : Type u} [DecidableEq Atom]

/-- Soundness of LK: every LK proof of a sequent witnesses its semantic validity.

By structural induction on the proof tree, each rule is verified to preserve the
property that every valuation satisfying all antecedents satisfies some succedent. -/
theorem LKProof.sound {seq : LKSequent Atom} (d : LKProof seq) : seq.valid := by
  induction d with
  | ax A Γ Δ hA hD =>
      intro v hant
      exact ⟨A, hD, hant A hA⟩
  | botL Γ Δ hbot =>
      intro v hant
      exact False.elim (Evaluate_bot (v := v) ▸ hant ⊥ hbot)
  | andL A B hAB _ ih =>
      intro v hant
      have hAval : Evaluate v A := by
        have := hant _ hAB; simp only [← Proposition.and_def, Evaluate_and] at this; exact this.1
      have hBval : Evaluate v B := by
        have := hant _ hAB; simp only [← Proposition.and_def, Evaluate_and] at this; exact this.2
      apply ih v
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with hCA | hCB | hC
      · subst hCA; exact hAval
      · subst hCB; exact hBval
      · exact hant C hC
  | andR A B hAB _ _ ih₁ ih₂ =>
      intro v hant
      obtain ⟨C, hC, hCval⟩ := ih₁ v hant
      simp only [Finset.mem_insert] at hC
      rcases hC with hCA | hC
      · -- C = A, so Evaluate v A holds
        obtain ⟨E, hE, hEval⟩ := ih₂ v hant
        simp only [Finset.mem_insert] at hE
        rcases hE with hEB | hE
        · -- E = B, so Evaluate v B holds
          refine ⟨A ∧ B, hAB, (Evaluate_and v A B).mpr ⟨?_, ?_⟩⟩
          · rw [← hCA]; exact hCval
          · rw [← hEB]; exact hEval
        · exact ⟨E, hE, hEval⟩
      · exact ⟨C, hC, hCval⟩
  | orL A B hAB _ _ ih₁ ih₂ =>
      intro v hant
      have hABval : Evaluate v A ∨ Evaluate v B := by
        have := hant _ hAB; simp only [← Proposition.or_def, Evaluate_or] at this; exact this
      rcases hABval with hA | hB
      · apply ih₁ v
        intro C hC
        simp only [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hA
        · exact hant C hC
      · apply ih₂ v
        intro C hC
        simp only [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hB
        · exact hant C hC
  | orR phiA phiB hAB _ ih =>
      intro v hant
      obtain ⟨C, hC, hCval⟩ := ih v hant
      simp only [Finset.mem_insert] at hC
      rcases hC with hCA | hCB | hC
      · -- C = phiA
        refine ⟨phiA ∨ phiB, hAB, (Evaluate_or v phiA phiB).mpr (.inl ?_)⟩
        rw [← hCA]; exact hCval
      · -- C = phiB
        refine ⟨phiA ∨ phiB, hAB, (Evaluate_or v phiA phiB).mpr (.inr ?_)⟩
        rw [← hCB]; exact hCval
      · exact ⟨C, hC, hCval⟩
  | impL A B hAB _ _ ih₁ ih₂ =>
      intro v hant
      have hABval : Evaluate v A → Evaluate v B := by
        have := hant _ hAB; simp only [← Proposition.imp_def, Evaluate_imp] at this; exact this
      obtain ⟨C, hC, hCval⟩ := ih₁ v hant
      simp only [Finset.mem_insert] at hC
      rcases hC with hCA | hC
      · subst hCA
        apply ih₂ v
        intro E hE
        simp only [Finset.mem_insert] at hE
        rcases hE with hEB | hE
        · subst hEB; exact hABval hCval
        · exact hant E hE
      · exact ⟨C, hC, hCval⟩
  | impR phiA phiB hAB _ ih =>
      intro v hant
      by_cases hA : Evaluate v phiA
      · obtain ⟨C, hC, hCval⟩ := ih v (fun E hE => by
          simp only [Finset.mem_insert] at hE
          rcases hE with hEA | hE
          · rw [hEA]; exact hA
          · exact hant E hE)
        simp only [Finset.mem_insert] at hC
        rcases hC with hCB | hC
        · -- C = phiB
          refine ⟨phiA → phiB, hAB, (Evaluate_imp v phiA phiB).mpr (fun _ => ?_)⟩
          rw [← hCB]; exact hCval
        · exact ⟨C, hC, hCval⟩
      · exact ⟨phiA → phiB, hAB, (Evaluate_imp v phiA phiB).mpr (fun hA' => absurd hA' hA)⟩
  | weakL A _ ih =>
      intro v hant
      apply ih v
      intro C hC
      exact hant C (Finset.mem_insert_of_mem hC)
  | weakR A _ ih =>
      intro v hant
      obtain ⟨C, hC, hCval⟩ := ih v hant
      exact ⟨C, Finset.mem_insert_of_mem hC, hCval⟩
  | cut A _ _ ih₁ ih₂ =>
      intro v hant
      obtain ⟨C, hC, hCval⟩ := ih₁ v hant
      simp only [Finset.mem_insert] at hC
      rcases hC with hCA | hC
      · subst hCA
        apply ih₂ v
        intro E hE
        simp only [Finset.mem_insert] at hE
        rcases hE with hEA | hE
        · subst hEA; exact hCval
        · exact hant E hE
      · exact ⟨C, hC, hCval⟩

/-- LK is sound: if a sequent has an LK proof then it is semantically valid. -/
lemma lk_sound {Γ Δ : Finset (Proposition Atom)} (d : LKProof (Γ ⊢ₛ Δ)) :
    (Γ ⊢ₛ Δ).valid :=
  d.sound

end Cslib.Logic.PL
