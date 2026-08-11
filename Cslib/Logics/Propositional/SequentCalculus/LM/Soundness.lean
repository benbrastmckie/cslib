/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LM.Basic
public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence

/-! # Kripke Soundness of LM for Minimal Propositional Logic

Every LM-derivable sequent is valid in all minimal Kripke models: if `LMProof (Γ ⊢ A)` holds
then, in every minimal Kripke model with an **arbitrary** upward-closed `bot_forces` predicate,
every world forcing all antecedents also forces the conclusion.

This generalizes `LJProof.sound` (`LJ/Soundness.lean`), which fixes `bot_forces = fun _ => False`.
Since `LMProof = SeqProof MPL` has no `botL` constructor available (`MPL` is not intuitionistic,
see `not_isIntuitionistic_mpl`), soundness holds against an arbitrary upward-closed `bot_forces`,
not just the trivial one.

## Main Results

- `SeqProofMinimal.sound`: Soundness by structural induction on `SeqProofMinimal`, threading an
  arbitrary upward-closed `bot_forces` predicate. The `botL` case is discharged by
  `not_isIntuitionistic_mpl` (unconstructible), rather than by `False.elim`.
- `lm_msemantic_entails`: If `Γ ⊢ A` is LM-derivable then it holds in every minimal Kripke model,
  i.e. `MSemanticEntails ↑Γ A`.

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

/-- Soundness of LM (`SeqProofMinimal`) with respect to minimal Kripke semantics.

By structural induction on the proof tree, each rule is verified to preserve the property that
every world forcing all antecedents also forces the conclusion. Unlike `LJProof.sound`, the
`bot_forces` predicate is an **arbitrary** upward-closed predicate `bf` (minimal semantics), not
fixed to `fun _ => False`.

The non-trivial cases are:
- `botL`: unconstructible at `MPL`, since `MPL` admits no `IsIntuitionistic` instance
  (`not_isIntuitionistic_mpl`); the hypothetical instance carried by this case yields `False`.
- `impR`: requires lifting antecedent forcing from `w` to `w' ≥ w` using `iforces_persistence`,
  now threading the real `bf`/`bf_uc` rather than the trivial `fun _ => False` witnesses. -/
theorem SeqProofMinimal.sound {seq : @Sequent Atom} (d : SeqProofMinimal seq) :
    ∀ {World : Type*} [Preorder World]
      (v : World → Atom → Prop) (bf : World → Prop)
      (_ : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
      (_ : ∀ {w w' : World}, w ≤ w' → bf w → bf w')
      (w : World),
      (∀ B ∈ seq.1, IForces v bf w B) → IForces v bf w seq.2 := by
  induction d with
  | ax A Γ hA =>
      intro _ _ v bf _ _ w hant
      exact hant A hA
  | botL Γ C hbot =>
      intro _ _ v bf _ _ w _
      exact absurd (by assumption) not_isIntuitionistic_mpl
  | andL A B hAB _ ih =>
      intro _ _ v bf v_uc bf_uc w hant
      have hAB_forces : IForces v bf w (A ∧ B) := hant _ hAB
      simp only [← Proposition.and_def, IForces_and] at hAB_forces
      apply ih v bf v_uc bf_uc w
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | rfl | hC
      · exact hAB_forces.1
      · exact hAB_forces.2
      · exact hant C hC
  | andR A B _ _ ih₁ ih₂ =>
      intro _ _ v bf v_uc bf_uc w hant
      simp only [IForces_and]
      exact ⟨ih₁ v bf v_uc bf_uc w hant, ih₂ v bf v_uc bf_uc w hant⟩
  | orL A B hAB _ _ ih₁ ih₂ =>
      intro _ _ v bf v_uc bf_uc w hant
      have hAB_forces : IForces v bf w (A ∨ B) := hant _ hAB
      simp only [← Proposition.or_def, IForces_or] at hAB_forces
      rcases hAB_forces with hA | hB
      · apply ih₁ v bf v_uc bf_uc w
        intro C hC
        simp only [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hA
        · exact hant C hC
      · apply ih₂ v bf v_uc bf_uc w
        intro C hC
        simp only [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hB
        · exact hant C hC
  | orR1 A B _ ih =>
      intro _ _ v bf v_uc bf_uc w hant
      simp only [IForces_or]
      exact Or.inl (ih v bf v_uc bf_uc w hant)
  | orR2 A B _ ih =>
      intro _ _ v bf v_uc bf_uc w hant
      simp only [IForces_or]
      exact Or.inr (ih v bf v_uc bf_uc w hant)
  | impL A B hAB _ _ ih₁ ih₂ =>
      intro _ _ v bf v_uc bf_uc w hant
      have hAB_forces : IForces v bf w (A → B) := hant _ hAB
      simp only [← Proposition.imp_def, IForces_imp] at hAB_forces
      have hA : IForces v bf w A := ih₁ v bf v_uc bf_uc w hant
      have hB : IForces v bf w B := hAB_forces w (le_refl w) hA
      apply ih₂ v bf v_uc bf_uc w
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact hB
      · exact hant C hC
  | impR A B _ ih =>
      intro _ inst v bf v_uc bf_uc w hant
      simp only [IForces_imp]
      intro w' hw' hA
      apply ih v bf v_uc bf_uc w'
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact hA
      · exact iforces_persistence v_uc bf_uc hw' (hant C hC)
  | weakL A _ ih =>
      intro _ _ v bf v_uc bf_uc w hant
      apply ih v bf v_uc bf_uc w
      intro C hC
      exact hant C (Finset.mem_insert_of_mem hC)
  | cut A _ _ ih₁ ih₂ =>
      intro _ _ v bf v_uc bf_uc w hant
      have hA : IForces v bf w A := ih₁ v bf v_uc bf_uc w hant
      apply ih₂ v bf v_uc bf_uc w
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact hA
      · exact hant C hC

/-- LM is minimally Kripke sound: if a sequent `Γ ⊢ A` has an LM proof then it is a minimal
Kripke semantic consequence of `Γ`, i.e. `MSemanticEntails ↑Γ A`. -/
theorem lm_msemantic_entails {Γ : Ctx Atom} {A : Proposition Atom}
    (d : SeqProofMinimal (Γ ⊢ A)) :
    MSemanticEntails (↑Γ : Set (Proposition Atom)) A := by
  intro World _ val bf v_uc bf_uc w hant
  exact d.sound val bf v_uc bf_uc w (fun B hB => hant B (Finset.mem_coe.mpr hB))

end Cslib.Logic.PL
