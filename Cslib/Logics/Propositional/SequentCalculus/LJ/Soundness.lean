/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.Basic
public import Cslib.Logics.Propositional.Semantics.Kripke

/-! # Kripke Soundness of LJ for Intuitionistic Propositional Logic

Every LJ-derivable sequent is valid in all intuitionistic Kripke models: if
`LJProof (Γ ⊢ A)` holds then, in every Kripke model with `botForces = fun _ => False`,
every world forcing all antecedents also forces the conclusion.

## Main Results

- `LJProof.sound`: Soundness by structural induction on `LJProof`.
- `lj_sound`: If `Γ ⊢ A` is LJ-derivable then it holds in every intuitionistic Kripke model.

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

/-- Soundness of LJ with respect to intuitionistic Kripke semantics.

By structural induction on the proof tree, each rule is verified to preserve the
property that every world forcing all antecedents also forces the conclusion.
The `botForces` predicate is fixed to `fun _ => False` (intuitionistic semantics),
so the `botL` case reduces to `False.elim` via `IForces v (fun _ => False) w ⊥ = False`.

The non-trivial cases are:
- `impR`: requires lifting antecedent forcing from `w` to `w' ≥ w` using `iforces_persistence`.
- `impL`: uses the fact that `IForces w (A → B)` gives `IForces w B` when `IForces w A` holds
  (instantiating the universal at `w' = w` with `le_refl`).
- `andL`: decomposes `IForces w (A ∧ B)` into its two components and inserts both. -/
theorem LJProof.sound {seq : @Sequent Atom} (d : LJProof seq) :
    ∀ {World : Type*} [Preorder World]
      (v : World → Atom → Prop)
      (_ : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
      (w : World),
      (∀ B ∈ seq.1, IForces v (fun _ => False) w B) →
      IForces v (fun _ => False) w seq.2 := by
  induction d with
  | ax A Γ hA =>
      intro _ _ v _ w hant
      exact hant A hA
  | botL Γ C hbot =>
      intro _ _ v _ w hant
      exact False.elim (hant ⊥ hbot)
  | andL A B hAB _ ih =>
      intro _ _ v v_uc w hant
      have hAB_forces : IForces v (fun _ => False) w (A ∧ B) := hant _ hAB
      simp only [← Proposition.and_def, IForces_and] at hAB_forces
      apply ih v v_uc w
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | rfl | hC
      · exact hAB_forces.1
      · exact hAB_forces.2
      · exact hant C hC
  | andR A B _ _ ih₁ ih₂ =>
      intro _ _ v v_uc w hant
      simp only [IForces_and]
      exact ⟨ih₁ v v_uc w hant, ih₂ v v_uc w hant⟩
  | orL A B hAB _ _ ih₁ ih₂ =>
      intro _ _ v v_uc w hant
      have hAB_forces : IForces v (fun _ => False) w (A ∨ B) := hant _ hAB
      simp only [← Proposition.or_def, IForces_or] at hAB_forces
      rcases hAB_forces with hA | hB
      · apply ih₁ v v_uc w
        intro C hC
        simp only [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hA
        · exact hant C hC
      · apply ih₂ v v_uc w
        intro C hC
        simp only [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hB
        · exact hant C hC
  | orR1 A B _ ih =>
      intro _ _ v v_uc w hant
      simp only [IForces_or]
      exact Or.inl (ih v v_uc w hant)
  | orR2 A B _ ih =>
      intro _ _ v v_uc w hant
      simp only [IForces_or]
      exact Or.inr (ih v v_uc w hant)
  | impL A B hAB _ _ ih₁ ih₂ =>
      intro _ _ v v_uc w hant
      have hAB_forces : IForces v (fun _ => False) w (A → B) := hant _ hAB
      simp only [← Proposition.imp_def, IForces_imp] at hAB_forces
      have hA : IForces v (fun _ => False) w A := ih₁ v v_uc w hant
      have hB : IForces v (fun _ => False) w B := hAB_forces w (le_refl w) hA
      apply ih₂ v v_uc w
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact hB
      · exact hant C hC
  | impR A B _ ih =>
      intro _ inst v v_uc w hant
      simp only [IForces_imp]
      intro w' hw' hA
      apply ih v v_uc w'
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact hA
      · exact iforces_persistence v_uc (fun {_ _} h hf => absurd hf id) hw' (hant C hC)
  | weakL A _ ih =>
      intro _ _ v v_uc w hant
      apply ih v v_uc w
      intro C hC
      exact hant C (Finset.mem_insert_of_mem hC)
  | cut A _ _ ih₁ ih₂ =>
      intro _ _ v v_uc w hant
      have hA : IForces v (fun _ => False) w A := ih₁ v v_uc w hant
      apply ih₂ v v_uc w
      intro C hC
      simp only [Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact hA
      · exact hant C hC

/-- LJ is Kripke sound: if a sequent `Γ ⊢ A` has an LJ proof then for every intuitionistic
Kripke model `(World, v)` and world `w`, forcing all formulas in `Γ` at `w` implies
forcing `A` at `w`. -/
lemma lj_sound {Γ : Ctx Atom} {A : Proposition Atom} (d : LJProof (Γ ⊢ A)) :
    ∀ {World : Type*} [Preorder World]
      (v : World → Atom → Prop)
      (_ : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
      (w : World),
      (∀ B ∈ Γ, IForces v (fun _ => False) w B) →
      IForces v (fun _ => False) w A :=
  d.sound

end Cslib.Logic.PL
