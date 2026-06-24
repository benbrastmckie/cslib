/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
public import Cslib.Logics.Propositional.Subformula

/-! # Subformula Property for LK (Corollary of Cut Elimination)

We prove the *subformula property* for classical propositional sequent calculus LK:
every formula appearing in a cut-free LK proof is a subformula of some formula in the
conclusion sequent. The general case follows from Gentzen's *Hauptsatz* (`LKProof.cutElim`).

## Main Definitions

- `LKProof.formulas`: The set of all formulas appearing in any sequent of an LK proof tree.

## Main Results

- `CutFreeLKProof.subformula_property`: Every formula in a cut-free LK proof of `Γ ⊢ₛ Δ`
  is a subformula of some formula in `Γ ∪ Δ`.
- `LKProof.subformula_property`: Every LK proof has a cut-free variant satisfying the
  subformula property.

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

/-! ## Formula Collection -/

/-- The set of all formula occurrences in an LK proof tree: every node contributes
all formulas from its antecedent and succedent. -/
def LKProof.formulas {seq : LKSequent Atom} : LKProof seq → Finset (Proposition Atom)
  | .ax _ Γ Δ _ _       => Γ ∪ Δ
  | .botL Γ Δ _          => Γ ∪ Δ
  | .andL _ _ _ d        => d.formulas
  | .andR _ _ _ d₁ d₂   => d₁.formulas ∪ d₂.formulas
  | .orL _ _ _ d₁ d₂    => d₁.formulas ∪ d₂.formulas
  | .orR _ _ _ d         => d.formulas
  | .impL _ _ _ d₁ d₂   => d₁.formulas ∪ d₂.formulas
  | .impR _ _ _ d        => d.formulas
  | .weakL _ d           => d.formulas
  | .weakR _ d           => d.formulas
  | .cut _ d₁ d₂         => d₁.formulas ∪ d₂.formulas

/-! ## Membership Helpers -/

/-- Lift an `IsSubformula` witness to the left component of a union membership. -/
private lemma liftSubformulaLeft
    {B C : Proposition Atom}
    {Γ' Δ' : Finset (Proposition Atom)}
    (hmem : C ∈ Γ') (hsub : B.IsSubformula C) :
    ∃ D ∈ Γ' ∪ Δ', B.IsSubformula D :=
  ⟨C, Finset.mem_union_left _ hmem, hsub⟩

/-- Lift an `IsSubformula` witness to the right component of a union membership. -/
private lemma liftSubformulaRight
    {B C : Proposition Atom}
    {Γ' Δ' : Finset (Proposition Atom)}
    (hmem : C ∈ Δ') (hsub : B.IsSubformula C) :
    ∃ D ∈ Γ' ∪ Δ', B.IsSubformula D :=
  ⟨C, Finset.mem_union_right _ hmem, hsub⟩

/-! ## Subformula Property for Cut-Free Proofs (Core) -/

/-- Core subformula property: in any cut-free LK proof, every formula in `d.formulas` is
a subformula of some formula in the conclusion sequent.

This helper takes `(d : LKProof seq)` and `(hcf : CutFree d)` separately so that
`induction d with` can proceed without the Finset-quotient index problem.
The `cut` case is vacuous since `CutFree` is `False` for `cut` steps. -/
private lemma cutFreeSubformulaProp {seq : LKSequent Atom}
    (d : LKProof seq) (hcf : CutFree d) :
    ∀ B ∈ d.formulas, ∃ C ∈ seq.ant ∪ seq.suc, B.IsSubformula C := by
  induction d with
  | ax A Γ Δ hL hR =>
    intro B hB
    simp only [LKProof.formulas] at hB
    exact ⟨B, hB, Proposition.IsSubformula.refl B⟩
  | botL Γ Δ hbot =>
    intro B hB
    simp only [LKProof.formulas] at hB
    exact ⟨B, hB, Proposition.IsSubformula.refl B⟩
  | andL A B hAB d' ih =>
    -- Conclusion sequent: Γ ⊢ₛ Δ where Γ contains A ∧ B.
    -- Premise sequent: insert A (insert B Γ) ⊢ₛ Δ.
    -- d.formulas = d'.formulas.
    -- A and B are subformulas of A ∧ B, which lies in the conclusion Γ.
    intro B' hB'
    simp only [LKProof.formulas] at hB'
    obtain ⟨C, hC, hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_union, Finset.mem_insert] at hC
    rcases hC with (rfl | (rfl | hC)) | hC
    · -- C = A, and A is a subformula of A ∧ B ∈ seq.ant
      exact liftSubformulaLeft hAB
        (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.and_left)
    · -- C = B, and B is a subformula of A ∧ B ∈ seq.ant
      exact liftSubformulaLeft hAB
        (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.and_right)
    · exact liftSubformulaLeft hC hCS
    · exact liftSubformulaRight hC hCS
  | andR A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion sequent: Γ ⊢ₛ Δ where Δ contains A ∧ B.
    -- Premises: Γ ⊢ₛ insert A Δ and Γ ⊢ₛ insert B Δ.
    -- d.formulas = d₁.formulas ∪ d₂.formulas.
    intro B' hB'
    simp only [LKProof.formulas, Finset.mem_union] at hB'
    rcases hB' with hB₁ | hB₂
    · obtain ⟨C, hC, hCS⟩ := ih₁ hcf.1 B' hB₁
      simp only [Finset.mem_union, Finset.mem_insert] at hC
      rcases hC with hC | (rfl | hC)
      · exact liftSubformulaLeft hC hCS
      · -- C = A, and A is a subformula of A ∧ B ∈ seq.suc
        exact liftSubformulaRight hAB
          (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.and_left)
      · exact liftSubformulaRight hC hCS
    · obtain ⟨C, hC, hCS⟩ := ih₂ hcf.2 B' hB₂
      simp only [Finset.mem_union, Finset.mem_insert] at hC
      rcases hC with hC | (rfl | hC)
      · exact liftSubformulaLeft hC hCS
      · -- C = B, and B is a subformula of A ∧ B ∈ seq.suc
        exact liftSubformulaRight hAB
          (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.and_right)
      · exact liftSubformulaRight hC hCS
  | orL A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion sequent: Γ ⊢ₛ Δ where Γ contains A ∨ B.
    -- Premises: insert A Γ ⊢ₛ Δ and insert B Γ ⊢ₛ Δ.
    intro B' hB'
    simp only [LKProof.formulas, Finset.mem_union] at hB'
    rcases hB' with hB₁ | hB₂
    · obtain ⟨C, hC, hCS⟩ := ih₁ hcf.1 B' hB₁
      simp only [Finset.mem_union, Finset.mem_insert] at hC
      rcases hC with (rfl | hC) | hC
      · -- C = A, and A is a subformula of A ∨ B ∈ seq.ant
        exact liftSubformulaLeft hAB
          (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.or_left)
      · exact liftSubformulaLeft hC hCS
      · exact liftSubformulaRight hC hCS
    · obtain ⟨C, hC, hCS⟩ := ih₂ hcf.2 B' hB₂
      simp only [Finset.mem_union, Finset.mem_insert] at hC
      rcases hC with (rfl | hC) | hC
      · -- C = B, and B is a subformula of A ∨ B ∈ seq.ant
        exact liftSubformulaLeft hAB
          (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.or_right)
      · exact liftSubformulaLeft hC hCS
      · exact liftSubformulaRight hC hCS
  | orR A B hAB d' ih =>
    -- Conclusion sequent: Γ ⊢ₛ Δ where Δ contains A ∨ B.
    -- Premise: Γ ⊢ₛ insert A (insert B Δ).
    intro B' hB'
    simp only [LKProof.formulas] at hB'
    obtain ⟨C, hC, hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_union, Finset.mem_insert] at hC
    rcases hC with hC | (rfl | (rfl | hC))
    · exact liftSubformulaLeft hC hCS
    · -- C = A, and A is a subformula of A ∨ B ∈ seq.suc
      exact liftSubformulaRight hAB
        (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.or_left)
    · -- C = B, and B is a subformula of A ∨ B ∈ seq.suc
      exact liftSubformulaRight hAB
        (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.or_right)
    · exact liftSubformulaRight hC hCS
  | impL A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion sequent: Γ ⊢ₛ Δ where Γ contains A → B.
    -- Premises: Γ ⊢ₛ insert A Δ and insert B Γ ⊢ₛ Δ.
    intro B' hB'
    simp only [LKProof.formulas, Finset.mem_union] at hB'
    rcases hB' with hB₁ | hB₂
    · obtain ⟨C, hC, hCS⟩ := ih₁ hcf.1 B' hB₁
      simp only [Finset.mem_union, Finset.mem_insert] at hC
      rcases hC with hC | (rfl | hC)
      · exact liftSubformulaLeft hC hCS
      · -- C = A, and A is a subformula of A → B ∈ seq.ant
        exact liftSubformulaLeft hAB
          (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.imp_left)
      · exact liftSubformulaRight hC hCS
    · obtain ⟨C, hC, hCS⟩ := ih₂ hcf.2 B' hB₂
      simp only [Finset.mem_union, Finset.mem_insert] at hC
      rcases hC with (rfl | hC) | hC
      · -- C = B, and B is a subformula of A → B ∈ seq.ant
        exact liftSubformulaLeft hAB
          (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.imp_right)
      · exact liftSubformulaLeft hC hCS
      · exact liftSubformulaRight hC hCS
  | impR A B hAB d' ih =>
    -- Conclusion sequent: Γ ⊢ₛ Δ where Δ contains A → B.
    -- Premise: insert A Γ ⊢ₛ insert B Δ.
    intro B' hB'
    simp only [LKProof.formulas] at hB'
    obtain ⟨C, hC, hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_union, Finset.mem_insert] at hC
    rcases hC with (rfl | hC) | (rfl | hC)
    · -- C = A, and A is a subformula of A → B ∈ seq.suc
      exact liftSubformulaRight hAB
        (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.imp_left)
    · exact liftSubformulaLeft hC hCS
    · -- C = B, and B is a subformula of A → B ∈ seq.suc
      exact liftSubformulaRight hAB
        (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.imp_right)
    · exact liftSubformulaRight hC hCS
  | weakL A d' ih =>
    -- Conclusion sequent: insert A Γ ⊢ₛ Δ.
    -- Premise: Γ ⊢ₛ Δ.
    -- d.formulas = d'.formulas, subformulas of Γ ∪ Δ ⊆ insert A Γ ∪ Δ.
    intro B' hB'
    simp only [LKProof.formulas] at hB'
    obtain ⟨C, hC, hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_union] at hC
    rcases hC with hC | hC
    · exact liftSubformulaLeft (Finset.mem_insert_of_mem hC) hCS
    · exact liftSubformulaRight hC hCS
  | weakR A d' ih =>
    -- Conclusion sequent: Γ ⊢ₛ insert A Δ.
    -- Premise: Γ ⊢ₛ Δ.
    -- d.formulas = d'.formulas, subformulas of Γ ∪ Δ ⊆ Γ ∪ insert A Δ.
    intro B' hB'
    simp only [LKProof.formulas] at hB'
    obtain ⟨C, hC, hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_union] at hC
    rcases hC with hC | hC
    · exact liftSubformulaLeft hC hCS
    · exact liftSubformulaRight (Finset.mem_insert_of_mem hC) hCS
  | cut _ _ _ =>
    -- The cut case is vacuous: CutFree is False for cut steps.
    exact absurd hcf id

/-! ## Subformula Property for Cut-Free Proofs -/

/-- The subformula property for cut-free LK proofs: every formula appearing in any
sequent of a cut-free proof of `Γ ⊢ₛ Δ` is a subformula of some formula in `Γ ∪ Δ`.

Proved by structural induction on the proof tree using `cutFreeSubformulaProp`.
The `cut` case is vacuous since `CutFree` is `False` for `cut` steps.

This is Theorem 4.1.6 of [TroelstraSchwichtenberg2000] and Corollary 3.2.4
of [NegriVonPlato2001]. -/
lemma CutFreeLKProof.subformula_property
    {Γ Δ : Finset (Proposition Atom)}
    (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    ∀ B ∈ d.val.formulas,
      ∃ C ∈ Γ ∪ Δ, B.IsSubformula C :=
  cutFreeSubformulaProp d.val d.property

/-! ## Subformula Property for General LK Proofs -/

/-- Subformula property for LK: every sequent provable in LK has a cut-free proof
satisfying the subformula property. Every formula in the cut-free proof is a subformula
of some formula in the conclusion sequent.

This is an immediate corollary of `LKProof.cutElim` (Gentzen's *Hauptsatz*) and
`CutFreeLKProof.subformula_property`. -/
theorem LKProof.subformula_property
    {seq : LKSequent Atom} (d : LKProof seq) :
    ∃ d' : CutFreeLKProof seq,
      ∀ B ∈ d'.val.formulas,
        ∃ C ∈ seq.ant ∪ seq.suc, B.IsSubformula C := by
  obtain ⟨d'⟩ := d.cutElim
  exact ⟨d', cutFreeSubformulaProp d'.val d'.property⟩

end Cslib.Logic.PL
