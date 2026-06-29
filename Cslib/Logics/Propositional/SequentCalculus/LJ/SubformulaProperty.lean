/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.Subformula

/-! # Subformula Property for LJ (Corollary of Cut Elimination)

We prove the *subformula property* for intuitionistic propositional sequent calculus LJ:
every formula appearing in a cut-free LJ proof is a subformula of some formula in the
conclusion sequent. The general case follows from Gentzen's *Hauptsatz* (`LJProof.cutElim`).

## Main Definitions

- `SeqProof.formulas`: The set of all formulas appearing in any sequent of an LJ proof tree.

## Main Results

- `CutFreeLJProof.subformula_property`: Every formula in a cut-free LJ proof of `Γ ⊢ C`
  is a subformula of some formula in `insert C Γ`.
- `LJProof.subformula_property`: Every LJ proof has a cut-free variant satisfying the
  subformula property.

## References

* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Formula Collection -/

/-- The set of all formula occurrences in a proof tree: every node contributes
all formulas from its premise sequents, propagated upward from the leaves. Generic over `T`. -/
def SeqProof.formulas {T : Theory Atom} {seq : @Sequent Atom} :
    SeqProof T seq → Finset (Proposition Atom)
  | .ax A Γ _         => insert A Γ
  | @SeqProof.botL _ _ _ Γ C _ _ => insert C Γ
  | .andL _ _ _ d     => d.formulas
  | .andR _ _ d₁ d₂  => d₁.formulas ∪ d₂.formulas
  | .orL _ _ _ d₁ d₂ => d₁.formulas ∪ d₂.formulas
  | .orR1 _ _ d       => d.formulas
  | .orR2 _ _ d       => d.formulas
  | .impL _ _ _ d₁ d₂ => d₁.formulas ∪ d₂.formulas
  | .impR _ _ d       => d.formulas
  | .weakL _ d        => d.formulas
  | .cut _ d₁ d₂      => d₁.formulas ∪ d₂.formulas

/-! ## Membership Helpers -/

/-- Lift an `IsSubformula` witness to a given target set. -/
private lemma ljLiftSub
    {B C : Proposition Atom}
    {tgt : Finset (Proposition Atom)}
    (hmem : C ∈ tgt) (hsub : B.IsSubformula C) :
    ∃ D ∈ tgt, B.IsSubformula D :=
  ⟨C, hmem, hsub⟩

/-! ## Subformula Property for Cut-Free Proofs (Core) -/

/-- Core subformula property: in any cut-free LJ proof, every formula in `d.formulas` is
a subformula of some formula in the conclusion sequent `insert seq.2 seq.1`.

This helper takes `(d : LJProof seq)` and `(hcf : LJCutFree d)` separately so that
`induction d with` can proceed without the Finset-quotient index problem.
The `cut` case is vacuous since `LJCutFree` is `False` for `cut` steps. -/
private lemma ljCutFreeSubformulaProp {seq : @Sequent Atom}
    (d : LJProof seq) (hcf : LJCutFree d) :
    ∀ B ∈ d.formulas, ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C := by
  induction d with
  | ax A Γ hA =>
    intro B hB
    simp only [SeqProof.formulas] at hB
    exact ⟨B, hB, Proposition.IsSubformula.refl B⟩
  | botL Γ C hbot =>
    intro B hB
    simp only [SeqProof.formulas] at hB
    exact ⟨B, hB, Proposition.IsSubformula.refl B⟩
  | andL A B hAB d' ih =>
    -- Conclusion: Γ ⊢ C where (A ∧ B) ∈ Γ.  Target: insert C Γ.
    -- Premise: insert A (insert B Γ) ⊢ C.  IH target: insert C (insert A (insert B Γ)).
    -- After simp: C' = C ∨ C' = A ∨ C' = B ∨ C' ∈ Γ  (4 cases).
    intro B' hB'
    simp only [SeqProof.formulas] at hB'
    obtain ⟨C', hC', hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_insert] at hC'
    rcases hC' with rfl | rfl | rfl | hC'
    · -- C' is the conclusion formula C.
      exact ljLiftSub (Finset.mem_insert_self _ _) hCS
    · -- C' = A; A is a subformula of A ∧ B ∈ Γ.
      exact ljLiftSub (Finset.mem_insert_of_mem hAB)
        (hCS.trans Proposition.IsSubformula.and_left)
    · -- C' = B; B is a subformula of A ∧ B ∈ Γ.
      exact ljLiftSub (Finset.mem_insert_of_mem hAB)
        (hCS.trans Proposition.IsSubformula.and_right)
    · -- C' ∈ Γ ⊆ insert C Γ.
      exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
  | andR A B d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ A ∧ B.  Target: insert (A ∧ B) Γ.
    -- IH₁ target: insert A Γ.  After simp: C' = A ∨ C' ∈ Γ  (2 cases).
    -- IH₂ target: insert B Γ.  After simp: C' = B ∨ C' ∈ Γ  (2 cases).
    intro B' hB'
    simp only [SeqProof.formulas, Finset.mem_union] at hB'
    rcases hB' with hB₁ | hB₂
    · obtain ⟨C', hC', hCS⟩ := ih₁ hcf.1 B' hB₁
      simp only [Finset.mem_insert] at hC'
      rcases hC' with rfl | hC'
      · -- C' = A; A is a subformula of A ∧ B (the conclusion).
        exact ljLiftSub (Finset.mem_insert_self _ _)
          (hCS.trans Proposition.IsSubformula.and_left)
      · -- C' ∈ Γ ⊆ insert (A ∧ B) Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
    · obtain ⟨C', hC', hCS⟩ := ih₂ hcf.2 B' hB₂
      simp only [Finset.mem_insert] at hC'
      rcases hC' with rfl | hC'
      · -- C' = B; B is a subformula of A ∧ B (the conclusion).
        exact ljLiftSub (Finset.mem_insert_self _ _)
          (hCS.trans Proposition.IsSubformula.and_right)
      · -- C' ∈ Γ ⊆ insert (A ∧ B) Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
  | orL A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ C where (A ∨ B) ∈ Γ.  Target: insert C Γ.
    -- IH₁ target: insert C (insert A Γ).  After simp: C' = C ∨ C' = A ∨ C' ∈ Γ  (3 cases).
    -- IH₂ target: insert C (insert B Γ).  After simp: C' = C ∨ C' = B ∨ C' ∈ Γ  (3 cases).
    intro B' hB'
    simp only [SeqProof.formulas, Finset.mem_union] at hB'
    rcases hB' with hB₁ | hB₂
    · obtain ⟨C', hC', hCS⟩ := ih₁ hcf.1 B' hB₁
      simp only [Finset.mem_insert] at hC'
      rcases hC' with rfl | rfl | hC'
      · -- C' is the conclusion formula C.
        exact ljLiftSub (Finset.mem_insert_self _ _) hCS
      · -- C' = A; A is a subformula of A ∨ B ∈ Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hAB)
          (hCS.trans Proposition.IsSubformula.or_left)
      · -- C' ∈ Γ ⊆ insert C Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
    · obtain ⟨C', hC', hCS⟩ := ih₂ hcf.2 B' hB₂
      simp only [Finset.mem_insert] at hC'
      rcases hC' with rfl | rfl | hC'
      · -- C' is the conclusion formula C.
        exact ljLiftSub (Finset.mem_insert_self _ _) hCS
      · -- C' = B; B is a subformula of A ∨ B ∈ Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hAB)
          (hCS.trans Proposition.IsSubformula.or_right)
      · -- C' ∈ Γ ⊆ insert C Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
  | orR1 A B d' ih =>
    -- Conclusion: Γ ⊢ A ∨ B.  Target: insert (A ∨ B) Γ.
    -- IH target: insert A Γ.  After simp: C' = A ∨ C' ∈ Γ  (2 cases).
    intro B' hB'
    simp only [SeqProof.formulas] at hB'
    obtain ⟨C', hC', hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_insert] at hC'
    rcases hC' with rfl | hC'
    · -- C' = A; A is a subformula of A ∨ B (the conclusion).
      exact ljLiftSub (Finset.mem_insert_self _ _)
        (hCS.trans Proposition.IsSubformula.or_left)
    · -- C' ∈ Γ ⊆ insert (A ∨ B) Γ.
      exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
  | orR2 A B d' ih =>
    -- Conclusion: Γ ⊢ A ∨ B.  Target: insert (A ∨ B) Γ.
    -- IH target: insert B Γ.  After simp: C' = B ∨ C' ∈ Γ  (2 cases).
    intro B' hB'
    simp only [SeqProof.formulas] at hB'
    obtain ⟨C', hC', hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_insert] at hC'
    rcases hC' with rfl | hC'
    · -- C' = B; B is a subformula of A ∨ B (the conclusion).
      exact ljLiftSub (Finset.mem_insert_self _ _)
        (hCS.trans Proposition.IsSubformula.or_right)
    · -- C' ∈ Γ ⊆ insert (A ∨ B) Γ.
      exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
  | impL A B hAB d₁ d₂ ih₁ ih₂ =>
    -- Conclusion: Γ ⊢ C where (A → B) ∈ Γ.  Target: insert C Γ.
    -- IH₁ target (Γ ⊢ A): insert A Γ.  After simp: C' = A ∨ C' ∈ Γ  (2 cases).
    -- IH₂ target (insert B Γ ⊢ C): insert C (insert B Γ).
    -- After simp: C' = C ∨ C' = B ∨ C' ∈ Γ  (3 cases).
    intro B' hB'
    simp only [SeqProof.formulas, Finset.mem_union] at hB'
    rcases hB' with hB₁ | hB₂
    · obtain ⟨C', hC', hCS⟩ := ih₁ hcf.1 B' hB₁
      simp only [Finset.mem_insert] at hC'
      rcases hC' with rfl | hC'
      · -- C' = A; A is a subformula of (A → B) ∈ Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hAB)
          (hCS.trans Proposition.IsSubformula.imp_left)
      · -- C' ∈ Γ ⊆ insert C Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
    · obtain ⟨C', hC', hCS⟩ := ih₂ hcf.2 B' hB₂
      simp only [Finset.mem_insert] at hC'
      rcases hC' with rfl | rfl | hC'
      · -- C' is the conclusion formula C.
        exact ljLiftSub (Finset.mem_insert_self _ _) hCS
      · -- C' = B; B is a subformula of (A → B) ∈ Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hAB)
          (hCS.trans Proposition.IsSubformula.imp_right)
      · -- C' ∈ Γ ⊆ insert C Γ.
        exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
  | impR A B d' ih =>
    -- Conclusion: Γ ⊢ A → B.  Target: insert (A → B) Γ.
    -- Premise: insert A Γ ⊢ B.  IH target: insert B (insert A Γ).
    -- After simp: C' = B ∨ C' = A ∨ C' ∈ Γ  (3 cases).
    intro B' hB'
    simp only [SeqProof.formulas] at hB'
    obtain ⟨C', hC', hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_insert] at hC'
    rcases hC' with rfl | rfl | hC'
    · -- C' = B; B is a subformula of (A → B) (the conclusion).
      exact ljLiftSub (Finset.mem_insert_self _ _)
        (hCS.trans Proposition.IsSubformula.imp_right)
    · -- C' = A; A is a subformula of (A → B) (the conclusion).
      exact ljLiftSub (Finset.mem_insert_self _ _)
        (hCS.trans Proposition.IsSubformula.imp_left)
    · -- C' ∈ Γ ⊆ insert (A → B) Γ.
      exact ljLiftSub (Finset.mem_insert_of_mem hC') hCS
  | weakL A d' ih =>
    -- Conclusion: insert A Γ ⊢ C.  Target: insert C (insert A Γ).
    -- Premise: Γ ⊢ C.  IH target: insert C Γ.
    -- After simp: C' = C ∨ C' ∈ Γ  (2 cases).
    intro B' hB'
    simp only [SeqProof.formulas] at hB'
    obtain ⟨C', hC', hCS⟩ := ih hcf B' hB'
    simp only [Finset.mem_insert] at hC'
    rcases hC' with rfl | hC'
    · -- C' = C (the conclusion formula); C ∈ insert C (insert A Γ).
      exact ljLiftSub (Finset.mem_insert_self _ _) hCS
    · -- C' ∈ Γ ⊆ insert A Γ ⊆ insert C (insert A Γ).
      exact ljLiftSub (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hC')) hCS
  | cut _ _ _ =>
    -- The cut case is vacuous: LJCutFree is False for cut steps.
    exact absurd hcf id

/-! ## Subformula Property for Cut-Free Proofs -/

/-- The subformula property for cut-free LJ proofs: every formula appearing in any
sequent of a cut-free proof of `Γ ⊢ C` is a subformula of some formula in `insert C Γ`.

Proved by structural induction on the proof tree using `ljCutFreeSubformulaProp`.
The `cut` case is vacuous since `LJCutFree` is `False` for `cut` steps.

This is the intuitionistic analogue of `CutFreeLKProof.subformula_property` and follows
from Gentzen's *Hauptsatz* for LJ (Theorem 4.1.6 of [TroelstraSchwichtenberg2000]). -/
lemma CutFreeLJProof.subformula_property
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d : CutFreeLJProof (Γ ⊢ C)) :
    ∀ B ∈ d.val.formulas,
      ∃ D ∈ insert C Γ, B.IsSubformula D :=
  ljCutFreeSubformulaProp d.val d.property

/-! ## Subformula Property for General LJ Proofs -/

/-- Subformula property for LJ: every sequent provable in LJ has a cut-free proof
satisfying the subformula property. Every formula in the cut-free proof is a subformula
of some formula in the conclusion sequent `insert seq.2 seq.1`.

This is an immediate corollary of `LJProof.cutElim` (Gentzen's *Hauptsatz*) and
`CutFreeLJProof.subformula_property`. -/
theorem LJProof.subformula_property
    {seq : @Sequent Atom} (d : LJProof seq) :
    ∃ d' : CutFreeLJProof seq,
      ∀ B ∈ d'.val.formulas,
        ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C := by
  obtain ⟨d'⟩ := d.cutElim
  exact ⟨d', ljCutFreeSubformulaProp d'.val d'.property⟩

end Cslib.Logic.PL

end
