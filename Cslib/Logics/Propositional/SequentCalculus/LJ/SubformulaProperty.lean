/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.Subformula

/-! # Subformula Property (Corollary of Cut Elimination), Generic over `T`

We prove the *subformula property*, generic over the theory `T`: every formula appearing in a
cut-free `SeqProof T` proof is a subformula of some formula in the conclusion sequent. The
general case follows from Gentzen's *Hauptsatz*. Both `LJProof.subformula_property` (at `IPL`)
and `LM/SubformulaProperty.lean`'s instantiation (at `MPL`) specialise the generic results here.

## Main Definitions

- `SeqProof.formulas`: The set of all formulas appearing in any sequent of a proof tree, generic
  over `T`.

## Main Results

- `CutFreeSeqProof.subformula_property`: Every formula in a cut-free `SeqProof T` proof of
  `Γ ⊢ C` is a subformula of some formula in `insert C Γ`, generic over `T`.
- `SeqProof.subformula_property`: Every `SeqProof T`-provable sequent has a cut-free variant
  satisfying the subformula property, generic over `T`.
- `CutFreeLJProof.subformula_property`, `LJProof.subformula_property`: re-exports of the above
  at `IPL`, preserving their exact current signatures.

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

/-- Core subformula property, generic over the theory `T`: in any cut-free `SeqProof T` proof,
every formula in `d.formulas` is a subformula of some formula in the conclusion sequent
`insert seq.2 seq.1`.

This helper takes `(d : SeqProof T seq)` and `(hcf : SeqProof.CutFree d)` separately so that
`induction d with` can proceed without the Finset-quotient index problem.
The `cut` case is vacuous since `SeqProof.CutFree` is `False` for `cut` steps. -/
private lemma seqProofCutFreeSubformulaProp {T : Theory Atom} {seq : @Sequent Atom}
    (d : SeqProof T seq) (hcf : SeqProof.CutFree d) :
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
    -- The cut case is vacuous: SeqProof.CutFree is False for cut steps.
    exact absurd hcf id

/-! ## Subformula Property for Cut-Free Proofs -/

/-- The subformula property for cut-free proofs, generic over the theory `T`: every formula
appearing in any sequent of a cut-free proof of `Γ ⊢ C` is a subformula of some formula in
`insert C Γ`.

Proved by structural induction on the proof tree using `seqProofCutFreeSubformulaProp`.
The `cut` case is vacuous since `SeqProof.CutFree` is `False` for `cut` steps.

This is the intuitionistic analogue of `CutFreeLKProof.subformula_property` and follows
from Gentzen's *Hauptsatz* for LJ (Theorem 4.1.6 of [TroelstraSchwichtenberg2000]). -/
theorem CutFreeSeqProof.subformula_property {T : Theory Atom}
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d : CutFreeSeqProof T (Γ ⊢ C)) :
    ∀ B ∈ d.val.formulas,
      ∃ D ∈ insert C Γ, B.IsSubformula D :=
  seqProofCutFreeSubformulaProp d.val d.property

/-- The subformula property for cut-free LJ proofs. Re-export of
`CutFreeSeqProof.subformula_property` at `IPL`, preserving the exact current signature. -/
lemma CutFreeLJProof.subformula_property
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d : CutFreeLJProof (Γ ⊢ C)) :
    ∀ B ∈ d.val.formulas,
      ∃ D ∈ insert C Γ, B.IsSubformula D :=
  CutFreeSeqProof.subformula_property d

/-! ## Cut Elimination, Local to This File (Generic over `T`) -/

/-- Cut-free provability, generic over the theory `T`, local to this file. `LJProof.cutElim`
(`LJ/CutElimination.lean`) proves the same fact directly at `IPL`; this generic copy mirrors
`SeqProof.cutElim` (`LM/CutElimination.lean`) so that `SeqProof.subformula_property` below does
not need to depend on the `IPL`-specific proof. The `botL` case extracts the locally-bound
instance carried by the matched `botL` constructor via `letI`, following `SeqProof.mono`'s idiom
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

/-! ## Subformula Property for General Proofs -/

/-- Subformula property, generic over the theory `T`: every `SeqProof T`-provable sequent has a
cut-free proof satisfying the subformula property. Every formula in the cut-free proof is a
subformula of some formula in the conclusion sequent `insert seq.2 seq.1`.

This is an immediate corollary of `seqProofCutElim` (Gentzen's *Hauptsatz*, generic over `T`) and
`CutFreeSeqProof.subformula_property`. -/
theorem SeqProof.subformula_property
    {T : Theory Atom} {seq : @Sequent Atom} (d : SeqProof T seq) :
    ∃ d' : CutFreeSeqProof T seq,
      ∀ B ∈ d'.val.formulas,
        ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C := by
  obtain ⟨d'⟩ := seqProofCutElim d
  exact ⟨d', seqProofCutFreeSubformulaProp d'.val d'.property⟩

/-- Subformula property for LJ. Re-export of `SeqProof.subformula_property` at `IPL`, preserving
the exact current signature. -/
theorem LJProof.subformula_property
    {seq : @Sequent Atom} (d : LJProof seq) :
    ∃ d' : CutFreeLJProof seq,
      ∀ B ∈ d'.val.formulas,
        ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C :=
  SeqProof.subformula_property d

end Cslib.Logic.PL

end
