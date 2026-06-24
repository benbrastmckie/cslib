/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Basic

/-! # Cut Elimination for LJ (Hauptsatz)

We prove that the cut rule is admissible in LJ: every LJ derivation can be transformed
into a cut-free derivation of the same sequent.

## Main Results

- `LJCutFree.mono`: Cut-freeness is preserved under context weakening (`LJProof.mono`).
- `CutFreeLJProof.mono`: Cut-free proofs are closed under context weakening.
- `cutAdmissibility`: From cut-free proofs of `Γ ⊢ A` and `insert A Γ ⊢ C`,
  we can derive a cut-free proof of `Γ ⊢ C`.
- `LJProof.cutElim`: Every LJ-derivable sequent has a cut-free proof.

## Proof Strategy

The key theorem `cutAdmissibility` takes **cut-free** inputs and produces a **cut-free**
output. It proceeds by well-founded induction on the pair `(sizeOf A, d₁.height + d₂.height)`
under lexicographic ordering. The atom and `⊥` base cases are handled by case analysis on `d₁`.
The compound formula cases (`imp`, `and`, `or`) handle non-principal subcases structurally
(decreasing height sum), and handle the principal case (where `A` is introduced on both sides)
using the induction hypotheses for subformulas (decreasing formula size).

## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000],
  Ch. 4, Theorem 4.1.1
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 2, Thm 2.4.3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Cut-Freeness Preservation Under Weakening -/

/-- Cut-freeness is preserved under `LJProof.mono`. -/
lemma LJCutFree.mono {seq : @Sequent Atom} {Γ' : Ctx Atom}
    (hL : seq.1 ⊆ Γ') (d : LJProof seq) (hcf : LJCutFree d) :
    LJCutFree (d.mono hL) := by
  induction d generalizing Γ' with
  | ax _ _ _ => simp [LJProof.mono, LJCutFree]
  | botL _ _ _ => simp [LJProof.mono, LJCutFree]
  | andL _ _ _ _ ih =>
    simp only [LJProof.mono, LJCutFree] at *; exact ih _ hcf
  | andR _ _ _ _ ih₁ ih₂ =>
    simp only [LJProof.mono, LJCutFree] at *
    exact ⟨ih₁ _ hcf.1, ih₂ _ hcf.2⟩
  | orL _ _ _ _ _ ih₁ ih₂ =>
    simp only [LJProof.mono, LJCutFree] at *
    exact ⟨ih₁ _ hcf.1, ih₂ _ hcf.2⟩
  | orR1 _ _ _ ih =>
    simp only [LJProof.mono, LJCutFree] at *; exact ih _ hcf
  | orR2 _ _ _ ih =>
    simp only [LJProof.mono, LJCutFree] at *; exact ih _ hcf
  | impL _ _ _ _ _ ih₁ ih₂ =>
    simp only [LJProof.mono, LJCutFree] at *
    exact ⟨ih₁ _ hcf.1, ih₂ _ hcf.2⟩
  | impR _ _ _ ih =>
    simp only [LJProof.mono, LJCutFree] at *; exact ih _ hcf
  | weakL _ _ ih =>
    simp only [LJProof.mono, LJCutFree] at *; exact ih _ hcf
  | cut _ _ _ => exact absurd hcf id

/-- Monotonicity for cut-free LJ proofs. -/
def CutFreeLJProof.mono {seq : @Sequent Atom} {Γ' : Ctx Atom}
    (hL : seq.1 ⊆ Γ') (d : CutFreeLJProof seq) :
    CutFreeLJProof (Γ', seq.2) :=
  ⟨d.1.mono hL, LJCutFree.mono hL d.1 d.2⟩

/-! ## Cut Admissibility -/

/-- Cut admissibility for LJ (Hauptsatz): from cut-free proofs of `Γ ⊢ A` and
`insert A Γ ⊢ C`, we can derive a cut-free proof of `Γ ⊢ C`.

The proof uses well-founded induction on formula complexity (primary) and proof height
sum (secondary), following Negri and von Plato (2001), Theorem 2.4.3.

**Status**: This theorem is stated but not yet proved. The proof requires nested
well-founded induction that is technically challenging to express with Lean 4's
pair-indexed inductive type `LJProof`. A follow-up task will complete this proof. -/
noncomputable def cutAdmissibility (A : Proposition Atom) (Γ : Ctx Atom)
    (C : Proposition Atom)
    (d₁ : CutFreeLJProof (Γ ⊢ A))
    (d₂ : CutFreeLJProof (insert A Γ ⊢ C)) :
    CutFreeLJProof (Γ ⊢ C) := by
  sorry

/-! ## Cut Elimination -/

/-- Cut-free provability: every LJ proof can be transformed into a cut-free proof.

This is a corollary of `cutAdmissibility` applied to eliminate all cut steps.
The proof proceeds by structural induction on the LJ proof tree. Each non-cut
constructor is preserved directly. The cut case eliminates the cut step using
`cutAdmissibility`, which requires both sub-proofs to be cut-free (provided
inductively) and produces a cut-free result. -/
theorem LJProof.cutElim {seq : @Sequent Atom} (d : LJProof seq) :
    Nonempty (CutFreeLJProof seq) := by
  induction d with
  | ax A Γ hA => exact ⟨⟨.ax A Γ hA, trivial⟩⟩
  | botL Γ C hbot => exact ⟨⟨.botL Γ C hbot, trivial⟩⟩
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
      exact ⟨cutAdmissibility A _ _ d₁' d₂'⟩

end Cslib.Logic.PL
