/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.SequentCalculus.LM.Basic

/-! # Cut Elimination for LM (Minimal Propositional Logic)

Instantiates the generic `ljCutAdmissibility` (`LJ/CutElimination.lean`) at `MPL`, giving
cut elimination for the minimal calculus `SeqProofMinimal := SeqProof MPL`.

## Main Results

- `SeqProofMinimal.cutElim`: Every `SeqProofMinimal`-derivable sequent has a cut-free proof.

## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000],
  Ch. 4, Theorem 4.1.1
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 2, Thm 2.4.3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Theory

variable {Atom : Type u} [DecidableEq Atom]

/-- Cut-free provability, generic over the theory `T`: every `SeqProof T` proof can be
transformed into a cut-free proof. Mirrors `LJProof.cutElim`'s shape and proof, generalised.

Kept as an ordinary theorem taking `{T}` as a genuine bound variable (rather than proved
directly for `SeqProofMinimal`/`MPL`) so that `induction d` does not need to revert a
non-variable occurrence of `T` in `d`'s type -- attempting the induction directly on
`d : SeqProofMinimal seq` makes `T` unify with the reducible `MPL := ∅` abbreviation, which the
`induction` tactic then generalises into a *fresh* local hypothesis (confusingly also displayed
as `MPL`), breaking the `botL` case's access to the concrete `MPL.IsIntuitionistic` instance
search space. Proving the generic statement first and specialising avoids that pitfall
entirely. The `botL` case extracts the locally-bound instance carried by the matched `botL`
constructor itself via `letI` (following `SeqProof.mono`'s idiom, `LJ/Basic.lean:184-186`),
since -- for `T = MPL` specifically -- no global `IsIntuitionistic MPL` instance exists. -/
theorem SeqProof.cutElim {T : Theory Atom} {seq : @Sequent Atom} (d : SeqProof T seq) :
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

/-- Cut-free provability for LM: every `SeqProofMinimal` proof can be transformed into a
cut-free proof. Specialises the generic `SeqProof.cutElim` at `MPL`, mirroring
`LJProof.cutElim`'s shape. -/
theorem SeqProofMinimal.cutElim {seq : @Sequent Atom} (d : SeqProofMinimal seq) :
    Nonempty (CutFreeSeqProof MPL seq) := by
  exact SeqProof.cutElim (T := MPL) d

end Cslib.Logic.PL

end
