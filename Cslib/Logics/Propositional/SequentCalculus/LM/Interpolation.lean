/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.Interpolation
public import Cslib.Logics.Propositional.SequentCalculus.LM.Basic

/-! # Craig Interpolation for LM (Minimal Propositional Logic)

Instantiates the generic `CutFreeSeqProof.splitInterpolation` and `SeqProof.interpolation`
(`LJ/Interpolation.lean`) at `MPL`, giving Craig interpolation for the minimal calculus
`SeqProofMinimal := SeqProof MPL`. Reuses the Phase 3 public wrapper shape
(`CutFreeSeqProof.splitInterpolation`) rather than introducing a second one.

## Main Results

- `SeqProofMinimal.splitInterpolation`: the general-partition form of Craig interpolation for
  LM, mirroring `LJProof.splitInterpolation`'s shape.
- `SeqProofMinimal.interpolation`: Craig interpolation for LM, mirroring
  `LJProof.interpolation`'s shape.

## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Theory

variable {Atom : Type u} [DecidableEq Atom]

/-- Split interpolation for LM: the general-partition form of Craig interpolation. Specialises
the generic `CutFreeSeqProof.splitInterpolation` at `MPL`, mirroring
`LJProof.splitInterpolation`'s shape. -/
theorem SeqProofMinimal.splitInterpolation {seq : @Sequent Atom} (d : CutFreeSeqProof MPL seq)
    (Γ₁ Γ₂ : Finset (Proposition Atom)) (hant : seq.1 = Γ₁ ∪ Γ₂) :
    ∃ I : Proposition Atom,
      I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars ∧
      Nonempty (SeqProofMinimal (Γ₁ ⊢ I)) ∧
      Nonempty (SeqProofMinimal (insert I Γ₂ ⊢ seq.2)) :=
  CutFreeSeqProof.splitInterpolation (T := MPL) d Γ₁ Γ₂ hant

/-- Craig Interpolation for LM: For any `SeqProofMinimal` proof of `∅ ⊢ A → B`, there exists an
interpolant `I` with `I.vars ⊆ A.vars ∩ B.vars`, `∅ ⊢ A → I`, and `∅ ⊢ I → B`. Specialises the
generic `SeqProof.interpolation` at `MPL`, mirroring `LJProof.interpolation`'s shape. -/
theorem SeqProofMinimal.interpolation {A B : Proposition Atom}
    (d : SeqProofMinimal ((∅ : Finset (Proposition Atom)) ⊢ A → B)) :
    ∃ I : Proposition Atom,
      I.vars ⊆ A.vars ∩ B.vars ∧
      Nonempty (SeqProofMinimal ((∅ : Finset (Proposition Atom)) ⊢ A → I)) ∧
      Nonempty (SeqProofMinimal ((∅ : Finset (Proposition Atom)) ⊢ I → B)) :=
  SeqProof.interpolation (T := MPL) d

end Cslib.Logic.PL

end
