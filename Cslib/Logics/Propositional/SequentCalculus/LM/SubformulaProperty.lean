/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.SubformulaProperty
public import Cslib.Logics.Propositional.SequentCalculus.LM.Basic

/-! # Subformula Property for LM (Minimal Propositional Logic)

Instantiates the generic `SeqProof.subformula_property` (`LJ/SubformulaProperty.lean`) at `MPL`,
giving the subformula property for the minimal calculus `SeqProofMinimal := SeqProof MPL`.

## Main Results

- `SeqProofMinimal.subformula_property`: Every `SeqProofMinimal`-derivable sequent has a
  cut-free proof satisfying the subformula property.

## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Theory

variable {Atom : Type u} [DecidableEq Atom]

/-- Subformula property for LM: every `SeqProofMinimal` proof has a cut-free variant satisfying
the subformula property. Specialises the generic `SeqProof.subformula_property` at `MPL`,
mirroring `LJProof.subformula_property`'s shape. -/
theorem SeqProofMinimal.subformula_property
    {seq : @Sequent Atom} (d : SeqProofMinimal seq) :
    ∃ d' : CutFreeSeqProof MPL seq,
      ∀ B ∈ d'.val.formulas,
        ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C :=
  SeqProof.subformula_property (T := MPL) d

end Cslib.Logic.PL

end
