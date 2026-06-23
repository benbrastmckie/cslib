/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Propositional.HilbertConjImp and Propositional.HilbertImp

This module registers `InferenceSystem`, `ModusPonens`, axiom instances,
and `MinimalHilbert` instances for the `Propositional.HilbertConjImp` and
`Propositional.HilbertImp` tag types, connecting the abstract typeclass hierarchy to the
concrete derivation trees parameterized over `ConjImpAxiom` and `ImpAxiom` respectively.

## Architecture

- `HilbertConjImp` instances use `DerivationTree ConjImpAxiom [] phi`.
- `HilbertImp` instances use `DerivationTree ImpAxiom [] phi`.

## References

* Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean -- pattern for minimal/int instances
* Cslib/Foundations/Logic/ProofSystem.lean -- typeclass hierarchy
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type*} [DecidableEq Atom]

namespace Cslib.Logic.PL

/-! ## HilbertConjImp Instances -/

section ConjImpInstances

instance : InferenceSystem Propositional.HilbertConjImp
    (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree ConjImpAxiom
    ([] : List (PL.Proposition Atom)) φ

instance :
    ModusPonens Propositional.HilbertConjImp
      (F := PL.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨PL.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    HasAxiomImplyK Propositional.HilbertConjImp
      (F := PL.Proposition Atom) where
  implyK := ⟨PL.DerivationTree.ax [] _ (.implyK _ _)⟩

instance :
    HasAxiomImplyS Propositional.HilbertConjImp
      (F := PL.Proposition Atom) where
  implyS := ⟨PL.DerivationTree.ax [] _ (.implyS _ _ _)⟩

instance :
    HasAxiomAndI Propositional.HilbertConjImp
      (F := PL.Proposition Atom) where
  andI := ⟨PL.DerivationTree.ax [] _ (.andI _ _)⟩

instance :
    HasAxiomAndE1 Propositional.HilbertConjImp
      (F := PL.Proposition Atom) where
  andE1 := ⟨PL.DerivationTree.ax [] _ (.andE1 _ _)⟩

instance :
    HasAxiomAndE2 Propositional.HilbertConjImp
      (F := PL.Proposition Atom) where
  andE2 := ⟨PL.DerivationTree.ax [] _ (.andE2 _ _)⟩

instance :
    MinimalHilbert Propositional.HilbertConjImp
      (F := PL.Proposition Atom) where

end ConjImpInstances

/-! ## HilbertImp Instances -/

section ImpInstances

instance : InferenceSystem Propositional.HilbertImp
    (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree ImpAxiom
    ([] : List (PL.Proposition Atom)) φ

instance :
    ModusPonens Propositional.HilbertImp
      (F := PL.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨PL.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    HasAxiomImplyK Propositional.HilbertImp
      (F := PL.Proposition Atom) where
  implyK := ⟨PL.DerivationTree.ax [] _ (.implyK _ _)⟩

instance :
    HasAxiomImplyS Propositional.HilbertImp
      (F := PL.Proposition Atom) where
  implyS := ⟨PL.DerivationTree.ax [] _ (.implyS _ _ _)⟩

instance :
    MinimalHilbert Propositional.HilbertImp
      (F := PL.Proposition Atom) where

end ImpInstances

end Cslib.Logic.PL
