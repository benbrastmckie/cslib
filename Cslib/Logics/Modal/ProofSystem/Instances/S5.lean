/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem
public import Cslib.Logics.Modal.ProofSystem.SchemaUnion

/-! # Instance Registration for Modal Logic S5

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic S5. Reuses the existing `S5Axiom` type.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-! ### System S5 Instances -/

instance : InferenceSystem Modal.HilbertS5
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.S5Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomImplyS Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyS, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomEFQ Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (⟨.efq, by decide, _, rfl⟩)⟩

instance :
    HasAxiomPeirce Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (⟨.peirce, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomK Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomT Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalT, by decide, _, rfl⟩)⟩

instance :
    HasAxiom4 Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalFour, by decide, _, rfl⟩)⟩

instance :
    HasAxiomB Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalB, by decide, _, rfl⟩)⟩

instance :
    ModalHilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

instance :
    ModalTHilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

instance :
    ModalS4Hilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

instance :
    ModalS5Hilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

instance :
    HasAxiomAndI Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (⟨.andI, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE1 Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE2 Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI1 Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI2 Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrE Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (⟨.orE, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityFwd Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  diamondDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityFwd, by decide, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityBack Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  diamondDualityBack := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityBack, by decide, _, rfl⟩)⟩

end ModalInstances

end Cslib.Logic.Modal
