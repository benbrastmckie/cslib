/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem
public import Cslib.Logics.Modal.ProofSystem.SchemaUnion
public import Cslib.Logics.Modal.ProofSystem.SchemaTags

/-! # Instance Registration for Modal Logic D4

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic D4.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic D4, as the schema-union combinator over `d4Tags`
(the inductive is retired; `D4Axiom` is now definitionally
`SchemaUnion d4Tags`, preserving the name and public API via redefinition-in-place).

The 7 axiom-schema families covered by `d4Tags`:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalD` (seriality), `modalFour` (transitivity)
- plus the and/or/diamond-duality characterization tags, all part of `kCore`. -/
abbrev D4Axiom : Proposition Atom → Prop := SchemaUnion d4Tags

end Cslib.Logic.Modal

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-! ### System D4 Instances -/

instance : InferenceSystem Modal.HilbertD4
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.D4Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomImplyS Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyS, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomEFQ Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (⟨.efq, by decide, _, rfl⟩)⟩

instance :
    HasAxiomPeirce Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (⟨.peirce, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomK Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomD Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalD, by decide, _, rfl⟩)⟩

instance :
    HasAxiom4 Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalFour, by decide, _, rfl⟩)⟩

instance :
    ModalHilbert Modal.HilbertD4
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertD4
      (F := Modal.Proposition Atom) where

instance :
    ModalD4Hilbert Modal.HilbertD4
      (F := Modal.Proposition Atom) where


instance :
    HasAxiomAndI Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (⟨.andI, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE1 Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE2 Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI1 Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI2 Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrE Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (⟨.orE, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityFwd Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  diamondDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityFwd, by decide, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityBack Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  diamondDualityBack := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityBack, by decide, _, rfl⟩)⟩

end ModalInstances

end Cslib.Logic.Modal
