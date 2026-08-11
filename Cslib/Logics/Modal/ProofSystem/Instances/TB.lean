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

/-! # Instance Registration for Modal Logic TB

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic TB.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic TB, as the schema-union combinator over `tbTags`
(the inductive is retired; `TBAxiom` is now definitionally
`SchemaUnion tbTags`, preserving the name and public API via redefinition-in-place).

The 7 axiom-schema families covered by `tbTags`:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalT` (reflexivity), `modalB` (symmetry)
- plus the and/or/diamond-duality characterization tags, all part of `kCore`. -/
abbrev TBAxiom : Proposition Atom → Prop := SchemaUnion tbTags

end Cslib.Logic.Modal

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-! ### System TB Instances -/

instance : InferenceSystem Modal.HilbertTB
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.TBAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomImplyS Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyS, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomEFQ Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (⟨.efq, by decide, _, rfl⟩)⟩

instance :
    HasAxiomPeirce Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (⟨.peirce, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomK Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomT Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalT, by decide, _, rfl⟩)⟩

instance :
    HasAxiomB Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalB, by decide, _, rfl⟩)⟩

instance :
    ModalHilbert Modal.HilbertTB
      (F := Modal.Proposition Atom) where

instance :
    ModalTHilbert Modal.HilbertTB
      (F := Modal.Proposition Atom) where

instance :
    ModalTBHilbert Modal.HilbertTB
      (F := Modal.Proposition Atom) where


instance :
    HasAxiomAndI Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (⟨.andI, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE1 Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE2 Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI1 Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI2 Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrE Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (⟨.orE, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityFwd Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  diamondDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityFwd, by decide, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityBack Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  diamondDualityBack := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityBack, by decide, _, rfl⟩)⟩

end ModalInstances

end Cslib.Logic.Modal
