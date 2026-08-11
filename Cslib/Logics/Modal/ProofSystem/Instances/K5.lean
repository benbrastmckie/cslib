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

/-! # Instance Registration for Modal Logic K5

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic K5.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic K5, as the schema-union combinator over `k5Tags`
(the inductive is retired; `K5Axiom` is now definitionally
`SchemaUnion k5Tags`, preserving the name and public API via redefinition-in-place).

The 6 axiom-schema families covered by `k5Tags`:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalFive` (Euclideanness: `◇φ → □◇φ` where
  `◇φ = (□(φ → ⊥)) → ⊥`; see [Blackburn2001] Section 1.4 and
  [ChagrovZakharyaschev1997] Section 3.2)
- plus the and/or/diamond-duality characterization tags, all part of `kCore`. -/
abbrev K5Axiom : Proposition Atom → Prop := SchemaUnion k5Tags

end Cslib.Logic.Modal

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-! ### System K5 Instances -/

instance : InferenceSystem Modal.HilbertK5
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.K5Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomImplyS Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (⟨.implyS, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomEFQ Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (⟨.efq, by decide, _, rfl⟩)⟩

instance :
    HasAxiomPeirce Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (⟨.peirce, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomK Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiom5 Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (⟨.modalFive, by decide, _, rfl⟩)⟩

instance :
    ModalHilbert Modal.HilbertK5
      (F := Modal.Proposition Atom) where

instance :
    ModalK5Hilbert Modal.HilbertK5
      (F := Modal.Proposition Atom) where


instance :
    HasAxiomAndI Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (⟨.andI, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE1 Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE2 Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.andE2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI1 Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI2 Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (⟨.orI2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrE Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (⟨.orE, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityFwd Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  diamondDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityFwd, by decide, _, rfl⟩)⟩

instance :
    HasAxiomDiamondDualityBack Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  diamondDualityBack := ⟨Modal.DerivationTree.ax [] _
    (⟨.diamondDualityBack, by decide, _, rfl⟩)⟩

end ModalInstances

end Cslib.Logic.Modal
