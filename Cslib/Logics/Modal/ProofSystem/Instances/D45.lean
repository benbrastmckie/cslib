/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Logic D45

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic D45.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic D45.

The 8 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (4): `modalK` (K distribution), `modalD` (seriality),
  `modalFour` (transitivity), `modalFive` (Euclideanness) -/
inductive D45Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      D45Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      D45Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      D45Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`.

  Sanctioned schema (task 441): with native `and`/`or`/`diamond` constructors, this
  characterization axiom is necessary (it was a derivable theorem under the prior
  Łukasiewicz encoding, so this is conservative). See `Axioms.AndI`. -/
  | andI (φ ψ : Proposition Atom) :
      D45Axiom (Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. See `Axioms.AndE1`. -/
  | andE1 (φ ψ : Proposition Atom) :
      D45Axiom (Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. See `Axioms.AndE2`. -/
  | andE2 (φ ψ : Proposition Atom) :
      D45Axiom (Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. See `Axioms.OrI1`. -/
  | orI1 (φ ψ : Proposition Atom) :
      D45Axiom (Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. See `Axioms.OrI2`. -/
  | orI2 (φ ψ : Proposition Atom) :
      D45Axiom (Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. See `Axioms.OrE`. -/
  | orE (φ ψ χ : Proposition Atom) :
      D45Axiom (Axioms.OrE φ ψ χ)
  /-- Diamond duality, forward direction: `◇φ → ¬□¬φ`. See `Axioms.AxiomDiaDualityFwd`. -/
  | diaDualityFwd (φ : Proposition Atom) :
      D45Axiom (Axioms.AxiomDiaDualityFwd φ)
  /-- Diamond duality, backward direction: `¬□¬φ → ◇φ`. See `Axioms.AxiomDiaDualityBack`. -/
  | diaDualityBack (φ : Proposition Atom) :
      D45Axiom (Axioms.AxiomDiaDualityBack φ)


end Cslib.Logic.Modal

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-! ### System D45 Instances -/

instance : InferenceSystem Modal.HilbertD45
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.D45Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalK _ _)⟩

instance :
    HasAxiomD Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalD _)⟩

instance :
    HasAxiom4 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalFour _)⟩

instance :
    HasAxiom5 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalFive _)⟩

instance :
    ModalHilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where

instance :
    ModalD4Hilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where

instance :
    ModalD45Hilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where


instance :
    HasAxiomAndI Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.andI _ _)⟩

instance :
    HasAxiomAndE1 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.andE1 _ _)⟩

instance :
    HasAxiomAndE2 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.andE2 _ _)⟩

instance :
    HasAxiomOrI1 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.orI1 _ _)⟩

instance :
    HasAxiomOrI2 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.orI2 _ _)⟩

instance :
    HasAxiomOrE Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.orE _ _ _)⟩

instance :
    HasAxiomDiaDualityFwd Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  diaDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.diaDualityFwd _)⟩

instance :
    HasAxiomDiaDualityBack Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  diaDualityBack := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.diaDualityBack _)⟩

end ModalInstances

end Cslib.Logic.Modal
