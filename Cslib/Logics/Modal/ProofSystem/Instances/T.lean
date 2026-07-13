/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Logic T

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic T.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic T.

The 6 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalT` (reflexivity) -/
inductive TAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      TAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      TAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- T / reflexivity: `□φ → φ` -/
  | modalT (φ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.box φ) φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`.

  Sanctioned schema (task 441): with native `and`/`or`/`diamond` constructors, this
  characterization axiom is necessary (it was a derivable theorem under the prior
  Łukasiewicz encoding, so this is conservative). See `Axioms.AndI`. -/
  | andI (φ ψ : Proposition Atom) :
      TAxiom (Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. See `Axioms.AndE1`. -/
  | andE1 (φ ψ : Proposition Atom) :
      TAxiom (Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. See `Axioms.AndE2`. -/
  | andE2 (φ ψ : Proposition Atom) :
      TAxiom (Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. See `Axioms.OrI1`. -/
  | orI1 (φ ψ : Proposition Atom) :
      TAxiom (Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. See `Axioms.OrI2`. -/
  | orI2 (φ ψ : Proposition Atom) :
      TAxiom (Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. See `Axioms.OrE`. -/
  | orE (φ ψ χ : Proposition Atom) :
      TAxiom (Axioms.OrE φ ψ χ)
  /-- Diamond duality, forward direction: `◇φ → ¬□¬φ`. See `Axioms.AxiomDiaDualityFwd`. -/
  | diaDualityFwd (φ : Proposition Atom) :
      TAxiom (Axioms.AxiomDiaDualityFwd φ)
  /-- Diamond duality, backward direction: `¬□¬φ → ◇φ`. See `Axioms.AxiomDiaDualityBack`. -/
  | diaDualityBack (φ : Proposition Atom) :
      TAxiom (Axioms.AxiomDiaDualityBack φ)


end Cslib.Logic.Modal

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-! ### System T Instances -/

instance : InferenceSystem Modal.HilbertT
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.TAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertT
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertT
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertT
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertT
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertT
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertT
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertT
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.modalK _ _)⟩

instance :
    HasAxiomT Modal.HilbertT
      (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.modalT _)⟩

instance :
    ModalHilbert Modal.HilbertT
      (F := Modal.Proposition Atom) where

instance :
    ModalTHilbert Modal.HilbertT
      (F := Modal.Proposition Atom) where


instance :
    HasAxiomAndI Modal.HilbertT
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.andI _ _)⟩

instance :
    HasAxiomAndE1 Modal.HilbertT
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.andE1 _ _)⟩

instance :
    HasAxiomAndE2 Modal.HilbertT
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.andE2 _ _)⟩

instance :
    HasAxiomOrI1 Modal.HilbertT
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.orI1 _ _)⟩

instance :
    HasAxiomOrI2 Modal.HilbertT
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.orI2 _ _)⟩

instance :
    HasAxiomOrE Modal.HilbertT
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.orE _ _ _)⟩

instance :
    HasAxiomDiaDualityFwd Modal.HilbertT
      (F := Modal.Proposition Atom) where
  diaDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.diaDualityFwd _)⟩

instance :
    HasAxiomDiaDualityBack Modal.HilbertT
      (F := Modal.Proposition Atom) where
  diaDualityBack := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.diaDualityBack _)⟩

end ModalInstances

end Cslib.Logic.Modal
