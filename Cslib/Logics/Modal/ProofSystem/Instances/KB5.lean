/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Logic KB5

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic KB5.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic KB5.

The 13 axiom constructors cover:
- **Propositional** (10): `implyK`, `implyS`, `efq`, `peirce`, `andI`, `andE1`, `andE2`,
  `orI1`, `orI2`, `orE`
- **Modal** (3): `modalK` (K distribution), `modalB` (symmetry),
  `modalFive` (Euclideanness) -/
inductive KB5Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      KB5Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp φ (Proposition.imp ψ (Proposition.and φ ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.and φ ψ) φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.and φ ψ) ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ` -/
  | orI1 (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp φ (Proposition.or φ ψ))
  /-- Right disjunction introduction: `ψ → φ ∨ ψ` -/
  | orI2 (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp ψ (Proposition.or φ ψ))
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))` -/
  | orE (φ ψ χ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.imp φ χ)
        (Proposition.imp (Proposition.imp ψ χ) (Proposition.imp (Proposition.or φ ψ) χ)))
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- B / symmetry: `φ → □◇φ` -/
  | modalB (φ : Proposition Atom) :
      KB5Axiom (φ.imp (Proposition.box (Proposition.diamond φ)))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      KB5Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))

end Cslib.Logic.Modal

/-! ## Instance Registrations -/

section ModalInstances

/-! ### System KB5 Instances -/

instance : InferenceSystem Modal.HilbertKB5
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.KB5Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.modalK _ _)⟩

instance :
    HasAxiomB Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.modalB _)⟩

instance :
    HasAxiom5 Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.modalFive _)⟩

instance :
    HasAxiomAndI Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _ (Modal.KB5Axiom.andI _ _)⟩

instance :
    HasAxiomAndE1 Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _ (Modal.KB5Axiom.andE1 _ _)⟩

instance :
    HasAxiomAndE2 Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _ (Modal.KB5Axiom.andE2 _ _)⟩

instance :
    HasAxiomOrI1 Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _ (Modal.KB5Axiom.orI1 _ _)⟩

instance :
    HasAxiomOrI2 Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _ (Modal.KB5Axiom.orI2 _ _)⟩

instance :
    HasAxiomOrE Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _ (Modal.KB5Axiom.orE _ _ _)⟩

instance :
    ModalHilbert Modal.HilbertKB5
      (F := Modal.Proposition Atom) where

instance :
    ModalBHilbert Modal.HilbertKB5
      (F := Modal.Proposition Atom) where

instance :
    ModalKB5Hilbert Modal.HilbertKB5
      (F := Modal.Proposition Atom) where

end ModalInstances
