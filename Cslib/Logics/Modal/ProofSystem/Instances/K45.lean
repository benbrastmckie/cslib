/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem
public import Cslib.Logics.Modal.ProofSystem.SchemaUnion

/-! # Instance Registration for Modal Logic K45

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic K45.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic K45.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalFour` (transitivity),
  `modalFive` (Euclideanness) -/
inductive K45Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      K45Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      K45Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      K45Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`.

  Sanctioned schema (task 441): with native `and`/`or`/`diamond` constructors, this
  characterization axiom is necessary (it was a derivable theorem under the prior
  Łukasiewicz encoding, so this is conservative). See `Axioms.AndI`. -/
  | andI (φ ψ : Proposition Atom) :
      K45Axiom (Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. See `Axioms.AndE1`. -/
  | andE1 (φ ψ : Proposition Atom) :
      K45Axiom (Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. See `Axioms.AndE2`. -/
  | andE2 (φ ψ : Proposition Atom) :
      K45Axiom (Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. See `Axioms.OrI1`. -/
  | orI1 (φ ψ : Proposition Atom) :
      K45Axiom (Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. See `Axioms.OrI2`. -/
  | orI2 (φ ψ : Proposition Atom) :
      K45Axiom (Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. See `Axioms.OrE`. -/
  | orE (φ ψ χ : Proposition Atom) :
      K45Axiom (Axioms.OrE φ ψ χ)
  /-- Diamond duality, forward direction: `◇φ → ¬□¬φ`. See `Axioms.AxiomDiaDualityFwd`. -/
  | diaDualityFwd (φ : Proposition Atom) :
      K45Axiom (Axioms.AxiomDiaDualityFwd φ)
  /-- Diamond duality, backward direction: `¬□¬φ → ◇φ`. See `Axioms.AxiomDiaDualityBack`. -/
  | diaDualityBack (φ : Proposition Atom) :
      K45Axiom (Axioms.AxiomDiaDualityBack φ)


end Cslib.Logic.Modal

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-- Local forward-direction discharge from `SchemaUnion` to `K45Axiom`, used by
the instance registrations below. Mirrors the `.mp` half of
`Cslib.Logics.Modal.ProofSystem.SchemaBridges.schemaUnion_k45Tags_iff_K45Axiom`;
it cannot import that theorem directly because `SchemaBridges.lean` imports the
`Instances` barrel (which imports this file), so importing it here would create an
import cycle (confirmed via a direct `lake build` attempt: `bad import
'Cslib.Logics.Modal.ProofSystem.Instances'`). Only `SchemaUnion.lean` (which does not
depend on `Instances`) is imported here. Phase 8 deletes this helper alongside the
`inductive K45Axiom` it targets, once the redefinition makes the conversion a
defeq no-op. -/
private theorem k45Tags_of_schemaUnion {χ : Proposition Atom}
    (h : SchemaUnion (insert .implyK <| insert .implyS <| insert .efq <| insert .peirce <|
      insert .modalK <| insert .andI <| insert .andE1 <| insert .andE2 <|
      insert .orI1 <| insert .orI2 <| insert .orE <| insert .diaDualityFwd
      <| insert .diaDualityBack <| insert .modalFour <| insert .modalFive ∅ :
      Finset ModalSchemaTag) χ) : K45Axiom χ := by
  simp only [SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
    ModalSchemaTag.Holds] at h
  rcases h with ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
  all_goals first
    | exact K45Axiom.implyK _ _
    | exact K45Axiom.implyS _ _ _
    | exact K45Axiom.efq _
    | exact K45Axiom.peirce _ _
    | exact K45Axiom.modalK _ _
    | exact K45Axiom.andI _ _
    | exact K45Axiom.andE1 _ _
    | exact K45Axiom.andE2 _ _
    | exact K45Axiom.orI1 _ _
    | exact K45Axiom.orI2 _ _
    | exact K45Axiom.orE _ _ _
    | exact K45Axiom.diaDualityFwd _
    | exact K45Axiom.diaDualityBack _
    | exact K45Axiom.modalFour _
    | exact K45Axiom.modalFive _

/-! ### System K45 Instances -/

instance : InferenceSystem Modal.HilbertK45
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.K45Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.implyK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomImplyS Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.implyS, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomEFQ Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.efq, by decide, _, rfl⟩)⟩

instance :
    HasAxiomPeirce Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.peirce, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomK Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.modalK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiom4 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.modalFour, by decide, _, rfl⟩)⟩

instance :
    HasAxiom5 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.modalFive, by decide, _, rfl⟩)⟩

instance :
    ModalHilbert Modal.HilbertK45
      (F := Modal.Proposition Atom) where

instance :
    ModalK4Hilbert Modal.HilbertK45
      (F := Modal.Proposition Atom) where

instance :
    ModalK45Hilbert Modal.HilbertK45
      (F := Modal.Proposition Atom) where


instance :
    HasAxiomAndI Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.andI, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE1 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.andE1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE2 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.andE2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI1 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.orI1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI2 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.orI2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrE Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.orE, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomDiaDualityFwd Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  diaDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.diaDualityFwd, by decide, _, rfl⟩)⟩

instance :
    HasAxiomDiaDualityBack Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  diaDualityBack := ⟨Modal.DerivationTree.ax [] _
    (k45Tags_of_schemaUnion ⟨.diaDualityBack, by decide, _, rfl⟩)⟩

end ModalInstances

end Cslib.Logic.Modal
