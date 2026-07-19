/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem
public import Cslib.Logics.Modal.ProofSystem.SchemaUnion

/-! # Instance Registration for Modal Logic D

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic D.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic D.

The 6 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalD` (seriality) -/
inductive DAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      DAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      DAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥`.

  Diamond is encoded classically as the negation of box-negation (see `Axioms.AxiomD`).
  This corresponds to seriality of the accessibility relation (`∀ w, ∃ v, r w v`).
  See [Blackburn2001] Section 1.4 and [ChagrovZakharyaschev1997] Section 3.2. -/
  | modalD (φ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`.

  Sanctioned schema (task 441): with native `and`/`or`/`diamond` constructors, this
  characterization axiom is necessary (it was a derivable theorem under the prior
  Łukasiewicz encoding, so this is conservative). See `Axioms.AndI`. -/
  | andI (φ ψ : Proposition Atom) :
      DAxiom (Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. See `Axioms.AndE1`. -/
  | andE1 (φ ψ : Proposition Atom) :
      DAxiom (Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. See `Axioms.AndE2`. -/
  | andE2 (φ ψ : Proposition Atom) :
      DAxiom (Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. See `Axioms.OrI1`. -/
  | orI1 (φ ψ : Proposition Atom) :
      DAxiom (Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. See `Axioms.OrI2`. -/
  | orI2 (φ ψ : Proposition Atom) :
      DAxiom (Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. See `Axioms.OrE`. -/
  | orE (φ ψ χ : Proposition Atom) :
      DAxiom (Axioms.OrE φ ψ χ)
  /-- Diamond duality, forward direction: `◇φ → ¬□¬φ`. See `Axioms.AxiomDiaDualityFwd`. -/
  | diaDualityFwd (φ : Proposition Atom) :
      DAxiom (Axioms.AxiomDiaDualityFwd φ)
  /-- Diamond duality, backward direction: `¬□¬φ → ◇φ`. See `Axioms.AxiomDiaDualityBack`. -/
  | diaDualityBack (φ : Proposition Atom) :
      DAxiom (Axioms.AxiomDiaDualityBack φ)


end Cslib.Logic.Modal

/-! ## Instance Registrations -/

namespace Cslib.Logic.Modal

section ModalInstances

/-- Local forward-direction discharge from `SchemaUnion` to `DAxiom`, used by
the instance registrations below. Mirrors the `.mp` half of
`Cslib.Logics.Modal.ProofSystem.SchemaBridges.schemaUnion_dTags_iff_DAxiom`;
it cannot import that theorem directly because `SchemaBridges.lean` imports the
`Instances` barrel (which imports this file), so importing it here would create an
import cycle (confirmed via a direct `lake build` attempt: `bad import
'Cslib.Logics.Modal.ProofSystem.Instances'`). Only `SchemaUnion.lean` (which does not
depend on `Instances`) is imported here. Phase 8 deletes this helper alongside the
`inductive DAxiom` it targets, once the redefinition makes the conversion a
defeq no-op. -/
private theorem dTags_of_schemaUnion {χ : Proposition Atom}
    (h : SchemaUnion (insert .implyK <| insert .implyS <| insert .efq <| insert .peirce <|
      insert .modalK <| insert .andI <| insert .andE1 <| insert .andE2 <|
      insert .orI1 <| insert .orI2 <| insert .orE <| insert .diaDualityFwd
      <| insert .diaDualityBack <| insert .modalD ∅ :
      Finset ModalSchemaTag) χ) : DAxiom χ := by
  simp only [SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
    ModalSchemaTag.Holds] at h
  rcases h with ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', rfl⟩ | ⟨φ', rfl⟩
  all_goals first
    | exact DAxiom.implyK _ _
    | exact DAxiom.implyS _ _ _
    | exact DAxiom.efq _
    | exact DAxiom.peirce _ _
    | exact DAxiom.modalK _ _
    | exact DAxiom.andI _ _
    | exact DAxiom.andE1 _ _
    | exact DAxiom.andE2 _ _
    | exact DAxiom.orI1 _ _
    | exact DAxiom.orI2 _ _
    | exact DAxiom.orE _ _ _
    | exact DAxiom.diaDualityFwd _
    | exact DAxiom.diaDualityBack _
    | exact DAxiom.modalD _

/-! ### System D Instances -/

instance : InferenceSystem Modal.HilbertD
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.DAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertD
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertD
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertD
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.implyK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomImplyS Modal.HilbertD
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.implyS, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomEFQ Modal.HilbertD
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.efq, by decide, _, rfl⟩)⟩

instance :
    HasAxiomPeirce Modal.HilbertD
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.peirce, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomK Modal.HilbertD
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.modalK, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomD Modal.HilbertD
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.modalD, by decide, _, rfl⟩)⟩

instance :
    ModalHilbert Modal.HilbertD
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertD
      (F := Modal.Proposition Atom) where


instance :
    HasAxiomAndI Modal.HilbertD
      (F := Modal.Proposition Atom) where
  andI := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.andI, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE1 Modal.HilbertD
      (F := Modal.Proposition Atom) where
  andE1 := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.andE1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomAndE2 Modal.HilbertD
      (F := Modal.Proposition Atom) where
  andE2 := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.andE2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI1 Modal.HilbertD
      (F := Modal.Proposition Atom) where
  orI1 := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.orI1, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrI2 Modal.HilbertD
      (F := Modal.Proposition Atom) where
  orI2 := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.orI2, by decide, _, _, rfl⟩)⟩

instance :
    HasAxiomOrE Modal.HilbertD
      (F := Modal.Proposition Atom) where
  orE := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.orE, by decide, _, _, _, rfl⟩)⟩

instance :
    HasAxiomDiaDualityFwd Modal.HilbertD
      (F := Modal.Proposition Atom) where
  diaDualityFwd := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.diaDualityFwd, by decide, _, rfl⟩)⟩

instance :
    HasAxiomDiaDualityBack Modal.HilbertD
      (F := Modal.Proposition Atom) where
  diaDualityBack := ⟨Modal.DerivationTree.ax [] _
    (dTags_of_schemaUnion ⟨.diaDualityBack, by decide, _, rfl⟩)⟩

end ModalInstances

end Cslib.Logic.Modal
