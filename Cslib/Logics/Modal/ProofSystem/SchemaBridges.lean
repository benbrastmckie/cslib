/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.SchemaUnion
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Schema-Union Bridges: Per-System Tag Sets and Bridge Equivalences

This module defines `kCore` (the 13-tag shared propositional + K + and/or + diamond-duality
core) and the 15 per-system `Finset ModalSchemaTag` tag sets, and proves the bridge
equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` connecting the schema-union combinator
(`Cslib.Logics.Modal.ProofSystem.SchemaUnion`) to each of the 15 pre-existing per-system axiom
inductives (`KAxiom`, …, and S5's `ModalAxiom`).

This is purely additive (Phase 3 of the schema-union rollout): none of the 15 instance files,
`SchemaUnion.lean`, or `DerivationTree.lean` is modified. The inductives stay live until
Phase 8.

## Main Definitions

- `kCore`: the 13 shared tags (`implyK, implyS, efq, peirce, modalK, andI, andE1, andE2, orI1,
  orI2, orE, diaDualityFwd, diaDualityBack`).
- `kTags, tTags, dTags, bTags, k4Tags, k5Tags, k45Tags, s4Tags, s5Tags, tbTags, kb5Tags, d4Tags,
  d5Tags, d45Tags, dbTags`: the 15 per-system tag sets, each `kCore` unioned with that system's
  modal-strength differentiator tag(s) (`K` has none beyond `modalK`, already in `kCore`).

## Main Results

The 15 bridge equivalences, one per system (S5 bridges to `Modal.ModalAxiom`, the pre-existing
S5 axiom inductive in `Metalogic/DerivationTree.lean`):
`SchemaUnion kTags ↔ KAxiom`, `SchemaUnion tTags ↔ TAxiom`, …, `SchemaUnion s5Tags ↔ ModalAxiom`.

## Design

Each bridge's forward direction unfolds `SchemaUnion sysTags φ` via the Phase-2 elimination API
(`SchemaUnion.insert_iff`, `SchemaUnion.empty_iff`) into the named disjunction of its tags'
`.Holds` clauses, then maps each `.Holds` existential witness to the matching constructor of the
target inductive. The backward direction cases on the inductive's constructor and directly
supplies the matching tag (via the anonymous `SchemaUnion` witness `⟨tag, membership, …⟩`) plus
the `.Holds` existential witness — no simp unfolding needed since the witness is constructed
directly. Every system's tag set was cross-checked against the actual constructors present in
that system's inductive (`Instances/{K,T,D,B,K4,K5,K45,S4,TB,KB5,D4,D5,D45,DB}.lean`, and S5's
`ModalAxiom`) before being finalized here.

## References

* Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean -- `ModalSchemaTag`, `SchemaUnion`, elim. API
* Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,...}.lean -- the 15 per-system axiom inductives
* Cslib/Logics/Modal/Metalogic/DerivationTree.lean -- S5's `ModalAxiom`
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type u}

/-! ## Shared Core Tag Set -/

/-- The 13 shared tags: propositional (`implyK`, `implyS`, `efq`, `peirce`), K distribution
(`modalK`), and the and/or/diamond-duality characterization tags (`andI`, `andE1`, `andE2`,
`orI1`, `orI2`, `orE`, `diaDualityFwd`, `diaDualityBack`). Every one of the 15 classical normal
modal systems is `kCore` unioned with a subset of the 5 modal-strength differentiator tags
(`modalT`, `modalD`, `modalB`, `modalFour`, `modalFive`). -/
def kCore : Finset ModalSchemaTag :=
  insert .implyK <| insert .implyS <| insert .efq <| insert .peirce <| insert .modalK <|
    insert .andI <| insert .andE1 <| insert .andE2 <| insert .orI1 <| insert .orI2 <|
      insert .orE <| insert .diaDualityFwd <| insert .diaDualityBack ∅

/-! ## Sub-Phase 3.1: `kCore` + K, T, D, B -/

/-- System K's tag set: `kCore` alone — K has no differentiator beyond `modalK`, which is
already in `kCore`. -/
def kTags : Finset ModalSchemaTag := kCore

/-- System T's tag set: `kCore ∪ {modalT}` (reflexivity). -/
def tTags : Finset ModalSchemaTag := insert .modalT kCore

/-- System D's tag set: `kCore ∪ {modalD}` (seriality). -/
def dTags : Finset ModalSchemaTag := insert .modalD kCore

/-- System KB's tag set: `kCore ∪ {modalB}` (symmetry). -/
def bTags : Finset ModalSchemaTag := insert .modalB kCore

/-- Bridge: `SchemaUnion kTags φ ↔ KAxiom φ`. -/
theorem schemaUnion_kTags_iff_KAxiom {φ : Proposition Atom} :
    SchemaUnion kTags φ ↔ KAxiom φ := by
  constructor
  · intro h
    simp only [kTags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact KAxiom.implyK _ _
      | exact KAxiom.implyS _ _ _
      | exact KAxiom.efq _
      | exact KAxiom.peirce _ _
      | exact KAxiom.modalK _ _
      | exact KAxiom.andI _ _
      | exact KAxiom.andE1 _ _
      | exact KAxiom.andE2 _ _
      | exact KAxiom.orI1 _ _
      | exact KAxiom.orI2 _ _
      | exact KAxiom.orE _ _ _
      | exact KAxiom.diaDualityFwd _
      | exact KAxiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion tTags φ ↔ TAxiom φ`. -/
theorem schemaUnion_tTags_iff_TAxiom {φ : Proposition Atom} :
    SchemaUnion tTags φ ↔ TAxiom φ := by
  constructor
  · intro h
    simp only [tTags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact TAxiom.implyK _ _
      | exact TAxiom.implyS _ _ _
      | exact TAxiom.efq _
      | exact TAxiom.peirce _ _
      | exact TAxiom.modalK _ _
      | exact TAxiom.modalT _
      | exact TAxiom.andI _ _
      | exact TAxiom.andE1 _ _
      | exact TAxiom.andE2 _ _
      | exact TAxiom.orI1 _ _
      | exact TAxiom.orI2 _ _
      | exact TAxiom.orE _ _ _
      | exact TAxiom.diaDualityFwd _
      | exact TAxiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalT φ => exact ⟨.modalT, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion dTags φ ↔ DAxiom φ`. -/
theorem schemaUnion_dTags_iff_DAxiom {φ : Proposition Atom} :
    SchemaUnion dTags φ ↔ DAxiom φ := by
  constructor
  · intro h
    simp only [dTags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact DAxiom.implyK _ _
      | exact DAxiom.implyS _ _ _
      | exact DAxiom.efq _
      | exact DAxiom.peirce _ _
      | exact DAxiom.modalK _ _
      | exact DAxiom.modalD _
      | exact DAxiom.andI _ _
      | exact DAxiom.andE1 _ _
      | exact DAxiom.andE2 _ _
      | exact DAxiom.orI1 _ _
      | exact DAxiom.orI2 _ _
      | exact DAxiom.orE _ _ _
      | exact DAxiom.diaDualityFwd _
      | exact DAxiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalD φ => exact ⟨.modalD, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion bTags φ ↔ BAxiom φ`. -/
theorem schemaUnion_bTags_iff_BAxiom {φ : Proposition Atom} :
    SchemaUnion bTags φ ↔ BAxiom φ := by
  constructor
  · intro h
    simp only [bTags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact BAxiom.implyK _ _
      | exact BAxiom.implyS _ _ _
      | exact BAxiom.efq _
      | exact BAxiom.peirce _ _
      | exact BAxiom.modalK _ _
      | exact BAxiom.modalB _
      | exact BAxiom.andI _ _
      | exact BAxiom.andE1 _ _
      | exact BAxiom.andE2 _ _
      | exact BAxiom.orI1 _ _
      | exact BAxiom.orI2 _ _
      | exact BAxiom.orE _ _ _
      | exact BAxiom.diaDualityFwd _
      | exact BAxiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalB φ => exact ⟨.modalB, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-! ## Sub-Phase 3.2: K4, K5, K45, S4 -/

/-- System K4's tag set: `kCore ∪ {modalFour}` (transitivity). -/
def k4Tags : Finset ModalSchemaTag := insert .modalFour kCore

/-- System K5's tag set: `kCore ∪ {modalFive}` (Euclideanness). -/
def k5Tags : Finset ModalSchemaTag := insert .modalFive kCore

/-- System K45's tag set: `kCore ∪ {modalFour, modalFive}`. -/
def k45Tags : Finset ModalSchemaTag := insert .modalFour (insert .modalFive kCore)

/-- System S4's tag set: `kCore ∪ {modalT, modalFour}`. -/
def s4Tags : Finset ModalSchemaTag := insert .modalT (insert .modalFour kCore)

/-- Bridge: `SchemaUnion k4Tags φ ↔ K4Axiom φ`. -/
theorem schemaUnion_k4Tags_iff_K4Axiom {φ : Proposition Atom} :
    SchemaUnion k4Tags φ ↔ K4Axiom φ := by
  constructor
  · intro h
    simp only [k4Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact K4Axiom.implyK _ _
      | exact K4Axiom.implyS _ _ _
      | exact K4Axiom.efq _
      | exact K4Axiom.peirce _ _
      | exact K4Axiom.modalK _ _
      | exact K4Axiom.modalFour _
      | exact K4Axiom.andI _ _
      | exact K4Axiom.andE1 _ _
      | exact K4Axiom.andE2 _ _
      | exact K4Axiom.orI1 _ _
      | exact K4Axiom.orI2 _ _
      | exact K4Axiom.orE _ _ _
      | exact K4Axiom.diaDualityFwd _
      | exact K4Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalFour φ => exact ⟨.modalFour, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion k5Tags φ ↔ K5Axiom φ`. -/
theorem schemaUnion_k5Tags_iff_K5Axiom {φ : Proposition Atom} :
    SchemaUnion k5Tags φ ↔ K5Axiom φ := by
  constructor
  · intro h
    simp only [k5Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact K5Axiom.implyK _ _
      | exact K5Axiom.implyS _ _ _
      | exact K5Axiom.efq _
      | exact K5Axiom.peirce _ _
      | exact K5Axiom.modalK _ _
      | exact K5Axiom.modalFive _
      | exact K5Axiom.andI _ _
      | exact K5Axiom.andE1 _ _
      | exact K5Axiom.andE2 _ _
      | exact K5Axiom.orI1 _ _
      | exact K5Axiom.orI2 _ _
      | exact K5Axiom.orE _ _ _
      | exact K5Axiom.diaDualityFwd _
      | exact K5Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalFive φ => exact ⟨.modalFive, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion k45Tags φ ↔ K45Axiom φ`. -/
theorem schemaUnion_k45Tags_iff_K45Axiom {φ : Proposition Atom} :
    SchemaUnion k45Tags φ ↔ K45Axiom φ := by
  constructor
  · intro h
    simp only [k45Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact K45Axiom.implyK _ _
      | exact K45Axiom.implyS _ _ _
      | exact K45Axiom.efq _
      | exact K45Axiom.peirce _ _
      | exact K45Axiom.modalK _ _
      | exact K45Axiom.modalFour _
      | exact K45Axiom.modalFive _
      | exact K45Axiom.andI _ _
      | exact K45Axiom.andE1 _ _
      | exact K45Axiom.andE2 _ _
      | exact K45Axiom.orI1 _ _
      | exact K45Axiom.orI2 _ _
      | exact K45Axiom.orE _ _ _
      | exact K45Axiom.diaDualityFwd _
      | exact K45Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalFour φ => exact ⟨.modalFour, by decide, φ, rfl⟩
    | modalFive φ => exact ⟨.modalFive, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion s4Tags φ ↔ S4Axiom φ`. -/
theorem schemaUnion_s4Tags_iff_S4Axiom {φ : Proposition Atom} :
    SchemaUnion s4Tags φ ↔ S4Axiom φ := by
  constructor
  · intro h
    simp only [s4Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact S4Axiom.implyK _ _
      | exact S4Axiom.implyS _ _ _
      | exact S4Axiom.efq _
      | exact S4Axiom.peirce _ _
      | exact S4Axiom.modalK _ _
      | exact S4Axiom.modalT _
      | exact S4Axiom.modalFour _
      | exact S4Axiom.andI _ _
      | exact S4Axiom.andE1 _ _
      | exact S4Axiom.andE2 _ _
      | exact S4Axiom.orI1 _ _
      | exact S4Axiom.orI2 _ _
      | exact S4Axiom.orE _ _ _
      | exact S4Axiom.diaDualityFwd _
      | exact S4Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalT φ => exact ⟨.modalT, by decide, φ, rfl⟩
    | modalFour φ => exact ⟨.modalFour, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-! ## Sub-Phase 3.3: S5, TB, KB5 -/

/-- System S5's tag set: `kCore ∪ {modalT, modalFour, modalB}` (S5 = T + 4 + B; carries
`modalB`, NOT `modalFive` — the deliberately-omitted `KB5 → S5` subsumption edge follows from
this, per the resolved design decision). -/
def s5Tags : Finset ModalSchemaTag :=
  insert .modalT (insert .modalFour (insert .modalB kCore))

/-- System TB's tag set: `kCore ∪ {modalT, modalB}`. -/
def tbTags : Finset ModalSchemaTag := insert .modalT (insert .modalB kCore)

/-- System KB5's tag set: `kCore ∪ {modalB, modalFive}`. -/
def kb5Tags : Finset ModalSchemaTag := insert .modalB (insert .modalFive kCore)

/-- Bridge: `SchemaUnion s5Tags φ ↔ ModalAxiom φ` (S5 = T+4+B; generalizes S5's pre-existing
`ModalAxiom` inductive toward the schema-union combinator, per the resolved design decision). -/
theorem schemaUnion_s5Tags_iff_ModalAxiom {φ : Proposition Atom} :
    SchemaUnion s5Tags φ ↔ ModalAxiom φ := by
  constructor
  · intro h
    simp only [s5Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ |
      ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact ModalAxiom.implyK _ _
      | exact ModalAxiom.implyS _ _ _
      | exact ModalAxiom.efq _
      | exact ModalAxiom.peirce _ _
      | exact ModalAxiom.modalK _ _
      | exact ModalAxiom.modalT _
      | exact ModalAxiom.modalFour _
      | exact ModalAxiom.modalB _
      | exact ModalAxiom.andI _ _
      | exact ModalAxiom.andE1 _ _
      | exact ModalAxiom.andE2 _ _
      | exact ModalAxiom.orI1 _ _
      | exact ModalAxiom.orI2 _ _
      | exact ModalAxiom.orE _ _ _
      | exact ModalAxiom.diaDualityFwd _
      | exact ModalAxiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalT φ => exact ⟨.modalT, by decide, φ, rfl⟩
    | modalFour φ => exact ⟨.modalFour, by decide, φ, rfl⟩
    | modalB φ => exact ⟨.modalB, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion tbTags φ ↔ TBAxiom φ`. -/
theorem schemaUnion_tbTags_iff_TBAxiom {φ : Proposition Atom} :
    SchemaUnion tbTags φ ↔ TBAxiom φ := by
  constructor
  · intro h
    simp only [tbTags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact TBAxiom.implyK _ _
      | exact TBAxiom.implyS _ _ _
      | exact TBAxiom.efq _
      | exact TBAxiom.peirce _ _
      | exact TBAxiom.modalK _ _
      | exact TBAxiom.modalT _
      | exact TBAxiom.modalB _
      | exact TBAxiom.andI _ _
      | exact TBAxiom.andE1 _ _
      | exact TBAxiom.andE2 _ _
      | exact TBAxiom.orI1 _ _
      | exact TBAxiom.orI2 _ _
      | exact TBAxiom.orE _ _ _
      | exact TBAxiom.diaDualityFwd _
      | exact TBAxiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalT φ => exact ⟨.modalT, by decide, φ, rfl⟩
    | modalB φ => exact ⟨.modalB, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion kb5Tags φ ↔ KB5Axiom φ`. -/
theorem schemaUnion_kb5Tags_iff_KB5Axiom {φ : Proposition Atom} :
    SchemaUnion kb5Tags φ ↔ KB5Axiom φ := by
  constructor
  · intro h
    simp only [kb5Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact KB5Axiom.implyK _ _
      | exact KB5Axiom.implyS _ _ _
      | exact KB5Axiom.efq _
      | exact KB5Axiom.peirce _ _
      | exact KB5Axiom.modalK _ _
      | exact KB5Axiom.modalB _
      | exact KB5Axiom.modalFive _
      | exact KB5Axiom.andI _ _
      | exact KB5Axiom.andE1 _ _
      | exact KB5Axiom.andE2 _ _
      | exact KB5Axiom.orI1 _ _
      | exact KB5Axiom.orI2 _ _
      | exact KB5Axiom.orE _ _ _
      | exact KB5Axiom.diaDualityFwd _
      | exact KB5Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalB φ => exact ⟨.modalB, by decide, φ, rfl⟩
    | modalFive φ => exact ⟨.modalFive, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

end Cslib.Logic.Modal
