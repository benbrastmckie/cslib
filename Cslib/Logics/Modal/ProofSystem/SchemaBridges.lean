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

end Cslib.Logic.Modal
