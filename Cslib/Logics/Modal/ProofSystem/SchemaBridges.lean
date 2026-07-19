/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.SchemaUnion
public import Cslib.Logics.Modal.ProofSystem.SchemaTags
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Schema-Union Bridges: Bridge Equivalences

This module proves the bridge equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` connecting
the schema-union combinator (`Cslib.Logics.Modal.ProofSystem.SchemaUnion`) to each of the 15
pre-existing per-system axiom inductives (`KAxiom`, …, and S5's `ModalAxiom`), using the tag
sets defined in `Cslib.Logics.Modal.ProofSystem.SchemaTags`.

This is purely additive (Phase 3 of the schema-union rollout): none of the 15 instance files,
`SchemaUnion.lean`, or `DerivationTree.lean` is modified. The inductives stay live until
Phase 8.

## Import-Cycle Note (Phase 8 sub-phase 8.1)

`kCore` and the 15 per-system tag sets used to live in this file, but were relocated to
`SchemaTags.lean` (a foundational file importing only `SchemaUnion.lean`) because
`Instances/*.lean` files need the tag sets (to redefine each `<Sys>Axiom` as `SchemaUnion
sysTags`, Phase 8 sub-phase 8.2) but cannot import this file -- this file imports the
`Instances` barrel, so `Instances/*.lean` importing it back would be a cycle. This is a pure
move: the bridge proofs below are unchanged, only the tag-set definitions moved out.

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

/-! ## Sub-Phase 3.1: `kCore` + K, T, D, B -/

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

/-! ## Sub-Phase 3.4: D4, D5, D45, DB -/

/-- Bridge: `SchemaUnion d4Tags φ ↔ D4Axiom φ`. -/
theorem schemaUnion_d4Tags_iff_D4Axiom {φ : Proposition Atom} :
    SchemaUnion d4Tags φ ↔ D4Axiom φ := by
  constructor
  · intro h
    simp only [d4Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact D4Axiom.implyK _ _
      | exact D4Axiom.implyS _ _ _
      | exact D4Axiom.efq _
      | exact D4Axiom.peirce _ _
      | exact D4Axiom.modalK _ _
      | exact D4Axiom.modalD _
      | exact D4Axiom.modalFour _
      | exact D4Axiom.andI _ _
      | exact D4Axiom.andE1 _ _
      | exact D4Axiom.andE2 _ _
      | exact D4Axiom.orI1 _ _
      | exact D4Axiom.orI2 _ _
      | exact D4Axiom.orE _ _ _
      | exact D4Axiom.diaDualityFwd _
      | exact D4Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalD φ => exact ⟨.modalD, by decide, φ, rfl⟩
    | modalFour φ => exact ⟨.modalFour, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion d5Tags φ ↔ D5Axiom φ`. -/
theorem schemaUnion_d5Tags_iff_D5Axiom {φ : Proposition Atom} :
    SchemaUnion d5Tags φ ↔ D5Axiom φ := by
  constructor
  · intro h
    simp only [d5Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact D5Axiom.implyK _ _
      | exact D5Axiom.implyS _ _ _
      | exact D5Axiom.efq _
      | exact D5Axiom.peirce _ _
      | exact D5Axiom.modalK _ _
      | exact D5Axiom.modalD _
      | exact D5Axiom.modalFive _
      | exact D5Axiom.andI _ _
      | exact D5Axiom.andE1 _ _
      | exact D5Axiom.andE2 _ _
      | exact D5Axiom.orI1 _ _
      | exact D5Axiom.orI2 _ _
      | exact D5Axiom.orE _ _ _
      | exact D5Axiom.diaDualityFwd _
      | exact D5Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalD φ => exact ⟨.modalD, by decide, φ, rfl⟩
    | modalFive φ => exact ⟨.modalFive, by decide, φ, rfl⟩
    | andI φ ψ => exact ⟨.andI, by decide, φ, ψ, rfl⟩
    | andE1 φ ψ => exact ⟨.andE1, by decide, φ, ψ, rfl⟩
    | andE2 φ ψ => exact ⟨.andE2, by decide, φ, ψ, rfl⟩
    | orI1 φ ψ => exact ⟨.orI1, by decide, φ, ψ, rfl⟩
    | orI2 φ ψ => exact ⟨.orI2, by decide, φ, ψ, rfl⟩
    | orE φ ψ χ => exact ⟨.orE, by decide, φ, ψ, χ, rfl⟩
    | diaDualityFwd φ => exact ⟨.diaDualityFwd, by decide, φ, rfl⟩
    | diaDualityBack φ => exact ⟨.diaDualityBack, by decide, φ, rfl⟩

/-- Bridge: `SchemaUnion d45Tags φ ↔ D45Axiom φ`. -/
theorem schemaUnion_d45Tags_iff_D45Axiom {φ : Proposition Atom} :
    SchemaUnion d45Tags φ ↔ D45Axiom φ := by
  constructor
  · intro h
    simp only [d45Tags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ |
      ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact D45Axiom.implyK _ _
      | exact D45Axiom.implyS _ _ _
      | exact D45Axiom.efq _
      | exact D45Axiom.peirce _ _
      | exact D45Axiom.modalK _ _
      | exact D45Axiom.modalD _
      | exact D45Axiom.modalFour _
      | exact D45Axiom.modalFive _
      | exact D45Axiom.andI _ _
      | exact D45Axiom.andE1 _ _
      | exact D45Axiom.andE2 _ _
      | exact D45Axiom.orI1 _ _
      | exact D45Axiom.orI2 _ _
      | exact D45Axiom.orE _ _ _
      | exact D45Axiom.diaDualityFwd _
      | exact D45Axiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalD φ => exact ⟨.modalD, by decide, φ, rfl⟩
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

/-- Bridge: `SchemaUnion dbTags φ ↔ DBAxiom φ`. -/
theorem schemaUnion_dbTags_iff_DBAxiom {φ : Proposition Atom} :
    SchemaUnion dbTags φ ↔ DBAxiom φ := by
  constructor
  · intro h
    simp only [dbTags, kCore, SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false,
      ModalSchemaTag.Holds] at h
    rcases h with ⟨φ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ |
      ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', rfl⟩ | ⟨φ', ψ', χ', rfl⟩ | ⟨φ', rfl⟩ | ⟨φ', rfl⟩
    all_goals first
      | exact DBAxiom.implyK _ _
      | exact DBAxiom.implyS _ _ _
      | exact DBAxiom.efq _
      | exact DBAxiom.peirce _ _
      | exact DBAxiom.modalK _ _
      | exact DBAxiom.modalD _
      | exact DBAxiom.modalB _
      | exact DBAxiom.andI _ _
      | exact DBAxiom.andE1 _ _
      | exact DBAxiom.andE2 _ _
      | exact DBAxiom.orI1 _ _
      | exact DBAxiom.orI2 _ _
      | exact DBAxiom.orE _ _ _
      | exact DBAxiom.diaDualityFwd _
      | exact DBAxiom.diaDualityBack _
  · intro h
    cases h with
    | implyK φ ψ => exact ⟨.implyK, by decide, φ, ψ, rfl⟩
    | implyS φ ψ χ => exact ⟨.implyS, by decide, φ, ψ, χ, rfl⟩
    | efq φ => exact ⟨.efq, by decide, φ, rfl⟩
    | peirce φ ψ => exact ⟨.peirce, by decide, φ, ψ, rfl⟩
    | modalK φ ψ => exact ⟨.modalK, by decide, φ, ψ, rfl⟩
    | modalD φ => exact ⟨.modalD, by decide, φ, rfl⟩
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
