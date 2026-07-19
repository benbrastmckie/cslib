/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.SchemaUnion

/-! # Schema Tag Sets: `kCore` and the 15 Per-System Tag Sets

This module defines `kCore` (the 13-tag shared propositional + K + and/or + diamond-duality
core) and the 15 per-system `Finset ModalSchemaTag` tag sets used to redefine each of the 15
classical normal modal systems' axiom predicates as a `SchemaUnion` instance
(`Cslib.Logics.Modal.ProofSystem.SchemaUnion`).

## Why This Foundational File Exists (Import-Cycle Architecture Note)

`SchemaBridges.lean` imports the `Instances` barrel (to state and prove the bridge equivalences
`SchemaUnion sysTags φ ↔ <Sys>Axiom φ` against the pre-existing per-system inductives), so
`Instances/*.lean` files cannot import `SchemaBridges.lean` without an import cycle (confirmed
via a direct `lake build` attempt in Phase 7: `bad import 'Cslib.Logics.Modal.ProofSystem.
Instances'`). Since the per-system tag sets are needed *inside* `Instances/*.lean` (Phase 8
redefines each `<Sys>Axiom` in place as `SchemaUnion sysTags`), the tag sets must live in a
foundational file that imports only `SchemaUnion.lean` -- this file. `SchemaBridges.lean` is
updated (this sub-phase) to import from here instead of defining these tag sets itself; its
bridge proofs are untouched and stay green.

The tag sets belong at the foundation anyway: a system's tag set is its essence (which schemata
it admits), not scaffolding built on top of the system.

## Main Definitions

- `kCore`: the 13 shared tags (`implyK, implyS, efq, peirce, modalK, andI, andE1, andE2, orI1,
  orI2, orE, diaDualityFwd, diaDualityBack`).
- `kTags, tTags, dTags, bTags, k4Tags, k5Tags, k45Tags, s4Tags, s5Tags, tbTags, kb5Tags, d4Tags,
  d5Tags, d45Tags, dbTags`: the 15 per-system tag sets, each `kCore` unioned with that system's
  modal-strength differentiator tag(s) (`K` has none beyond `modalK`, already in `kCore`).

## References

* Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean -- `ModalSchemaTag`, `SchemaUnion`, elim. API
* Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean -- bridge equivalences using these tag sets
* Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,...}.lean -- the 15 per-system axiom
  inductives (redefined in terms of these tag sets, Phase 8)
-/

@[expose] public section

namespace Cslib.Logic.Modal

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

/-! ## Per-System Tag Sets -/

/-- System K's tag set: `kCore` alone -- K has no differentiator beyond `modalK`, which is
already in `kCore`. -/
def kTags : Finset ModalSchemaTag := kCore

/-- System T's tag set: `kCore ∪ {modalT}` (reflexivity). -/
def tTags : Finset ModalSchemaTag := insert .modalT kCore

/-- System D's tag set: `kCore ∪ {modalD}` (seriality). -/
def dTags : Finset ModalSchemaTag := insert .modalD kCore

/-- System KB's tag set: `kCore ∪ {modalB}` (symmetry). -/
def bTags : Finset ModalSchemaTag := insert .modalB kCore

/-- System K4's tag set: `kCore ∪ {modalFour}` (transitivity). -/
def k4Tags : Finset ModalSchemaTag := insert .modalFour kCore

/-- System K5's tag set: `kCore ∪ {modalFive}` (Euclideanness). -/
def k5Tags : Finset ModalSchemaTag := insert .modalFive kCore

/-- System K45's tag set: `kCore ∪ {modalFour, modalFive}`. -/
def k45Tags : Finset ModalSchemaTag := insert .modalFour (insert .modalFive kCore)

/-- System S4's tag set: `kCore ∪ {modalT, modalFour}`. -/
def s4Tags : Finset ModalSchemaTag := insert .modalT (insert .modalFour kCore)

/-- System S5's tag set: `kCore ∪ {modalT, modalFour, modalB}` (S5 = T + 4 + B; carries
`modalB`, NOT `modalFive` -- the deliberately-omitted `KB5 → S5` subsumption edge follows from
this, per the resolved design decision). -/
def s5Tags : Finset ModalSchemaTag :=
  insert .modalT (insert .modalFour (insert .modalB kCore))

/-- System TB's tag set: `kCore ∪ {modalT, modalB}`. -/
def tbTags : Finset ModalSchemaTag := insert .modalT (insert .modalB kCore)

/-- System KB5's tag set: `kCore ∪ {modalB, modalFive}`. -/
def kb5Tags : Finset ModalSchemaTag := insert .modalB (insert .modalFive kCore)

/-- System D4's tag set: `kCore ∪ {modalD, modalFour}`. -/
def d4Tags : Finset ModalSchemaTag := insert .modalD (insert .modalFour kCore)

/-- System D5's tag set: `kCore ∪ {modalD, modalFive}`. -/
def d5Tags : Finset ModalSchemaTag := insert .modalD (insert .modalFive kCore)

/-- System D45's tag set: `kCore ∪ {modalD, modalFour, modalFive}`. -/
def d45Tags : Finset ModalSchemaTag :=
  insert .modalD (insert .modalFour (insert .modalFive kCore))

/-- System DB's tag set: `kCore ∪ {modalD, modalB}`. -/
def dbTags : Finset ModalSchemaTag := insert .modalD (insert .modalB kCore)

end Cslib.Logic.Modal
