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

The now-deleted `SchemaBridges.lean` (transitional scaffolding, removed once its bridge
equivalences became identities with no remaining users) imported the `Instances` barrel, so
`Instances/*.lean` files could not import it without an import cycle (confirmed via a direct
`lake build` attempt: `bad import 'Cslib.Logics.Modal.ProofSystem.Instances'`). Since the
per-system tag sets are needed *inside* `Instances/*.lean` (each `<Sys>Axiom` is redefined in
place as `SchemaUnion sysTags`), the tag sets live in this foundational file, which imports only
`SchemaUnion.lean`.

The tag sets belong at the foundation anyway: a system's tag set is its essence (which schemata
it admits), not scaffolding built on top of the system.

## Main Definitions

- `kCore`: the 13 shared tags (`implyK, implyS, efq, peirce, modalK, andI, andE1, andE2, orI1,
  orI2, orE, diamondDualityFwd, diamondDualityBack`).
- `kTags, tTags, dTags, bTags, k4Tags, k5Tags, k45Tags, s4Tags, s5Tags, tbTags, kb5Tags, d4Tags,
  d5Tags, d45Tags, dbTags`: the 15 per-system tag sets, each `kCore` unioned with that system's
  modal-strength differentiator tag(s) (`K` has none beyond `modalK`, already in `kCore`).

## References

* Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean -- `ModalSchemaTag`, `SchemaUnion`, elim. API
* Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,...}.lean -- the 15 per-system axiom
  predicates (`abbrev <Sys>Axiom := SchemaUnion sysTags`)
-/

@[expose] public section

namespace Cslib.Logic.Modal

/-! ## Shared Core Tag Set -/

/-- The 13 shared tags: propositional (`implyK`, `implyS`, `efq`, `peirce`), K distribution
(`modalK`), and the and/or/diamond-duality characterization tags (`andI`, `andE1`, `andE2`,
`orI1`, `orI2`, `orE`, `diamondDualityFwd`, `diamondDualityBack`). Every one of the 15 classical normal
modal systems is `kCore` unioned with a subset of the 5 modal-strength differentiator tags
(`modalT`, `modalD`, `modalB`, `modalFour`, `modalFive`). -/
def kCore : Finset ModalSchemaTag :=
  insert .implyK <| insert .implyS <| insert .efq <| insert .peirce <| insert .modalK <|
    insert .andI <| insert .andE1 <| insert .andE2 <| insert .orI1 <| insert .orI2 <|
      insert .orE <| insert .diamondDualityFwd <| insert .diamondDualityBack ∅

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

/-! ## Generic Per-Core-Tag Witness Helpers

Thin one-liners over `SchemaUnion.subsumption`, one per `kCore` tag. Given
`h : kCore ⊆ S` for any per-system tag set `S`, each helper produces the corresponding
axiom-schema witness for `SchemaUnion S` -- collapsing what used to be 13 copy-pasted
`⟨.tag, by decide, …, rfl⟩` witness terms per call site (432 across the 15 systems' truth
lemma applications, strong-completeness, and compactness invocations) down to a single
`(by decide : kCore ⊆ S)` subset fact shared by all 13. Named without the originally-proposed
`_of` suffix (`implyKOf`, …) since `defsWithUnderscore` flags underscores in declaration
names; `holds*` reads naturally as "S holds the *-schema witness". -/

variable {Atom : Type u}

/-- `SchemaUnion S` holds the `implyK` witness `φ → (ψ → φ)` whenever `kCore ⊆ S`. -/
theorem holdsImplyK {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) : SchemaUnion S (φ.imp (ψ.imp φ)) :=
  SchemaUnion.subsumption h ⟨.implyK, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `implyS` witness (distribution) whenever `kCore ⊆ S`. -/
theorem holdsImplyS {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ χ : Proposition Atom) :
    SchemaUnion S ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  SchemaUnion.subsumption h ⟨.implyS, by decide, φ, ψ, χ, rfl⟩

/-- `SchemaUnion S` holds the `efq` witness `⊥ → φ` whenever `kCore ⊆ S`. -/
theorem holdsEfq {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ : Proposition Atom) : SchemaUnion S (Proposition.bot.imp φ) :=
  SchemaUnion.subsumption h ⟨.efq, by decide, φ, rfl⟩

/-- `SchemaUnion S` holds the `peirce` witness `((φ → ψ) → φ) → φ` whenever `kCore ⊆ S`. -/
theorem holdsPeirce {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) : SchemaUnion S (((φ.imp ψ).imp φ).imp φ) :=
  SchemaUnion.subsumption h ⟨.peirce, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `modalK` witness `□(φ → ψ) → (□φ → □ψ)` whenever `kCore ⊆ S`. -/
theorem holdsModalK {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) :
    SchemaUnion S ((Proposition.box (φ.imp ψ)).imp
      ((Proposition.box φ).imp (Proposition.box ψ))) :=
  SchemaUnion.subsumption h ⟨.modalK, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `andI` witness whenever `kCore ⊆ S`. -/
theorem holdsAndI {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.AndI φ ψ) :=
  SchemaUnion.subsumption h ⟨.andI, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `andE1` witness whenever `kCore ⊆ S`. -/
theorem holdsAndE1 {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.AndE1 φ ψ) :=
  SchemaUnion.subsumption h ⟨.andE1, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `andE2` witness whenever `kCore ⊆ S`. -/
theorem holdsAndE2 {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.AndE2 φ ψ) :=
  SchemaUnion.subsumption h ⟨.andE2, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `orI1` witness whenever `kCore ⊆ S`. -/
theorem holdsOrI1 {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.OrI1 φ ψ) :=
  SchemaUnion.subsumption h ⟨.orI1, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `orI2` witness whenever `kCore ⊆ S`. -/
theorem holdsOrI2 {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.OrI2 φ ψ) :=
  SchemaUnion.subsumption h ⟨.orI2, by decide, φ, ψ, rfl⟩

/-- `SchemaUnion S` holds the `orE` witness whenever `kCore ⊆ S`. -/
theorem holdsOrE {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ ψ χ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.OrE φ ψ χ) :=
  SchemaUnion.subsumption h ⟨.orE, by decide, φ, ψ, χ, rfl⟩

/-- `SchemaUnion S` holds the `diamondDualityFwd` witness whenever `kCore ⊆ S`. -/
theorem holdsDiaDualityFwd {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.AxiomDiamondDualityFwd φ) :=
  SchemaUnion.subsumption h ⟨.diamondDualityFwd, by decide, φ, rfl⟩

/-- `SchemaUnion S` holds the `diamondDualityBack` witness whenever `kCore ⊆ S`. -/
theorem holdsDiaDualityBack {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (φ : Proposition Atom) : SchemaUnion S (Cslib.Logic.Axioms.AxiomDiamondDualityBack φ) :=
  SchemaUnion.subsumption h ⟨.diamondDualityBack, by decide, φ, rfl⟩

end Cslib.Logic.Modal
