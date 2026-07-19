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

/-- Bridge: `SchemaUnion kTags φ ↔ KAxiom φ`. Trivial post-8.3: `KAxiom` is now definitionally
`SchemaUnion kTags` (redefined in `Instances/K.lean`), so the two sides are the same predicate. -/
theorem schemaUnion_kTags_iff_KAxiom {φ : Proposition Atom} :
    SchemaUnion kTags φ ↔ KAxiom φ := Iff.rfl

/-- Bridge: `SchemaUnion tTags φ ↔ TAxiom φ`. Trivial post-8.3: `TAxiom` is now definitionally
`SchemaUnion tTags` (redefined in `Instances/T.lean`), so the two sides are the same predicate. -/
theorem schemaUnion_tTags_iff_TAxiom {φ : Proposition Atom} :
    SchemaUnion tTags φ ↔ TAxiom φ := Iff.rfl

/-- Bridge: `SchemaUnion dTags φ ↔ DAxiom φ`. Trivial post-8.3: `DAxiom` is now definitionally
`SchemaUnion dTags` (redefined in `Instances/D.lean`), so the two sides are the same predicate. -/
theorem schemaUnion_dTags_iff_DAxiom {φ : Proposition Atom} :
    SchemaUnion dTags φ ↔ DAxiom φ := Iff.rfl

/-- Bridge: `SchemaUnion bTags φ ↔ BAxiom φ`. Trivial post-8.3: `BAxiom` is now definitionally
`SchemaUnion bTags` (redefined in `Instances/B.lean`), so the two sides are the same predicate. -/
theorem schemaUnion_bTags_iff_BAxiom {φ : Proposition Atom} :
    SchemaUnion bTags φ ↔ BAxiom φ := Iff.rfl

/-! ## Sub-Phase 3.2: K4, K5, K45, S4 -/

/-- Bridge: `SchemaUnion k4Tags φ ↔ K4Axiom φ`. Trivial post-8.3: `K4Axiom` is now definitionally
`SchemaUnion k4Tags` (redefined in `Instances/K4.lean`), so the two sides are the same
predicate. -/
theorem schemaUnion_k4Tags_iff_K4Axiom {φ : Proposition Atom} :
    SchemaUnion k4Tags φ ↔ K4Axiom φ := Iff.rfl

/-- Bridge: `SchemaUnion k5Tags φ ↔ K5Axiom φ`. Trivial post-8.3: `K5Axiom` is now definitionally
`SchemaUnion k5Tags` (redefined in `Instances/K5.lean`), so the two sides are the same
predicate. -/
theorem schemaUnion_k5Tags_iff_K5Axiom {φ : Proposition Atom} :
    SchemaUnion k5Tags φ ↔ K5Axiom φ := Iff.rfl

/-- Bridge: `SchemaUnion k45Tags φ ↔ K45Axiom φ`. Trivial post-8.3: `K45Axiom` is now
definitionally `SchemaUnion k45Tags` (redefined in `Instances/K45.lean`), so the two sides are
the same predicate. -/
theorem schemaUnion_k45Tags_iff_K45Axiom {φ : Proposition Atom} :
    SchemaUnion k45Tags φ ↔ K45Axiom φ := Iff.rfl

/-- Bridge: `SchemaUnion s4Tags φ ↔ S4Axiom φ`. Trivial post-8.3: `S4Axiom` is now definitionally
`SchemaUnion s4Tags` (redefined in `Instances/S4.lean`), so the two sides are the same
predicate. -/
theorem schemaUnion_s4Tags_iff_S4Axiom {φ : Proposition Atom} :
    SchemaUnion s4Tags φ ↔ S4Axiom φ := Iff.rfl

/-! ## Sub-Phase 3.3: S5, TB, KB5 -/

/-- Bridge: `SchemaUnion s5Tags φ ↔ ModalAxiom φ` (S5 = T+4+B). Trivial post-8.3: `ModalAxiom` is
now definitionally `SchemaUnion s5Tags` (redefined in `Metalogic/DerivationTree.lean`), so the
two sides are the same predicate. -/
theorem schemaUnion_s5Tags_iff_ModalAxiom {φ : Proposition Atom} :
    SchemaUnion s5Tags φ ↔ ModalAxiom φ := Iff.rfl

/-- Bridge: `SchemaUnion tbTags φ ↔ TBAxiom φ`. Trivial post-8.3: `TBAxiom` is now definitionally
`SchemaUnion tbTags` (redefined in `Instances/TB.lean`), so the two sides are the same
predicate. -/
theorem schemaUnion_tbTags_iff_TBAxiom {φ : Proposition Atom} :
    SchemaUnion tbTags φ ↔ TBAxiom φ := Iff.rfl

/-- Bridge: `SchemaUnion kb5Tags φ ↔ KB5Axiom φ`. Trivial post-8.3: `KB5Axiom` is now
definitionally `SchemaUnion kb5Tags` (redefined in `Instances/KB5.lean`), so the two sides are
the same predicate. -/
theorem schemaUnion_kb5Tags_iff_KB5Axiom {φ : Proposition Atom} :
    SchemaUnion kb5Tags φ ↔ KB5Axiom φ := Iff.rfl

/-! ## Sub-Phase 3.4: D4, D5, D45, DB -/

/-- Bridge: `SchemaUnion d4Tags φ ↔ D4Axiom φ`. Trivial post-8.3: `D4Axiom` is now definitionally
`SchemaUnion d4Tags` (redefined in `Instances/D4.lean`), so the two sides are the same
predicate. -/
theorem schemaUnion_d4Tags_iff_D4Axiom {φ : Proposition Atom} :
    SchemaUnion d4Tags φ ↔ D4Axiom φ := Iff.rfl

/-- Bridge: `SchemaUnion d5Tags φ ↔ D5Axiom φ`. Trivial post-8.3: `D5Axiom` is now definitionally
`SchemaUnion d5Tags` (redefined in `Instances/D5.lean`), so the two sides are the same
predicate. -/
theorem schemaUnion_d5Tags_iff_D5Axiom {φ : Proposition Atom} :
    SchemaUnion d5Tags φ ↔ D5Axiom φ := Iff.rfl

/-- Bridge: `SchemaUnion d45Tags φ ↔ D45Axiom φ`. Trivial post-8.3: `D45Axiom` is now
definitionally `SchemaUnion d45Tags` (redefined in `Instances/D45.lean`), so the two sides are
the same predicate. -/
theorem schemaUnion_d45Tags_iff_D45Axiom {φ : Proposition Atom} :
    SchemaUnion d45Tags φ ↔ D45Axiom φ := Iff.rfl

/-- Bridge: `SchemaUnion dbTags φ ↔ DBAxiom φ`. Trivial post-8.3: `DBAxiom` is now definitionally
`SchemaUnion dbTags` (redefined in `Instances/DB.lean`), so the two sides are the same
predicate. -/
theorem schemaUnion_dbTags_iff_DBAxiom {φ : Proposition Atom} :
    SchemaUnion dbTags φ ↔ DBAxiom φ := Iff.rfl

end Cslib.Logic.Modal
