/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.Instances
public import Cslib.Logics.Modal.ProofSystem.SchemaUnion
public import Cslib.Logics.Modal.ProofSystem.SchemaBridges

/-! # Axiom Subsumption Lemmas for the Modal Cube

This module proves all 24 direct-edge axiom subsumption lemmas for the modal cube,
establishing that each weaker system's axiom predicate implies the corresponding
stronger system's axiom predicate. These lemmas are the foundational building blocks
for the derivability monotonicity theorems in `Conservativity.lean`.

## Structure (schema-union rollout, Phase 5)

Each lemma has the form `XAxiom_implies_YAxiom : XAxiom φ → YAxiom φ`, where X is
the weaker system and Y is the stronger system. Every proof now routes uniformly through
the single generic `SchemaUnion.subsumption` lemma
(`Cslib.Logics.Modal.ProofSystem.SchemaUnion`): convert `XAxiom φ` to `SchemaUnion xTags φ`
via the Phase-3 bridge (`Cslib.Logics.Modal.ProofSystem.SchemaBridges`), apply
`SchemaUnion.subsumption` with `xTags ⊆ yTags` discharged by `decide` (the tag sets are
concrete `Finset`s), then convert back to `YAxiom φ` via the target bridge. No hand-written
per-edge `match`/`cases` on constructors remains — the modal cube IS the `⊆`-order on
per-system tag sets (design invariant 1 of the schema-union rollout), and each subsumption
edge is a `decide`-able `Finset.subset` fact. Every public lemma name is preserved verbatim.

## Direct Edges Covered (24 edges)

**From K (weakest)**:
- K → T, K → D, K → B (KB), K → K4, K → K5

**From D**:
- D → D4, D → D5, D → DB

**From T**:
- T → S4, T → TB

**From B (KB)**:
- B → TB, B → DB, B → KB5

**From K4**:
- K4 → S4, K4 → D4, K4 → K45

**From K5**:
- K5 → D5, K5 → K45, K5 → KB5

**From K45**:
- K45 → D45

**From D4**:
- D4 → D45

**From D5**:
- D5 → D45

**Into S5 (top-level)**:
- S4 → S5, TB → S5

Note: The edge KB5 → S5 is omitted because `kb5Tags` (`kCore ∪ {modalB, modalFive}`) is not a
subset of `s5Tags` (`kCore ∪ {modalT, modalFour, modalB}`) — S5 = T+4+B and carries `modalB`,
NOT `modalFive` (task 523's resolved design decision). The `decide`-able `Finset.subset` fact
this rollout is built on makes the omission mechanically evident: no `hsub : kb5Tags ⊆ s5Tags`
proof exists, since `modalFive ∈ kb5Tags` but `modalFive ∉ s5Tags`.

## References

* `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` -- `SchemaUnion.subsumption` (the generic
  lemma every edge below routes through)
* `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean` -- the 15 per-system tag sets and bridge
  equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ`
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## K-Based Edges -/

/-- K axioms are subsumed by T axioms: every K-axiom instance is a T-axiom instance. -/
lemma KAxiom_implies_TAxiom {φ : Proposition Atom} (h : KAxiom φ) : TAxiom φ :=
  schemaUnion_tTags_iff_TAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_kTags_iff_KAxiom.mpr h))

/-- K axioms are subsumed by D axioms: every K-axiom instance is a D-axiom instance. -/
lemma KAxiom_implies_DAxiom {φ : Proposition Atom} (h : KAxiom φ) : DAxiom φ :=
  schemaUnion_dTags_iff_DAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_kTags_iff_KAxiom.mpr h))

/-- K axioms are subsumed by B (KB) axioms: every K-axiom instance is a B-axiom instance. -/
lemma KAxiom_implies_BAxiom {φ : Proposition Atom} (h : KAxiom φ) : BAxiom φ :=
  schemaUnion_bTags_iff_BAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_kTags_iff_KAxiom.mpr h))

/-- K axioms are subsumed by K4 axioms: every K-axiom instance is a K4-axiom instance. -/
lemma KAxiom_implies_K4Axiom {φ : Proposition Atom} (h : KAxiom φ) : K4Axiom φ :=
  schemaUnion_k4Tags_iff_K4Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_kTags_iff_KAxiom.mpr h))

/-- K axioms are subsumed by K5 axioms: every K-axiom instance is a K5-axiom instance. -/
lemma KAxiom_implies_K5Axiom {φ : Proposition Atom} (h : KAxiom φ) : K5Axiom φ :=
  schemaUnion_k5Tags_iff_K5Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_kTags_iff_KAxiom.mpr h))

/-! ## D-Based Edges -/

/-- D axioms are subsumed by D4 axioms: every D-axiom instance is a D4-axiom instance. -/
lemma DAxiom_implies_D4Axiom {φ : Proposition Atom} (h : DAxiom φ) : D4Axiom φ :=
  schemaUnion_d4Tags_iff_D4Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_dTags_iff_DAxiom.mpr h))

/-- D axioms are subsumed by D5 axioms: every D-axiom instance is a D5-axiom instance. -/
lemma DAxiom_implies_D5Axiom {φ : Proposition Atom} (h : DAxiom φ) : D5Axiom φ :=
  schemaUnion_d5Tags_iff_D5Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_dTags_iff_DAxiom.mpr h))

/-- D axioms are subsumed by DB axioms: every D-axiom instance is a DB-axiom instance. -/
lemma DAxiom_implies_DBAxiom {φ : Proposition Atom} (h : DAxiom φ) : DBAxiom φ :=
  schemaUnion_dbTags_iff_DBAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_dTags_iff_DAxiom.mpr h))

/-! ## T-Based Edges -/

/-- T axioms are subsumed by S4 axioms: every T-axiom instance is an S4-axiom instance. -/
lemma TAxiom_implies_S4Axiom {φ : Proposition Atom} (h : TAxiom φ) : S4Axiom φ :=
  schemaUnion_s4Tags_iff_S4Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_tTags_iff_TAxiom.mpr h))

/-- T axioms are subsumed by TB axioms: every T-axiom instance is a TB-axiom instance. -/
lemma TAxiom_implies_TBAxiom {φ : Proposition Atom} (h : TAxiom φ) : TBAxiom φ :=
  schemaUnion_tbTags_iff_TBAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_tTags_iff_TAxiom.mpr h))

/-! ## B-Based Edges -/

/-- B (KB) axioms are subsumed by TB axioms: every B-axiom instance is a TB-axiom instance. -/
lemma BAxiom_implies_TBAxiom {φ : Proposition Atom} (h : BAxiom φ) : TBAxiom φ :=
  schemaUnion_tbTags_iff_TBAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_bTags_iff_BAxiom.mpr h))

/-- B (KB) axioms are subsumed by DB axioms: every B-axiom instance is a DB-axiom instance. -/
lemma BAxiom_implies_DBAxiom {φ : Proposition Atom} (h : BAxiom φ) : DBAxiom φ :=
  schemaUnion_dbTags_iff_DBAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_bTags_iff_BAxiom.mpr h))

/-- B (KB) axioms are subsumed by KB5 axioms: every B-axiom instance is a KB5-axiom instance. -/
lemma BAxiom_implies_KB5Axiom {φ : Proposition Atom} (h : BAxiom φ) : KB5Axiom φ :=
  schemaUnion_kb5Tags_iff_KB5Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_bTags_iff_BAxiom.mpr h))

/-! ## K4-Based Edges -/

/-- K4 axioms are subsumed by S4 axioms: every K4-axiom instance is an S4-axiom instance. -/
lemma K4Axiom_implies_S4Axiom {φ : Proposition Atom} (h : K4Axiom φ) : S4Axiom φ :=
  schemaUnion_s4Tags_iff_S4Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_k4Tags_iff_K4Axiom.mpr h))

/-- K4 axioms are subsumed by D4 axioms: every K4-axiom instance is a D4-axiom instance. -/
lemma K4Axiom_implies_D4Axiom {φ : Proposition Atom} (h : K4Axiom φ) : D4Axiom φ :=
  schemaUnion_d4Tags_iff_D4Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_k4Tags_iff_K4Axiom.mpr h))

/-- K4 axioms are subsumed by K45 axioms: every K4-axiom instance is a K45-axiom instance. -/
lemma K4Axiom_implies_K45Axiom {φ : Proposition Atom} (h : K4Axiom φ) : K45Axiom φ :=
  schemaUnion_k45Tags_iff_K45Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_k4Tags_iff_K4Axiom.mpr h))

/-! ## K5-Based Edges -/

/-- K5 axioms are subsumed by D5 axioms: every K5-axiom instance is a D5-axiom instance. -/
lemma K5Axiom_implies_D5Axiom {φ : Proposition Atom} (h : K5Axiom φ) : D5Axiom φ :=
  schemaUnion_d5Tags_iff_D5Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_k5Tags_iff_K5Axiom.mpr h))

/-- K5 axioms are subsumed by K45 axioms: every K5-axiom instance is a K45-axiom instance. -/
lemma K5Axiom_implies_K45Axiom {φ : Proposition Atom} (h : K5Axiom φ) : K45Axiom φ :=
  schemaUnion_k45Tags_iff_K45Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_k5Tags_iff_K5Axiom.mpr h))

/-- K5 axioms are subsumed by KB5 axioms: every K5-axiom instance is a KB5-axiom instance. -/
lemma K5Axiom_implies_KB5Axiom {φ : Proposition Atom} (h : K5Axiom φ) : KB5Axiom φ :=
  schemaUnion_kb5Tags_iff_KB5Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_k5Tags_iff_K5Axiom.mpr h))

/-! ## K45-Based Edges -/

/-- K45 axioms are subsumed by D45 axioms: every K45-axiom instance is a D45-axiom instance. -/
lemma K45Axiom_implies_D45Axiom {φ : Proposition Atom} (h : K45Axiom φ) : D45Axiom φ :=
  schemaUnion_d45Tags_iff_D45Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_k45Tags_iff_K45Axiom.mpr h))

/-! ## D4-Based Edges -/

/-- D4 axioms are subsumed by D45 axioms: every D4-axiom instance is a D45-axiom instance. -/
lemma D4Axiom_implies_D45Axiom {φ : Proposition Atom} (h : D4Axiom φ) : D45Axiom φ :=
  schemaUnion_d45Tags_iff_D45Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_d4Tags_iff_D4Axiom.mpr h))

/-! ## D5-Based Edges -/

/-- D5 axioms are subsumed by D45 axioms: every D5-axiom instance is a D45-axiom instance. -/
lemma D5Axiom_implies_D45Axiom {φ : Proposition Atom} (h : D5Axiom φ) : D45Axiom φ :=
  schemaUnion_d45Tags_iff_D45Axiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_d5Tags_iff_D5Axiom.mpr h))

/-! ## Top-Level Edges (into S5) -/

/-- S4 axioms are subsumed by S5 (ModalAxiom): every S4-axiom instance is a ModalAxiom instance.
S5 adds B (symmetry) to S4. -/
lemma S4Axiom_implies_ModalAxiom {φ : Proposition Atom} (h : S4Axiom φ) : ModalAxiom φ :=
  schemaUnion_s5Tags_iff_ModalAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_s4Tags_iff_S4Axiom.mpr h))

/-- TB axioms are subsumed by S5 (ModalAxiom): every TB-axiom instance is a ModalAxiom instance.
S5 adds 4 (transitivity) to TB. -/
lemma TBAxiom_implies_ModalAxiom {φ : Proposition Atom} (h : TBAxiom φ) : ModalAxiom φ :=
  schemaUnion_s5Tags_iff_ModalAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_tbTags_iff_TBAxiom.mpr h))

end Cslib.Logic.Modal

end
