/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.Instances
public import Cslib.Logics.Modal.ProofSystem.SchemaUnion

/-! # Axiom Subsumption Lemmas for the Modal Cube

This module proves all 24 direct-edge axiom subsumption lemmas for the modal cube,
establishing that each weaker system's axiom predicate implies the corresponding
stronger system's axiom predicate. These lemmas are the foundational building blocks
for the derivability monotonicity theorems in `Conservativity.lean`.

## Structure (Schema-Union Rollout)

Each lemma has the form `XAxiom_implies_YAxiom : XAxiom φ → YAxiom φ`, where X is
the weaker system and Y is the stronger system. Every proof routes uniformly through
the single generic `SchemaUnion.subsumption` lemma
(`Cslib.Logics.Modal.ProofSystem.SchemaUnion`) applied directly to `h : XAxiom φ`, with
`xTags ⊆ yTags` discharged by `decide` (the tag sets are concrete `Finset`s). Since each
`<Sys>Axiom` is `abbrev <Sys>Axiom := SchemaUnion sysTags`, `XAxiom φ` and
`SchemaUnion xTags φ` are definitionally the same type, so no bridge conversion is needed
on either side of `SchemaUnion.subsumption`. No hand-written
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
NOT `modalFive`. The `decide`-able `Finset.subset` fact this rollout is built on makes the
omission mechanically evident: no `hsub : kb5Tags ⊆ s5Tags` proof exists, since
`modalFive ∈ kb5Tags` but `modalFive ∉ s5Tags`.

## References

* `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` -- `SchemaUnion.subsumption` (the generic
  lemma every edge below routes through)
* `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` -- the 15 per-system tag sets
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## K-Based Edges -/

/-- K axioms are subsumed by T axioms: every K-axiom instance is a T-axiom instance. -/
lemma KAxiom_implies_TAxiom {φ : Proposition Atom} (h : KAxiom φ) : TAxiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K axioms are subsumed by D axioms: every K-axiom instance is a D-axiom instance. -/
lemma KAxiom_implies_DAxiom {φ : Proposition Atom} (h : KAxiom φ) : DAxiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K axioms are subsumed by B (KB) axioms: every K-axiom instance is a B-axiom instance. -/
lemma KAxiom_implies_BAxiom {φ : Proposition Atom} (h : KAxiom φ) : BAxiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K axioms are subsumed by K4 axioms: every K-axiom instance is a K4-axiom instance. -/
lemma KAxiom_implies_K4Axiom {φ : Proposition Atom} (h : KAxiom φ) : K4Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K axioms are subsumed by K5 axioms: every K-axiom instance is a K5-axiom instance. -/
lemma KAxiom_implies_K5Axiom {φ : Proposition Atom} (h : KAxiom φ) : K5Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## D-Based Edges -/

/-- D axioms are subsumed by D4 axioms: every D-axiom instance is a D4-axiom instance. -/
lemma DAxiom_implies_D4Axiom {φ : Proposition Atom} (h : DAxiom φ) : D4Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- D axioms are subsumed by D5 axioms: every D-axiom instance is a D5-axiom instance. -/
lemma DAxiom_implies_D5Axiom {φ : Proposition Atom} (h : DAxiom φ) : D5Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- D axioms are subsumed by DB axioms: every D-axiom instance is a DB-axiom instance. -/
lemma DAxiom_implies_DBAxiom {φ : Proposition Atom} (h : DAxiom φ) : DBAxiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## T-Based Edges -/

/-- T axioms are subsumed by S4 axioms: every T-axiom instance is an S4-axiom instance. -/
lemma TAxiom_implies_S4Axiom {φ : Proposition Atom} (h : TAxiom φ) : S4Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- T axioms are subsumed by TB axioms: every T-axiom instance is a TB-axiom instance. -/
lemma TAxiom_implies_TBAxiom {φ : Proposition Atom} (h : TAxiom φ) : TBAxiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## B-Based Edges -/

/-- B (KB) axioms are subsumed by TB axioms: every B-axiom instance is a TB-axiom instance. -/
lemma BAxiom_implies_TBAxiom {φ : Proposition Atom} (h : BAxiom φ) : TBAxiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- B (KB) axioms are subsumed by DB axioms: every B-axiom instance is a DB-axiom instance. -/
lemma BAxiom_implies_DBAxiom {φ : Proposition Atom} (h : BAxiom φ) : DBAxiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- B (KB) axioms are subsumed by KB5 axioms: every B-axiom instance is a KB5-axiom instance. -/
lemma BAxiom_implies_KB5Axiom {φ : Proposition Atom} (h : BAxiom φ) : KB5Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## K4-Based Edges -/

/-- K4 axioms are subsumed by S4 axioms: every K4-axiom instance is an S4-axiom instance. -/
lemma K4Axiom_implies_S4Axiom {φ : Proposition Atom} (h : K4Axiom φ) : S4Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K4 axioms are subsumed by D4 axioms: every K4-axiom instance is a D4-axiom instance. -/
lemma K4Axiom_implies_D4Axiom {φ : Proposition Atom} (h : K4Axiom φ) : D4Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K4 axioms are subsumed by K45 axioms: every K4-axiom instance is a K45-axiom instance. -/
lemma K4Axiom_implies_K45Axiom {φ : Proposition Atom} (h : K4Axiom φ) : K45Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## K5-Based Edges -/

/-- K5 axioms are subsumed by D5 axioms: every K5-axiom instance is a D5-axiom instance. -/
lemma K5Axiom_implies_D5Axiom {φ : Proposition Atom} (h : K5Axiom φ) : D5Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K5 axioms are subsumed by K45 axioms: every K5-axiom instance is a K45-axiom instance. -/
lemma K5Axiom_implies_K45Axiom {φ : Proposition Atom} (h : K5Axiom φ) : K45Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- K5 axioms are subsumed by KB5 axioms: every K5-axiom instance is a KB5-axiom instance. -/
lemma K5Axiom_implies_KB5Axiom {φ : Proposition Atom} (h : K5Axiom φ) : KB5Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## K45-Based Edges -/

/-- K45 axioms are subsumed by D45 axioms: every K45-axiom instance is a D45-axiom instance. -/
lemma K45Axiom_implies_D45Axiom {φ : Proposition Atom} (h : K45Axiom φ) : D45Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## D4-Based Edges -/

/-- D4 axioms are subsumed by D45 axioms: every D4-axiom instance is a D45-axiom instance. -/
lemma D4Axiom_implies_D45Axiom {φ : Proposition Atom} (h : D4Axiom φ) : D45Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## D5-Based Edges -/

/-- D5 axioms are subsumed by D45 axioms: every D5-axiom instance is a D45-axiom instance. -/
lemma D5Axiom_implies_D45Axiom {φ : Proposition Atom} (h : D5Axiom φ) : D45Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-! ## Top-Level Edges (into S5) -/

/-- S4 axioms are subsumed by S5: every S4-axiom instance is an S5Axiom instance.
S5 adds B (symmetry) to S4. -/
lemma S4Axiom_implies_ModalAxiom {φ : Proposition Atom} (h : S4Axiom φ) : S5Axiom φ :=
  SchemaUnion.subsumption (by decide) h

/-- TB axioms are subsumed by S5: every TB-axiom instance is an S5Axiom instance.
S5 adds 4 (transitivity) to TB. -/
lemma TBAxiom_implies_ModalAxiom {φ : Proposition Atom} (h : TBAxiom φ) : S5Axiom φ :=
  SchemaUnion.subsumption (by decide) h

end Cslib.Logic.Modal

end
