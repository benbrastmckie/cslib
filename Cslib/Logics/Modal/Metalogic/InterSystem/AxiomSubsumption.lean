/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Axiom Subsumption Lemmas for the Modal Cube

This module proves all 24 direct-edge axiom subsumption lemmas for the modal cube,
establishing that each weaker system's axiom predicate implies the corresponding
stronger system's axiom predicate. These lemmas are the foundational building blocks
for the derivability monotonicity theorems in `Conservativity.lean`.

## Structure

Each lemma has the form `XAxiom_implies_YAxiom : XAxiom φ → YAxiom φ`, where X is
the weaker system and Y is the stronger system. The proofs are mechanical case-splits:
each constructor of the source axiom predicate maps to the same-named constructor of
the target axiom predicate. The extra constructors in the target are simply not needed.

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

Note: The edge KB5 → S5 is omitted because S5's `ModalAxiom` predicate does not include
axiom 5 (Euclideanness) as a named axiom schema; it derives from T + 4 + B instead.
The syntactic subsumption approach requires formula-level axiom inclusion.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## K-Based Edges -/

/-- K axioms are subsumed by T axioms: every K-axiom instance is a T-axiom instance. -/
lemma KAxiom_implies_TAxiom {φ : Proposition Atom} (h : KAxiom φ) : TAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ

/-- K axioms are subsumed by D axioms: every K-axiom instance is a D-axiom instance. -/
lemma KAxiom_implies_DAxiom {φ : Proposition Atom} (h : KAxiom φ) : DAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ

/-- K axioms are subsumed by B (KB) axioms: every K-axiom instance is a B-axiom instance. -/
lemma KAxiom_implies_BAxiom {φ : Proposition Atom} (h : KAxiom φ) : BAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ

/-- K axioms are subsumed by K4 axioms: every K-axiom instance is a K4-axiom instance. -/
lemma KAxiom_implies_K4Axiom {φ : Proposition Atom} (h : KAxiom φ) : K4Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ

/-- K axioms are subsumed by K5 axioms: every K-axiom instance is a K5-axiom instance. -/
lemma KAxiom_implies_K5Axiom {φ : Proposition Atom} (h : KAxiom φ) : K5Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ

/-! ## D-Based Edges -/

/-- D axioms are subsumed by D4 axioms: every D-axiom instance is a D4-axiom instance. -/
lemma DAxiom_implies_D4Axiom {φ : Proposition Atom} (h : DAxiom φ) : D4Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalD φ => .modalD φ

/-- D axioms are subsumed by D5 axioms: every D-axiom instance is a D5-axiom instance. -/
lemma DAxiom_implies_D5Axiom {φ : Proposition Atom} (h : DAxiom φ) : D5Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalD φ => .modalD φ

/-- D axioms are subsumed by DB axioms: every D-axiom instance is a DB-axiom instance. -/
lemma DAxiom_implies_DBAxiom {φ : Proposition Atom} (h : DAxiom φ) : DBAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalD φ => .modalD φ

/-! ## T-Based Edges -/

/-- T axioms are subsumed by S4 axioms: every T-axiom instance is an S4-axiom instance. -/
lemma TAxiom_implies_S4Axiom {φ : Proposition Atom} (h : TAxiom φ) : S4Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalT φ => .modalT φ

/-- T axioms are subsumed by TB axioms: every T-axiom instance is a TB-axiom instance. -/
lemma TAxiom_implies_TBAxiom {φ : Proposition Atom} (h : TAxiom φ) : TBAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalT φ => .modalT φ

/-! ## B-Based Edges -/

/-- B (KB) axioms are subsumed by TB axioms: every B-axiom instance is a TB-axiom instance. -/
lemma BAxiom_implies_TBAxiom {φ : Proposition Atom} (h : BAxiom φ) : TBAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalB φ => .modalB φ

/-- B (KB) axioms are subsumed by DB axioms: every B-axiom instance is a DB-axiom instance. -/
lemma BAxiom_implies_DBAxiom {φ : Proposition Atom} (h : BAxiom φ) : DBAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalB φ => .modalB φ

/-- B (KB) axioms are subsumed by KB5 axioms: every B-axiom instance is a KB5-axiom instance. -/
lemma BAxiom_implies_KB5Axiom {φ : Proposition Atom} (h : BAxiom φ) : KB5Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalB φ => .modalB φ

/-! ## K4-Based Edges -/

/-- K4 axioms are subsumed by S4 axioms: every K4-axiom instance is an S4-axiom instance. -/
lemma K4Axiom_implies_S4Axiom {φ : Proposition Atom} (h : K4Axiom φ) : S4Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalFour φ => .modalFour φ

/-- K4 axioms are subsumed by D4 axioms: every K4-axiom instance is a D4-axiom instance. -/
lemma K4Axiom_implies_D4Axiom {φ : Proposition Atom} (h : K4Axiom φ) : D4Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalFour φ => .modalFour φ

/-- K4 axioms are subsumed by K45 axioms: every K4-axiom instance is a K45-axiom instance. -/
lemma K4Axiom_implies_K45Axiom {φ : Proposition Atom} (h : K4Axiom φ) : K45Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalFour φ => .modalFour φ

/-! ## K5-Based Edges -/

/-- K5 axioms are subsumed by D5 axioms: every K5-axiom instance is a D5-axiom instance. -/
lemma K5Axiom_implies_D5Axiom {φ : Proposition Atom} (h : K5Axiom φ) : D5Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalFive φ => .modalFive φ

/-- K5 axioms are subsumed by K45 axioms: every K5-axiom instance is a K45-axiom instance. -/
lemma K5Axiom_implies_K45Axiom {φ : Proposition Atom} (h : K5Axiom φ) : K45Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalFive φ => .modalFive φ

/-- K5 axioms are subsumed by KB5 axioms: every K5-axiom instance is a KB5-axiom instance. -/
lemma K5Axiom_implies_KB5Axiom {φ : Proposition Atom} (h : K5Axiom φ) : KB5Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalFive φ => .modalFive φ

/-! ## K45-Based Edges -/

/-- K45 axioms are subsumed by D45 axioms: every K45-axiom instance is a D45-axiom instance. -/
lemma K45Axiom_implies_D45Axiom {φ : Proposition Atom} (h : K45Axiom φ) : D45Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalFour φ => .modalFour φ
  | .modalFive φ => .modalFive φ

/-! ## D4-Based Edges -/

/-- D4 axioms are subsumed by D45 axioms: every D4-axiom instance is a D45-axiom instance. -/
lemma D4Axiom_implies_D45Axiom {φ : Proposition Atom} (h : D4Axiom φ) : D45Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalD φ => .modalD φ
  | .modalFour φ => .modalFour φ

/-! ## D5-Based Edges -/

/-- D5 axioms are subsumed by D45 axioms: every D5-axiom instance is a D45-axiom instance. -/
lemma D5Axiom_implies_D45Axiom {φ : Proposition Atom} (h : D5Axiom φ) : D45Axiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalD φ => .modalD φ
  | .modalFive φ => .modalFive φ

/-! ## Top-Level Edges (into S5) -/

/-- S4 axioms are subsumed by S5 (ModalAxiom): every S4-axiom instance is a ModalAxiom instance.
S5 adds B (symmetry) to S4. -/
lemma S4Axiom_implies_ModalAxiom {φ : Proposition Atom} (h : S4Axiom φ) : ModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalT φ => .modalT φ
  | .modalFour φ => .modalFour φ

/-- TB axioms are subsumed by S5 (ModalAxiom): every TB-axiom instance is a ModalAxiom instance.
S5 adds 4 (transitivity) to TB. -/
lemma TBAxiom_implies_ModalAxiom {φ : Proposition Atom} (h : TBAxiom φ) : ModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
  | .peirce φ ψ => .peirce φ ψ
  | .modalK φ ψ => .modalK φ ψ
  | .modalT φ => .modalT φ
  | .modalB φ => .modalB φ

end Cslib.Logic.Modal

end
