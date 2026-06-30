/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union

/-! # Subformula Infrastructure for Propositional Logic

Canonical shared definitions for subformulas and complexity measure, used by both
the natural deduction normalizer (`Normalization.lean`) and the LK sequent calculus
subformula property (`SubformulaProperty.lean`).

## Main Definitions

- `Proposition.subformulas`: All subformulas of a proposition (including itself).
- `Proposition.IsSubformula`: Subformula predicate: `A.IsSubformula B` iff `A ∈ B.subformulas`.
- `Proposition.complexity`: Size measure for propositions (number of connective occurrences).

## Main Results

### Subformula Lemmas
- `Proposition.self_mem_subformulas`: Every proposition is a subformula of itself.
- `Proposition.IsSubformula.refl`: Reflexivity of `IsSubformula`.
- `Proposition.IsSubformula.trans`: Transitivity of `IsSubformula`.
- `Proposition.IsSubformula.and_left`, `.and_right`: Components of a conjunction are subformulas.
- `Proposition.IsSubformula.or_left`, `.or_right`: Components of a disjunction are subformulas.
- `Proposition.IsSubformula.imp_left`, `.imp_right`: Antecedent/consequent are subformulas.

### Complexity Lemmas
- `complexity_imp`, `complexity_and`, `complexity_or`: Complexity of binary connectives.
- `complexity_atom`, `complexity_bot`: Complexity of atoms and `⊥` is 0.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Subformula Definitions -/

/-- All subformulas of a proposition, including itself.

This is the canonical definition used by both the natural deduction subformula property
and the LK subformula property. -/
def Proposition.subformulas : Proposition Atom → Finset (Proposition Atom)
  | φ@(.atom _) => {φ}
  | φ@.bot => {φ}
  | φ@(.imp A B) => insert φ (A.subformulas ∪ B.subformulas)
  | φ@(.and A B) => insert φ (A.subformulas ∪ B.subformulas)
  | φ@(.or A B) => insert φ (A.subformulas ∪ B.subformulas)

/-- A proposition `A` is a subformula of `B` if `A` occurs in the subformula set of `B`. -/
def Proposition.IsSubformula (A B : Proposition Atom) : Prop :=
  A ∈ B.subformulas

/-- Every proposition is a subformula of itself. -/
theorem Proposition.self_mem_subformulas (A : Proposition Atom) : A ∈ A.subformulas := by
  cases A <;> simp [subformulas]

/-- Every proposition is a subformula of itself. -/
theorem Proposition.IsSubformula.refl (A : Proposition Atom) : A.IsSubformula A :=
  Proposition.self_mem_subformulas A

/-- If `A` is a subformula of `B` and `B` is a subformula of `C`,
then `A` is a subformula of `C`. -/
theorem Proposition.IsSubformula.trans {A B C : Proposition Atom}
    (h1 : A.IsSubformula B) (h2 : B.IsSubformula C) : A.IsSubformula C := by
  unfold IsSubformula at *
  induction C with
  | atom _ =>
    simp only [subformulas, Finset.mem_singleton] at h2; subst h2; exact h1
  | bot =>
    simp only [subformulas, Finset.mem_singleton] at h2; subst h2; exact h1
  | imp P Q ihP ihQ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h2
    rcases h2 with rfl | hP | hQ
    · exact h1
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (ihP hP))))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (ihQ hQ))))
  | and P Q ihP ihQ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h2
    rcases h2 with rfl | hP | hQ
    · exact h1
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (ihP hP))))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (ihQ hQ))))
  | or P Q ihP ihQ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h2
    rcases h2 with rfl | hP | hQ
    · exact h1
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (ihP hP))))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (ihQ hQ))))

/-- Left component of a conjunction is a subformula of the conjunction. -/
theorem Proposition.IsSubformula.and_left {A B : Proposition Atom} :
    A.IsSubformula (A.and B) := by
  simp only [IsSubformula, subformulas, Finset.mem_insert, Finset.mem_union]
  right; left; exact self_mem_subformulas A

/-- Right component of a conjunction is a subformula of the conjunction. -/
theorem Proposition.IsSubformula.and_right {A B : Proposition Atom} :
    B.IsSubformula (A.and B) := by
  simp only [IsSubformula, subformulas, Finset.mem_insert, Finset.mem_union]
  right; right; exact self_mem_subformulas B

/-- Left component of a disjunction is a subformula of the disjunction. -/
theorem Proposition.IsSubformula.or_left {A B : Proposition Atom} :
    A.IsSubformula (A.or B) := by
  simp only [IsSubformula, subformulas, Finset.mem_insert, Finset.mem_union]
  right; left; exact self_mem_subformulas A

/-- Right component of a disjunction is a subformula of the disjunction. -/
theorem Proposition.IsSubformula.or_right {A B : Proposition Atom} :
    B.IsSubformula (A.or B) := by
  simp only [IsSubformula, subformulas, Finset.mem_insert, Finset.mem_union]
  right; right; exact self_mem_subformulas B

/-- Antecedent of an implication is a subformula of the implication. -/
theorem Proposition.IsSubformula.imp_left {A B : Proposition Atom} :
    A.IsSubformula (A.imp B) := by
  simp only [IsSubformula, subformulas, Finset.mem_insert, Finset.mem_union]
  right; left; exact self_mem_subformulas A

/-- Consequent of an implication is a subformula of the implication. -/
theorem Proposition.IsSubformula.imp_right {A B : Proposition Atom} :
    B.IsSubformula (A.imp B) := by
  simp only [IsSubformula, subformulas, Finset.mem_insert, Finset.mem_union]
  right; right; exact self_mem_subformulas B

/-! ## Variable Occurrence -/

/-- The set of propositional atoms (variables) occurring in a proposition.

This is the total, Finset-valued atom-occurrence function used by the Craig interpolation
construction (Maehara's method). Unlike the List-valued partial `atoms` function, `vars` is
total and Finset-valued. -/
def Proposition.vars : Proposition Atom → Finset Atom
  | .atom x   => {x}
  | .bot      => ∅
  | .imp a b  => a.vars ∪ b.vars
  | .and a b  => a.vars ∪ b.vars
  | .or  a b  => a.vars ∪ b.vars

/-! ### Connective rewrite lemmas for `Proposition.vars` -/

/-- Atoms occurring in an atom proposition is the singleton `{x}`. -/
@[simp]
lemma vars_atom (x : Atom) : (Proposition.atom x : Proposition Atom).vars = {x} := rfl

/-- Falsum has no occurring atoms. -/
@[simp]
lemma vars_bot : (⊥ : Proposition Atom).vars = ∅ := rfl

/-- Atoms of an implication are the union of atoms of its components. -/
@[simp]
lemma vars_imp (a b : Proposition Atom) : (a → b).vars = a.vars ∪ b.vars := rfl

/-- Atoms of a conjunction are the union of atoms of its components. -/
@[simp]
lemma vars_and (a b : Proposition Atom) : (a ∧ b).vars = a.vars ∪ b.vars := rfl

/-- Atoms of a disjunction are the union of atoms of its components. -/
@[simp]
lemma vars_or (a b : Proposition Atom) : (a ∨ b).vars = a.vars ∪ b.vars := rfl

/-- Atoms of `¬A = A → ⊥` are the atoms of `A`.

Note: `@[nolint simpNF]` is needed because the LHS `a.neg.vars` is already reducible
by `vars_imp` + `vars_bot` + `Finset.union_empty`, making this a convenience restatement
kept as a named simp lemma for readability. -/
@[simp, nolint simpNF]
lemma vars_neg (a : Proposition Atom) : (¬a).vars = a.vars := by
  change (Proposition.imp a Proposition.bot).vars = a.vars
  simp only [Proposition.vars, Finset.union_empty]

/-- Verum `⊤ = ⊥ → ⊥` has no occurring atoms. -/
@[simp]
lemma vars_top : (⊤ : Proposition Atom).vars = ∅ := by
  change (Proposition.imp Proposition.bot Proposition.bot).vars = ∅
  simp only [Proposition.vars, Finset.empty_union]

/-! ## Complexity Measure -/

/-- The complexity (size) of a proposition: number of connective occurrences.
Atoms and `⊥` have complexity 0; binary connectives add 1 plus their children. -/
def Proposition.complexity : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp A B => 1 + A.complexity + B.complexity
  | .and A B => 1 + A.complexity + B.complexity
  | .or A B => 1 + A.complexity + B.complexity

omit [DecidableEq Atom] in
/-- Complexity is additive over implications. -/
@[simp]
lemma complexity_imp (a b : Proposition Atom) :
    (Proposition.imp a b).complexity = 1 + a.complexity + b.complexity := rfl

omit [DecidableEq Atom] in
/-- Complexity is additive over conjunctions. -/
@[simp]
lemma complexity_and (a b : Proposition Atom) :
    (Proposition.and a b).complexity = 1 + a.complexity + b.complexity := rfl

omit [DecidableEq Atom] in
/-- Complexity is additive over disjunctions. -/
@[simp]
lemma complexity_or (a b : Proposition Atom) :
    (Proposition.or a b).complexity = 1 + a.complexity + b.complexity := rfl

omit [DecidableEq Atom] in
/-- Atoms have complexity 0. -/
@[simp]
lemma complexity_atom (x : Atom) : (Proposition.atom x : Proposition Atom).complexity = 0 := rfl

omit [DecidableEq Atom] in
/-- Bot has complexity 0. -/
@[simp]
lemma complexity_bot : (Proposition.bot : Proposition Atom).complexity = 0 := rfl

end Cslib.Logic.PL

end

/-! ## Finset Lift of Variable Occurrence

`Finset.vars` lifts `Proposition.vars` to finite sets of propositions. It is defined in the
global `Finset` namespace so that dot notation `S.vars` is available for
`S : Finset (Proposition Atom)`. Used by the Craig interpolation theorem (Maehara's method). -/

@[expose] public section

open Cslib.Logic.PL

variable {Atom : Type*} [DecidableEq Atom]

/-- The set of atoms occurring in any proposition in a finite set of propositions.
The result is `S.biUnion Proposition.vars`. -/
def Finset.vars (S : Finset (Proposition Atom)) : Finset Atom :=
  S.biUnion Proposition.vars

/-- Variables of the empty set of propositions is empty. -/
@[simp]
theorem Finset.vars_empty : (∅ : Finset (Proposition Atom)).vars = ∅ :=
  Finset.biUnion_empty

/-- Variables of a singleton set are the variables of that proposition. -/
@[simp]
theorem Finset.vars_singleton (A : Proposition Atom) :
    ({A} : Finset (Proposition Atom)).vars = A.vars :=
  Finset.singleton_biUnion

/-- Variables of a union of proposition-sets is the union of their variables. -/
@[simp]
theorem Finset.vars_union (S T : Finset (Proposition Atom)) :
    (S ∪ T).vars = S.vars ∪ T.vars :=
  Finset.union_biUnion

/-- Variables of `insert A S` are the variables of `A` together with the variables of `S`. -/
@[simp]
theorem Finset.vars_insert (A : Proposition Atom) (S : Finset (Proposition Atom)) :
    (insert A S).vars = A.vars ∪ S.vars :=
  Finset.biUnion_insert

/-- If `A ∈ S`, then `A.vars ⊆ S.vars`. -/
theorem Finset.vars_subset_of_mem {A : Proposition Atom} {S : Finset (Proposition Atom)}
    (h : A ∈ S) : A.vars ⊆ S.vars :=
  Finset.subset_biUnion_of_mem Proposition.vars h

/-- `Finset.vars` is monotone: `S ⊆ T → S.vars ⊆ T.vars`. -/
theorem Finset.vars_mono {S T : Finset (Proposition Atom)} (h : S ⊆ T) :
    S.vars ⊆ T.vars :=
  Finset.biUnion_subset_biUnion_of_subset_left Proposition.vars h

end
