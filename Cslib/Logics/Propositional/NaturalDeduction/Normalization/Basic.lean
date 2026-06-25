/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Normalization Basics for Propositional Natural Deduction

This module defines the subformula infrastructure and the normality predicates used in
Prawitz-style normalization for the `Theory.Derivation` inductive type.

## Main Definitions

- `Proposition.subformulas`: All subformulas of a proposition (including itself).
- `Proposition.IsSubformula`: Subformula predicate.
- `Proposition.complexity`: Size measure for propositions.
- `Theory.Derivation.isNormal`: Boolean predicate detecting the absence of maximal formulas.
- `Theory.Derivation.isIntroRoot`: Boolean predicate for introduction-headed derivations.
- `Theory.Derivation.isStronglyNormal`: Boolean predicate detecting absence of both proper
  redexes and commuting conversions.
- `Theory.Derivation.formulas`: All formula occurrences in a derivation.
- `Theory.Derivation.SubformulaProperty`: The subformula property predicate.

## References

* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Ch. III–IV.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Subformula Infrastructure -/

/-- All subformulas of a proposition, including itself.

This is used to state the subformula property: every formula occurring in a normal
derivation is a subformula of the conclusion or a hypothesis. -/
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

/-- The complexity (size) of a proposition. Atoms and `⊥` have complexity 0;
connectives add 1 plus the sum of their children's complexities. -/
def Proposition.complexity : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp A B => 1 + A.complexity + B.complexity
  | .and A B => 1 + A.complexity + B.complexity
  | .or A B => 1 + A.complexity + B.complexity

/-! ## Derivation Definitions -/

variable {T : Theory Atom}

/-- The height of a derivation tree (maximum depth). -/
def Theory.Derivation.height : T.Derivation G A → Nat
  | ax _ => 0
  | ass _ => 0
  | andI _ D₁ D₂ => 1 + max D₁.height D₂.height
  | andE1 _ D => 1 + D.height
  | andE2 _ D => 1 + D.height
  | orI1 _ D => 1 + D.height
  | orI2 _ D => 1 + D.height
  | orE _ D DA DB => 1 + max D.height (max DA.height DB.height)
  | impI _ D => 1 + D.height
  | impE D E => 1 + max D.height E.height

/-! ## The isNormal Predicate -/

/-- A derivation is normal if it contains no maximal formula occurrences.
A maximal formula is one that is both introduced and immediately eliminated.
The five redex patterns are:
- `impE (impI Γ D) E`: implication redex (β-reduction)
- `andE1 G (andI G D₁ D₂)`: left conjunction redex
- `andE2 G (andI G D₁ D₂)`: right conjunction redex
- `orE G (orI1 G D) DA DB`: left disjunction redex
- `orE G (orI2 G D) DA DB`: right disjunction redex -/
def Theory.Derivation.isNormal : T.Derivation G A → Bool
  | ax _ => true
  | ass _ => true
  | andI _ D₁ D₂ => D₁.isNormal && D₂.isNormal
  | andE1 _ D =>
    match D with
    | andI _ _ _ => false
    | _ => D.isNormal
  | andE2 _ D =>
    match D with
    | andI _ _ _ => false
    | _ => D.isNormal
  | orI1 _ D => D.isNormal
  | orI2 _ D => D.isNormal
  | orE _ D DA DB =>
    match D with
    | orI1 _ _ => false
    | orI2 _ _ => false
    | _ => D.isNormal && DA.isNormal && DB.isNormal
  | impI _ D => D.isNormal
  | impE D E =>
    match D with
    | impI _ _ => false
    | _ => D.isNormal && E.isNormal

/-- Axiom derivations are normal (leaves, no redex). -/
theorem Theory.Derivation.isNormal_ax {G : Ctx Atom} {A : Proposition Atom} {h : A ∈ T} :
    (Derivation.ax h : T.Derivation G A).isNormal = true := rfl

/-- Assumption derivations are normal (leaves, no redex). -/
theorem Theory.Derivation.isNormal_ass {G : Ctx Atom} {A : Proposition Atom} {h : A ∈ G} :
    (Derivation.ass h : T.Derivation G A).isNormal = true := rfl

/-! ## Strong Normality and Introduction Root -/

/-- A derivation is introduction-headed if the outermost rule is an introduction rule.
Leaves (ax, ass) and elimination rules are not introduction-headed. -/
def Theory.Derivation.isIntroRoot : T.Derivation G A → Bool
  | andI _ _ _ => true
  | orI1 _ _ => true
  | orI2 _ _ => true
  | impI _ _ => true
  | _ => false

/-- A derivation is `orE`-headed if the outermost rule is disjunction elimination.
This predicate identifies derivations whose root is an `orE` rule application,
which is needed for the 3-way disjunction in `conclusion_grounded_or_intro`. -/
def Theory.Derivation.isOrERoot : T.Derivation G A → Bool
  | orE _ _ _ _ => true
  | _ => false

/-- A derivation is strongly normal if it contains no proper redexes (as in `isNormal`)
and additionally no commuting conversions. A commuting conversion occurs when an
elimination rule is applied to the result of a disjunction elimination (`orE`):
- `andE1 G (orE ...)`: commuting conversion
- `andE2 G (orE ...)`: commuting conversion
- `impE (orE ...) _`: commuting conversion
- `orE G (orE ...) _ _`: commuting conversion (nested disjunction elimination)

These patterns prevent the subformula property from holding in merely-normal derivations.
The classical example: `andE1(orE(ass, andI(ass,ass), andI(ass,ass)))` is normal but violates
the subformula property because `A ∧ B` in the `orE` branches is not a subformula of `A`. -/
def Theory.Derivation.isStronglyNormal : T.Derivation G A → Bool
  | ax _ => true
  | ass _ => true
  | andI _ D₁ D₂ => D₁.isStronglyNormal && D₂.isStronglyNormal
  | andE1 _ D =>
    match D with
    | andI _ _ _ => false      -- proper redex
    | orE _ _ _ _ => false     -- commuting conversion
    | _ => D.isStronglyNormal
  | andE2 _ D =>
    match D with
    | andI _ _ _ => false      -- proper redex
    | orE _ _ _ _ => false     -- commuting conversion
    | _ => D.isStronglyNormal
  | orI1 _ D => D.isStronglyNormal
  | orI2 _ D => D.isStronglyNormal
  | orE _ D DA DB =>
    match D with
    | orI1 _ _ => false        -- proper redex
    | orI2 _ _ => false        -- proper redex
    | orE _ _ _ _ => false     -- commuting conversion (nested orE)
    | _ => D.isStronglyNormal && DA.isStronglyNormal && DB.isStronglyNormal
  | impI _ D => D.isStronglyNormal
  | impE D E =>
    match D with
    | impI _ _ => false        -- proper redex
    | orE _ _ _ _ => false     -- commuting conversion
    | _ => D.isStronglyNormal && E.isStronglyNormal

/-- Strong normality implies normality: strongly normal derivations avoid all proper redexes
and additionally avoid commuting conversions. -/
theorem Theory.Derivation.isStronglyNormal_implies_isNormal
    {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A)
    (h : d.isStronglyNormal = true) : d.isNormal = true := by
  induction d with
  | ax _ | ass _ => rfl
  | andI _ D₁ D₂ ih₁ ih₂ =>
    simp only [isStronglyNormal, Bool.and_eq_true] at h
    simp only [isNormal, Bool.and_eq_true]
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | andE1 _ D ih =>
    -- D : T.Derivation G (A ∧ B). Valid constructors: ax, ass, andI, andE1, andE2, impE, orE.
    -- (orI1, orI2, impI would give wrong type.)
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at h   -- proper redex: false
    | orE _ _ _ _ => simp [isStronglyNormal] at h  -- commuting conversion: false
    | ax _ | ass _ =>
      simp [isNormal, isStronglyNormal] at *
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at h; simp only [isNormal]; exact ih h
  | andE2 _ D ih =>
    -- D : T.Derivation G (A ∧ B). Same valid constructors as andE1 case.
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at h
    | orE _ _ _ _ => simp [isStronglyNormal] at h
    | ax _ | ass _ => simp [isNormal, isStronglyNormal] at *
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at h; simp only [isNormal]; exact ih h
  | orI1 _ D ih =>
    simp only [isNormal, isStronglyNormal] at *; exact ih h
  | orI2 _ D ih =>
    simp only [isNormal, isStronglyNormal] at *; exact ih h
  | orE _ D DA DB ih ihA ihB =>
    -- D : T.Derivation G (A ∨ B). Valid constructors: ax, ass, orI1, orI2, andE1, andE2, impE, orE.
    -- (andI, impI would give wrong type.)
    cases D with
    | orI1 _ _ => simp [isStronglyNormal] at h   -- proper redex: false
    | orI2 _ _ => simp [isStronglyNormal] at h   -- proper redex: false
    | orE _ _ _ _ => simp [isStronglyNormal] at h  -- commuting conversion: false
    | ax _ | ass _ =>
      -- isStronglyNormal (orE G (ax _) DA DB) = true && DA.isStronglyNormal && DB.isStronglyNormal
      simp only [isStronglyNormal, isNormal] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨⟨trivial, ihA h.1.2⟩, ihB h.2⟩
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      -- isStronglyNormal (orE G D DA DB) = D.sn && DA.sn && DB.sn
      simp only [isStronglyNormal, isNormal, Bool.and_eq_true] at h ⊢
      exact ⟨⟨ih h.1.1, ihA h.1.2⟩, ihB h.2⟩
  | impI _ D ih =>
    simp only [isNormal, isStronglyNormal] at *; exact ih h
  | impE D E ih ihE =>
    -- D : T.Derivation G (A → B). Valid constructors: ax, ass, impI, impE, andE1, andE2, orE.
    -- (andI, orI1, orI2 would give wrong type.)
    cases D with
    | impI _ _ => simp [isStronglyNormal] at h    -- proper redex: false
    | orE _ _ _ _ => simp [isStronglyNormal] at h  -- commuting conversion: false
    | ax _ | ass _ =>
      simp only [isStronglyNormal, isNormal] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨trivial, ihE h.2⟩
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, isNormal, Bool.and_eq_true] at h ⊢
      exact ⟨ih h.1, ihE h.2⟩

/-! ## Formulas and Subformula Property -/

/-- The set of all formula occurrences in a derivation: every node contributes its conclusion. -/
def Theory.Derivation.formulas : T.Derivation G A → Finset (Proposition Atom)
  | ax _ => {A}
  | ass _ => {A}
  | andI _ D₁ D₂ => {A} ∪ D₁.formulas ∪ D₂.formulas
  | andE1 _ D => {A} ∪ D.formulas
  | andE2 _ D => {A} ∪ D.formulas
  | orI1 _ D => {A} ∪ D.formulas
  | orI2 _ D => {A} ∪ D.formulas
  | orE _ D DA DB => {A} ∪ D.formulas ∪ DA.formulas ∪ DB.formulas
  | impI _ D => {A} ∪ D.formulas
  | impE D E => {A} ∪ D.formulas ∪ E.formulas

/-- The subformula property: every formula occurring in the derivation is a subformula of
the conclusion, a hypothesis, or a theory axiom. -/
def Theory.Derivation.SubformulaProperty {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) : Prop :=
  ∀ B ∈ d.formulas,
    B.IsSubformula A ∨
    (∃ C ∈ G, B.IsSubformula C) ∨
    (∃ C ∈ T, B.IsSubformula C)

end Cslib.Logic.PL
