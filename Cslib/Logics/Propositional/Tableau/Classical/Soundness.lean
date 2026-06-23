/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Classical.Expansion
public import Cslib.Logics.Propositional.Semantics.Bool

/-! # Classical Tableau Soundness

This module proves soundness of the classical propositional tableau: if the tableau
closes on `φ` (starting from `F(φ)`), then `φ` is a classical tautology.

## Main Results

- `branchConsistent`: Predicate relating a Boolean valuation to a signed branch.
- `classicalBranchSatisfiable`: A branch is satisfiable if a consistent valuation exists.
- `classicalTableau_sound`: If `classicalTableau φ = closed`, then `Tautology φ`.

## Strategy

Soundness follows from two sub-lemmas:
1. Each classical rule preserves branch satisfiability.
2. A classically closed branch is unsatisfiable.

Together these imply: if the tableau closes (all branches are closed), then the initial
branch `[F(φ)]` was unsatisfiable, meaning every valuation satisfies `T(φ)`, i.e., `φ`
is a tautology.

## Notes on sorry

The soundness proof for the `classicalExpandBranches` loop (induction on fuel) requires
significant infrastructure. The key lemmas are stated and their proofs are marked sorry.
The decision procedure in `Classical/DecisionProcedure.lean` uses the existing Boolean
enumeration completeness to give a sorry-free `Decidable (Tautology φ)` instance.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Branch Satisfiability -/

/-- A Boolean valuation is consistent with a signed branch if:
- For every T(φ) on the branch, `BoolEvaluate v φ = true`
- For every F(φ) on the branch, `BoolEvaluate v φ = false` -/
def branchConsistent (v : BoolValuation Atom)
    (b : Branch (Proposition Atom) Unit) : Prop :=
  ∀ sf ∈ b,
    (sf.sign = .pos → BoolEvaluate v sf.formula = true) ∧
    (sf.sign = .neg → BoolEvaluate v sf.formula = false)

/-- A branch is satisfiable if there exists a Boolean valuation consistent with it. -/
def classicalBranchSatisfiable (b : Branch (Proposition Atom) Unit) : Prop :=
  ∃ v : BoolValuation Atom, branchConsistent v b

/-! ## Helper simp lemmas for classicalApplyOne -/

private lemma classicalApplyOne_pos_atom (l : Unit) (x : Atom) :
    classicalApplyOne (SignedFormula.pos (.atom x) l) = .notApplicable := rfl

private lemma classicalApplyOne_pos_bot (l : Unit) :
    classicalApplyOne (SignedFormula.pos (Proposition.bot (Atom := Atom)) l) = .notApplicable := rfl

private lemma classicalApplyOne_pos_and (l : Unit) (a b : Proposition Atom) :
    classicalApplyOne (SignedFormula.pos (.and a b) l) =
    .linear [SignedFormula.pos a l, SignedFormula.pos b l] := rfl

private lemma classicalApplyOne_pos_or (l : Unit) (a b : Proposition Atom) :
    classicalApplyOne (SignedFormula.pos (.or a b) l) =
    .branching [[SignedFormula.pos a l], [SignedFormula.pos b l]] := rfl

private lemma classicalApplyOne_pos_imp (l : Unit) (a b : Proposition Atom) (h : b ≠ .bot) :
    classicalApplyOne (SignedFormula.pos (.imp a b) l) =
    .branching [[SignedFormula.neg a l], [SignedFormula.pos b l]] := by
  cases b with
  | bot => exact absurd rfl h
  | atom x => rfl
  | imp c d => rfl
  | and c d => rfl
  | or c d => rfl

private lemma classicalApplyOne_pos_neg (l : Unit) (a : Proposition Atom) :
    classicalApplyOne (SignedFormula.pos (.imp a .bot) l) =
    .linear [SignedFormula.neg a l] := rfl

private lemma classicalApplyOne_neg_atom (l : Unit) (x : Atom) :
    classicalApplyOne (SignedFormula.neg (.atom x) l) = .notApplicable := rfl

private lemma classicalApplyOne_neg_bot (l : Unit) :
    classicalApplyOne (SignedFormula.neg (Proposition.bot (Atom := Atom)) l) = .notApplicable := rfl

private lemma classicalApplyOne_neg_and (l : Unit) (a b : Proposition Atom) :
    classicalApplyOne (SignedFormula.neg (.and a b) l) =
    .branching [[SignedFormula.neg a l], [SignedFormula.neg b l]] := rfl

private lemma classicalApplyOne_neg_or (l : Unit) (a b : Proposition Atom) :
    classicalApplyOne (SignedFormula.neg (.or a b) l) =
    .linear [SignedFormula.neg a l, SignedFormula.neg b l] := rfl

private lemma classicalApplyOne_neg_imp (l : Unit) (a b : Proposition Atom) (h : b ≠ .bot) :
    classicalApplyOne (SignedFormula.neg (.imp a b) l) =
    .linear [SignedFormula.pos a l, SignedFormula.neg b l] := by
  cases b with
  | bot => exact absurd rfl h
  | atom x => rfl
  | imp c d => rfl
  | and c d => rfl
  | or c d => rfl

private lemma classicalApplyOne_neg_neg (l : Unit) (a : Proposition Atom) :
    classicalApplyOne (SignedFormula.neg (.imp a .bot) l) =
    .linear [SignedFormula.pos a l] := rfl

private lemma prop_beq_eq :
    ∀ (a b : Proposition Atom), (a == b) = true → a = b := by
  intro a b h
  induction a generalizing b with
  | bot =>
    cases b <;> first
      | rfl
      | (change false = true at h; exact absurd h Bool.false_ne_true)
  | atom x => cases b with
    | atom y =>
      change (x == y) = true at h; exact congrArg _ (eq_of_beq h)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true
  | and a1 a2 ih1 ih2 => cases b with
    | and c d =>
      change (a1 == c && a2 == d) = true at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ _ (ih1 _ h.1) (ih2 _ h.2)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true
  | or a1 a2 ih1 ih2 => cases b with
    | or c d =>
      change (a1 == c && a2 == d) = true at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ _ (ih1 _ h.1) (ih2 _ h.2)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true
  | imp a1 a2 ih1 ih2 => cases b with
    | imp c d =>
      change (a1 == c && a2 == d) = true at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ _ (ih1 _ h.1) (ih2 _ h.2)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true

/-! ## Key Lemmas -/

/-- Each classical rule application preserves branch satisfiability.

If branch `b` is satisfiable and a rule applied to `sf ∈ b` gives sub-branches,
then at least one sub-branch is also satisfiable (for beta-rules) or the single
resulting branch is satisfiable (for alpha-rules).

NOTE: Proof by case analysis on all 8 classical rules and both signs. -/
lemma classicalRule_preserves_sat (b : Branch (Proposition Atom) Unit)
    (sf : SignedFormula (Proposition Atom) Unit)
    (hmem : sf ∈ b)
    (hsat : classicalBranchSatisfiable b) :
    match classicalApplyOne sf with
    | .linear newForms =>
      classicalBranchSatisfiable (Branch.extendMany b newForms)
    | .branching branches =>
      ∃ br ∈ branches, classicalBranchSatisfiable (Branch.extendMany b br)
    | .persistent newForms =>
      classicalBranchSatisfiable (Branch.extendMany b newForms)
    | .notApplicable => True := by
  obtain ⟨v, hv⟩ := hsat
  -- Helper: extending b with formulas consistent with v preserves satisfiability
  have extend_sat : ∀ newForms : List (SignedFormula (Proposition Atom) Unit),
      (∀ sf' ∈ newForms,
        (sf'.sign = .pos → BoolEvaluate v sf'.formula = true) ∧
        (sf'.sign = .neg → BoolEvaluate v sf'.formula = false)) →
      classicalBranchSatisfiable (Branch.extendMany b newForms) :=
    fun newForms hnew => ⟨v, fun sf' hmem' => by
      simp only [Branch.extendMany, List.mem_append] at hmem'
      rcases hmem' with h | h
      · exact hnew sf' h
      · exact hv sf' h⟩
  -- Helper: sf is consistent with v since sf ∈ b
  have hsf := hv sf hmem
  -- Reconstruct sf in terms of sign and formula to enable case analysis
  obtain ⟨sign, form, label⟩ := sf
  simp only at hsf hmem
  -- Case split on sign
  cases sign with
  | pos =>
    -- hsf says: (Sign.pos = Sign.pos → BoolEvaluate v form = true) ∧ ...
    -- which simp reduces to (True → ...) ∧ (False → ...)
    have htrue : BoolEvaluate v form = true := hsf.1 rfl
    -- Case split on formula structure
    cases form with
    | atom x =>
      -- classicalApplyOne ⟨.pos, .atom x, l⟩ = .notApplicable (by rfl on pos_atom lemma)
      show True; trivial
    | bot =>
      -- classicalApplyOne ⟨.pos, .bot, l⟩ = .notApplicable (by rfl on pos_bot lemma)
      show True; trivial
    | and a b_form =>
      -- classicalApplyOne ⟨.pos, .and a b, l⟩ = .linear [T(a), T(b)] (pos_and: rfl)
      simp only [show classicalApplyOne (⟨Sign.pos, a ∧ b_form, label⟩ :
        SignedFormula (Proposition Atom) Unit) =
        .linear [SignedFormula.pos a label, SignedFormula.pos b_form label] from rfl]
      rw [BoolEvaluate_and, Bool.and_eq_true] at htrue
      apply extend_sat
      intro sf' hmem'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      rcases hmem' with rfl | rfl
      · exact ⟨fun _ => htrue.1, fun h => absurd h (by simp [SignedFormula.pos])⟩
      · exact ⟨fun _ => htrue.2, fun h => absurd h (by simp [SignedFormula.pos])⟩
    | or a b_form =>
      -- classicalApplyOne ⟨.pos, .or a b, l⟩ = .branching [[T(a)], [T(b)]]
      simp only [show classicalApplyOne (⟨Sign.pos, a ∨ b_form, label⟩ :
        SignedFormula (Proposition Atom) Unit) =
        .branching [[SignedFormula.pos a label], [SignedFormula.pos b_form label]] from rfl]
      rw [BoolEvaluate_or, Bool.or_eq_true] at htrue
      rcases htrue with ha | hb
      · exact ⟨[SignedFormula.pos a label], List.mem_cons_self,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun _ => ha, fun h => absurd h (by simp [SignedFormula.pos])⟩)⟩
      · exact ⟨[SignedFormula.pos b_form label], by simp,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun _ => hb, fun h => absurd h (by simp [SignedFormula.pos])⟩)⟩
    | imp a b_form =>
      by_cases hbot : b_form = .bot
      · subst hbot
        -- classicalApplyOne ⟨.pos, .imp a .bot, l⟩ = .linear [F(a)]  (negPos: rfl)
        simp only [show classicalApplyOne (⟨Sign.pos, a.imp .bot, label⟩ :
          SignedFormula (Proposition Atom) Unit) =
          .linear [SignedFormula.neg a label] from rfl]
        rw [BoolEvaluate_imp, BoolEvaluate_bot, Bool.or_false] at htrue
        -- htrue : !BoolEvaluate v a = true, so BoolEvaluate v a = false
        have ha : BoolEvaluate v a = false := by
          rw [Bool.not_eq_true'] at htrue; exact htrue
        apply extend_sat
        intro sf' hmem'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        subst hmem'
        exact ⟨fun h => absurd h (by simp [SignedFormula.neg]), fun _ => ha⟩
      · -- classicalApplyOne ⟨.pos, .imp a b, l⟩ = .branching [[F(a)], [T(b)]]  (impPos)
        -- We need to case on b_form to see which rfl applies
        cases b_form with
        | atom x =>
          simp only [show classicalApplyOne (⟨Sign.pos, a.imp (.atom x), label⟩ :
            SignedFormula (Proposition Atom) Unit) =
            .branching [[SignedFormula.neg a label], [SignedFormula.pos (.atom x) label]] from rfl]
          rw [BoolEvaluate_imp] at htrue
          rcases Bool.or_eq_true_iff.mp htrue with h | h
          · exact ⟨[SignedFormula.neg a label], List.mem_cons_self,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun hh => absurd hh (by simp [SignedFormula.neg]),
                  fun _ => by rw [Bool.not_eq_true'] at h; exact h⟩)⟩
          · exact ⟨[SignedFormula.pos (.atom x) label], by simp,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun _ => h, fun hh => absurd hh (by simp [SignedFormula.pos])⟩)⟩
        | bot => exact absurd rfl hbot
        | imp c d =>
          simp only [show classicalApplyOne (⟨Sign.pos, a.imp (c.imp d), label⟩ :
            SignedFormula (Proposition Atom) Unit) =
            .branching [[SignedFormula.neg a label], [SignedFormula.pos (c.imp d) label]] from rfl]
          rw [BoolEvaluate_imp] at htrue
          rcases Bool.or_eq_true_iff.mp htrue with h | h
          · exact ⟨[SignedFormula.neg a label], List.mem_cons_self,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun hh => absurd hh (by simp [SignedFormula.neg]),
                  fun _ => by rw [Bool.not_eq_true'] at h; exact h⟩)⟩
          · exact ⟨[SignedFormula.pos (c.imp d) label], by simp,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun _ => h, fun hh => absurd hh (by simp [SignedFormula.pos])⟩)⟩
        | and c d =>
          simp only [show classicalApplyOne (⟨Sign.pos, a.imp (c.and d), label⟩ :
            SignedFormula (Proposition Atom) Unit) =
            .branching [[SignedFormula.neg a label], [SignedFormula.pos (c.and d) label]] from rfl]
          rw [BoolEvaluate_imp] at htrue
          rcases Bool.or_eq_true_iff.mp htrue with h | h
          · exact ⟨[SignedFormula.neg a label], List.mem_cons_self,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun hh => absurd hh (by simp [SignedFormula.neg]),
                  fun _ => by rw [Bool.not_eq_true'] at h; exact h⟩)⟩
          · exact ⟨[SignedFormula.pos (c.and d) label], by simp,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun _ => h, fun hh => absurd hh (by simp [SignedFormula.pos])⟩)⟩
        | or c d =>
          simp only [show classicalApplyOne (⟨Sign.pos, a.imp (c.or d), label⟩ :
            SignedFormula (Proposition Atom) Unit) =
            .branching [[SignedFormula.neg a label], [SignedFormula.pos (c.or d) label]] from rfl]
          rw [BoolEvaluate_imp] at htrue
          rcases Bool.or_eq_true_iff.mp htrue with h | h
          · exact ⟨[SignedFormula.neg a label], List.mem_cons_self,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun hh => absurd hh (by simp [SignedFormula.neg]),
                  fun _ => by rw [Bool.not_eq_true'] at h; exact h⟩)⟩
          · exact ⟨[SignedFormula.pos (c.or d) label], by simp,
              extend_sat _ (fun sf' hmem' => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                subst hmem'
                exact ⟨fun _ => h, fun hh => absurd hh (by simp [SignedFormula.pos])⟩)⟩
  | neg =>
    -- hsf says: (Sign.neg = Sign.pos → ...) ∧ (Sign.neg = Sign.neg → BoolEvaluate v form = false)
    have hfalse : BoolEvaluate v form = false := hsf.2 rfl
    -- Case split on formula structure
    cases form with
    | atom x =>
      show True; trivial
    | bot =>
      show True; trivial
    | and a b_form =>
      -- classicalApplyOne ⟨.neg, .and a b, l⟩ = .branching [[F(a)], [F(b)]]
      change ∃ br ∈ [[SignedFormula.neg a label], [SignedFormula.neg b_form label]],
        classicalBranchSatisfiable (Branch.extendMany b br)
      rw [BoolEvaluate_and] at hfalse
      simp only [Bool.and_eq_false_iff] at hfalse
      rcases hfalse with ha | hb
      · exact ⟨[SignedFormula.neg a label], List.mem_cons_self,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun h => absurd h (by simp [SignedFormula.neg]), fun _ => ha⟩)⟩
      · exact ⟨[SignedFormula.neg b_form label], by simp,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun h => absurd h (by simp [SignedFormula.neg]), fun _ => hb⟩)⟩
    | or a b_form =>
      -- classicalApplyOne ⟨.neg, .or a b, l⟩ = .linear [F(a), F(b)]
      change classicalBranchSatisfiable (Branch.extendMany b
        [SignedFormula.neg a label, SignedFormula.neg b_form label])
      rw [BoolEvaluate_or] at hfalse
      simp only [Bool.or_eq_false_iff] at hfalse
      apply extend_sat
      intro sf' hmem'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      rcases hmem' with rfl | rfl
      · exact ⟨fun h => absurd h (by simp [SignedFormula.neg]), fun _ => hfalse.1⟩
      · exact ⟨fun h => absurd h (by simp [SignedFormula.neg]), fun _ => hfalse.2⟩
    | imp a b_form =>
      by_cases hbot : b_form = .bot
      · subst hbot
        -- classicalApplyOne ⟨.neg, .imp a .bot, l⟩ = .linear [T(a)]  (negNeg rule)
        change classicalBranchSatisfiable (Branch.extendMany b [SignedFormula.pos a label])
        rw [BoolEvaluate_imp, BoolEvaluate_bot, Bool.or_false] at hfalse
        -- hfalse : !BoolEvaluate v a = false, i.e., BoolEvaluate v a = true
        have ha : BoolEvaluate v a = true := (Bool.not_eq_false' _).mp hfalse
        apply extend_sat
        intro sf' hmem'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        subst hmem'
        exact ⟨fun _ => ha, fun h => absurd h (by simp [SignedFormula.pos])⟩
      · -- classicalApplyOne ⟨.neg, .imp a b, l⟩ = .linear [T(a), F(b)]  (negImp rule)
        -- Case split on b_form to reduce classicalApplyOne (abstract b_form won't reduce)
        cases b_form with
        | bot => exact absurd rfl hbot
        | atom x =>
          change classicalBranchSatisfiable (Branch.extendMany b
            [SignedFormula.pos a label, SignedFormula.neg (.atom x) label])
          rw [BoolEvaluate_imp] at hfalse; rw [Bool.or_eq_false_iff] at hfalse
          obtain ⟨h1, h2⟩ := hfalse
          have ha : BoolEvaluate v a = true := (Bool.not_eq_false' _).mp h1
          apply extend_sat; intro sf' hmem'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | rfl
          · exact ⟨fun _ => ha, fun h => absurd h (Sign.noConfusion)⟩
          · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => h2⟩
        | imp c d =>
          change classicalBranchSatisfiable (Branch.extendMany b
            [SignedFormula.pos a label, SignedFormula.neg (.imp c d) label])
          rw [BoolEvaluate_imp] at hfalse; rw [Bool.or_eq_false_iff] at hfalse
          obtain ⟨h1, h2⟩ := hfalse
          have ha : BoolEvaluate v a = true := (Bool.not_eq_false' _).mp h1
          apply extend_sat; intro sf' hmem'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | rfl
          · exact ⟨fun _ => ha, fun h => absurd h (Sign.noConfusion)⟩
          · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => h2⟩
        | and c d =>
          change classicalBranchSatisfiable (Branch.extendMany b
            [SignedFormula.pos a label, SignedFormula.neg (.and c d) label])
          rw [BoolEvaluate_imp] at hfalse; rw [Bool.or_eq_false_iff] at hfalse
          obtain ⟨h1, h2⟩ := hfalse
          have ha : BoolEvaluate v a = true := (Bool.not_eq_false' _).mp h1
          apply extend_sat; intro sf' hmem'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | rfl
          · exact ⟨fun _ => ha, fun h => absurd h (Sign.noConfusion)⟩
          · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => h2⟩
        | or c d =>
          change classicalBranchSatisfiable (Branch.extendMany b
            [SignedFormula.pos a label, SignedFormula.neg (.or c d) label])
          rw [BoolEvaluate_imp] at hfalse; rw [Bool.or_eq_false_iff] at hfalse
          obtain ⟨h1, h2⟩ := hfalse
          have ha : BoolEvaluate v a = true := (Bool.not_eq_false' _).mp h1
          apply extend_sat; intro sf' hmem'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with rfl | rfl
          · exact ⟨fun _ => ha, fun h => absurd h (Sign.noConfusion)⟩
          · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => h2⟩

/-- A classically closed branch is unsatisfiable.

Classical closure holds when T(⊥) is present (which is never satisfiable) or when
T(φ) and F(φ) coexist (which forces `BoolEvaluate v φ = true` and `= false` simultaneously). -/
lemma classically_closed_unsatisfiable (b : Branch (Proposition Atom) Unit)
    (hclosed : isClassicallyClosed b = true) :
    ¬ classicalBranchSatisfiable b := by
  intro ⟨v, hv⟩
  have hrewrite : isClassicallyClosed b =
      (match b.find? (fun sf => sf.isPos &&
        sf.formula == (HasBot.bot : Proposition Atom)) with
      | some _ => true
      | none => b.hasContradiction) := by
    simp only [isClassicallyClosed, ClosureCondition.isClosed, ClosureCondition.findClosure]
    cases b.find? (fun sf => sf.isPos &&
        sf.formula == (HasBot.bot : Proposition Atom)) with
    | some sf => rfl
    | none => simp only [Branch.hasContradiction]; cases b.findContradiction <;> rfl
  rw [hrewrite] at hclosed
  cases hfind : b.find? (fun sf =>
      sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) with
  | some sf =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true] at hpred
    obtain ⟨hpos, hbot_eq⟩ := hpred
    obtain ⟨sign, form, label⟩ := sf
    simp only [SignedFormula.isPos, Sign.isPos] at hpos
    cases sign with
    | neg => contradiction
    | pos =>
      have hvc := hv ⟨.pos, form, label⟩ hmem
      have htrue := hvc.1 rfl
      have hfb := prop_beq_eq _ _ hbot_eq
      simp only [SignedFormula.formula] at hfb
      rw [hfb] at htrue
      rw [show (HasBot.bot : Proposition Atom) = .bot from rfl,
        BoolEvaluate_bot] at htrue
      exact absurd htrue Bool.false_ne_true
  | none =>
    simp [hfind] at hclosed
    simp only [Branch.hasContradiction, Option.isSome_iff_exists] at hclosed
    obtain ⟨⟨phi, l⟩, hpair⟩ := hclosed
    simp only [Branch.findContradiction] at hpair
    obtain ⟨sf, hsfmem, hsfcond⟩ :=
      List.exists_of_findSome?_eq_some hpair
    have hpos : sf.isPos = true := by
      by_contra h; simp only [Bool.not_eq_true] at h; simp [h] at hsfcond
    simp only [hpos, ite_true, Option.ite_some_none_eq_some] at hsfcond
    obtain ⟨hany, hphi_eq⟩ := hsfcond
    obtain ⟨sign, form, label⟩ := sf
    simp only [SignedFormula.isPos, Sign.isPos] at hpos
    have hsign : sign = .pos := by cases sign <;> simp_all
    subst hsign
    have htrue := (hv ⟨.pos, form, label⟩ hsfmem).1 rfl
    obtain ⟨sf_neg, hsfneg_mem, hsfneg_cond⟩ :=
      List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, Bool.and_eq_true] at hsfneg_cond
    obtain ⟨⟨hsneg, hformEq⟩, _⟩ := hsfneg_cond
    have hfeq := prop_beq_eq _ _ hformEq
    obtain ⟨sign', form', label'⟩ := sf_neg
    simp only at hfeq
    have hsn : sign' = .neg := by
      change (sign' == .neg) = true at hsneg
      cases sign' with
      | neg => rfl
      | pos => change false = true at hsneg; exact absurd hsneg Bool.false_ne_true
    have hfalse := (hv ⟨sign', form', label'⟩ hsfneg_mem).2
      (by rw [hsn])
    rw [hfeq] at hfalse
    exact absurd htrue (Bool.eq_false_iff.mp hfalse)

/-! ## Main Soundness Theorem -/

/-- **Classical Tableau Soundness**: If the classical tableau closes on `φ`,
then `φ` is a classical tautology.

The proof proceeds by contrapositive: if `φ` is not a tautology, there is a Boolean
valuation `v` with `BoolEvaluate v φ = false`. The initial branch `[F(φ)]` is satisfiable
via `v`. By `classicalRule_preserves_sat`, no branch can become unsatisfiable through rule
applications. By `classically_closed_unsatisfiable`, no satisfiable branch can close.
Hence the tableau cannot return `closed`, contradiction.

NOTE: The formal loop induction is marked sorry; the `Decidable` instance in
`DecisionProcedure.lean` uses the existing Boolean enumeration for classical logic. -/
theorem classicalTableau_sound (φ : Proposition Atom)
    (h : classicalTableau φ = .closed) : Tautology φ := by
  sorry

end Cslib.Logic.PL

end
