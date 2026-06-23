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
      · sorry

/-- A classically closed branch is unsatisfiable.

Classical closure holds when T(⊥) is present (which is never satisfiable) or when
T(φ) and F(φ) coexist (which forces `BoolEvaluate v φ = true` and `= false` simultaneously). -/
lemma classically_closed_unsatisfiable (b : Branch (Proposition Atom) Unit)
    (hclosed : isClassicallyClosed b = true) :
    ¬ classicalBranchSatisfiable b := by
  sorry
  /-  intro ⟨v, hv⟩
  -- isClassicallyClosed b is definitionally equal to b.hasBotPos || b.hasContradiction
  -- because isClassicallyClosed uses ClassicalClosure which checks find? then findContradiction
  -- Extract the closure condition: either T(bot) present or T(phi)/F(phi) pair
  -- isClassicallyClosed uses ClassicalClosure, which checks hasBotPos then hasContradiction
  -- Use by_cases on hasBotPos to avoid typeclass instance resolution issues
  have hkey : b.hasBotPos ∨ b.hasContradiction := by
    by_cases hbf : b.hasBotPos = true
    · exact Or.inl hbf
    · right
      -- b.hasBotPos = false, so b.find? (...bot...) = none
      simp only [Branch.hasBotPos, Bool.not_eq_true] at hbf
      -- findContradiction must be some (otherwise ClassicalClosure returns false, contradiction)
      by_contra hcontra
      simp only [Branch.hasContradiction, Bool.not_eq_true, Option.not_isSome_iff_eq_none] at hcontra
      -- Both conditions false: isClassicallyClosed b should be false
      -- The definition: isClassicallyClosed = open ClassicalClosure in ClosureCondition.isClosed
      -- ClassicalClosure.isClosed = (ClassicalClosure.findClosure b).isSome
      -- ClassicalClosure.findClosure b = match b.find? (...bot...) with | some sf => ... | none =>
      --   match b.findContradiction with | some ... => ... | none => none
      -- With hbf (b.any (...bot...) = false → b.find? (...) = none) and hcontra (findContradiction = none)
      -- ClassicalClosure.findClosure b = none, so isClassicallyClosed b = false
      -- Contradiction with hclosed
      -- We use: the match structure of ClassicalClosure.findClosure with simp + the list.find? none condition
      simp only [Bool.not_eq_true] at hbf
      have hfind_none : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) = none := by
        rwa [List.find?_eq_none]
        intro sf hmem hcond
        simp only [Bool.and_eq_true] at hcond
        simp only [List.any_eq_false] at hbf
        exact absurd hcond.1 (by
          have := hbf sf hmem
          simp only [Bool.and_eq_true, Bool.not_and_eq_true_iff_not_left_or_not_right] at this
          -- this says: NOT (sf.isPos && sf.formula == bot)
          rcases this with h | h
          · simp [h] at hcond
          · simp [hcond.2] at h)
      -- Now ClassicalClosure.findClosure b = none
      -- isClassicallyClosed b = false, contradiction
      have : isClassicallyClosed b = false := by
        simp only [isClassicallyClosed, ClosureCondition.isClosed, Option.isSome]
        -- ClassicalClosure.findClosure b, with explicit instance, returns none
        -- We avoid using ClosureCondition.findClosure (wrong instance) by using hfind_none and hcontra
        -- Prove: (ClassicalClosure.findClosure b).isSome = false
        -- The match structure: ... hfind_none ... hcontra => none
        -- Use that isClassicallyClosed b = b.hasBotPos || b.hasContradiction via the ClassicalClosure def
        -- isClassicallyClosed b defined as: open ClassicalClosure in ClosureCondition.isClosed b
        -- ClassicalClosure.isClosed b = (ClassicalClosure.findClosure b).isSome
        -- ClassicalClosure.findClosure b = match b.find? ... with ... | none => match findContradiction with | none => none
        -- So isSome = false when both are none
        -- We can't directly use ClosureCondition.findClosure (wrong instance resolution)
        -- But we CAN convert: isClassicallyClosed b uses ClassicalClosure's isClosed
        -- After `simp only [isClassicallyClosed, ClosureCondition.isClosed, Option.isSome]`,
        -- we get the exact match expression from ClassicalClosure (not MinimalClosure)
        -- because ClosureCondition.isClosed was inlined from ClassicalClosure at def time.
        -- Let's try to prove it's false using split:
        split
        · rename_i cr hcr
          -- hcr : ClosureCondition.findClosure b = some cr
          -- This should be ClassicalClosure's (since we unfolded isClassicallyClosed)
          -- We now split on hfind_none vs hcontra:
          -- ClassicalClosure.findClosure matches b.find? (...) first
          -- With hfind_none, it goes to the none arm -> matches findContradiction = hcontra = none
          -- So findClosure = none, but hcr says some. Contradiction.
          -- Unfortunately the instance issue makes this hard. Let's just show False
          -- by deriving that isClassicallyClosed b = false from an indirect argument:
          -- We just need to show hcr leads to contradiction with hfind_none and hcontra
          -- The ONLY way hcr can hold is if b.find? (...) ≠ none OR b.findContradiction ≠ none
          -- Since we know both are none (hfind_none, hcontra), hcr must be false
          -- Use the contrapositive computation:
          -- hcr is the ClassicalClosure findClosure result. If we could unfold it here...
          -- Try: directly show None = some cr is absurd by extracting the structure
          -- After split, hcr is from the match on ClassicalClosure's findClosure
          -- match b.find? (...) with | some sf => some (.botPos sf.label) | none =>
          --   match b.findContradiction with | some (phi, l) => some (.contradiction phi l) | none => none
          -- = some cr
          -- We know b.find? (...) = none (from hfind_none)
          -- And b.findContradiction = none (from hcontra)
          -- So the match reduces to: none = some cr. But wait...
          -- The split is on the COMPUTED value of ClosureCondition.findClosure b
          -- After simp only [isClassicallyClosed, ClosureCondition.isClosed, Option.isSome],
          -- the exact ClassicalClosure match expression appears in hclosed.
          -- The split at this point splits this exact ClassicalClosure match.
          -- So hcr : (ClassicalClosure's findClosure logic) = some cr
          -- We can now directly use hfind_none and hcontra:
          simp only [hfind_none, hcontra] at hcr
          -- After rewriting hfind_none (b.find? = none) and hcontra (findContradiction = none)
          -- in hcr, we should get none = some cr which simp closes
        · rfl
      simp [this] at hclosed
  rcases hkey with hbot | hcontra
  · -- Case 1: T(bot) is present on the branch
    simp only [Branch.hasBotPos] at hbot
    obtain ⟨sf, hmem, hcond⟩ := List.any_eq_true.mp hbot
    simp only [Bool.and_eq_true, SignedFormula.isPos, Sign.isPos] at hcond
    obtain ⟨hpos, hbot_form⟩ := hcond
    have hssign : sf.sign = .pos := by cases sf.sign <;> simp_all
    have hformbot : sf.formula = .bot := by simp only [beq_iff_eq] at hbot_form; exact hbot_form
    have hvc := hv sf hmem
    rw [hssign] at hvc
    have htrue := hvc.1 rfl
    rw [hformbot] at htrue
    simp [BoolEvaluate_bot] at htrue
  · -- Case 2: T(phi) and F(phi) are both on the branch
    simp only [Branch.hasContradiction, Option.isSome_eq_true] at hcontra
    rw [Option.isSome_iff_exists] at hcontra
    obtain ⟨⟨phi, l⟩, hpair⟩ := hcontra
    simp only [Branch.findContradiction] at hpair
    obtain ⟨sf, hsfmem, hsfcond⟩ := List.findSome?_some hpair
    simp only [ite_some_none_eq_some] at hsfcond
    obtain ⟨hpos, hany, _⟩ := hsfcond
    simp only [Bool.and_eq_true, SignedFormula.isPos, Sign.isPos] at hpos
    obtain ⟨sf', hsfmem', hsfcond'⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfcond'
    obtain ⟨⟨hsneg, hformEq⟩, _⟩ := hsfcond'
    have hssign : sf.sign = .pos := by cases sf.sign <;> simp_all
    have hTphi := hv sf hsfmem
    have hFphi := hv sf' hsfmem'
    rw [hssign] at hTphi
    rw [hsneg] at hFphi
    have htrue := hTphi.1 rfl
    have hfalse := hFphi.2 rfl
    rw [hformEq] at hfalse
    simp_all  -/

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
