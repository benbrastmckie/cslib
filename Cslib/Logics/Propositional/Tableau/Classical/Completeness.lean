/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Classical.Soundness

/-! # Classical Tableau Completeness

This module proves completeness of the classical propositional tableau: if `φ` is a
classical tautology, then the tableau closes on `φ`.

## Main Results

- `classicalOpenBranch_countermodel`: An open saturated branch yields a Boolean countermodel.
- `classicalTableau_complete`: If `Tautology φ`, then `classicalTableau φ = closed`.

## Strategy

By contrapositive: if the tableau returns `openBranch b`, then `b` is an open saturated
branch from which we extract a Boolean valuation:
  `v p = true ↔ T(atom p) is on branch b`

We define the classical Hintikka set condition (`classicalHintikkaSet`): every compound
formula on the branch has its rule outputs also on the branch (for linear rules: all outputs;
for branching rules: at least one full branch). The truth lemma proves by formula induction
that `extractValuation b` satisfies all T-formulas and falsifies all F-formulas on `b`.

When `classicalTableau φ = openBranch b`, we prove `b` is a classical Hintikka set by the
loop invariant: the expansion loop preserves Hintikka membership via `extendMany`.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Countermodel Extraction -/

/-- Extract a Boolean valuation from an open saturated branch.

An atom `p` is assigned `true` iff T(atom p) appears on the branch.
Saturatedness ensures this valuation is consistent with all signed formulas. -/
def extractValuation (b : Branch (Proposition Atom) Unit) : BoolValuation Atom :=
  fun p => b.any fun sf => sf.sign == .pos && sf.formula == .atom p

/-! ## Classical Hintikka Set -/

/-- A branch is a classical Hintikka set if it is open and every signed formula on the branch
has its rule outputs also present on the branch.

For linear rules (alpha-rules), all outputs must be on the branch.
For branching rules (beta-rules), at least one complete set of branch outputs is on the branch.

This condition captures exactly what the expansion loop guarantees for a returned open branch. -/
def classicalHintikkaSet (b : Branch (Proposition Atom) Unit) : Prop :=
  isClassicallyClosed b = false ∧
  ∀ sf ∈ b,
    match classicalApplyOne sf with
    | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
    | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
    | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
    | .notApplicable => True

/-! ## Truth Lemma -/

/-- Truth lemma for the extracted valuation.

If `b` is a classical Hintikka set (every signed formula has its rule outputs on `b`),
then the valuation `extractValuation b` satisfies every T(φ) on `b` and falsifies every F(φ)
on `b`. Proof by induction on the structure of `φ`. -/
lemma classicalTruthLemma (b : Branch (Proposition Atom) Unit)
    (hH : classicalHintikkaSet b)
    (φ : Proposition Atom) :
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ) →
      BoolEvaluate (extractValuation b) φ = true) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ) →
      BoolEvaluate (extractValuation b) φ = false) := by
  obtain ⟨hopen, hrule⟩ := hH
  induction φ with
  | atom p =>
    constructor
    · -- T(atom p) on branch → extractValuation b p = true
      intro hmem
      simp only [BoolEvaluate_atom, extractValuation]
      exact hmem
    · -- F(atom p) on branch → extractValuation b p = false
      intro hmem
      simp only [BoolEvaluate_atom, extractValuation]
      -- If T(atom p) ∈ b, then T/F contradiction makes b closed
      by_contra h
      simp only [Bool.not_eq_false] at h
      -- h : T(atom p) ∈ b; together with F(atom p) ∈ b gives closed branch
      obtain ⟨sf_pos, hsfpos_mem, hsfpos_cond⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true] at hsfpos_cond
      obtain ⟨sf_neg, hsfneg_mem, hsfneg_cond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfneg_cond
      have hpos_sign : sf_pos.sign = .pos := eq_of_beq hsfpos_cond.1
      have hneg_sign : sf_neg.sign = .neg := eq_of_beq hsfneg_cond.1
      have hpos_form : sf_pos.formula = .atom p := eq_of_beq hsfpos_cond.2
      have hneg_form : sf_neg.formula = .atom p := eq_of_beq hsfneg_cond.2
      have hcont : b.hasContradiction = true := by
        simp only [Branch.hasContradiction, Branch.findContradiction, Option.isSome]
        cases hfind : b.findSome? (fun sf =>
            if sf.isPos then
              if b.any fun sf' => sf'.sign == .neg && sf'.formula == sf.formula && sf'.label == sf.label
              then some (sf.formula, sf.label)
              else none
            else none) with
        | some _ => rfl
        | none =>
          exfalso
          simp only [List.findSome?_eq_none_iff] at hfind
          have h_none := hfind sf_pos hsfpos_mem
          simp only [hpos_sign, SignedFormula.isPos, Sign.isPos, ite_true] at h_none
          simp only [ite_eq_right_iff] at h_none
          have h_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == sf_pos.formula &&
              sf'.label == sf_pos.label) = true := by
            apply List.any_eq_true.mpr
            exact ⟨sf_neg, hsfneg_mem, by simp [hneg_sign, hpos_form, hneg_form]⟩
          exact absurd (h_none h_any) (by simp)
      have hclosed : isClassicallyClosed b = true := by
        simp only [isClassicallyClosed, ClosureCondition.isClosed, ClosureCondition.findClosure,
          Option.isSome_iff_exists]
        simp only [Branch.hasContradiction, Option.isSome_iff_exists] at hcont
        obtain ⟨⟨phi, l⟩, hfind⟩ := hcont
        cases hfind_bot : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) with
        | some sf => exact ⟨_, rfl⟩
        | none => exact ⟨_, by rw [hfind]⟩
      simp [hclosed] at hopen
  | bot =>
    constructor
    · -- T(bot) on branch → contradiction with hopen
      intro hmem
      exfalso
      have hclosed : isClassicallyClosed b = true := by
        simp only [isClassicallyClosed, ClosureCondition.isClosed, ClosureCondition.findClosure,
          Option.isSome_iff_exists]
        obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
        simp only [Bool.and_eq_true] at hsfcond
        have hsign : sf.sign = .pos := eq_of_beq hsfcond.1
        have hbot_form : sf.formula = (HasBot.bot : Proposition Atom) := eq_of_beq hsfcond.2
        have hpred : (sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) = true := by
          simp [SignedFormula.isPos, hsign, Sign.isPos, hbot_form]
        cases hf : b.find? (fun sf' => sf'.isPos && sf'.formula == (HasBot.bot : Proposition Atom)) with
        | none =>
          exfalso
          have hsome : (b.find? (fun sf' => sf'.isPos && sf'.formula == (HasBot.bot : Proposition Atom))).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨sf, hsfmem, hpred⟩
          simp [hf] at hsome
        | some sf' => exact ⟨.botPos sf'.label, rfl⟩
      simp [hclosed] at hopen
    · -- F(bot) on branch → BoolEvaluate ... bot = false
      intro _
      simp [BoolEvaluate_bot]
  | imp a c ih_a ih_c =>
    constructor
    · -- T(imp a c) on branch → BoolEvaluate v (imp a c) = true
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .pos := eq_of_beq hsfcond.1
      have hform : sf.formula = .imp a c := eq_of_beq hsfcond.2
      -- The rule for T(imp a c) is branching: [F(a)] or [T(c)]
      -- By the Hintikka condition, one of these branches is in b
      have hout := hrule sf hsfmem
      cases hbot : c with
      | bot =>
        -- T(imp a bot) = T(neg a): negPos rule gives .linear [F(a)]
        have hca : classicalApplyOne sf = .linear [SignedFormula.neg a sf.label] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        -- F(a) ∈ b
        have hfa_mem : SignedFormula.neg a sf.label ∈ b :=
          hout _ List.mem_cons_self
        have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true := by
          apply List.any_eq_true.mpr
          exact ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
        rw [BoolEvaluate_imp, BoolEvaluate_bot]
        simp [ih_a.2 hfa_any]
      | atom x =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.atom x) sf.label]] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · -- br = [F(a)], so F(a) ∈ b
          have hfa_mem := hbr _ List.mem_cons_self
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · -- br = [T(atom x)], so T(atom x) ∈ b
          have htc_mem := hbr _ List.mem_cons_self
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .atom x) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          have htval := ih_c.1 (hbot ▸ htc_any)
          rw [hbot] at htval
          rw [htval]; simp
      | imp b1 b2 =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.imp b1 b2) sf.label]] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · have hfa_mem := hbr _ List.mem_cons_self
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · have htc_mem := hbr _ List.mem_cons_self
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .imp b1 b2) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          have htval := ih_c.1 (hbot ▸ htc_any)
          rw [hbot] at htval
          rw [htval]; simp
      | and b1 b2 =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.and b1 b2) sf.label]] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · have hfa_mem := hbr _ List.mem_cons_self
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · have htc_mem := hbr _ List.mem_cons_self
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .and b1 b2) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          have htval := ih_c.1 (hbot ▸ htc_any)
          rw [hbot] at htval
          rw [htval]; simp
      | or b1 b2 =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.or b1 b2) sf.label]] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · have hfa_mem := hbr _ List.mem_cons_self
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · have htc_mem := hbr _ List.mem_cons_self
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .or b1 b2) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          have htval := ih_c.1 (hbot ▸ htc_any)
          rw [hbot] at htval
          rw [htval]; simp
    · -- F(imp a c) on branch → BoolEvaluate v (imp a c) = false
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .neg := eq_of_beq hsfcond.1
      have hform : sf.formula = .imp a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      -- The impNeg rule (and negNeg) gives .linear outputs
      -- F(imp a c): either T(a) and F(c) (impNeg) or T(a) (negNeg if c = bot)
      cases hbot : c with
      | bot =>
        -- F(imp a bot) = F(neg a): negNeg rule gives .linear [T(a)]
        have hca : classicalApplyOne sf = .linear [SignedFormula.pos a sf.label] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        -- T(a) ∈ b
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ List.mem_cons_self
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hta := ih_a.1 hta_any
        -- BoolEvaluate v (imp a bot) = !true || false = false
        rw [BoolEvaluate_imp, hta, BoolEvaluate_bot]; simp
      | atom x =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.atom x) sf.label] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.atom x) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .atom x) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        have hcval := ih_c.2 (hbot ▸ hfc_any)
        rw [hbot] at hcval
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hcval]; simp
      | imp b1 b2 =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.imp b1 b2) sf.label] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.imp b1 b2) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .imp b1 b2) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        have hcval := ih_c.2 (hbot ▸ hfc_any)
        rw [hbot] at hcval
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hcval]; simp
      | and b1 b2 =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.and b1 b2) sf.label] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.and b1 b2) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .and b1 b2) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        have hcval := ih_c.2 (hbot ▸ hfc_any)
        rw [hbot] at hcval
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hcval]; simp
      | or b1 b2 =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.or b1 b2) sf.label] := by
          obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.or b1 b2) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .or b1 b2) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        have hcval := ih_c.2 (hbot ▸ hfc_any)
        rw [hbot] at hcval
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hcval]; simp
  | and a c ih_a ih_c =>
    constructor
    · -- T(and a c) on branch → BoolEvaluate v (and a c) = true
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .pos := eq_of_beq hsfcond.1
      have hform : sf.formula = .and a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .linear [SignedFormula.pos a sf.label, SignedFormula.pos c sf.label] := by
        obtain ⟨s, fm, l⟩ := sf; subst hsign hform; rfl
      rw [hca] at hout
      have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
      have htc_mem : SignedFormula.pos c sf.label ∈ b := hout _ (by simp)
      have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
        List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
      have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == c) = true :=
        List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
      simp [BoolEvaluate_and, ih_a.1 hta_any, ih_c.1 htc_any]
    · -- F(and a c) on branch → BoolEvaluate v (and a c) = false
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .neg := eq_of_beq hsfcond.1
      have hform : sf.formula = .and a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .branching [[SignedFormula.neg a sf.label], [SignedFormula.neg c sf.label]] := by
        obtain ⟨s, fm, l⟩ := sf; subst hsign hform; rfl
      rw [hca] at hout
      obtain ⟨br, hbr_mem, hbr⟩ := hout
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
      rcases hbr_mem with rfl | rfl
      · have hfa_mem := hbr _ List.mem_cons_self
        have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
        simp [BoolEvaluate_and, ih_a.2 hfa_any]
      · have hfc_mem := hbr _ List.mem_cons_self
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == c) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        simp [BoolEvaluate_and, ih_c.2 hfc_any]
  | or a c ih_a ih_c =>
    constructor
    · -- T(or a c) on branch → BoolEvaluate v (or a c) = true
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .pos := eq_of_beq hsfcond.1
      have hform : sf.formula = .or a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .branching [[SignedFormula.pos a sf.label], [SignedFormula.pos c sf.label]] := by
        obtain ⟨s, fm, l⟩ := sf; subst hsign hform; rfl
      rw [hca] at hout
      obtain ⟨br, hbr_mem, hbr⟩ := hout
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
      rcases hbr_mem with rfl | rfl
      · have hta_mem := hbr _ List.mem_cons_self
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        simp [BoolEvaluate_or, ih_a.1 hta_any]
      · have htc_mem := hbr _ List.mem_cons_self
        have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == c) = true :=
          List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
        simp [BoolEvaluate_or, ih_c.1 htc_any]
    · -- F(or a c) on branch → BoolEvaluate v (or a c) = false
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .neg := eq_of_beq hsfcond.1
      have hform : sf.formula = .or a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .linear [SignedFormula.neg a sf.label, SignedFormula.neg c sf.label] := by
        obtain ⟨s, fm, l⟩ := sf; subst hsign hform; rfl
      rw [hca] at hout
      have hfa_mem : SignedFormula.neg a sf.label ∈ b := hout _ (by simp)
      have hfc_mem : SignedFormula.neg c sf.label ∈ b := hout _ (by simp)
      have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
        List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
      have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == c) = true :=
        List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
      simp [BoolEvaluate_or, ih_a.2 hfa_any, ih_c.2 hfc_any]

/-! ## Hintikka Property of Open Branches -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extending a branch preserves membership: if sf ∈ b then sf ∈ extendMany b newForms. -/
private lemma mem_extendMany_of_mem (b : Branch (Proposition Atom) Unit)
    (newForms : List (SignedFormula (Proposition Atom) Unit))
    (sf : SignedFormula (Proposition Atom) Unit)
    (hmem : sf ∈ b) : sf ∈ Branch.extendMany b newForms := by
  simp only [Branch.extendMany, List.mem_append]
  exact Or.inr hmem

omit [DecidableEq Atom] [Hashable Atom] in
/-- The Hintikka rule condition for a branch b lifted to an extended branch b' = b ++ newForms.

If every formula in `e` satisfies the Hintikka condition w.r.t. `b`, and `b ⊆ b'`,
then every formula in `e` satisfies the Hintikka condition w.r.t. `b'`. -/
private lemma hintikka_inv_mono (b b' : Branch (Proposition Atom) Unit)
    (hsub : ∀ sf ∈ b, sf ∈ b')
    (e : List (SignedFormula (Proposition Atom) Unit))
    (hH : ∀ sf ∈ e, match classicalApplyOne sf with
        | .linear out => ∀ sf' ∈ out, sf' ∈ b
        | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b
        | .persistent out => ∀ sf' ∈ out, sf' ∈ b
        | .notApplicable => True) :
    ∀ sf ∈ e, match classicalApplyOne sf with
        | .linear out => ∀ sf' ∈ out, sf' ∈ b'
        | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b'
        | .persistent out => ∀ sf' ∈ out, sf' ∈ b'
        | .notApplicable => True := by
  intro sf hmem
  have h := hH sf hmem
  cases hca : classicalApplyOne sf with
  | linear out => rw [hca] at h; intro sf' hmem'; exact hsub _ (h sf' hmem')
  | branching brs =>
    rw [hca] at h
    obtain ⟨br, hbr_mem, hbr⟩ := h
    exact ⟨br, hbr_mem, fun sf' hmem' => hsub _ (hbr sf' hmem')⟩
  | persistent out => rw [hca] at h; intro sf' hmem'; exact hsub _ (h sf' hmem')
  | notApplicable => trivial

/-- The open branch returned by `classicalExpandBranches` is a classical Hintikka set.

The proof is by induction on fuel with an inner induction on the pending list, tracking
the Hintikka invariant: for every pair (b, e) in the list, the Hintikka condition holds
for all formulas in b that were expanded (are in e), and the rule outputs are in b.

Technical note: This requires the full loop invariant for `classicalExpandBranches`. -/
private lemma classicalExpandBranches_hintikka (fuel : Nat) :
    ∀ (branches : List (Branch (Proposition Atom) Unit))
      (expandedSets : List (List (SignedFormula (Proposition Atom) Unit))),
      expandedSets.length = branches.length →
      -- Invariant: each branch satisfies Hintikka for its expanded formulas
      (∀ i (b : Branch (Proposition Atom) Unit) (e : List (SignedFormula (Proposition Atom) Unit)),
        List.getElem? branches i = some b → List.getElem? expandedSets i = some e →
        ∀ sf ∈ e, match classicalApplyOne sf with
          | .linear out => ∀ sf' ∈ out, sf' ∈ b
          | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b
          | .persistent out => ∀ sf' ∈ out, sf' ∈ b
          | .notApplicable => True) →
      ∀ b, classicalExpandBranches branches expandedSets fuel = .openBranch b →
        classicalHintikkaSet b := by
  sorry

/-- Any formula on a branch is still present on every branch produced by `classicalStepBranch`.
Uses `Branch.extendMany b x = x ++ b`. -/
private lemma classicalStepBranch_mem_preserved
    (b : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit))
    (sf : SignedFormula (Proposition Atom) Unit)
    (hsfb : sf ∈ b)
    (newBs : List (Branch (Proposition Atom) Unit))
    (newExp : List (SignedFormula (Proposition Atom) Unit))
    (hstep : classicalStepBranch b e = some (newBs, newExp)) :
    ∀ b' ∈ newBs, sf ∈ b' := by
  -- classicalStepBranch finds sf' ∈ b with classicalApplyOne sf' ≠ notApplicable,
  -- producing newBs from extendMany b applied to the rule output.
  -- In all cases, every b' ∈ newBs is extendMany b x = x ++ b, so sf ∈ b → sf ∈ b'.
  simp only [classicalStepBranch] at hstep
  obtain ⟨sf', hb'_mem, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hexp
  · -- hfound : (match classicalApplyOne sf' with ...) = some (newBs, newExp)
    -- split on classicalApplyOne result
    rcases hca : classicalApplyOne sf' with out | brs | out | _
    all_goals simp only [hca] at hfound
    · -- linear: newBs = [extendMany b out]
      obtain ⟨rfl, _⟩ := Option.some.inj hfound
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      simp only [Branch.extendMany, List.mem_append]
      exact Or.inr hsfb
    · -- branching: newBs = brs.map (extendMany b ·)
      obtain ⟨rfl, _⟩ := Option.some.inj hfound
      intro b' hb'
      obtain ⟨br, _, rfl⟩ := List.mem_map.mp hb'
      simp only [Branch.extendMany, List.mem_append]
      exact Or.inr hsfb
    · -- persistent: newBs = [extendMany b out]
      obtain ⟨rfl, _⟩ := Option.some.inj hfound
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      simp only [Branch.extendMany, List.mem_append]
      exact Or.inr hsfb
    · -- notApplicable: none — but hfound says some
      simp at hfound

/-- Every formula in every initial branch appears in the open branch returned by
`classicalExpandBranches`. Used to show F(φ) is on the countermodel branch. -/
private lemma classicalExpandBranches_openBranch_initial_mem (fuel : Nat)
    (sf : SignedFormula (Proposition Atom) Unit) :
    ∀ (branches : List (Branch (Proposition Atom) Unit))
      (expandedSets : List (List (SignedFormula (Proposition Atom) Unit))),
      expandedSets.length = branches.length →
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ b, classicalExpandBranches branches expandedSets fuel = .openBranch b →
        sf ∈ b := by
  induction fuel with
  | zero =>
    intro branches expandedSets _ hAll b h
    simp only [classicalExpandBranches] at h
    -- h comes from: match findSome? ... with | some b' => .openBranch b' | none => .closed
    -- Split on findSome? result
    cases hfs : branches.findSome? (fun b' => if isClassicallyClosed b' then none else some b') with
    | none =>
      simp only [hfs] at h
      exact absurd h (by simp)
    | some b' =>
      simp only [hfs] at h
      injection h with heq
      subst heq
      obtain ⟨b₀, hb₀_mem, hf⟩ := List.exists_of_findSome?_eq_some hfs
      by_cases hcl : isClassicallyClosed b₀ = true
      · -- hf : none = some b' when closed — contradiction
        simp only [hcl, ite_true] at hf
        -- hf is now none = some b', which is False
        exact absurd hf (by simp)
      · -- hf : some b₀ = some b' when not closed
        simp only [Bool.not_eq_true] at hcl
        have hfval : b₀ = b' := by simp only [hcl, ite_false] at hf; exact Option.some.inj hf
        exact hfval ▸ hAll b₀ hb₀_mem
  | succ fuel' ih =>
    intro branches expandedSets hlength hAll b h
    -- Key inner lemma: if every branch in pending has sf, then sf ∈ result open branch.
    -- We track both pending and done, with sf in all of them.
    suffices key : ∀ (pending : List (Branch (Proposition Atom) Unit))
        (pendingExp : List (List (SignedFormula (Proposition Atom) Unit)))
        (done : List (Branch (Proposition Atom) Unit))
        (doneExp : List (List (SignedFormula (Proposition Atom) Unit))),
        pendingExp.length = pending.length →
        doneExp.length = done.length →
        (∀ bp ∈ pending, sf ∈ bp) →
        (∀ bd ∈ done, sf ∈ bd) →
        classicalExpandBranches.processNext fuel' pending pendingExp done doneExp = .openBranch b →
        sf ∈ b from
      key branches expandedSets [] [] hlength rfl hAll (by simp)
        (by simpa [classicalExpandBranches] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp done doneExp _ _ _ _ hinner
      simp [classicalExpandBranches.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp done doneExp hlength_p hdlength hAll_p hAll_d hinner
      simp only [List.length_cons] at hlength_p
      cases hpendingExp : pendingExp with
      | nil =>
        simp only [hpendingExp, List.length_nil] at hlength_p; omega
      | cons e es =>
        simp only [hpendingExp, List.length_cons, Nat.add_right_cancel_iff] at hlength_p
        rw [hpendingExp] at hinner
        simp only [classicalExpandBranches.processNext] at hinner
        by_cases hcl : isClassicallyClosed bh = true
        · rw [if_pos hcl] at hinner
          have hAll_bt : ∀ bp ∈ bt, sf ∈ bp := by
            intro bp hbp
            exact hAll_p bp (by simp [hbp])
          have hAll_done_bh : ∀ bd ∈ done ++ [bh], sf ∈ bd := by
            intro bd hbd
            simp only [List.mem_append, List.mem_singleton] at hbd
            rcases hbd with hd | heq
            · exact hAll_d bd hd
            · subst heq; exact hAll_p bd (by simp)
          exact ih_inner es (done ++ [bh]) (doneExp ++ [e]) hlength_p
            (by simp [hdlength]) hAll_bt hAll_done_bh hinner
        · simp only [Bool.not_eq_true] at hcl
          rw [if_neg (by simp [hcl])] at hinner
          cases hstep : classicalStepBranch bh e with
          | none =>
            rw [hstep] at hinner
            -- hinner : .openBranch bh = .openBranch b → bh = b
            have hbeq : bh = b := by cases hinner; rfl
            exact hbeq ▸ hAll_p bh (by simp)
          | some step =>
            obtain ⟨newBs, newExp⟩ := step
            rw [hstep] at hinner
            have hbh_sf : sf ∈ bh := hAll_p bh (by simp)
            -- Each b' ∈ newBs satisfies sf ∈ b' since extendMany bh x = x ++ bh
            have hNewBs_sf : ∀ b' ∈ newBs, sf ∈ b' :=
              classicalStepBranch_mem_preserved bh e sf hbh_sf newBs newExp hstep
            apply ih (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es)
              (by simp [hdlength, hlength_p]) _ b hinner
            intro b' hb'_mem
            simp only [List.mem_append] at hb'_mem
            rcases hb'_mem with (hd | hn) | hbt
            · exact hAll_d b' hd
            · exact hNewBs_sf b' hn
            · exact hAll_p b' (by simp [hbt])

/-- The open branch returned by the classical tableau is a classical Hintikka set.

This is the key bridge between the expansion loop and the truth lemma. -/
lemma classicalTableau_hintikka (φ : Proposition Atom) (b : Branch (Proposition Atom) Unit)
    (h : classicalTableau φ = .openBranch b) : classicalHintikkaSet b := by
  simp only [classicalTableau] at h
  -- Apply classicalExpandBranches_hintikka with:
  -- - branches = [[⟨.neg, φ, ()⟩]], expandedSets = [[]], fuel from h
  -- - Length: rfl (both length 1)
  -- - Initial invariant: vacuously true since expandedSets[0] = [] (empty)
  -- Apply classicalExpandBranches_hintikka. The invariant holds vacuously because
  -- the initial expandedSets is [[]] (one empty list), so every e we look up is [].
  exact classicalExpandBranches_hintikka _ _ _ rfl
    (fun i b' e _ he sf hsfin => by
      -- he : List.getElem? [[]] i = some e
      -- For i=0, this is some [] = some e, so e = [] and hsfin is absurd.
      -- For i≥1, this is none = some e — contradiction.
      cases i with
      | zero =>
        -- he : List.getElem? [[]] 0 = some e, i.e., some [] = some e, so e = []
        have heq : e = [] := by simpa using he
        exact absurd hsfin (heq ▸ List.not_mem_nil _)
      | succ n =>
        -- he : List.getElem? [[]] (n+1) = some e, i.e., none = some e — contradiction
        simp at he)
    b h

/-! ## Countermodel Extraction -/

/-- An open saturated branch from the classical tableau yields a Boolean countermodel.

If the tableau returns `openBranch b`, then `b` is a classical Hintikka set, and
`classicalTruthLemma` shows that `extractValuation b` falsifies every F-formula on `b`.
The initial formula F(φ) is on every branch returned by the tableau, so `φ` is falsified. -/
lemma classicalOpenBranch_countermodel (φ : Proposition Atom)
    (h : classicalTableau φ = .openBranch b) :
    BoolEvaluate (extractValuation b) φ = false := by
  have hH := classicalTableau_hintikka φ b h
  -- Show F(φ) is on the branch b
  -- The initial branch is [F(φ)] and the expansion only prepends, so F(φ) ∈ b
  have hfphi : b.any (fun sf => sf.sign == .neg && sf.formula == φ) = true := by
    -- F(φ) = ⟨.neg, φ, ()⟩ is on the initial branch and is preserved by expansion
    have h' : classicalExpandBranches [[⟨.neg, φ, ()⟩]] [[]] (4 * (φ.complexity + 1) + 1) =
        .openBranch b := by simp only [classicalTableau] at h; exact h
    have hmem : (⟨.neg, φ, ()⟩ : SignedFormula (Proposition Atom) Unit) ∈ b :=
      classicalExpandBranches_openBranch_initial_mem _ _
        [[⟨.neg, φ, ()⟩]] [[]] rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb₀
          subst hb₀
          exact List.mem_cons_self)
        b h'
    exact List.any_eq_true.mpr ⟨⟨.neg, φ, ()⟩, hmem, by simp⟩
  exact (classicalTruthLemma b hH φ).2 hfphi

/-! ## Main Completeness Theorem -/

/-- **Classical Tableau Completeness**: If `φ` is a classical tautology,
then the classical tableau closes on `φ`.

Proof by contrapositive: if `classicalTableau φ ≠ closed`, then
`classicalTableau φ = openBranch b` for some `b`, and by `classicalOpenBranch_countermodel`,
`BoolEvaluate (extractValuation b) φ = false`, contradicting `Tautology φ`. -/
theorem classicalTableau_complete (φ : Proposition Atom)
    (h : Tautology φ) : classicalTableau φ = .closed := by
  by_contra hnt
  cases htab : classicalTableau φ with
  | closed => exact hnt htab
  | openBranch b =>
    have hcm := classicalOpenBranch_countermodel φ htab
    rw [tautology_iff_boolEvaluate_true] at h
    exact absurd (h (extractValuation b)) (by simp [hcm])

end Cslib.Logic.PL

end
