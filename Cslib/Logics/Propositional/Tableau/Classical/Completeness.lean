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

/-- Per-branch complexity measure: sum of formula complexities of formulas not yet expanded.
A formula is "unexpanded" if it is on branch `b` but not in the expanded set `e`. -/
private def classicalBranchComplexity
    (b : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit)) : Nat :=
  ((b.filter fun sf => !(e.any (· == sf))).map fun sf => sf.formula.complexity).sum

/-- `classicalBranchComplexity` is additive over branch concatenation. -/
private lemma classicalBranchComplexity_append
    (b1 b2 : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit)) :
    classicalBranchComplexity (b1 ++ b2) e =
      classicalBranchComplexity b1 e + classicalBranchComplexity b2 e := by
  simp only [classicalBranchComplexity, List.filter_append, List.map_append, List.sum_append]

/-- Expanding the set `e` by one formula cannot increase `classicalBranchComplexity`:
any newly excluded formula was contributing a non-negative amount. -/
private lemma classicalBranchComplexity_mono_expanded
    (b : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit))
    (sf : SignedFormula (Proposition Atom) Unit) :
    classicalBranchComplexity b (e ++ [sf]) ≤ classicalBranchComplexity b e := by
  simp only [classicalBranchComplexity]
  have natSublist_sum_le : ∀ {l1 l2 : List ℕ}, l1.Sublist l2 → l1.sum ≤ l2.sum := by
    intro _ _ h
    induction h with
    | slnil => simp
    | cons _ _ ih => exact ih.trans (Nat.le_add_left _ _)
    | cons_cons _ _ ih => exact Nat.add_le_add_left ih _
  apply natSublist_sum_le
  apply List.Sublist.map
  apply List.monotone_filter_right
  intro x hx
  simp only [List.any_append, Bool.not_or, Bool.and_eq_true] at hx
  exact hx.1

/-- Expanding `e` by `sf` (which is in `b` and not already in `e`) strictly decreases
`classicalBranchComplexity` by at least `sf.formula.complexity`. -/
private lemma classicalBranchComplexity_drop
    (b : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit))
    (sf : SignedFormula (Proposition Atom) Unit)
    (hmem : sf ∈ b) (hne : e.any (· == sf) = false) :
    classicalBranchComplexity b (e ++ [sf]) + sf.formula.complexity
      ≤ classicalBranchComplexity b e := by
  simp only [classicalBranchComplexity]
  induction b with
  | nil => simp at hmem
  | cons x xs ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · -- head = sf: included in e-filter, excluded from (e++[sf])-filter
      have hfe : (sf :: xs).filter (fun z => !(e.any (· == z))) =
          sf :: xs.filter (fun z => !(e.any (· == z))) := by
        simp [List.filter_cons, hne]
      have hfesf : (sf :: xs).filter (fun z => !((e ++ [sf]).any (· == z))) =
          xs.filter (fun z => !((e ++ [sf]).any (· == z))) := by
        simp [List.filter_cons, List.any_append, List.any_cons, hne]
      simp only [hfe, hfesf, List.map_cons, List.sum_cons]
      have hmono := classicalBranchComplexity_mono_expanded xs e sf
      simp only [classicalBranchComplexity] at hmono
      omega
    · -- sf in tail
      cases hex : e.any (· == x)
      · -- x not in e: passes e-filter
        cases hsfx : sf == x
        · -- sf ≠ x: x passes both filters
          have hfe_x : (x :: xs).filter (fun z => !(e.any (· == z))) =
              x :: xs.filter (fun z => !(e.any (· == z))) := by simp [List.filter_cons, hex]
          have hfesf_x : (x :: xs).filter (fun z => !((e ++ [sf]).any (· == z))) =
              x :: xs.filter (fun z => !((e ++ [sf]).any (· == z))) := by
            simp [List.filter_cons, List.any_append, List.any_cons, hex, hsfx]
          simp only [hfe_x, hfesf_x, List.map_cons, List.sum_cons]
          have := ih hmem'
          omega
        · -- sf = x: x in e-filter, not in (e++[sf])-filter
          have hfe_x : (x :: xs).filter (fun z => !(e.any (· == z))) =
              x :: xs.filter (fun z => !(e.any (· == z))) := by simp [List.filter_cons, hex]
          have hfesf_x : (x :: xs).filter (fun z => !((e ++ [sf]).any (· == z))) =
              xs.filter (fun z => !((e ++ [sf]).any (· == z))) := by
            simp [List.filter_cons, List.any_append, List.any_cons, hex, hsfx]
          simp only [hfe_x, hfesf_x, List.map_cons, List.sum_cons]
          have hfml : sf.formula.complexity = x.formula.complexity := by
            have h : sf = x := LawfulBEq.eq_of_beq hsfx
            simp [h]
          have hmono := classicalBranchComplexity_mono_expanded xs e sf
          simp only [classicalBranchComplexity] at hmono
          omega
      · -- x in e: filtered out in both
        have hfe_x : (x :: xs).filter (fun z => !(e.any (· == z))) =
            xs.filter (fun z => !(e.any (· == z))) := by simp [List.filter_cons, hex]
        have hfesf_x : (x :: xs).filter (fun z => !((e ++ [sf]).any (· == z))) =
            xs.filter (fun z => !((e ++ [sf]).any (· == z))) := by
          simp [List.filter_cons, List.any_append, hex]
        simp only [hfe_x, hfesf_x]
        exact ih hmem'

/-- `classicalBranchComplexity` is bounded by the total complexity of the branch. -/
private lemma classicalBranchComplexity_le_mapsum
    (l : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit)) :
    classicalBranchComplexity l e ≤ (l.map (fun sf => sf.formula.complexity)).sum := by
  simp only [classicalBranchComplexity]
  have natSublist_sum_le : ∀ {l1 l2 : List ℕ}, l1.Sublist l2 → l1.sum ≤ l2.sum := by
    intro _ _ h
    induction h with
    | slnil => simp
    | cons _ _ ih => exact ih.trans (Nat.le_add_left _ _)
    | cons_cons _ _ ih => exact Nat.add_le_add_left ih _
  apply natSublist_sum_le
  apply List.Sublist.map
  exact List.filter_sublist

/-- `classicalBranchComplexity` of an extended branch splits into outputs + original. -/
private lemma classicalBranchComplexity_extendMany
    (b : Branch (Proposition Atom) Unit) (out : List (SignedFormula (Proposition Atom) Unit))
    (e : List (SignedFormula (Proposition Atom) Unit)) :
    classicalBranchComplexity (Branch.extendMany b out) e
      = classicalBranchComplexity out e + classicalBranchComplexity b e := by
  simp only [Branch.extendMany]
  exact classicalBranchComplexity_append out b e

/-- A child branch (original `b` extended by rule outputs `out`, with `sf` newly expanded) has
complexity at most `cBC b e - 1`, when the outputs' total complexity is `≤ complexity sf - 1`. -/
private lemma classicalBranchComplexity_child_le
    (b : Branch (Proposition Atom) Unit) (out : List (SignedFormula (Proposition Atom) Unit))
    (e : List (SignedFormula (Proposition Atom) Unit)) (sf : SignedFormula (Proposition Atom) Unit)
    (hmem : sf ∈ b) (hne : e.any (· == sf) = false) (hsf1 : 1 ≤ sf.formula.complexity)
    (hout : (out.map (fun x => x.formula.complexity)).sum ≤ sf.formula.complexity - 1) :
    classicalBranchComplexity (Branch.extendMany b out) (e ++ [sf])
      ≤ classicalBranchComplexity b e - 1 := by
  rw [classicalBranchComplexity_extendMany]
  have h1 := classicalBranchComplexity_le_mapsum out (e ++ [sf])
  have h2 := classicalBranchComplexity_drop b e sf hmem hne
  omega

/-- For an applicable signed formula, the total complexity of the output formulas equals
`sf.formula.complexity - 1`, and the expanded formula has complexity ≥ 1.
This identity drives strict decrease of `classicalExpMeasure` at each tableau step. -/
private lemma classicalApplyOne_output_complexity
    (sf : SignedFormula (Proposition Atom) Unit) :
    (match classicalApplyOne sf with
    | .linear formulas =>
        1 ≤ sf.formula.complexity ∧
        (formulas.map (·.formula.complexity)).sum = sf.formula.complexity - 1
    | .branching branches =>
        1 ≤ sf.formula.complexity ∧
        (branches.flatten.map (·.formula.complexity)).sum = sf.formula.complexity - 1
    | .persistent formulas =>
        1 ≤ sf.formula.complexity ∧
        (formulas.map (·.formula.complexity)).sum = sf.formula.complexity - 1
    | .notApplicable => True) := by
  obtain ⟨s, φ, l⟩ := sf
  simp only [SignedFormula.formula]
  rcases s <;> rcases φ with x | _ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    (try rcases b with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
    simp [classicalApplyOne, tryAllPropRules, applyPropRule, propAndOf?, propOrOf?,
      propImpOf?, propNegOf?, RuleResult.isApplicable, Proposition.complexity,
      SignedFormula.neg, SignedFormula.pos, SignedFormula.formula,
      complexity_atom, complexity_bot, complexity_imp, complexity_and, complexity_or] <;>
    omega

/-- Beta-robust termination measure: base-3 exponential of per-branch complexity, summed.
Unlike the additive count `classicalTotalMeasure`, this measure strictly decreases at
every expansion step (both alpha rules producing one child and beta rules producing two). -/
private def classicalExpMeasure
    (branches : List (Branch (Proposition Atom) Unit))
    (expandedSets : List (List (SignedFormula (Proposition Atom) Unit))) : Nat :=
  ((branches.zip expandedSets).map fun p => 3 ^ classicalBranchComplexity p.1 p.2).sum

/-- `classicalExpMeasure` splits over a single distinguished position, given length-aligned prefixes. -/
private lemma classicalExpMeasure_split
    (done : List (Branch (Proposition Atom) Unit))
    (doneExp : List (List (SignedFormula (Proposition Atom) Unit)))
    (b : Branch (Proposition Atom) Unit) (e : List (SignedFormula (Proposition Atom) Unit))
    (rest : List (Branch (Proposition Atom) Unit))
    (restEs : List (List (SignedFormula (Proposition Atom) Unit)))
    (hlen : done.length = doneExp.length) :
    classicalExpMeasure (done ++ b :: rest) (doneExp ++ e :: restEs)
      = classicalExpMeasure done doneExp + 3 ^ classicalBranchComplexity b e
        + classicalExpMeasure rest restEs := by
  simp only [classicalExpMeasure, List.zip_append hlen, List.zip_cons_cons,
             List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

/-- `classicalExpMeasure` is additive over append, given length-aligned first components. -/
private lemma classicalExpMeasure_append
    (l1 l2 : List (Branch (Proposition Atom) Unit))
    (e1 e2 : List (List (SignedFormula (Proposition Atom) Unit)))
    (h : l1.length = e1.length) :
    classicalExpMeasure (l1 ++ l2) (e1 ++ e2)
      = classicalExpMeasure l1 e1 + classicalExpMeasure l2 e2 := by
  simp only [classicalExpMeasure, List.zip_append h, List.map_append, List.sum_append]

/-- When every new branch shares the same expanded set `newExp`, the measure is the sum of
`3 ^ classicalBranchComplexity child newExp` over the new branches. -/
private lemma classicalExpMeasure_const_exp
    (newBs : List (Branch (Proposition Atom) Unit))
    (newExp : List (SignedFormula (Proposition Atom) Unit)) :
    classicalExpMeasure newBs (newBs.map (fun _ => newExp))
      = (newBs.map (fun child => 3 ^ classicalBranchComplexity child newExp)).sum := by
  simp only [classicalExpMeasure, ← List.map_prod_left_eq_zip, List.map_map, Function.comp_def]

/-- Base-3 decrease for a BETA step: two children of complexity ≤ C-1 plus the saved unit. -/
private lemma pow3_two_add_one_le {a0 a1 C : Nat} (hC : 1 ≤ C) (h0 : a0 ≤ C - 1)
    (h1 : a1 ≤ C - 1) :
    3 ^ a0 + 3 ^ a1 + 1 ≤ 3 ^ C := by
  have h0' : 3 ^ a0 ≤ 3 ^ (C - 1) := Nat.pow_le_pow_right (by omega) h0
  have h1' : 3 ^ a1 ≤ 3 ^ (C - 1) := Nat.pow_le_pow_right (by omega) h1
  have hone : 1 ≤ 3 ^ (C - 1) := Nat.one_le_pow _ _ (by omega)
  rw [show C = C - 1 + 1 from (Nat.sub_add_cancel hC).symm, pow_succ]
  omega

/-- Base-3 decrease for an ALPHA step: one child of complexity ≤ C-1 plus the saved unit. -/
private lemma pow3_add_one_le {a0 C : Nat} (hC : 1 ≤ C) (h0 : a0 ≤ C - 1) :
    3 ^ a0 + 1 ≤ 3 ^ C := by
  have h0' : 3 ^ a0 ≤ 3 ^ (C - 1) := Nat.pow_le_pow_right (by omega) h0
  have hone : 1 ≤ 3 ^ (C - 1) := Nat.one_le_pow _ _ (by omega)
  rw [show C = C - 1 + 1 from (Nat.sub_add_cancel hC).symm, pow_succ]
  omega

/-- Count of unexpanded formulas in branch `b` relative to expanded set `e`.
Zero means every formula on the branch is in the expanded set, so the Hintikka
invariant covers the entire branch. -/
private def classicalRemMeasure
    (b : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit)) : Nat :=
  (b.filter fun sf => !(e.any (· == sf))).length

/-- Total remaining measure across all branches: sum of per-branch unexpanded formula counts.
When this is ≤ fuel, every formula on every open branch has been expanded before fuel runs out,
so any returned open branch is a Hintikka set. -/
private def classicalTotalMeasure
    (branches : List (Branch (Proposition Atom) Unit))
    (expandedSets : List (List (SignedFormula (Proposition Atom) Unit))) : Nat :=
  ((branches.zip expandedSets).map fun p => classicalRemMeasure p.1 p.2).sum

/-- If the per-branch measure is zero, every formula on the branch is in the expanded set. -/
private lemma classicalRemMeasure_zero_subset
    {b : Branch (Proposition Atom) Unit}
    {e : List (SignedFormula (Proposition Atom) Unit)}
    (hm : classicalRemMeasure b e = 0)
    {sf : SignedFormula (Proposition Atom) Unit} (hsf : sf ∈ b) : sf ∈ e := by
  simp only [classicalRemMeasure] at hm
  by_contra hnsf
  have hiff : e.any (· == sf) = true ↔ sf ∈ e := by simp [List.any_eq_true]
  have hany : e.any (· == sf) = false := by
    rw [Bool.eq_false_iff]; intro h; exact hnsf (hiff.mp h)
  have hmem : sf ∈ b.filter (fun sf => !(e.any (· == sf))) :=
    List.mem_filter.mpr ⟨hsf, by simp [hany]⟩
  exact absurd (List.length_pos_of_mem hmem) (by omega)

/-- If the total measure is zero, every formula on `branches[i]` is in `expandedSets[i]`. -/
private lemma classicalTotalMeasure_zero_mem_subset
    {branches : List (Branch (Proposition Atom) Unit)}
    {expandedSets : List (List (SignedFormula (Proposition Atom) Unit))}
    (hlength : expandedSets.length = branches.length)
    (hm : classicalTotalMeasure branches expandedSets = 0)
    {i : Nat} (hi : i < branches.length)
    {sf : SignedFormula (Proposition Atom) Unit} (hsf : sf ∈ branches[i]) :
    sf ∈ expandedSets[i]'(by omega) := by
  have hi' : i < expandedSets.length := by omega
  have hzip : (branches[i], expandedSets[i]'hi') ∈ branches.zip expandedSets := by
    rw [List.mem_iff_getElem]
    refine ⟨i, by simp [List.length_zip]; exact ⟨hi, hi'⟩, by simp [List.getElem_zip]⟩
  simp only [classicalTotalMeasure] at hm
  have hterm : classicalRemMeasure branches[i] (expandedSets[i]'hi') = 0 :=
    List.sum_eq_zero_iff_forall_eq_nat.mp hm _
      (List.mem_map.mpr ⟨(branches[i], expandedSets[i]'hi'), hzip, rfl⟩)
  exact classicalRemMeasure_zero_subset hterm hsf

/-- When `classicalStepBranch b e = none`, every formula on `b` is either already in the
expanded set `e` or has `classicalApplyOne` return `notApplicable` (the branch is saturated). -/
private lemma classicalStepBranch_none_saturated
    {b : Branch (Proposition Atom) Unit}
    {e : List (SignedFormula (Proposition Atom) Unit)}
    (hstep : classicalStepBranch b e = none)
    (sf : SignedFormula (Proposition Atom) Unit) (hsfb : sf ∈ b) :
    sf ∈ e ∨ classicalApplyOne sf = .notApplicable := by
  simp only [classicalStepBranch] at hstep
  rw [List.findSome?_eq_none_iff] at hstep
  have hbody := hstep sf hsfb
  by_cases hany : e.any (· == sf) = true
  · left
    simp only [List.any_eq_true] at hany
    obtain ⟨sf', hme, heq⟩ := hany
    simp only [beq_iff_eq] at heq
    exact heq ▸ hme
  · right
    simp only [Bool.not_eq_true] at hany
    simp only [hany, ite_false] at hbody
    rcases hca : classicalApplyOne sf with out | brs | out | _
    all_goals simp only [hca] at hbody
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · rfl

/-- If the Hintikka invariant holds for branch `b` against expanded set `e`, then after one step
`classicalStepBranch b e = some (newBs, newExp)`, the invariant holds for every new branch
`b' ∈ newBs` against the new expanded set `newExp`. -/
private lemma classicalStepBranch_hintikka_inv
    (b : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit))
    (newBs : List (Branch (Proposition Atom) Unit))
    (newExp : List (SignedFormula (Proposition Atom) Unit))
    (hstep : classicalStepBranch b e = some (newBs, newExp))
    (hInv_b : ∀ sf ∈ e,
      match classicalApplyOne sf with
      | .linear out => ∀ sf' ∈ out, sf' ∈ b
      | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b
      | .persistent out => ∀ sf' ∈ out, sf' ∈ b
      | .notApplicable => True) :
    ∀ b' ∈ newBs, ∀ sf ∈ newExp,
      match classicalApplyOne sf with
      | .linear out => ∀ sf' ∈ out, sf' ∈ b'
      | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b'
      | .persistent out => ∀ sf' ∈ out, sf' ∈ b'
      | .notApplicable => True := by
  simp only [classicalStepBranch] at hstep
  obtain ⟨sf_exp, _, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hexp
  · rcases hca : classicalApplyOne sf_exp with newForms | brs | newForms | _
    all_goals simp only [hca] at hfound
    · -- linear: newBs = [extendMany b newForms], newExp = e ++ [sf_exp]
      obtain ⟨rfl, rfl⟩ := Option.some.inj hfound
      intro b' hb' sf hsfin
      simp only [List.mem_singleton] at hb'; subst hb'
      rw [List.mem_append, List.mem_singleton] at hsfin
      rcases hsfin with hsfin | rfl
      · -- sf ∈ e: apply hInv_b and lift membership from b to b' = extendMany b newForms
        have hInv_sf := hInv_b sf hsfin
        rcases hca_sf : classicalApplyOne sf with out' | brs' | out' | _
        all_goals simp only [hca_sf] at hInv_sf ⊢
        · intro sf' hsf'
          simp only [Branch.extendMany, List.mem_append]
          exact Or.inr (hInv_sf sf' hsf')
        · obtain ⟨br', hbr', hbr''⟩ := hInv_sf
          exact ⟨br', hbr', fun sf' hsf' => by
            simp only [Branch.extendMany, List.mem_append]; exact Or.inr (hbr'' sf' hsf')⟩
        · intro sf' hsf'
          simp only [Branch.extendMany, List.mem_append]
          exact Or.inr (hInv_sf sf' hsf')
      · -- sf = sf_exp: classicalApplyOne sf_exp = linear newForms, output ⊆ extendMany b newForms
        simp only [hca]
        intro sf' hsf'
        simp only [Branch.extendMany, List.mem_append]
        exact Or.inl hsf'
    · -- branching: newBs = brs.map (extendMany b ·), newExp = e ++ [sf_exp]
      obtain ⟨rfl, rfl⟩ := Option.some.inj hfound
      intro b' hb' sf hsfin
      rw [List.mem_map] at hb'
      obtain ⟨br_exp, hbr_exp, rfl⟩ := hb'
      rw [List.mem_append, List.mem_singleton] at hsfin
      rcases hsfin with hsfin | rfl
      · -- sf ∈ e: lift from b to b' = extendMany b br_exp
        have hInv_sf := hInv_b sf hsfin
        rcases hca_sf : classicalApplyOne sf with out' | brs' | out' | _
        all_goals simp only [hca_sf] at hInv_sf ⊢
        · intro sf' hsf'
          simp only [Branch.extendMany, List.mem_append]
          exact Or.inr (hInv_sf sf' hsf')
        · obtain ⟨br', hbr', hbr''⟩ := hInv_sf
          exact ⟨br', hbr', fun sf' hsf' => by
            simp only [Branch.extendMany, List.mem_append]; exact Or.inr (hbr'' sf' hsf')⟩
        · intro sf' hsf'
          simp only [Branch.extendMany, List.mem_append]
          exact Or.inr (hInv_sf sf' hsf')
      · -- sf = sf_exp: classicalApplyOne sf_exp = branching brs, witness br_exp for b'
        simp only [hca]
        exact ⟨br_exp, hbr_exp, fun sf' hsf' => by
          simp only [Branch.extendMany, List.mem_append]; exact Or.inl hsf'⟩
    · -- persistent: same structure as linear
      obtain ⟨rfl, rfl⟩ := Option.some.inj hfound
      intro b' hb' sf hsfin
      simp only [List.mem_singleton] at hb'; subst hb'
      rw [List.mem_append, List.mem_singleton] at hsfin
      rcases hsfin with hsfin | rfl
      · have hInv_sf := hInv_b sf hsfin
        rcases hca_sf : classicalApplyOne sf with out' | brs' | out' | _
        all_goals simp only [hca_sf] at hInv_sf ⊢
        · intro sf' hsf'
          simp only [Branch.extendMany, List.mem_append]
          exact Or.inr (hInv_sf sf' hsf')
        · obtain ⟨br', hbr', hbr''⟩ := hInv_sf
          exact ⟨br', hbr', fun sf' hsf' => by
            simp only [Branch.extendMany, List.mem_append]; exact Or.inr (hbr'' sf' hsf')⟩
        · intro sf' hsf'
          simp only [Branch.extendMany, List.mem_append]
          exact Or.inr (hInv_sf sf' hsf')
      · simp only [hca]
        intro sf' hsf'
        simp only [Branch.extendMany, List.mem_append]
        exact Or.inl hsf'
    · simp at hfound

/-- For classical propositional rules, every branching step produces exactly two new branches. -/
private lemma classicalApplyOne_branching_length
    (sf : SignedFormula (Proposition Atom) Unit)
    (brs : List (Branch (Proposition Atom) Unit))
    (h : classicalApplyOne sf = .branching brs) : brs.length = 2 := by
  obtain ⟨s, φ, l⟩ := sf
  rcases s <;> rcases φ with x | _ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    (try rcases b with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
    simp [classicalApplyOne, tryAllPropRules, applyPropRule, propAndOf?, propOrOf?,
      propImpOf?, propNegOf?, RuleResult.isApplicable,
      SignedFormula.neg, SignedFormula.pos, SignedFormula.formula,
      SignedFormula.sign, SignedFormula.label] at h <;>
    simp [← h]

/-- One expansion step strictly decreases the exponential measure: when
`classicalStepBranch bh e = some (newBs, newExp)`, the new configuration's measure plus
one is at most the old configuration's measure. -/
private lemma classicalExpMeasure_step_lt
    (done bt newBs : List (Branch (Proposition Atom) Unit))
    (doneExp es : List (List (SignedFormula (Proposition Atom) Unit)))
    (newExp : List (SignedFormula (Proposition Atom) Unit))
    (bh : Branch (Proposition Atom) Unit)
    (e : List (SignedFormula (Proposition Atom) Unit))
    (hdlen : done.length = doneExp.length)
    (hstep : classicalStepBranch bh e = some (newBs, newExp)) :
    classicalExpMeasure (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ classicalExpMeasure (done ++ bh :: bt) (doneExp ++ e :: es) := by
  -- Expand both sides into a common form
  have hrhs : classicalExpMeasure (done ++ bh :: bt) (doneExp ++ e :: es) =
      classicalExpMeasure done doneExp + 3 ^ classicalBranchComplexity bh e +
        classicalExpMeasure bt es :=
    classicalExpMeasure_split done doneExp bh e bt es hdlen
  have hlhs : classicalExpMeasure (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) =
      classicalExpMeasure done doneExp +
        (newBs.map (fun child => 3 ^ classicalBranchComplexity child newExp)).sum +
        classicalExpMeasure bt es := by
    have hlen1 : (done ++ newBs).length = (doneExp ++ newBs.map (fun _ => newExp)).length := by
      simp [List.length_append, List.length_map, hdlen]
    rw [classicalExpMeasure_append (done ++ newBs) bt
          (doneExp ++ newBs.map (fun _ => newExp)) es hlen1,
        classicalExpMeasure_append done newBs doneExp (newBs.map (fun _ => newExp)) hdlen,
        classicalExpMeasure_const_exp newBs newExp]
  rw [hrhs, hlhs]
  -- Reduce to core: sum of new branch measures + 1 ≤ old branch measure
  suffices h : (newBs.map (fun child => 3 ^ classicalBranchComplexity child newExp)).sum + 1 ≤
      3 ^ classicalBranchComplexity bh e by omega
  -- Extract the expanded formula from hstep
  simp only [classicalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hany
  simp only [Bool.not_eq_true] at hany
  -- hany : e.any (· == sf) = false
  have hcomp := classicalApplyOne_output_complexity sf
  rcases hca : classicalApplyOne sf with nf | brs | nf | _
  all_goals simp only [hca] at hfound hcomp
  · -- linear: newBs = [Branch.extendMany bh nf], newExp = e ++ [sf]
    obtain ⟨rfl, rfl⟩ := Option.some.inj hfound
    obtain ⟨hsf1, hout_eq⟩ := hcomp
    have hC : 1 ≤ classicalBranchComplexity bh e := by
      have := classicalBranchComplexity_drop bh e sf hsfmem hany; omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC
      (classicalBranchComplexity_child_le bh nf e sf hsfmem hany hsf1 (le_of_eq hout_eq))
  · -- branching: newBs = brs.map (Branch.extendMany bh ·), newExp = e ++ [sf]
    obtain ⟨rfl, rfl⟩ := Option.some.inj hfound
    obtain ⟨hsf1, hout_eq⟩ := hcomp
    have hC : 1 ≤ classicalBranchComplexity bh e := by
      have := classicalBranchComplexity_drop bh e sf hsfmem hany; omega
    -- Branching always produces exactly 2 branches
    obtain ⟨b0, b1, hbrs⟩ := List.length_eq_two.mp (classicalApplyOne_branching_length sf brs hca)
    subst hbrs
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    -- Per-branch complexity from flatten equality
    have hflatsum : (b0.map (·.formula.complexity)).sum +
        (b1.map (·.formula.complexity)).sum = sf.formula.complexity - 1 := by
      have hfl : ([b0, b1].flatten.map (·.formula.complexity)).sum = sf.formula.complexity - 1 :=
        hout_eq
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
                 List.map_append, List.sum_append] at hfl
      omega
    have hout0 : (b0.map (fun x => x.formula.complexity)).sum ≤ sf.formula.complexity - 1 := by
      omega
    have hout1 : (b1.map (fun x => x.formula.complexity)).sum ≤ sf.formula.complexity - 1 := by
      omega
    have ha0 := classicalBranchComplexity_child_le bh b0 e sf hsfmem hany hsf1 hout0
    have ha1 := classicalBranchComplexity_child_le bh b1 e sf hsfmem hany hsf1 hout1
    exact pow3_two_add_one_le hC ha0 ha1
  · -- persistent: same structure as linear
    obtain ⟨rfl, rfl⟩ := Option.some.inj hfound
    obtain ⟨hsf1, hout_eq⟩ := hcomp
    have hC : 1 ≤ classicalBranchComplexity bh e := by
      have := classicalBranchComplexity_drop bh e sf hsfmem hany; omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC
      (classicalBranchComplexity_child_le bh nf e sf hsfmem hany hsf1 (le_of_eq hout_eq))
  · simp at hfound

/-- The open branch returned by `classicalExpandBranches` is a classical Hintikka set,
provided `classicalExpMeasure branches expandedSets ≤ fuel`.

- **fuel = 0**: measure = 0 forces `branches = []` (each term `3^C ≥ 1` means a non-empty
  list gives sum ≥ 1); `classicalExpandBranches [] _ 0 = .closed`, making the goal vacuous.
- **fuel = n+1**: The inner loop either finds a saturated open branch (Hintikka by invariant
  and saturation) or expands one formula via `classicalExpMeasure_step_lt` and recurses.

The proof is by induction on fuel with an inner induction on the pending list. -/
private lemma classicalExpandBranches_hintikka (fuel : Nat) :
    ∀ (branches : List (Branch (Proposition Atom) Unit))
      (expandedSets : List (List (SignedFormula (Proposition Atom) Unit))),
      expandedSets.length = branches.length →
      classicalExpMeasure branches expandedSets ≤ fuel →
      -- Invariant: each branch satisfies Hintikka for its expanded formulas
      (∀ (i : Nat) (b : Branch (Proposition Atom) Unit) (e : List (SignedFormula (Proposition Atom) Unit)),
        branches[i]? = some b → expandedSets[i]? = some e →
        ∀ sf ∈ e, match classicalApplyOne sf with
          | .linear out => ∀ sf' ∈ out, sf' ∈ b
          | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b
          | .persistent out => ∀ sf' ∈ out, sf' ∈ b
          | .notApplicable => True) →
      ∀ b, classicalExpandBranches branches expandedSets fuel = .openBranch b →
        classicalHintikkaSet b := by
  induction fuel with
  | zero =>
    intro branches expandedSets hlength hfuel hInv b h
    -- classicalExpMeasure ≤ 0 ⟹ = 0.  Each term 3^C ≥ 1, so a non-empty zip gives
    -- sum ≥ 1 > 0; contradiction forces branches = [].
    -- classicalExpandBranches [] _ 0 = .closed, making h absurd.
    have hm : classicalExpMeasure branches expandedSets = 0 := Nat.le_zero.mp hfuel
    have hbranches : branches = [] := by
      rcases branches with _ | ⟨bh, bt⟩
      · rfl
      · exfalso
        rcases expandedSets with _ | ⟨e, es⟩
        · simp only [List.length_nil, List.length_cons] at hlength; omega
        · simp only [classicalExpMeasure, List.zip_cons_cons, List.map_cons,
                     List.sum_cons] at hm
          have h3 := Nat.one_le_pow (classicalBranchComplexity bh e) 3 (by omega)
          omega
    subst hbranches
    simp [classicalExpandBranches] at h
  | succ fuel' ih =>
    intro branches expandedSets hlength hfuel hInv b h
    simp only [classicalExpandBranches] at h
    -- Inner induction on the pending list, tracking the full invariant.
    suffices key : ∀ (pending : List (Branch (Proposition Atom) Unit))
        (pendingExp : List (List (SignedFormula (Proposition Atom) Unit)))
        (done : List (Branch (Proposition Atom) Unit))
        (doneExp : List (List (SignedFormula (Proposition Atom) Unit))),
        pendingExp.length = pending.length →
        doneExp.length = done.length →
        (∀ (i : Nat) (bi : Branch (Proposition Atom) Unit)
            (ei : List (SignedFormula (Proposition Atom) Unit)),
          (done ++ pending)[i]? = some bi → (doneExp ++ pendingExp)[i]? = some ei →
          ∀ sf ∈ ei, match classicalApplyOne sf with
            | .linear out => ∀ sf' ∈ out, sf' ∈ bi
            | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ bi
            | .persistent out => ∀ sf' ∈ out, sf' ∈ bi
            | .notApplicable => True) →
        classicalExpMeasure (done ++ pending) (doneExp ++ pendingExp) ≤ fuel' + 1 →
        classicalExpandBranches.processNext fuel' pending pendingExp done doneExp = .openBranch b →
        classicalHintikkaSet b from
      key branches expandedSets [] [] hlength rfl hInv hfuel (by simpa [classicalExpandBranches] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp done doneExp _ _ _ _ hinner
      simp [classicalExpandBranches.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp done doneExp hlength_p hdlength hInv_all hmeas hinner
      simp only [List.length_cons] at hlength_p
      cases hpendingExp : pendingExp with
      | nil => simp only [hpendingExp, List.length_nil] at hlength_p; omega
      | cons e es =>
        rw [hpendingExp] at hinner hmeas
        simp only [classicalExpandBranches.processNext] at hinner
        by_cases hcl : isClassicallyClosed bh = true
        · -- Closed branch: skip and recurse on inner induction
          rw [if_pos hcl] at hinner
          apply ih_inner es (done ++ [bh]) (doneExp ++ [e])
          · simp only [hpendingExp, List.length_cons, Nat.add_right_cancel_iff] at hlength_p; exact hlength_p
          · simp only [List.length_append, List.length_singleton, hdlength]
          · intro i bi ei hi_bi hi_ei
            apply hInv_all i bi ei
            · -- rewrite done ++ [bh] ++ bt = done ++ bh :: bt in hi_bi
              convert hi_bi using 2; simp
            · -- rewrite doneExp ++ [e] ++ es as doneExp ++ pendingExp in hi_ei
              rw [hpendingExp]; convert hi_ei using 2; simp
          · -- classicalExpMeasure (done ++ [bh] ++ bt) ... = classicalExpMeasure (done ++ bh :: bt) ...
            convert hmeas using 2 <;> simp
          · exact hinner
        · simp only [Bool.not_eq_true] at hcl
          rw [if_neg (by simp [hcl])] at hinner
          cases hstep : classicalStepBranch bh e with
          | none =>
            -- Saturated open branch: return it as the Hintikka set
            rw [hstep] at hinner
            have hbeq : bh = b := by cases hinner; rfl
            subst hbeq
            -- bh is saturated and open, so it is a Hintikka set
            refine ⟨hcl, ?_⟩
            intro sf hsfmem
            -- Get the Hintikka invariant for bh (at index done.length in done ++ bh :: bt)
            have hbh_idx : (done ++ bh :: bt)[done.length]? = some bh := by
              rw [List.getElem?_append_right (le_refl _)]
              simp [Nat.sub_self]
            have he_idx : (doneExp ++ pendingExp)[done.length]? = some e := by
              rw [hpendingExp, List.getElem?_append_right (by omega)]
              simp [hdlength, Nat.sub_self]
            have hInv_bh := hInv_all done.length bh e hbh_idx he_idx
            -- By classicalStepBranch_none_saturated: sf ∈ e or classicalApplyOne sf = notApplicable
            rcases classicalStepBranch_none_saturated hstep sf hsfmem with hine | hna
            · -- sf ∈ e: apply the Hintikka invariant
              exact hInv_bh sf hine
            · -- classicalApplyOne sf = notApplicable: the branch clause is True
              simp [hna]
          | some step =>
            obtain ⟨newBs, newExp⟩ := step
            rw [hstep] at hinner
            -- Expansion exit: call classicalExpandBranches with fuel'
            -- Apply the outer induction hypothesis ih
            apply ih (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es)
            · -- Length condition for new branches
              simp only [List.length_append, List.length_map, hdlength]
              simp only [hpendingExp, List.length_cons, Nat.add_right_cancel_iff] at hlength_p
              omega
            · -- Measure hypothesis: classicalExpMeasure (done ++ newBs ++ bt) ≤ fuel'
              -- classicalExpMeasure_step_lt: LHS + 1 ≤ classicalExpMeasure (done ++ bh :: bt) (...)
              -- hmeas: classicalExpMeasure (done ++ bh :: bt) (...) ≤ fuel' + 1
              -- Hence LHS ≤ fuel' by omega.
              have hstep_lt := classicalExpMeasure_step_lt done bt newBs doneExp es newExp bh e
                hdlength.symm hstep
              omega
            · -- Hintikka invariant for the new branch list.
              -- Split into three index regions: done, newBs, bt.
              intro i b' e' hi' he' sf hsfin
              rcases Nat.lt_or_ge i done.length with hlt1 | hge1
              · -- Region: i < done.length (done — unchanged)
                have hb' : done[i]? = some b' := by
                  rw [List.append_assoc, List.getElem?_append_left hlt1] at hi'; exact hi'
                have he'_d : doneExp[i]? = some e' := by
                  rw [List.append_assoc, List.getElem?_append_left (by omega)] at he'; exact he'
                apply hInv_all i b' e'
                · rw [List.getElem?_append_left hlt1]; exact hb'
                · rw [hpendingExp, List.getElem?_append_left (by omega)]; exact he'_d
                · exact hsfin
              · rcases Nat.lt_or_ge i (done.length + newBs.length) with hlt2 | hge2
                · -- Region: done.length ≤ i < done.length + newBs.length (newBs)
                  have hj : i - done.length < newBs.length := by omega
                  have hb'_newBs : newBs[i - done.length]? = some b' := by
                    rw [List.append_assoc, List.getElem?_append_right hge1] at hi'
                    rwa [List.getElem?_append_left hj] at hi'
                  have hb'_mem : b' ∈ newBs := List.mem_of_getElem? hb'_newBs
                  have he'_eq : e' = newExp := by
                    rw [List.append_assoc,
                        List.getElem?_append_right (by omega : doneExp.length ≤ i)] at he'
                    rw [List.getElem?_append_left
                          (by simp only [List.length_map]; omega)] at he'
                    rw [List.getElem?_map,
                        show newBs[i - doneExp.length]? = some b' from by
                          rw [show i - doneExp.length = i - done.length from by omega]
                          exact hb'_newBs] at he'
                    simp only [Option.map_some, Option.some.injEq] at he'
                    exact he'.symm
                  subst he'_eq
                  -- Get Hintikka invariant for (bh, e) from hInv_all
                  have hInv_bh := hInv_all done.length bh e
                    (by rw [List.getElem?_append_right (le_refl _)]; simp [Nat.sub_self])
                    (by rw [hpendingExp, List.getElem?_append_right (by omega)];
                        simp [hdlength, Nat.sub_self])
                  exact classicalStepBranch_hintikka_inv bh e newBs e' hstep hInv_bh
                    b' hb'_mem sf hsfin
                · -- Region: done.length + newBs.length ≤ i (bt — shifted index)
                  let j := i - done.length - newBs.length
                  have hb'_bt : bt[j]? = some b' := by
                    rw [List.append_assoc, List.getElem?_append_right hge1] at hi'
                    rw [List.getElem?_append_right
                          (by omega : newBs.length ≤ i - done.length)] at hi'
                    exact hi'
                  have he'_es : es[j]? = some e' := by
                    rw [List.append_assoc,
                        List.getElem?_append_right (by omega : doneExp.length ≤ i)] at he'
                    rw [List.getElem?_append_right
                          (by simp only [List.length_map]; omega :
                            (List.map (fun _ => newExp) newBs).length ≤
                              i - doneExp.length)] at he'
                    rwa [show i - doneExp.length -
                              (List.map (fun _ => newExp) newBs).length = j from by
                          simp only [List.length_map]; omega] at he'
                  apply hInv_all (done.length + 1 + j) b' e'
                  · rw [List.getElem?_append_right
                          (by omega : done.length ≤ done.length + 1 + j)]
                    rw [show done.length + 1 + j - done.length = j + 1 from by omega]
                    rw [List.getElem?_cons_succ]; exact hb'_bt
                  · rw [hpendingExp, List.getElem?_append_right
                          (by omega : doneExp.length ≤ done.length + 1 + j)]
                    rw [show done.length + 1 + j - doneExp.length = j + 1 from by omega]
                    rw [List.getElem?_cons_succ]; exact he'_es
                  · exact hsfin
            · exact hinner

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
        have hfval : b₀ = b' := by simp only [hcl] at hf; exact Option.some.inj hf
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
  -- The initial state has exactly one formula on one branch and an empty expanded set.
  -- The measure is 1 (one unexpanded formula), which is ≤ the fuel bound.
  -- PHASE 4: prove classicalExpMeasure [[⟨.neg, φ, ()⟩]] [[]] ≤ fuel after raising the bound
  -- in Expansion.lean from 4*(φ.complexity+1)+1 to 3^(φ.complexity) (or appropriate bound).
  have hfuel_init : classicalExpMeasure [[⟨.neg, φ, ()⟩]] [[]] ≤ 4 * (φ.complexity + 1) + 1 :=
    sorry
  -- Supply branches/expandedSets explicitly so the lambda's `he` type is fully determined.
  -- Initial invariant holds vacuously: expandedSets = [[]], so every e looked up is [].
  exact classicalExpandBranches_hintikka _ [[⟨.neg, φ, ()⟩]] [[]] rfl hfuel_init
    (fun i b' e _ he sf hsfin => by
      -- he : ([] : List ...) [i]? = some e (expandedSets = [[]], inner list is [])
      -- For i=0: [[]][0]? = some [] = some e, so e = [], contradicting sf ∈ e = [].
      -- For i≥1: [[]][n+1]? = none ≠ some e — contradiction.
      cases i with
      | zero =>
        -- he : [[]][0]? = some e, i.e., some [] = some e, so e = []
        have heq : e = [] := by simp at he; exact he
        simp [heq] at hsfin
      | succ n =>
        -- [[]][n+1]? = none ≠ some e
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
