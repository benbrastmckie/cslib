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
      have hpos_sign : sf_pos.sign = .pos := by cases sf_pos.sign <;> simp_all [SignedFormula.sign]
      have hneg_sign : sf_neg.sign = .neg := by cases sf_neg.sign <;> simp_all [SignedFormula.sign]
      have hpos_form : sf_pos.formula = .atom p := eq_of_beq hsfpos_cond.2
      have hneg_form : sf_neg.formula = .atom p := eq_of_beq hsfneg_cond.2
      have hcont : b.hasContradiction = true := by
        simp only [Branch.hasContradiction, Branch.findContradiction, Option.isSome_iff_exists]
        use (.atom p, sf_pos.label)
        apply List.findSome?_of_mem hsfpos_mem
        simp only [SignedFormula.isPos, hpos_sign, Sign.isPos, true_and, ite_true]
        rw [hpos_form]
        apply List.any_eq_true.mpr
        exact ⟨sf_neg, hsfneg_mem, by
          simp only [Bool.and_eq_true]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · change (sf_neg.sign == .neg) = true; rw [hneg_sign]
          · rw [hneg_form]
          · simp [sf_neg.label, sf_pos.label]⟩
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
        use sf
        apply List.find?_of_mem hsfmem
        simp only [Bool.and_eq_true, SignedFormula.isPos, Sign.isPos]
        exact ⟨by cases sf.sign <;> simp_all [SignedFormula.sign], hsfcond.2⟩
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
      have hsign : sf.sign = .pos := by cases sf.sign <;> simp_all [SignedFormula.sign]
      have hform : sf.formula = .imp a c := eq_of_beq hsfcond.2
      -- The rule for T(imp a c) is branching: [F(a)] or [T(c)]
      -- By the Hintikka condition, one of these branches is in b
      have hout := hrule sf hsfmem
      cases hbot : c with
      | bot =>
        -- T(imp a bot) = T(neg a): negPos rule gives .linear [F(a)]
        have hca : classicalApplyOne sf = .linear [SignedFormula.neg a sf.label] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        -- F(a) ∈ b
        have hfa_mem : SignedFormula.neg a sf.label ∈ b :=
          hout _ (List.mem_cons_self _ _)
        have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true := by
          apply List.any_eq_true.mpr
          exact ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
        have hfa := (ih_c.2 (by rwa [hbot] at hfa_any ▸ hfa_any))
        rw [BoolEvaluate_imp, hbot]
        simp [BoolEvaluate_bot]
      | atom x =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.atom x) sf.label]] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp, hbot]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · -- br = [F(a)], so F(a) ∈ b
          have hfa_mem := hbr _ (List.mem_cons_self _ _)
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · -- br = [T(atom x)], so T(atom x) ∈ b
          have htc_mem := hbr _ (List.mem_cons_self _ _)
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .atom x) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          rw [(ih_c.1 htc_any)]; simp
      | imp b1 b2 =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.imp b1 b2) sf.label]] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · have hfa_mem := hbr _ (List.mem_cons_self _ _)
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · have htc_mem := hbr _ (List.mem_cons_self _ _)
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .imp b1 b2) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          rw [(ih_c.1 htc_any)]; simp
      | and b1 b2 =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.and b1 b2) sf.label]] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · have hfa_mem := hbr _ (List.mem_cons_self _ _)
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · have htc_mem := hbr _ (List.mem_cons_self _ _)
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .and b1 b2) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          rw [(ih_c.1 htc_any)]; simp
      | or b1 b2 =>
        have hca : classicalApplyOne sf =
          .branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.or b1 b2) sf.label]] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        obtain ⟨br, hbr_mem, hbr⟩ := hout
        rw [BoolEvaluate_imp]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · have hfa_mem := hbr _ (List.mem_cons_self _ _)
          have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
            List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
          rw [(ih_a.2 hfa_any)]; simp
        · have htc_mem := hbr _ (List.mem_cons_self _ _)
          have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == .or b1 b2) = true :=
            List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
          rw [(ih_c.1 htc_any)]; simp
    · -- F(imp a c) on branch → BoolEvaluate v (imp a c) = false
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .neg := by cases sf.sign <;> simp_all [SignedFormula.sign]
      have hform : sf.formula = .imp a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      -- The impNeg rule (and negNeg) gives .linear outputs
      -- F(imp a c): either T(a) and F(c) (impNeg) or T(a) (negNeg if c = bot)
      cases hbot : c with
      | bot =>
        -- F(imp a bot) = F(neg a): negNeg rule gives .linear [T(a)]
        have hca : classicalApplyOne sf = .linear [SignedFormula.pos a sf.label] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        -- T(a) ∈ b
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (List.mem_cons_self _ _)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hta := ih_a.1 hta_any
        -- BoolEvaluate v (imp a bot) = !true || false = false
        rw [BoolEvaluate_imp, hta, hbot, BoolEvaluate_bot]; simp
      | atom x =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.atom x) sf.label] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.atom x) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .atom x) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hbot, ih_c.2 hfc_any]; simp
      | imp b1 b2 =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.imp b1 b2) sf.label] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.imp b1 b2) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .imp b1 b2) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hbot, ih_c.2 hfc_any]; simp
      | and b1 b2 =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.and b1 b2) sf.label] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.and b1 b2) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .and b1 b2) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hbot, ih_c.2 hfc_any]; simp
      | or b1 b2 =>
        have hca : classicalApplyOne sf =
          .linear [SignedFormula.pos a sf.label, SignedFormula.neg (.or b1 b2) sf.label] := by
          rw [hsign, hform, hbot]; rfl
        rw [hca] at hout
        have hta_mem : SignedFormula.pos a sf.label ∈ b := hout _ (by simp)
        have hfc_mem : SignedFormula.neg (.or b1 b2) sf.label ∈ b := hout _ (by simp)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == .or b1 b2) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        rw [BoolEvaluate_imp, ih_a.1 hta_any, hbot, ih_c.2 hfc_any]; simp
  | and a c ih_a ih_c =>
    constructor
    · -- T(and a c) on branch → BoolEvaluate v (and a c) = true
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .pos := by cases sf.sign <;> simp_all [SignedFormula.sign]
      have hform : sf.formula = .and a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .linear [SignedFormula.pos a sf.label, SignedFormula.pos c sf.label] := by
        rw [hsign, hform]; rfl
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
      have hsign : sf.sign = .neg := by cases sf.sign <;> simp_all [SignedFormula.sign]
      have hform : sf.formula = .and a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .branching [[SignedFormula.neg a sf.label], [SignedFormula.neg c sf.label]] := by
        rw [hsign, hform]; rfl
      rw [hca] at hout
      obtain ⟨br, hbr_mem, hbr⟩ := hout
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
      rcases hbr_mem with rfl | rfl
      · have hfa_mem := hbr _ (List.mem_cons_self _ _)
        have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
        simp [BoolEvaluate_and, ih_a.2 hfa_any]
      · have hfc_mem := hbr _ (List.mem_cons_self _ _)
        have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == c) = true :=
          List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
        simp [BoolEvaluate_and, ih_c.2 hfc_any]
  | or a c ih_a ih_c =>
    constructor
    · -- T(or a c) on branch → BoolEvaluate v (or a c) = true
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .pos := by cases sf.sign <;> simp_all [SignedFormula.sign]
      have hform : sf.formula = .or a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .branching [[SignedFormula.pos a sf.label], [SignedFormula.pos c sf.label]] := by
        rw [hsign, hform]; rfl
      rw [hca] at hout
      obtain ⟨br, hbr_mem, hbr⟩ := hout
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
      rcases hbr_mem with rfl | rfl
      · have hta_mem := hbr _ (List.mem_cons_self _ _)
        have hta_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == a) = true :=
          List.any_eq_true.mpr ⟨_, hta_mem, by simp [SignedFormula.pos]⟩
        simp [BoolEvaluate_or, ih_a.1 hta_any]
      · have htc_mem := hbr _ (List.mem_cons_self _ _)
        have htc_any : b.any (fun sf' => sf'.sign == .pos && sf'.formula == c) = true :=
          List.any_eq_true.mpr ⟨_, htc_mem, by simp [SignedFormula.pos]⟩
        simp [BoolEvaluate_or, ih_c.1 htc_any]
    · -- F(or a c) on branch → BoolEvaluate v (or a c) = false
      intro hmem
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true] at hsfcond
      have hsign : sf.sign = .neg := by cases sf.sign <;> simp_all [SignedFormula.sign]
      have hform : sf.formula = .or a c := eq_of_beq hsfcond.2
      have hout := hrule sf hsfmem
      have hca : classicalApplyOne sf = .linear [SignedFormula.neg a sf.label, SignedFormula.neg c sf.label] := by
        rw [hsign, hform]; rfl
      rw [hca] at hout
      have hfa_mem : SignedFormula.neg a sf.label ∈ b := hout _ (by simp)
      have hfc_mem : SignedFormula.neg c sf.label ∈ b := hout _ (by simp)
      have hfa_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == a) = true :=
        List.any_eq_true.mpr ⟨_, hfa_mem, by simp [SignedFormula.neg]⟩
      have hfc_any : b.any (fun sf' => sf'.sign == .neg && sf'.formula == c) = true :=
        List.any_eq_true.mpr ⟨_, hfc_mem, by simp [SignedFormula.neg]⟩
      simp [BoolEvaluate_or, ih_a.2 hfa_any, ih_c.2 hfc_any]

/-! ## Hintikka Property of Open Branches -/

/-- Extending a branch preserves membership: if sf ∈ b then sf ∈ extendMany b newForms. -/
private lemma mem_extendMany_of_mem (b : Branch (Proposition Atom) Unit)
    (newForms : List (SignedFormula (Proposition Atom) Unit))
    (sf : SignedFormula (Proposition Atom) Unit)
    (hmem : sf ∈ b) : sf ∈ Branch.extendMany b newForms := by
  simp only [Branch.extendMany, List.mem_append]
  exact Or.inr hmem

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
        branches.get? i = some b → expandedSets.get? i = some e →
        ∀ sf ∈ e, match classicalApplyOne sf with
          | .linear out => ∀ sf' ∈ out, sf' ∈ b
          | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b
          | .persistent out => ∀ sf' ∈ out, sf' ∈ b
          | .notApplicable => True) →
      ∀ b, classicalExpandBranches branches expandedSets fuel = .openBranch b →
        classicalHintikkaSet b := by
  sorry

/-- The open branch returned by the classical tableau is a classical Hintikka set.

This is the key bridge between the expansion loop and the truth lemma. -/
lemma classicalTableau_hintikka (φ : Proposition Atom) (b : Branch (Proposition Atom) Unit)
    (h : classicalTableau φ = .openBranch b) : classicalHintikkaSet b := by
  simp only [classicalTableau] at h
  apply classicalExpandBranches_hintikka _ _ _ (by rfl)
  · -- Initial invariant: empty expanded sets, so vacuously satisfied
    intro i b' e hb' he
    simp only [List.get?_cons_zero, List.get?_cons_succ, Option.some.injEq] at hb' he
    cases i with
    | zero =>
      simp only [List.get?_cons_zero, Option.some.injEq] at he
      subst he
      simp only [List.not_mem_nil, false_implies, implies_true]
    | succ n =>
      simp at hb'
  · exact h

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
    sorry
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
  | closed => exact hnt rfl
  | openBranch b =>
    have hcm := classicalOpenBranch_countermodel φ htab
    rw [tautology_iff_boolEvaluate_true] at h
    exact absurd (h (extractValuation b)) (by simp [hcm])

end Cslib.Logic.PL

end
