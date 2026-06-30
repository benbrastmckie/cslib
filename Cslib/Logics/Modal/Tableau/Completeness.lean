/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.LoopInduction

/-! # Modal K Tableau Completeness

This module proves completeness of the modal K tableau: if the tableau returns an open
branch, we can extract a finite Kripke countermodel refuting the formula.

## Main Results

- `extractModel`: Extract a Kripke model from an open branch + accessibility relation.
- `modalTruthLemma`: Truth in the extracted model tracks signed membership in the branch.
- `modalOpenBranch_countermodel`: An open branch with Hintikka property yields a countermodel.
- `modalTableau_complete`: `modalTableau φ = .openBranch b acc → ¬ kValid φ`.
- `modalTableau_decides`: `modalTableau φ = .closed ↔ kValid φ`.

## Strategy

Given an open saturated branch `b` with accessibility relation `acc`, define
`extractModel b acc` with relation `r w w' := acc.hasEdge w w' = true` and
valuation `v w p := T(atom p)@w ∈ b`. The modal truth lemma then shows every
`T(φ)@w ∈ b` is satisfied and every `F(φ)@w ∈ b` is falsified.

## Box Rule Design

- T(□φ)@w: handled by the `persistent` clause. `boxPropagation b acc φ w` is
  either empty (all `T(φ)@w'` already in `b`) or the persistent condition forces
  them in. Either way, all successors of `w` have `T(φ)@w'` in `b`.
- F(□φ)@w: handled by the explicit witness conjunct of `modalHintikkaSet`:
  `∃ w', acc.hasEdge w w' = true ∧ F(φ)@w' ∈ b`.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v u
variable {Atom : Type v} [DecidableEq Atom] [Hashable Atom]

/-! ## Model Extraction -/

/-- Extract a Kripke model from an open saturated branch `b` and accessibility relation `acc`.

The world type is `WorldIndex` (= Nat). The relation reads from `acc`; the valuation
maps atom `p` at world `w` to `true` iff `T(atom p)@w ∈ b`. -/
def extractModel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom where
  r w w' := acc.hasEdge w w' = true
  v w p  := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true

/-! ## Basic Model Properties -/

/-- Atom satisfaction in `extractModel b acc` at world `w` is equivalent to
`T(atom p)@w` appearing on the branch `b`. -/
lemma extractModel_atom_sat_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (p : Atom) :
    Satisfies (extractModel b acc) w (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true := by
  simp only [Satisfies, extractModel]

/-- `T(atom p)@w ∈ b` implies atom `p` is satisfied at `w` in `extractModel b acc`. -/
lemma extractModel_atomPos_sat
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (p : Atom)
    (hmem : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    Satisfies (extractModel b acc) w (.atom p) := by
  rw [extractModel_atom_sat_iff, List.any_eq_true]
  exact ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩

/-- `⊥` is never satisfied at any world in `extractModel b acc`. -/
lemma extractModel_bot_false
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) :
    ¬ Satisfies (extractModel b acc) w .bot := by
  simp only [Satisfies]

/-! ## Open-Branch Helpers -/

/-- An open modal branch contains no `T(⊥)@w` for any world `w`. -/
lemma openBranch_noTBot
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hopen : isModalClosed b = false) (w : WorldIndex) :
    (⟨.pos, .bot, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  intro hmem
  simp only [isModalClosed, ClosureCondition.isClosed, ClosureCondition.findClosure] at hopen
  cases hfind : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) with
  | some _ => simp [hfind] at hopen
  | none =>
    have hno := List.find?_eq_none.mp hfind ⟨.pos, .bot, w⟩ hmem
    simp [SignedFormula.isPos, Sign.isPos] at hno

/-- If `T(φ)@w ∈ b` and the branch is open, then `F(φ)@w ∉ b`. -/
lemma openBranch_noContradiction
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hopen : isModalClosed b = false) (φ : Proposition Atom) (w : WorldIndex)
    (hpos : (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  intro hneg
  simp only [isModalClosed, ClosureCondition.isClosed, ClosureCondition.findClosure] at hopen
  cases hfind_bot : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) with
  | some _ => simp [hfind_bot] at hopen
  | none =>
    simp only [hfind_bot] at hopen
    cases hcontra : b.findContradiction with
    | some pair => simp [hcontra] at hopen
    | none =>
      simp only [Branch.findContradiction, List.findSome?_eq_none_iff] at hcontra
      have hno := hcontra ⟨.pos, φ, w⟩ hpos
      simp only [SignedFormula.isPos, Sign.isPos, ↓reduceIte] at hno
      have hany : b.any (fun sf' => sf'.sign == .neg && sf'.formula == φ && sf'.label == w) = true :=
        List.any_eq_true.mpr ⟨⟨.neg, φ, w⟩, hneg, by simp⟩
      simp [hany] at hno

/-! ## Per-Rule Semantic Bridge Lemmas (Phase 5b) -/

/-- Box-positive bridge: `T(□ψ)@w ∈ b`, `acc.hasEdge w w' = true`, `modalHintikkaSet b acc`
imply `T(ψ)@w' ∈ b`.

Proof by contradiction: if `T(ψ)@w' ∉ b`, then `T(ψ)@w' ∈ boxPropagation b acc ψ w`
(since `w' ∈ successorsOf w` and the filtering only excludes formulas already in `b`).
So `boxPropagation` is non-empty and `modalApplyOne` returns `.persistent`, whose Hintikka
condition forces `T(ψ)@w' ∈ b`, a contradiction. -/
lemma hintikka_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : acc.hasEdge w w' = true) :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  -- Apply the Hintikka rule condition to T(□ψ)@w (non-boxNeg case)
  have hcond := hrule ⟨.pos, .box ψ, w⟩ hmem
  simp only at hcond
  -- Unfold modalApplyOne for T(□ψ)@w: propositional rules don't match .box, so boxPos fires
  simp only [modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
    modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hcond
  -- The boxPos case: `if boxPropagation b acc ψ w |>.isEmpty then notApplicable else persistent`
  split_ifs at hcond with hemp
  · -- hemp : boxPropagation b acc ψ w = [] (via isEmpty)
    -- This means: for all w'' ∈ successorsOf w, T(ψ)@w'' ∈ b
    by_contra habs
    -- T(ψ)@w' ∉ b, but w' ∈ successorsOf w (from hr)
    simp only [boxPropagation, List.filterMap_eq_nil_iff] at hemp
    -- w' ∈ acc.successorsOf w
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hr
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    -- hemp applied to w' gives: if T(ψ)@w' ∈ b then it's not in the filterMap output; but
    -- since this is "filterMap_eq_nil_iff", every element of successorsOf maps to none
    have hnil := hemp w' hw'_succ
    simp only at hnil
    split_ifs at hnil with hinb
    · -- T(ψ)@w' ∈ b (via b.any = true), contradicts habs
      simp only [List.any_eq_true] at hinb
      obtain ⟨sf', hsf'mem, hbeq⟩ := hinb
      simp only [beq_iff_eq] at hbeq
      rw [← hbeq] at hsf'mem
      exact habs hsf'mem
    · simp at hnil
  · -- hemp : boxPropagation b acc ψ w ≠ [] (via isEmpty)
    -- hcond : ∀ sf' ∈ boxPropagation b acc ψ w, sf' ∈ b
    by_contra habs
    -- T(ψ)@w' ∉ b; show T(ψ)@w' ∈ boxPropagation
    have hw'_in_boxProp : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        boxPropagation b acc ψ w := by
      simp only [boxPropagation, Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hr
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      refine ⟨(src, tgt), hedge_mem, ?_⟩
      simp only [hbeq.1, ↓reduceIte]
      simp only [hbeq.2]
      split_ifs with hinb
      · -- b.any (· == T(ψ)@w') = true → T(ψ)@w' ∈ b → contradiction
        exfalso; apply habs
        simp only [List.any_eq_true] at hinb
        obtain ⟨sf', hsf'mem, hbeq'⟩ := hinb
        simp only [beq_iff_eq] at hbeq'
        rw [← hbeq'] at hsf'mem
        exact hsf'mem
      · rfl
    exact habs (hcond _ hw'_in_boxProp)

/-- Box-negative bridge: `F(□ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' = true ∧ F(ψ)@w' ∈ b`.

This follows directly from the third conjunct of `modalHintikkaSet`. -/
lemma hintikka_box_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧ (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2 ψ w hmem

/-- Implication-positive bridge: `T(a → c)@w ∈ b` and `modalHintikkaSet b acc`
imply `F(a)@w ∈ b ∨ T(c)@w ∈ b`.

Proof: unfold `modalApplyOne` on `T(a → c)@w`. For a "pure" implication (not neg/or/and),
the branching rule gives branches `[[F(a)@w], [T(c)@w]]`, and the Hintikka branching
condition yields one complete branch. For `T(a → ⊥)` (neg), the linear rule gives `[F(a)@w]`,
so `F(a)@w ∈ b` and `Or.inl` applies. -/
lemma hintikka_imp_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (a c : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .imp a c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∨
    (⟨.pos, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.pos, .imp a c, w⟩ hmem
  simp only at hcond
  simp only [modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
    modalImpOf?, modalNegOf?, RuleResult.isApplicable] at hcond
  -- Case split on the structure of the imp formula to determine which propositional rule fires
  cases c with
  | bot =>
    -- T(a → ⊥) = T(¬a): neg rule → linear [F(a)@w]
    cases a with
    | atom name =>
      -- T(¬(atom name)): linear rule → F(atom name)@w
      simp only [List.map, List.find?, Option.isSome, ↓reduceIte] at hcond
      simp only [List.mem_singleton] at hcond
      exact Or.inl (hcond ⟨.neg, .atom name, w⟩ (List.mem_cons_self _ _))
    | bot =>
      -- T(⊥ → ⊥) = T(¬⊥) = T(⊤): linear rule → F(⊥)@w
      simp only [List.map, List.find?, Option.isSome, ↓reduceIte] at hcond
      exact Or.inl (hcond ⟨.neg, .bot, w⟩ (List.mem_cons_self _ _))
    | imp a1 a2 =>
      -- T(¬(a1 → a2)): check if a1 → a2 has special structure
      simp only [List.map, List.find?, Option.isSome] at hcond
      split_ifs at hcond with h1
      all_goals (
        simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hcond
        try exact Or.inl (hcond ⟨.neg, .imp a1 a2, w⟩ (Or.inl rfl))
        try exact Or.inl (hcond ⟨.neg, .imp a1 a2, w⟩ (List.mem_cons_self _ _)))
    | box a1 =>
      simp only [List.map, List.find?, Option.isSome, ↓reduceIte] at hcond
      exact Or.inl (hcond ⟨.neg, .box a1, w⟩ (List.mem_cons_self _ _))
  | atom name =>
    -- T(a → atom name): pure implication, branching rule
    simp only [List.map, List.find?, Option.isSome] at hcond
    split_ifs at hcond with h1 h2
    all_goals simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false,
      List.mem_append] at hcond
    all_goals (
      try {
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl (hbr ⟨.neg, a, w⟩ (List.mem_cons_self _ _))
        · exact Or.inr (hbr ⟨.pos, .atom name, w⟩ (List.mem_cons_self _ _))
      })
  | imp c1 c2 =>
    simp only [List.map, List.find?, Option.isSome] at hcond
    split_ifs at hcond with h1 h2 h3
    all_goals simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false,
      List.mem_append] at hcond
    all_goals (
      try {
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl (hbr ⟨.neg, a, w⟩ (List.mem_cons_self _ _))
        · exact Or.inr (hbr ⟨.pos, .imp c1 c2, w⟩ (List.mem_cons_self _ _))
      })
  | box c1 =>
    simp only [List.map, List.find?, Option.isSome, ↓reduceIte] at hcond
    obtain ⟨br, hbr_mem, hbr⟩ := hcond
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hbr_mem
    rcases hbr_mem with rfl | rfl
    · exact Or.inl (hbr ⟨.neg, a, w⟩ (List.mem_cons_self _ _))
    · exact Or.inr (hbr ⟨.pos, .box c1, w⟩ (List.mem_cons_self _ _))

/-- Implication-negative bridge: `F(a → c)@w ∈ b` and `modalHintikkaSet b acc`
imply `T(a)@w ∈ b` and either `c = .bot` or `F(c)@w ∈ b`.

When `c ≠ .bot`, the F(a→c) linear alpha rule gives `[T(a)@w, F(c)@w]` and the
Hintikka condition forces both into `b`.  When `c = .bot`, `F(a→⊥) = F(¬a)` is
handled by the neg rule which gives only `[T(a)@w]`; the `Or.inl rfl` branch
suffices because the truth lemma only needs `T(a)@w` to prove
`¬(Satisfies m w a → False)`. -/
lemma hintikka_imp_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (a c : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .imp a c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∧
    (c = .bot ∨ (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.neg, .imp a c, w⟩ hmem
  simp only at hcond
  simp only [modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
    modalImpOf?, modalNegOf?, RuleResult.isApplicable] at hcond
  cases c with
  | bot =>
    -- F(a → ⊥) = F(¬a): the neg rule fires, giving linear output [T(a)@w].
    -- The new signature only requires T(a)@w ∧ (.bot = .bot ∨ F(.bot)@w ∈ b),
    -- so the second conjunct is Or.inl rfl.
    simp only [List.map, List.find?, Option.isSome] at hcond
    split_ifs at hcond with h1
    · simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hcond
      exact ⟨hcond ⟨.pos, a, w⟩ (List.mem_cons_self _ _), Or.inl rfl⟩
    · simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hcond
      exact ⟨hcond ⟨.pos, a, w⟩ (List.mem_cons_self _ _), Or.inl rfl⟩
  | atom name =>
    simp only [List.map, List.find?, Option.isSome] at hcond
    split_ifs at hcond with h1 h2
    all_goals (
      simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hcond
      try exact ⟨hcond ⟨.pos, a, w⟩ (List.mem_cons_self _ _),
                 Or.inr (hcond ⟨.neg, .atom name, w⟩ (by simp))⟩)
  | imp c1 c2 =>
    simp only [List.map, List.find?, Option.isSome] at hcond
    split_ifs at hcond with h1 h2 h3
    all_goals (
      simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hcond
      try exact ⟨hcond ⟨.pos, a, w⟩ (List.mem_cons_self _ _),
                 Or.inr (hcond ⟨.neg, .imp c1 c2, w⟩ (by simp))⟩)
  | box c1 =>
    simp only [List.map, List.find?, Option.isSome, ↓reduceIte] at hcond
    exact ⟨hcond ⟨.pos, a, w⟩ (List.mem_cons_self _ _),
           Or.inr (hcond ⟨.neg, .box c1, w⟩ (by simp))⟩

/-! ## Modal Truth Lemma (Phase 5c) -/

/-- Modal Truth Lemma: membership in a Hintikka branch tracks satisfaction in the
extracted Kripke model `extractModel b acc`.

For every formula `φ` and world `w`, `T(φ)@w ∈ b` implies `φ` is satisfied at `w`
in `extractModel b acc`, and `F(φ)@w ∈ b` implies it is not.

Proof by structural induction on `φ`.  The atom case uses `extractModel_atomPos_sat`
(positive) and `openBranch_noContradiction` (negative).  The bot case uses
`openBranch_noTBot` (positive is impossible) and `extractModel_bot_false` (negative).
The imp and box cases delegate to the bridge lemmas `hintikka_imp_pos`,
`hintikka_imp_neg`, `hintikka_box_pos`, and `hintikka_box_neg`. -/
lemma modalTruthLemma
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) := by
  intro φ
  induction φ with
  | atom p =>
    intro w
    constructor
    · exact extractModel_atomPos_sat b acc w p
    · intro hmem hsat
      simp only [Satisfies, extractModel, List.any_eq_true] at hsat
      obtain ⟨sf, hsf_mem, hcond⟩ := hsat
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
      -- Convert BEq to Eq; eq_of_beq works because Proposition Atom has LawfulBEq via DecidableEq
      have hsign_eq : sf.sign = .pos := eq_of_beq hsign
      have hform_eq : sf.formula = .atom p := eq_of_beq hform
      have hlab_eq : sf.label = w := eq_of_beq hlab
      have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
      exact openBranch_noContradiction b hH.1 (.atom p) w hpos hmem
  | bot =>
    intro w
    constructor
    · intro hmem
      exact absurd hmem (openBranch_noTBot b hH.1 w)
    · intro _
      exact extractModel_bot_false b acc w
  | imp a c ih_a ih_c =>
    intro w
    constructor
    · intro hmem hsa
      rcases hintikka_imp_pos b acc hH a c w hmem with ha | hc
      · exact absurd hsa ((ih_a w).2 ha)
      · exact (ih_c w).1 hc
    · intro hmem
      intro hsa
      rcases hintikka_imp_neg b acc hH a c w hmem with ⟨hpos_a, hc_or⟩
      have hsa_val : Satisfies (extractModel b acc) w a := (ih_a w).1 hpos_a
      rcases hc_or with rfl | hF_c
      · exact extractModel_bot_false b acc w (hsa hsa_val)
      · exact (ih_c w).2 hF_c (hsa hsa_val)
  | box ψ ih_ψ =>
    intro w
    constructor
    · intro hmem w' hr
      exact (ih_ψ w').1 (hintikka_box_pos b acc hH ψ w w' hmem hr)
    · intro hmem hall
      obtain ⟨w', hw', hF⟩ := hintikka_box_neg b acc hH ψ w hmem
      exact (ih_ψ w').2 hF (hall w' hw')

/-! ## Open-Branch Countermodel (Phase 5d) -/

/-- An open Hintikka branch with `F(φ)@0 ∈ b` yields a Kripke countermodel to `φ`.

The extracted model `extractModel b acc` falsifies `φ` at world `0`. -/
theorem modalOpenBranch_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hH : modalHintikkaSet b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModel b acc) 0 φ :=
  (modalTruthLemma b acc hH φ 0).2 hF

end Cslib.Logic.Modal.Tableau

end
