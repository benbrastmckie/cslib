/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.Saturation

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

omit [Hashable Atom] in
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

omit [Hashable Atom] in
/-- `⊥` is never satisfied at any world in `extractModel b acc`. -/
lemma extractModel_bot_false
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) :
    ¬ Satisfies (extractModel b acc) w .bot := by
  simp [Satisfies]

/-! ## Open-Branch Helpers -/

omit [Hashable Atom] in
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
    exact hno rfl

omit [Hashable Atom] in
/-- If `T(φ)@w ∈ b` and the branch is open, then `F(φ)@w ∉ b`. -/
lemma openBranch_noContradiction
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hopen : isModalClosed b = false) (φ : Proposition Atom) (w : WorldIndex)
    (hpos : (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  intro hneg
  simp only [isModalClosed, ClosureCondition.isClosed, ClosureCondition.findClosure] at hopen
  cases hfind_bot : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom))
    with
  | some _ => simp [hfind_bot] at hopen
  | none =>
    simp only [hfind_bot] at hopen
    cases hcontra : Branch.findContradiction b with
    | some pair => simp [hcontra] at hopen
    | none =>
      simp only [Branch.findContradiction, List.findSome?_eq_none_iff] at hcontra
      have hno := hcontra ⟨.pos, φ, w⟩ hpos
      simp only [SignedFormula.isPos, Sign.isPos, ↓reduceIte] at hno
      have hany :
          b.any (fun sf' => sf'.sign == .neg && sf'.formula == φ && sf'.label == w) = true :=
        List.any_eq_true.mpr ⟨⟨.neg, φ, w⟩, hneg, by simp⟩
      simp [hany] at hno

/-! ## Per-Rule Semantic Bridge Lemmas (Phase 5b) -/

omit [Hashable Atom] in
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
  -- Unfold modalApplyOne for T(□ψ)@w: propositional rules return none, so boxPos fires
  simp only [modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
    modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hcond
  -- Reduce outer if: none.getD notApplicable = notApplicable → match gives false → if false
  simp [Option.getD_none] at hcond
  -- w' is a successor of w
  have hw'_succ : w' ∈ acc.successorsOf w := by
    simp only [Accessibility.successorsOf, List.mem_filterMap]
    simp only [Accessibility.hasEdge, List.any_eq_true] at hr
    obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
    exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
  -- The boxPos case: if boxPropagation = [] then notApplicable else persistent
  split_ifs at hcond with hemp
  · -- hemp : boxPropagation b acc ψ w = [] → every successor already has T(ψ) in b
    simp only [boxPropagation, List.filterMap_eq_nil_iff] at hemp
    have hnil := hemp w' hw'_succ
    by_cases hinb :
        (b.any fun x => x == (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
    · -- T(ψ)@w' already in b
      simp only [List.any_eq_true, beq_iff_eq] at hinb
      obtain ⟨sf', hsf'mem, rfl⟩ := hinb
      exact hsf'mem
    · simp [if_neg hinb] at hnil
      exact hnil
  · -- hemp : boxPropagation ≠ [] → hcond : ∀ sf' ∈ boxPropagation, sf' ∈ b
    by_cases hinb :
        (b.any fun x => x == (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
    · -- T(ψ)@w' already in b
      simp only [List.any_eq_true, beq_iff_eq] at hinb
      obtain ⟨sf', hsf'mem, rfl⟩ := hinb
      exact hsf'mem
    · -- T(ψ)@w' ∉ b, so T(ψ)@w' ∈ boxPropagation; apply hcond
      apply hcond
      simp only [boxPropagation, List.mem_filterMap]
      exact ⟨w', hw'_succ, if_neg hinb⟩

omit [Hashable Atom] in
/-- Box-negative bridge: `F(□ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' = true ∧ F(ψ)@w' ∈ b`.

This follows directly from the third conjunct of `modalHintikkaSet`. -/
lemma hintikka_box_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2 ψ w hmem

/-! ## Propositional Rule Reduction (encoding-aware)

Because `Proposition Atom` Lukasiewicz-encodes `and`/`or`/`neg` as nested `imp`, a single
`imp a c` may fire the `andPos`/`orPos`/`negPos` rule rather than the proper `impPos` rule.
The truth lemma therefore cannot use uniform implication bridge lemmas; instead it reduces
`modalApplyOne` on an `imp` to a decomposer-driven case split and recurses with strong
induction on `modalComplexity`. The lemmas below provide that reduction. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalAndOf? φ` succeeds then `φ` is the encoded conjunction. -/
lemma modalAndOf?_eq {φ x y : Proposition Atom} (h : modalAndOf? φ = some (x, y)) :
    φ = .imp (.imp x (.imp y .bot)) .bot := by
  unfold modalAndOf? at h; split at h <;> simp_all

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalOrOf? φ` succeeds then `φ` is the encoded disjunction. -/
lemma modalOrOf?_eq {φ x y : Proposition Atom} (h : modalOrOf? φ = some (x, y)) :
    φ = .imp (.imp x .bot) y := by
  unfold modalOrOf? at h; split at h <;> simp_all

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalImpOf? φ` succeeds then `φ` is the proper implication `x → y`. -/
lemma modalImpOf?_eq {φ x y : Proposition Atom} (h : modalImpOf? φ = some (x, y)) :
    φ = .imp x y := by
  unfold modalImpOf? at h
  split at h
  · next a b =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalNegOf? φ` succeeds then `φ` is the encoded negation `x → ⊥`. -/
lemma modalNegOf?_eq {φ x : Proposition Atom} (h : modalNegOf? φ = some x) :
    φ = .imp x .bot := by
  unfold modalNegOf? at h; split at h <;> simp_all

/-- Reduction of `tryAllPropRules` on a positively-signed formula to a priority-ordered
case split on the four decomposition functions (and > or > imp > neg). -/
lemma tryAllPropRules_pos {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (φ : F) (l : L) :
    tryAllPropRules andOf? orOf? impOf? negOf? ⟨.pos, φ, l⟩ =
      match andOf? φ with
      | some (x, y) => .linear [⟨.pos, x, l⟩, ⟨.pos, y, l⟩]
      | none =>
        match orOf? φ with
        | some (x, y) => .branching [[⟨.pos, x, l⟩], [⟨.pos, y, l⟩]]
        | none =>
          match impOf? φ with
          | some (x, y) => .branching [[⟨.neg, x, l⟩], [⟨.pos, y, l⟩]]
          | none =>
            match negOf? φ with
            | some x => .linear [⟨.neg, x, l⟩]
            | none => .notApplicable := by
  rcases hA : andOf? φ with _ | ⟨x, y⟩ <;> rcases hO : orOf? φ with _ | ⟨x, y⟩ <;>
    rcases hI : impOf? φ with _ | ⟨x, y⟩ <;> rcases hN : negOf? φ with _ | x <;>
    simp [tryAllPropRules, List.map, List.find?, applyPropRule, RuleResult.isApplicable,
      SignedFormula.pos, SignedFormula.neg, hA, hO, hI, hN]

/-- Reduction of `tryAllPropRules` on a negatively-signed formula. -/
lemma tryAllPropRules_neg {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (φ : F) (l : L) :
    tryAllPropRules andOf? orOf? impOf? negOf? ⟨.neg, φ, l⟩ =
      match andOf? φ with
      | some (x, y) => .branching [[⟨.neg, x, l⟩], [⟨.neg, y, l⟩]]
      | none =>
        match orOf? φ with
        | some (x, y) => .linear [⟨.neg, x, l⟩, ⟨.neg, y, l⟩]
        | none =>
          match impOf? φ with
          | some (x, y) => .linear [⟨.pos, x, l⟩, ⟨.neg, y, l⟩]
          | none =>
            match negOf? φ with
            | some x => .linear [⟨.pos, x, l⟩]
            | none => .notApplicable := by
  rcases hA : andOf? φ with _ | ⟨x, y⟩ <;> rcases hO : orOf? φ with _ | ⟨x, y⟩ <;>
    rcases hI : impOf? φ with _ | ⟨x, y⟩ <;> rcases hN : negOf? φ with _ | x <;>
    simp [tryAllPropRules, List.map, List.find?, applyPropRule, RuleResult.isApplicable,
      SignedFormula.pos, SignedFormula.neg, hA, hO, hI, hN]

omit [Hashable Atom] in
/-- When the propositional rules apply, `modalApplyOne` returns the propositional result. -/
lemma modalApplyOne_eq_prop_of_applicable
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable = true) :
    (modalApplyOne sf b acc).1
      = tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf := by
  simp only [modalApplyOne]
  rw [if_pos h]

/-- Reduction of `modalApplyOne` on a positive implication to a decomposer case split. -/
lemma modalApplyOne_imp_pos (a c : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.pos, .imp a c, w⟩ b acc).1 =
      match modalAndOf? (.imp a c) with
      | some (x, y) => .linear [⟨.pos, x, w⟩, ⟨.pos, y, w⟩]
      | none =>
        match modalOrOf? (.imp a c) with
        | some (x, y) => .branching [[⟨.pos, x, w⟩], [⟨.pos, y, w⟩]]
        | none =>
          match modalImpOf? (.imp a c) with
          | some (x, y) => .branching [[⟨.neg, x, w⟩], [⟨.pos, y, w⟩]]
          | none =>
            match modalNegOf? (.imp a c) with
            | some x => .linear [⟨.neg, x, w⟩]
            | none => .notApplicable := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .imp a c, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    rw [tryAllPropRules_pos]
    rcases hA : modalAndOf? (.imp a c) with _ | ⟨x, y⟩
    · rcases hO : modalOrOf? (.imp a c) with _ | ⟨x, y⟩
      · rcases hI : modalImpOf? (.imp a c) with _ | ⟨x, y⟩
        · rcases hN : modalNegOf? (.imp a c) with _ | x
          · exfalso
            rcases c with _|_|_|_ <;> rcases a with _|_|⟨a1, _|_|_|_⟩|_ <;>
              simp_all [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?]
          · simp [hA, hO, hI, hN, RuleResult.isApplicable]
        · simp [hA, hO, hI, RuleResult.isApplicable]
      · simp [hA, hO, RuleResult.isApplicable]
    · simp [hA, RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.pos, .imp a c, w⟩ b acc happ, tryAllPropRules_pos]
  rcases modalAndOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalOrOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalImpOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalNegOf? (.imp a c) with _ | x <;> rfl

/-- Reduction of `modalApplyOne` on a negative implication to a decomposer case split. -/
lemma modalApplyOne_imp_neg (a c : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.neg, .imp a c, w⟩ b acc).1 =
      match modalAndOf? (.imp a c) with
      | some (x, y) => .branching [[⟨.neg, x, w⟩], [⟨.neg, y, w⟩]]
      | none =>
        match modalOrOf? (.imp a c) with
        | some (x, y) => .linear [⟨.neg, x, w⟩, ⟨.neg, y, w⟩]
        | none =>
          match modalImpOf? (.imp a c) with
          | some (x, y) => .linear [⟨.pos, x, w⟩, ⟨.neg, y, w⟩]
          | none =>
            match modalNegOf? (.imp a c) with
            | some x => .linear [⟨.pos, x, w⟩]
            | none => .notApplicable := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .imp a c, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    rw [tryAllPropRules_neg]
    rcases hA : modalAndOf? (.imp a c) with _ | ⟨x, y⟩
    · rcases hO : modalOrOf? (.imp a c) with _ | ⟨x, y⟩
      · rcases hI : modalImpOf? (.imp a c) with _ | ⟨x, y⟩
        · rcases hN : modalNegOf? (.imp a c) with _ | x
          · exfalso
            rcases c with _|_|_|_ <;> rcases a with _|_|⟨a1, _|_|_|_⟩|_ <;>
              simp_all [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?]
          · simp [hA, hO, hI, hN, RuleResult.isApplicable]
        · simp [hA, hO, hI, RuleResult.isApplicable]
      · simp [hA, hO, RuleResult.isApplicable]
    · simp [hA, RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.neg, .imp a c, w⟩ b acc happ, tryAllPropRules_neg]
  rcases modalAndOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalOrOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalImpOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalNegOf? (.imp a c) with _ | x <;> rfl

/-! ## Modal Truth Lemma (Phase 5c) -/

/-- Modal Truth Lemma: membership in a Hintikka branch tracks satisfaction in the
extracted Kripke model `extractModel b acc`.

For every formula `φ` and world `w`, `T(φ)@w ∈ b` implies `φ` is satisfied at `w`
in `extractModel b acc`, and `F(φ)@w ∈ b` implies it is not.

Proof by strong induction on `modalComplexity φ`. The atom case uses
`extractModel_atomPos_sat`/`openBranch_noContradiction`; the bot case uses
`openBranch_noTBot`/`extractModel_bot_false`; the box case uses the bridge lemmas
`hintikka_box_pos`/`hintikka_box_neg`.

The `imp` case must inspect the Lukasiewicz encoding: `modalApplyOne` fires the
`and`/`or`/`neg` rule when the implication is an encoded connective. We reduce
`modalApplyOne` via `modalApplyOne_imp_pos`/`modalApplyOne_imp_neg` to a decomposer
case split, then recurse on the genuine sub-formulas (which are strictly smaller in
`modalComplexity`, hence reachable by the strong-induction hypothesis). Uniform
implication bridge lemmas are impossible here precisely because `T((φ→(ψ→⊥))→⊥)` fires
the conjunction rule, not the implication rule. -/
lemma modalTruthLemma
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModel b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModel b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    cases φ with
    | atom p =>
      refine ⟨extractModel_atomPos_sat b acc w p, ?_⟩
      intro hmem hsat
      simp only [Satisfies, extractModel, List.any_eq_true] at hsat
      obtain ⟨sf, hsf_mem, hcond⟩ := hsat
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
      have hsign_eq : sf.sign = .pos := eq_of_beq hsign
      have hform_eq : sf.formula = .atom p := eq_of_beq hform
      have hlab_eq : sf.label = w := eq_of_beq hlab
      have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
      exact openBranch_noContradiction b hH.1 (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hH.1 w), ?_⟩
      intro _; exact extractModel_bot_false b acc w
    | imp a c =>
      constructor
      · -- T(imp a c)@w ∈ b → Satisfies w (imp a c)
        intro hmem
        have hcond := hH.2.1 ⟨.pos, .imp a c, w⟩ hmem
        simp only at hcond
        rw [modalApplyOne_imp_pos] at hcond
        rcases hA : modalAndOf? (.imp a c) with _ | ⟨x, y⟩
        · rcases hO : modalOrOf? (.imp a c) with _ | ⟨x, y⟩
          · rcases hI : modalImpOf? (.imp a c) with _ | ⟨x, y⟩
            · rcases hN : modalNegOf? (.imp a c) with _ | x
              · exfalso
                rcases c with _|_|_|_ <;> rcases a with _|_|⟨a1, _|_|_|_⟩|_ <;>
                  simp_all [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?]
              · -- negPos: φ = ¬x; rule gives F(x)@w
                simp only [hA, hO, hI, hN] at hcond
                have hxmem : (⟨.neg, x, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
                  hcond ⟨.neg, x, w⟩ (by simp)
                have hshape := (modalNegOf?_eq hN).symm
                rw [Proposition.imp.injEq] at hshape
                obtain ⟨rfl, rfl⟩ := hshape
                exact (IH x (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
                  modalComplexity_atom, modalComplexity_bot]; omega) w).2 hxmem
            · -- impPos: proper implication, branching [[F x],[T y]]
              simp only [hA, hO, hI] at hcond
              have hshape := (modalImpOf?_eq hI).symm
              rw [Proposition.imp.injEq] at hshape
              obtain ⟨rfl, rfl⟩ := hshape
              intro hsx
              obtain ⟨br, hbr_mem, hbr⟩ := hcond
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · exact absurd hsx ((IH x (by rw [← hφ]; simp only [modalComplexity_imp,
                  modalComplexity_box, modalComplexity_atom, modalComplexity_bot]; omega) w).2
                  (hbr ⟨.neg, x, w⟩ (by simp)))
              · exact (IH y (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
                  modalComplexity_atom, modalComplexity_bot]; omega) w).1
                  (hbr ⟨.pos, y, w⟩ (by simp))
          · -- orPos: φ = x ∨ y, branching [[T x],[T y]]
            simp only [hA, hO] at hcond
            have hshape := (modalOrOf?_eq hO).symm
            rw [Proposition.imp.injEq] at hshape
            obtain ⟨rfl, rfl⟩ := hshape
            intro hsx
            obtain ⟨br, hbr_mem, hbr⟩ := hcond
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · exact absurd ((IH x (by rw [← hφ]; simp only [modalComplexity_imp,
                modalComplexity_box, modalComplexity_atom, modalComplexity_bot]; omega) w).1
                (hbr ⟨.pos, x, w⟩ (by simp))) hsx
            · exact (IH y (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
                modalComplexity_atom, modalComplexity_bot]; omega) w).1 (hbr ⟨.pos, y, w⟩ (by simp))
        · -- andPos: φ = x ∧ y, linear [T x, T y]
          simp only [hA] at hcond
          have hshape := (modalAndOf?_eq hA).symm
          rw [Proposition.imp.injEq] at hshape
          obtain ⟨rfl, rfl⟩ := hshape
          intro hsa
          exact hsa ((IH x (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
              modalComplexity_atom, modalComplexity_bot]; omega) w).1
              (hcond ⟨.pos, x, w⟩ (by simp)))
            ((IH y (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
              modalComplexity_atom, modalComplexity_bot]; omega) w).1
              (hcond ⟨.pos, y, w⟩ (by simp)))
      · -- F(imp a c)@w ∈ b → ¬ Satisfies w (imp a c)
        intro hmem
        have hcond := hH.2.1 ⟨.neg, .imp a c, w⟩ hmem
        simp only at hcond
        rw [modalApplyOne_imp_neg] at hcond
        rcases hA : modalAndOf? (.imp a c) with _ | ⟨x, y⟩
        · rcases hO : modalOrOf? (.imp a c) with _ | ⟨x, y⟩
          · rcases hI : modalImpOf? (.imp a c) with _ | ⟨x, y⟩
            · rcases hN : modalNegOf? (.imp a c) with _ | x
              · exfalso
                rcases c with _|_|_|_ <;> rcases a with _|_|⟨a1, _|_|_|_⟩|_ <;>
                  simp_all [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?]
              · -- negNeg: φ = ¬x; rule gives T(x)@w
                simp only [hA, hO, hI, hN] at hcond
                have hxmem : (⟨.pos, x, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
                  hcond ⟨.pos, x, w⟩ (by simp)
                have hshape := (modalNegOf?_eq hN).symm
                rw [Proposition.imp.injEq] at hshape
                obtain ⟨rfl, rfl⟩ := hshape
                intro hsa
                exact hsa ((IH x (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
                  modalComplexity_atom, modalComplexity_bot]; omega) w).1 hxmem)
            · -- impNeg: proper implication, linear [T x, F y]
              simp only [hA, hO, hI] at hcond
              have hxmem : (⟨.pos, x, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
                hcond ⟨.pos, x, w⟩ (by simp)
              have hymem : (⟨.neg, y, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
                hcond ⟨.neg, y, w⟩ (by simp)
              have hshape := (modalImpOf?_eq hI).symm
              rw [Proposition.imp.injEq] at hshape
              obtain ⟨rfl, rfl⟩ := hshape
              intro hsa
              exact (IH y (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
                modalComplexity_atom, modalComplexity_bot]; omega) w).2 hymem
                (hsa ((IH x (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
                  modalComplexity_atom, modalComplexity_bot]; omega) w).1 hxmem))
          · -- orNeg: φ = x ∨ y, linear [F x, F y]
            simp only [hA, hO] at hcond
            have hxmem : (⟨.neg, x, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
              hcond ⟨.neg, x, w⟩ (by simp)
            have hymem : (⟨.neg, y, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
              hcond ⟨.neg, y, w⟩ (by simp)
            have hshape := (modalOrOf?_eq hO).symm
            rw [Proposition.imp.injEq] at hshape
            obtain ⟨rfl, rfl⟩ := hshape
            intro hsa
            exact (IH y (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
              modalComplexity_atom, modalComplexity_bot]; omega) w).2 hymem
              (hsa (fun hsx => absurd hsx ((IH x (by rw [← hφ]; simp only [modalComplexity_imp,
                modalComplexity_box, modalComplexity_atom, modalComplexity_bot]; omega) w).2
                hxmem)))
        · -- andNeg: φ = x ∧ y, branching [[F x],[F y]]
          simp only [hA] at hcond
          have hshape := (modalAndOf?_eq hA).symm
          rw [Proposition.imp.injEq] at hshape
          obtain ⟨rfl, rfl⟩ := hshape
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact hsa (fun hsx _ => absurd hsx ((IH x (by rw [← hφ]; simp only [modalComplexity_imp,
              modalComplexity_box, modalComplexity_atom, modalComplexity_bot]; omega) w).2
              (hbr ⟨.neg, x, w⟩ (by simp))))
          · exact hsa (fun _ hsy => absurd hsy ((IH y (by rw [← hφ]; simp only [modalComplexity_imp,
              modalComplexity_box, modalComplexity_atom, modalComplexity_bot]; omega) w).2
              (hbr ⟨.neg, y, w⟩ (by simp))))
    | box ψ =>
      constructor
      · intro hmem w' hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
          modalComplexity_atom, modalComplexity_bot]; omega) w').1
          (hintikka_box_pos b acc hH ψ w w' hmem hr)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_box,
          modalComplexity_atom, modalComplexity_bot]; omega) w').2 hF (hall w' hw')

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

/-! ## Saturation Characterisation (Phase 4, task 442)

Two single-step lemmas about `modalStepBranch`, ported from the classical propositional
tableau's `classicalStepBranch_none_saturated` / `classicalStepBranch_hintikka_inv`
(`Classical/Completeness.lean:694,722`), feeding the future top-loop lemma
`modalExpandBranches_hintikka` (task 442 Phase 5).

`modalStepBranch_hintikka_inv` is stated against `(modalApplyOne sf b acc).1`, carving out
`.box _`-shaped formulas (both signs): `boxNeg` (`.neg, .box _`) mints a branch-fresh world
`modalNextWorld b`, so re-evaluating it at a strictly larger branch always yields a witness
that (by freshness) cannot lie on that branch — exactly why `modalHintikkaSet`'s own second
conjunct carves it out. `boxPos` (`.pos, .box _`) reads `boxPropagation b acc`, so it is
also branch/`acc`-dependent, but it is `.persistent` and never enters the expanded set `e`
(`Saturation.lean:116-117`; matches the `.persistent` case below, where `e` is left
unchanged), so the carve-out costs nothing in the lemma's actual use. Every other formula
shape (`.atom _`, `.bot`, `.imp _ _`) reaches `modalApplyOne`'s rule dispatch in a way that
is provably independent of the branch/`acc` (`modalApplyOne_fst_eq_of_not_box` below):
propositional rules are formula-structural, and `.atom`/`.bot` never match a modal rule.
In particular, the Lukasiewicz-encoded diamond patterns
(`.pos`/`.neg, .imp (.box (.imp _ .bot)) .bot`) are always intercepted by the propositional
negation decoder `modalNegOf?` first (it unconditionally matches `.imp a .bot`), so the
branch/`acc`-dependent `diamondPos`/`diamondNeg` arms of `modalApplyOne`'s modal-rule match
(`Rules.lean:91,142`) are dead code in practice — never actually reached. -/

/-- The box-excluded rule-application clause: for a signed formula `⟨s, φ, w⟩`, either `φ` is
`box`-shaped (vacuously `True` — handled elsewhere, see the section note above), or the
`modalApplyOne` rule output for `⟨s, φ, w⟩` evaluated at `(X, Y)` is already present on `X`.
Factored into a named `def` (rather than an inline `match` repeated at each use site) so that
Lean's equation compiler produces one shared matcher, avoiding spurious dependent-match
mismatches when the same clause is used as both a hypothesis and a goal across lemmas. -/
def modalHintikkaClause (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (X : List (SignedFormula (Proposition Atom) WorldIndex)) (Y : Accessibility) : Prop :=
  match φ with
  | .box _ => True
  | _ =>
    match (modalApplyOne ⟨s, φ, w⟩ X Y).1 with
    | .linear out => ∀ sf' ∈ out, sf' ∈ X
    | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ X
    | .persistent out => ∀ sf' ∈ out, sf' ∈ X
    | .notApplicable => True

/-- For a non-`box`-shaped signed formula, `modalApplyOne`'s rule result does not depend on
the branch or accessibility relation. Propositional rules are formula-structural
(`modalApplyOne_imp_pos`/`modalApplyOne_imp_neg`, themselves independent of `b`/`acc`), and
`.atom`/`.bot` formulas never match a propositional rule (not `.imp`-shaped) nor a modal rule
(only `.box _`-shaped formulas reach `boxPos`/`boxNeg` in `modalApplyOne`'s `else` branch),
so `modalApplyOne` returns the constant `.notApplicable` for them regardless of `b`/`acc`. -/
private lemma modalApplyOne_fst_eq_of_not_box
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) (hnb : ∀ ψ, φ ≠ .box ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOne ⟨s, φ, w⟩ b acc).1 = (modalApplyOne ⟨s, φ, w⟩ b' acc').1 := by
  cases φ with
  | atom p =>
    cases s <;> simp [modalApplyOne, tryAllPropRules_pos, tryAllPropRules_neg, modalAndOf?,
      modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  | bot =>
    cases s <;> simp [modalApplyOne, tryAllPropRules_pos, tryAllPropRules_neg, modalAndOf?,
      modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  | imp a c =>
    cases s with
    | pos => rw [modalApplyOne_imp_pos, modalApplyOne_imp_pos]
    | neg => rw [modalApplyOne_imp_neg, modalApplyOne_imp_neg]
  | box ψ => exact absurd rfl (hnb ψ)

/-- Lifting lemma for the box-excluded rule-application clause: if it holds for `⟨s, φ, w⟩`
against branch `b`/`acc`, it holds against any superset branch `b'` with any `acc'` (for
non-`box` `φ`; `box`-shaped `φ` is vacuous on both sides). Used by
`modalStepBranch_hintikka_inv` to lift the invariant for `sf ∈ e` from the old branch to the
new one, since `modalApplyOne`'s output for non-`box` formulas does not depend on `b`/`acc`
(`modalApplyOne_fst_eq_of_not_box`), so growing the branch only grows the witness set. -/
private lemma modalHintikkaClause_lift
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) (hsub : b ⊆ b')
    (hInv : modalHintikkaClause s φ w b acc) :
    modalHintikkaClause s φ w b' acc' := by
  unfold modalHintikkaClause at hInv ⊢
  rcases φ with p | _ | ⟨a, c⟩ | ψ
  · have heq := modalApplyOne_fst_eq_of_not_box s (.atom p) w (by intro _ h; simp at h)
        b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (modalApplyOne (⟨s, .atom p, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := modalApplyOne_fst_eq_of_not_box s .bot w (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (modalApplyOne (⟨s, .bot, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := modalApplyOne_fst_eq_of_not_box s (.imp a c) w (by intro _ h; simp at h)
        b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (modalApplyOne (⟨s, .imp a c, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · trivial

omit [Hashable Atom] in
/-- When `modalStepBranch b e acc = none`, every formula on `b` is either already in the
expanded set `e` or has `modalApplyOne` (evaluated at `b`, `acc`) return `notApplicable`
(the branch is saturated). Port of `classicalStepBranch_none_saturated`
(`Classical/Completeness.lean:694`), threaded with `acc`. -/
lemma modalStepBranch_none_saturated
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    (hstep : modalStepBranch b e acc = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (modalApplyOne sf b acc).1 = .notApplicable := by
  simp only [modalStepBranch] at hstep
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
    simp only [hany] at hbody
    rcases hca : modalApplyOne sf b acc with ⟨res, newAcc⟩
    simp only [hca] at hbody
    rcases res with out | brs | out | _
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · rfl

/-- If the rule-application invariant holds for branch `b` against expanded set `e` (every
non-`box`-shaped formula in `e` has its `modalApplyOne` output already present on `b`), then
after one step `modalStepBranch b e acc = some (newBs, newExps, newAcc)`, the invariant
holds for every new branch `b'` paired with its own new expanded set from `newExps`.

Port of `classicalStepBranch_hintikka_inv` (`Classical/Completeness.lean:722`). Two
modal-specific adjustments: (1) the invariant is evaluated via `(modalApplyOne sf b acc).1`
and carves out `.box _`-shaped formulas (see the section note above); (2) the `.persistent`
case leaves the expanded set unchanged (`newExp = e`, not `e ++ [sf_exp]`), since `boxPos`
re-fires when new successors are added and is never marked expanded
(`Saturation.lean:116-117`) — so unlike the classical port's `.persistent` case (identical
to `.linear`), here there is no `sf = sf_exp` sub-case to discharge at all. -/
lemma modalStepBranch_hintikka_inv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hInv_b : ∀ sf ∈ e, modalHintikkaClause sf.sign sf.formula sf.label b acc) :
    ∀ p ∈ newBs.zip newExps, ∀ sf ∈ p.2,
      modalHintikkaClause sf.sign sf.formula sf.label p.1 newAcc := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf_exp, _, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hexp
  rcases hca : modalApplyOne sf_exp b acc with ⟨res, acc'⟩
  obtain ⟨s_exp, φ_exp, w_exp⟩ := sf_exp
  simp only [hca] at hfound
  rcases res with newForms | brs | newForms | _
  · -- linear: newBs = [newForms ++ b], newExps = [e ++ [sf_exp]], newAcc = acc'
    obtain ⟨rfl, rfl, rfl⟩ := hfound
    intro p hp sf hsfin
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    simp only [List.mem_singleton] at hp1 hp2
    obtain ⟨s, φ, w⟩ := sf
    rw [hp2, List.mem_append, List.mem_singleton] at hsfin
    rw [hp1]
    rcases hsfin with hsfin | heq
    · exact modalHintikkaClause_lift s φ w b (newForms ++ b) acc newAcc
        (fun _ hx => List.mem_append.mpr (Or.inr hx)) (hInv_b ⟨s, φ, w⟩ hsfin)
    · obtain ⟨rfl, rfl, rfl⟩ := heq
      unfold modalHintikkaClause
      rcases φ_exp with p' | _ | ⟨a, c⟩ | ψ
      · have heq2 := modalApplyOne_fst_eq_of_not_box s_exp (.atom p') w_exp
          (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · have heq2 := modalApplyOne_fst_eq_of_not_box s_exp .bot w_exp
          (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · have heq2 := modalApplyOne_fst_eq_of_not_box s_exp (.imp a c) w_exp
          (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · trivial
  · -- branching: newBs = brs.map (·++b), newExps = brs.map (fun _ => e++[sf_exp]), newAcc = acc'
    obtain ⟨rfl, rfl, rfl⟩ := hfound
    intro p hp sf hsfin
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    rw [List.mem_map] at hp1 hp2
    obtain ⟨x, hx, hx1⟩ := hp1
    obtain ⟨x', hx', hx2⟩ := hp2
    obtain ⟨s, φ, w⟩ := sf
    rw [← hx2, List.mem_append, List.mem_singleton] at hsfin
    rw [← hx1]
    rcases hsfin with hsfin | heq
    · exact modalHintikkaClause_lift s φ w b (x ++ b) acc newAcc
        (fun _ hx'' => List.mem_append.mpr (Or.inr hx'')) (hInv_b ⟨s, φ, w⟩ hsfin)
    · obtain ⟨rfl, rfl, rfl⟩ := heq
      unfold modalHintikkaClause
      rcases φ_exp with p' | _ | ⟨a, c⟩ | ψ
      · have heq2 := modalApplyOne_fst_eq_of_not_box s_exp (.atom p') w_exp
          (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · have heq2 := modalApplyOne_fst_eq_of_not_box s_exp .bot w_exp
          (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · have heq2 := modalApplyOne_fst_eq_of_not_box s_exp (.imp a c) w_exp
          (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · trivial
  · -- persistent: newBs = [newForms ++ b], newExps = [e] (unchanged), newAcc = acc'
    obtain ⟨rfl, rfl, rfl⟩ := hfound
    intro p hp sf hsfin
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    simp only [List.mem_singleton] at hp1 hp2
    obtain ⟨s, φ, w⟩ := sf
    rw [hp1]
    exact modalHintikkaClause_lift s φ w b (newForms ++ b) acc newAcc
      (fun _ hx => List.mem_append.mpr (Or.inr hx)) (hInv_b ⟨s, φ, w⟩ (hp2 ▸ hsfin))
  · simp at hfound

end Cslib.Logic.Modal.Tableau

end
